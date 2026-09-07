# Programming Caliper

[Documentation](00-overview.md)

## Executable

`run C tape fuel c s` is a fuel-based reference interpreter; `run_sound` proves anything it returns is a genuine `Exec` derivation with the same costs, so `#eval` numbers are instances of the proved bounds (the examples check this with `#guard_msgs`).

`run` is a reference semantics, not a performance-realizing implementation.
Its `State` maps registers and buffer names through Lean functions, so every `setReg` stacks another closure and lookups walk the chain; the interpreter's own wall-clock time and heap usage are unrelated to the abstract cost `t` and profile `(d, p)` it computes.
A performant runner would be a separate artifact with its own refinement proof against `Exec`.

## Builder Definitions

The builder accumulates instructions and supplies fresh names.
Its state and expression types are defined in [Builder.lean](../Caliper/Builder.lean):

```lean
structure BuildState (w : ℕ) where
  nextReg : ℕ := 0
  nextBuf : ℕ := 0
  code : List (Stmt w) := []

def Build (w : ℕ) (α : Type) := BuildState w → α × BuildState w

inductive Exp (w : ℕ) where
  | reg (r : Reg)
  | lit (v : Word w)
  | un (op : UnOp) (e : Exp w)
  | bin (op : BinOp) (a b : Exp w)

structure Buf (w : ℕ) where
  id : BufId
deriving Repr
```

These are source excerpts from namespace `Caliper`.
`Build w α` returns an ordinary Lean value of type `α` together with updated builder state.
`Buf w` wraps a buffer name; it contains neither a pointer nor runtime data.

## Ergonomics

Programs can be written against the raw constructors (assembly-flavoured, what proofs are stated over) or through `Builder.lean`: a monad with `freshReg`/`freshBuf`, compound expressions (`x + y * z` compiling through fresh temporaries), `while_`/`if_`, and subroutines as ordinary Lean functions.
`freshReg` is a pure name counter: naming a register emits no code and costs nothing, and the register file's footprint is the statically inferred live peak, so there is no scoping ceremony and no lifetime to declare.
At the surface, buffers are the newtype `Buf w`, produced only by `Mem.alloc` (dynamic capacity) or `Mem.allocI` (immediate capacity, statically priced); reads, writes, pushes, pops, length and free are methods on the handle (`b.load i`, `b.store i e`, `b.push e`, `b.pop`, `b.len`, `b.free`).
In the core both `Reg` and `BufId` are `ℕ` (numeral-friendly proof goals), so the wrapper is what stops a buffer handle being confused with a register or an index.
Builder output is checked equal to the hand-written core syntax in the examples, so the sugar adds nothing to the trusted surface.
Subroutine *specs* are ordinary Lean theorems about the generated code (`SumBuf.spec`), reused at every call site.

Consider summing a buffer.
We allocate names for the accumulator, index, and length, then emit a loop.
This is `sumB` from [Examples.lean](../Caliper/Examples.lean), with imports and a separate namespace so the block can be checked on its own:

```lean
import Caliper.Builder

open Caliper Caliper.Build

namespace Documentation

variable {w : ℕ}

def sumB (xs : Buf w) : Build w Reg := do
  let acc ← var 0
  let i ← var 0
  let n ← xs.len
  while_ (var (i .< n)) do
    let tmp ← xs.load i
    acc <~ (acc : Exp w) + tmp
    i <~ (i : Exp w) + 1
  return acc

end Documentation
```

Generated programs are inspectable through the pretty-printer (`Stmt.render`, `Render.lean`), which prints the machine's assembly dialect: memory instructions carry the `mem.` qualifier, since Lean identifiers cannot contain dots, and `whileNZ` prints as a `loop { … }` whose guard ends in `bifz r<c>` (break-if-zero on the verdict register).
The hand-written buffer-summing program `SumBuf.code` renders as follows, pinned in `Examples.lean` by `#guard_msgs`; the builder version `sumB` emits exactly this program:

```text
imm   r0, 0
imm   r1, 0
mem.len   r2, b0
loop {
  ult  r3, r1, r2
  bifz r3
  mem.load  r4, b0[r1]
  add  r0, r0, r4
  imm   r5, 1
  add  r1, r1, r5
}
```

## Fixed 64-Bit Surface (`Caliper64`)

The core stays generic in the word size `w`, but for practical use `w = 64`, the word size of the intended backends.
`W64.lean` provides the namespace `Caliper64`: reducible `abbrev`s fixing `w := 64` for the types and entry points a program or spec author touches (`Word`, `Stmt`, `State`, `State.init`, `Exec`, `run`, `Triple`, `TimeTriple`, `SpaceTriple`, `Build`, `Exp`, `Buf`, `build`).
Import `Caliper.W64` and write against `Caliper64`; because the abbreviations are reducible, every generic theorem and proof rule applies definitionally.
Names that infer `w` from their arguments (the `Build` combinators, the `Triple` rules, `CostModel`, `Reg`, `BufId`) are used from `Caliper` unchanged.

For example, these definitions in namespace `Caliper64` simply fix the word width:

```lean
abbrev Word := Caliper.Word 64
abbrev Stmt := Caliper.Stmt 64
abbrev Triple := Caliper.Triple (w := 64)
abbrev Build := Caliper.Build 64
abbrev build {α : Type} (m : Build α) : α × Stmt := Caliper.Build.build m
```

The full list is in [W64.lean](../Caliper/W64.lean).

## A Program and Its Proof

We can see the entire pipeline on $3 + 4$: build the program, identify its instructions, prove its result and cost, and check the reference interpreter.
The following runnable example comes from [W64.lean](../Caliper/W64.lean):

```lean
import Caliper.W64

namespace Caliper64.Documentation

open Caliper.Build (var)

def sum34 : ℕ × Stmt := build do
  let x ← var 3
  let y ← var 4
  var ((x : Exp) + y)

example : sum34.2 = (.imm 0 3 ;; .imm 1 4 ;; .bin .add 2 0 1) := rfl

example :
    Triple .unit Caliper.RandomTape.zero (fun _ => True) sum34.2 (fun s => s.regs sum34.1 = 7) 3 0 0 := by
  intro s _
  refine ⟨_, _, _, _, .seq .imm (.seq .imm .bin), ?_, ?_, ?_, ?_⟩
  · simp [show sum34.1 = 2 from rfl, Caliper.State.setReg]
  · decide
  · simp
  · simp

example : (run .unit Caliper.RandomTape.zero 20 sum34.2 State.init).map (fun r => r.1.regs sum34.1)
    = some 7 := rfl

end Caliper64.Documentation
```

The bounds `3 0 0` mean at most three time units, zero net buffer growth, and zero peak buffer growth.
They do not say the program uses zero memory: its registers count in [SpaceBound](02-memory.md#the-static-register-metric-in-brief).
