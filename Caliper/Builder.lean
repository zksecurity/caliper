import Clean.Caliper.Core

/-!
# Surface syntax: the program builder

`Stmt` is deliberately austere — three-address code over registers and named buffers.
This file is the ergonomic layer for *writing* programs: a builder monad with

* automatic allocation of registers and buffer names (`freshReg`, `freshBuf`) —
  `freshReg` *emits* `regAlloc`, so builder programs pay for every register they
  acquire, and `Build.scope` (with the `RegCarrier` class) releases a block's
  temporaries when it ends,
* an expression language `Exp` that compiles compound arithmetic to three-address
  code through fresh temporaries,
* structured control flow (`if_`, `while_`) whose guards are builder actions, so
  guard *cost* is real emitted code, never a free side condition,
* subroutines as plain Lean functions `... → Build w α` — calling one splices its
  code in with fresh temporaries, so caller and callee cannot clash on registers.

Everything here is *generation-time only*: `build` runs the monad and returns a plain
`Stmt`, and that `Stmt` is what specs and cost theorems are about. The builder adds
nothing to the trusted surface — `Clean/Caliper/Examples.lean` checks by `rfl` that
builder output coincides with hand-written core syntax.

Data structures follow the same pattern: a "struct" is a Lean-level record of
registers/buffer names, an array-of-structs is a buffer with a stride convention, and
the accessor functions are ordinary Lean functions emitting indexing code. Because
buffer names are static, two different structures can never alias.
-/

namespace Caliper

variable {w : ℕ}

/-- Builder state: fresh-name counters and the code emitted so far (in order). -/
structure BuildState (w : ℕ) where
  nextReg : ℕ := 0
  nextBuf : ℕ := 0
  /-- Emitted code, in **reverse** order (prepending keeps generation linear;
  `capture`/`build` reverse once at the end). -/
  code : List (Stmt w) := []

/-- The program-builder monad. -/
def Build (w : ℕ) (α : Type) := BuildState w → α × BuildState w

namespace Build

instance : Monad (Build w) where
  pure a := fun s => (a, s)
  bind m f := fun s => let (a, s') := m s; f a s'

/-- Allocate a fresh register name **and emit `regAlloc` for it**: builder-produced
programs pay for every register they acquire — one word of live memory, one tick
(see `Stmt.regAlloc`). Pair with `Build.scope` to release temporaries when a block
ends. -/
def freshReg : Build w Reg :=
  fun s => (s.nextReg,
    { s with nextReg := s.nextReg + 1, code := .regAlloc s.nextReg :: s.code })

def freshBuf : Build w BufId :=
  fun s => (s.nextBuf, { s with nextBuf := s.nextBuf + 1 })

def emit (c : Stmt w) : Build w Unit :=
  fun s => ((), { s with code := c :: s.code })

/-- Right-nested sequencing of a code list (no trailing `skip`). -/
def seqAll : List (Stmt w) → Stmt w
  | [] => .skip
  | [c] => c
  | c :: cs => c ;; seqAll cs

/-- Run a sub-builder, capturing its code instead of emitting it. Fresh-name counters
keep advancing, so captured blocks never clash with the surrounding code. -/
def capture {α : Type} (m : Build w α) : Build w (α × Stmt w) := fun s =>
  let (a, s') := m { s with code := [] }
  ((a, seqAll s'.code.reverse), { s' with code := s.code })

/-- Run a builder to completion, returning its result and the generated program. -/
def build {α : Type} (m : Build w α) : α × Stmt w :=
  let (a, s) := m {}
  (a, seqAll s.code.reverse)

/-! ## Control flow -/

/-- `if_ c thn els`: branch on register `c`. -/
def if_ (c : Reg) (thn : Build w Unit) (els : Build w Unit := pure ()) :
    Build w Unit := do
  let (_, tc) ← capture thn
  let (_, ec) ← capture els
  emit (.ifNZ c tc ec)

/-- `while_ guard body`: the guard is a builder action returning the register its
verdict lands in; its code runs before every iteration check, and is billed there. -/
def while_ (guard : Build w Reg) (body : Build w Unit) : Build w Unit := do
  let (r, gc) ← capture guard
  let (_, bc) ← capture body
  emit (.whileNZ gc r bc)

end Build

/-! ## Register scoping

`Build.freshReg` emits `regAlloc`, so every builder temporary holds a word of live
memory from the moment it is named. `Build.scope` is the structured way to give
those words back: it runs a block and emits `regFree` for every register the block
allocated, **except** the ones its result consists of. Which registers a result
keeps live is what the `RegCarrier` instance of the result type says. -/

/-- Types whose values name the registers they keep live — what a scoped block's
*result* consists of, so `Build.scope` knows which registers must survive the
block. Instances exist for `Reg`, `Unit`, `Buf` (a buffer handle pins no
registers), `PairR`, products, `Option`, and `Fp` (`Field.lean`). -/
class RegCarrier (α : Type) where
  /-- The registers the value keeps live (they escape any enclosing scope). -/
  regsOf : α → List Reg

export RegCarrier (regsOf)

instance : RegCarrier Reg := ⟨fun r => [r]⟩
instance : RegCarrier Unit := ⟨fun _ => []⟩
instance {α β : Type} [RegCarrier α] [RegCarrier β] : RegCarrier (α × β) :=
  ⟨fun p => regsOf p.1 ++ regsOf p.2⟩
instance {α : Type} [RegCarrier α] : RegCarrier (Option α) :=
  ⟨fun | none => [] | some a => regsOf a⟩

namespace Build

/-- Run `m` and release its register temporaries: every register allocated inside
`m` (tracked by the `nextReg` counter delta — fresh names are handed out in
order) gets a `regFree`, except those in `regsOf` of the result. Frees are
emitted in **reverse allocation order** (stack-like). Freed names are never
reused — fresh-name monotonicity — which is fine: the liveness *count* is what
the memory profile meters, and a lowering can interval-color disciplined
(bracket-nested) lifetimes onto physical slots, so peak live count = slots
needed. -/
def scope {α : Type} [RegCarrier α] (m : Build w α) : Build w α := fun s =>
  let (a, s') := m s
  let keep := RegCarrier.regsOf a
  let toFree :=
    (List.range' s.nextReg (s'.nextReg - s.nextReg)).filter (fun r => !keep.contains r)
  (a, { s' with code := (toFree.map .regFree) ++ s'.code })

end Build

/-! ## Expressions

Compound arithmetic, compiled to three-address code through fresh temporaries.
`ℕ`-typed variables coerce as *registers*; numeric literals are word *constants*. -/

inductive Exp (w : ℕ) where
  | reg (r : Reg)
  | lit (v : Word w)
  | un (op : UnOp) (e : Exp w)
  | bin (op : BinOp) (a b : Exp w)

instance : Coe Reg (Exp w) := ⟨.reg⟩
instance {n : ℕ} : OfNat (Exp w) n := ⟨.lit (BitVec.ofNat w n)⟩
instance : Add (Exp w) := ⟨.bin .add⟩
instance : Sub (Exp w) := ⟨.bin .sub⟩
instance : Mul (Exp w) := ⟨.bin .mul⟩
instance : Div (Exp w) := ⟨.bin .udiv⟩
instance : Mod (Exp w) := ⟨.bin .umod⟩
instance : AndOp (Exp w) := ⟨.bin .and⟩
instance : OrOp (Exp w) := ⟨.bin .or⟩
instance : XorOp (Exp w) := ⟨.bin .xor⟩

/-- High word of the widening multiply (see `BinOp.mulhi`). -/
def Exp.mulhi (a b : Exp w) : Exp w := .bin .mulhi a b

/-- Unsigned less-than, valued in {0, 1}. -/
notation:50 a:51 " .< " b:51 => Exp.bin BinOp.ult a b
/-- Equality test, valued in {0, 1}. -/
notation:50 a:51 " .== " b:51 => Exp.bin BinOp.eq a b
/-- Disequality test, valued in {0, 1}. -/
notation:50 a:51 " .!= " b:51 => Exp.bin BinOp.ne a b

namespace Build

/-- Compile an expression; the result register holds its value. A bare register
compiles to itself (no code). -/
def compileExp : Exp w → Build w Reg
  | .reg r => pure r
  | .lit v => do
    let d ← freshReg
    emit (.imm d v)
    return d
  | .un op e => do
    let a ← compileExp e
    let d ← freshReg
    emit (.un op d a)
    return d
  | .bin op x y => do
    let a ← compileExp x
    let b ← compileExp y
    let d ← freshReg
    emit (.bin op d a b)
    return d

/-- `assign d e` — `d ← e`, compiling operands as needed. -/
def assign (d : Reg) (e : Exp w) : Build w Unit := do
  match e with
  | .reg a => emit (.mov d a)
  | .lit v => emit (.imm d v)
  | .un op a => do
    let ra ← compileExp a
    emit (.un op d ra)
  | .bin op a b => do
    let ra ← compileExp a
    let rb ← compileExp b
    emit (.bin op d ra rb)

@[inherit_doc] infix:20 " <~ " => assign

/-- Declare a fresh register initialized to `e` — `let x ← var e`. -/
def var (e : Exp w) : Build w Reg := do
  let d ← freshReg
  assign d e
  return d

end Build

/-! ## Buffers

At the surface, buffers are handled through the newtype `Buf w`, not raw `BufId`s.
`Reg` and `BufId` are both `ℕ` in the core (which keeps proof goals numeral-friendly),
so without the wrapper a buffer name could be passed where a register — or an
arbitrary index — was expected. The newtype prevents *accidental* mixing of the
three; it is not an enforced capability: the constructor stays public (tests write
`⟨0⟩` directly), so the intended source `Mem.alloc` is a convention, not a
guarantee.

Allocation lives in the `Mem` namespace (`Mem.alloc`/`Mem.allocI` — the two ways to
obtain a handle); everything that already *has* a handle is a method on `Buf`
(`Buf.load`, `Buf.store`, `Buf.push`, `Buf.pop`, `Buf.len`, `Buf.free`), so buffer
code reads as `b.push e`, `b.load i`, `b.free`. -/

/-- Typed handle to a buffer of `w`-bit words. Obtain one from `Mem.alloc` or
`Mem.allocI`. -/
structure Buf (w : ℕ) where
  id : BufId
deriving Repr

/-- A buffer handle keeps no registers live (its name is syntax, not a register). -/
instance : RegCarrier (Buf w) := ⟨fun _ => []⟩

namespace Mem

/-- Allocate a fresh buffer with capacity `n` (an expression, evaluated at runtime).
The capacity is charged now; pushes into it are memory-free. Emits a *dynamic*
`memAlloc`, whose time charge `C.memAlloc + cap * C.allocPerWord` depends on the
runtime capacity — the emitted code is therefore not `Stmt.Straight`. When the
capacity is known at generation time, prefer `Mem.allocI`, which is statically
priced. -/
def alloc (n : Exp w) : Build w (Buf w) := do
  let rn ← Build.compileExp n
  let b ← Build.freshBuf
  Build.emit (.memAlloc b rn)
  return ⟨b⟩

/-- Allocate a fresh buffer with the *immediate* capacity `n`, emitting `memAllocI`:
one instruction, no capacity register, and the time charge
`C.memAlloc + n * C.allocPerWord` is a syntactic constant, so the emitted code
stays `Stmt.Straight` (statically priced). Semantics are identical to `Mem.alloc`
at that capacity.

The immediate capacity of `Stmt.memAllocI` is a bare `ℕ` — unlike `Mem.alloc`,
whose capacity comes from a `w`-bit register and is therefore `< 2 ^ w`. An
oversized immediate (`n ≥ 2 ^ w`) would let the fill level grow past `2 ^ w`, at
which point `memLen` reads back a *wrapped* length while every theorem still
holds. The autoparam closes that hole at the builder surface: `Mem.allocI`
requires `n < 2 ^ w`, discharged by `norm_num` at concrete capacities (and
suppliable explicitly otherwise). The proof is not threaded anywhere — it exists
purely so that builder-produced programs keep `memLen` exact. -/
def allocI (n : ℕ) (_h : n < 2 ^ w := by norm_num) : Build w (Buf w) := do
  let b ← Build.freshBuf
  Build.emit (.memAllocI b n)
  return ⟨b⟩

end Mem

namespace Buf

/-- Read `b[i]` into a fresh register. -/
def load (b : Buf w) (i : Exp w) : Build w Reg := do
  let ri ← Build.compileExp i
  let d ← Build.freshReg
  Build.emit (.memLoad d b.id ri)
  return d

/-- Write `b[i] ← e`. -/
def store (b : Buf w) (i e : Exp w) : Build w Unit := do
  let ri ← Build.compileExp i
  let re ← Build.compileExp e
  Build.emit (.memStore b.id ri re)

/-- Append `e` to `b`. -/
def push (b : Buf w) (e : Exp w) : Build w Unit := do
  let re ← Build.compileExp e
  Build.emit (.memPush b.id re)

/-- Drop `b`'s last element (a no-op on an empty buffer; keeps the capacity). -/
def pop (b : Buf w) : Build w Unit :=
  Build.emit (.memPop b.id)

/-- Length of `b`, in a fresh register. -/
def len (b : Buf w) : Build w Reg := do
  let d ← Build.freshReg
  Build.emit (.memLen d b.id)
  return d

/-- Release `b`'s capacity. -/
def free (b : Buf w) : Build w Unit :=
  Build.emit (.memFree b.id)

end Buf

/-! ## Product types

A struct is *generation-time* data: scalar fields live in a Lean record of registers,
and an array-of-structs is one buffer with a stride convention. Field access compiles
to index arithmetic on the underlying buffer, so its cost (a multiply, an add, a read)
is fully visible to the cost model — the abstraction adds nothing trusted. `PairBuf`
below is the two-field case; an n-field record is the same construction with stride n
(and generating the accessors from a field list is ordinary Lean metaprogramming).

Because each `PairBuf` owns its own buffer name, two arrays-of-structs can never
alias, and framing across them is the usual decidable `Touches` check. -/

/-- A pair of words held in registers (a "local struct"). -/
structure PairR (w : ℕ) where
  fst : Reg
  snd : Reg

/-- A register pair keeps both its registers live. -/
instance : RegCarrier (PairR w) := ⟨fun p => [p.fst, p.snd]⟩

/-- Allocate a fresh local pair. -/
def Build.mkPairR : Build w (PairR w) := do
  let a ← Build.freshReg
  let b ← Build.freshReg
  return ⟨a, b⟩

/-- An array of pairs: one buffer, stride 2, fields interleaved. -/
structure PairBuf (w : ℕ) where
  buf : Buf w

/-- Allocate an array of pairs with room for `nPairs` entries (2·nPairs words,
charged now — pushes are then memory-free). -/
def Build.mkPairBuf (nPairs : Exp w) : Build w (PairBuf w) := do
  let b ← Mem.alloc (2 * nPairs)
  return ⟨b⟩

namespace PairBuf

/-- Append a pair: two pushes, requiring two words of free capacity. -/
def push (pb : PairBuf w) (x y : Exp w) : Build w Unit := do
  pb.buf.push x
  pb.buf.push y

/-- Number of pairs, in a fresh register. -/
def size (pb : PairBuf w) : Build w Reg := do
  let n ← pb.buf.len
  Build.var ((n : Exp w) / 2)

/-- First component of pair `i`. -/
def fst (pb : PairBuf w) (i : Exp w) : Build w Reg :=
  pb.buf.load (2 * i)

/-- Second component of pair `i`. -/
def snd (pb : PairBuf w) (i : Exp w) : Build w Reg :=
  pb.buf.load (2 * i + 1)

end PairBuf

end Caliper
