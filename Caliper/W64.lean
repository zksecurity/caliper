import Clean.Caliper.Triple
import Clean.Caliper.Builder
import Clean.Caliper.Field

/-!
# Caliper at word size 64

The Caliper core (`Clean/Caliper/Core.lean` and friends) is generic over the word
size `w`, but for all practical use — in particular Clean's witgen backend — the word
size is 64. This file is the surface programs and specs should be written against:
a thin layer of **reducible abbreviations** (`abbrev`) fixing `w := 64`, so that

* user code never mentions `w`, and
* every generic theorem still applies *definitionally* — nothing is redefined and no
  theorem is restated; `Caliper64.Stmt` *is* `Caliper.Stmt 64` up to `rfl`.

Only names where a user would otherwise write `(w := 64)` or a `w`-annotated type are
covered. Everything that infers `w` from its arguments (the `Build` combinators
`var`/`while_`/`Mem.alloc`/the `Buf` methods/…, the `Triple` proof rules,
`CostModel`, `Reg`, `BufId`, …)
is used directly from the `Caliper` namespace, unchanged.

The demo at the end writes a small program and proves a `Triple` about it entirely
through `Caliper64` names — the word size never appears.
-/

namespace Caliper64

/-! ## Types -/

/-- 64-bit machine words. -/
abbrev Word := Caliper.Word 64

/-- Statements over 64-bit words. -/
abbrev Stmt := Caliper.Stmt 64

/-- Machine state with 64-bit registers and buffers. -/
abbrev State := Caliper.State 64

/-- The initial state: all registers zero, all buffers empty and unallocated. -/
abbrev State.init : State := Caliper.State.init 64

/-! ## Semantics -/

/-- Cost semantics at word size 64: `Exec C c s s' t d p`. -/
abbrev Exec := Caliper.Exec (w := 64)

/-- The reference interpreter at word size 64. -/
abbrev run := Caliper.run (w := 64)

/-! ## Program logic -/

/-- Total-correctness triple with time, net-memory and peak-memory bounds. -/
abbrev Triple := Caliper.Triple (w := 64)

/-- Time-only total-correctness triple. -/
abbrev TimeTriple := Caliper.TimeTriple (w := 64)

/-- Space-only total-correctness triple. -/
abbrev SpaceTriple := Caliper.SpaceTriple (w := 64)

/-! ## Surface syntax -/

/-- The program-builder monad at word size 64. -/
abbrev Build := Caliper.Build 64

/-- Expressions over 64-bit words. -/
abbrev Exp := Caliper.Exp 64

/-- Typed handle to a buffer of 64-bit words. -/
abbrev Buf := Caliper.Buf 64

/-- Run a builder to completion, returning its result and the generated program. -/
abbrev build {α : Type} (m : Build α) : α × Stmt := Caliper.Build.build m

/-! ## Field arithmetic -/

/-- A canonical element of `ZMod p` in a 64-bit register. -/
abbrev Fp (p : ℕ) := Caliper.Fp 64 p

/-! ## Demo: `w` never appears

A small program through the surface syntax, its generated code, one `Triple` about
it, and an interpreter run — all stated purely in `Caliper64` names. Because the
abbreviations are reducible, the generic rules (`Caliper.Triple.imm`, the `Exec`
constructors, …) apply as-is. -/

namespace Demo

open Caliper.Build (var)

/-- `x ← 3; y ← 4; r ← x + y`: the result register together with the generated
program. Each `var` acquires its register explicitly (`freshReg` emits
`regAlloc`), so the three words the program keeps live are visible instructions. -/
def sum34 : ℕ × Stmt := build do
  let x ← var 3
  let y ← var 4
  var ((x : Exp) + y)

/-- The builder emitted the three-instruction sum plus the three explicit
register acquisitions. -/
example : sum34.2 = (.regAlloc 0 ;; .imm 0 3 ;; .regAlloc 1 ;; .imm 1 4 ;;
    .regAlloc 2 ;; .bin .add 2 0 1) := rfl

/-- The sum lands in the result register within 6 unit-cost instructions — the
3 ALU/imm steps plus one tick per register acquired — holding at most the 3
register words of live memory. -/
example :
    Triple .unit (fun _ => True) sum34.2 (fun s => s.regs sum34.1 = 7) 6 3 3 := by
  intro s _
  refine ⟨_, _, _, _,
    .seq .regAlloc (.seq .imm (.seq .regAlloc (.seq .imm (.seq .regAlloc .bin)))),
    ?_, ?_, ?_, ?_⟩
  · simp [show sum34.1 = 2 from rfl, Caliper.State.setReg]
  · decide
  · simp
    omega
  · simp
    omega

/-- The reference interpreter agrees. -/
example : (run .unit 20 sum34.2 State.init).map (fun r => r.1.regs sum34.1)
    = some 7 := rfl

end Demo

end Caliper64
