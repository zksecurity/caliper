import Caliper.Corpus.Util
import Caliper.Liveness

/-!
# Corpus: nested loops

* `InsertionSort`: in-place sort with nested `whileNZ` loops whose inner trip count
  is data-dependent, a guard that must itself branch (`ifNZ` inside the guard
  statement, since testing `b[j-1] > b[j]` is only legal once `j ≠ 0` is known), and
  swaps via `memStore`. The pins run the same length-6 input sorted,
  reverse-sorted and shuffled: three different times for one program.
* `MatMul3`: 3×3 matrix multiply through the builder surface, with triply nested
  `while_` loops, compound index expressions (`3*i + k`), and a result buffer filled
  by `push`.
-/

namespace Caliper.Corpus

open Caliper

variable {w : ℕ}

/-! ## Insertion sort -/

namespace InsertionSort

/--
```c
n = b.len; i = 1;
while (i < n) {
  j = i;
  while (j != 0 && b[j] < b[j-1]) {   // short-circuit via ifNZ in the guard
    swap(b[j-1], b[j]); j -= 1;
  }
  i += 1;
}
```
Registers: `r0` = `i`, `r1` = `n`, `r2` outer flag, `r3` = `j`, `r4` the
constant 1, `r5` = `j - 1`, `r6` = `b[j-1]`, `r7` = `b[j]`, `r8` inner flag.

The inner guard is a compound statement: it tests `j ≠ 0` first and only *then*
loads `b[j-1]`. The load's in-range obligation is what forces the short circuit,
since at `j = 0` the index `j - 1` wraps and has no `Exec` rule. The `ifNZ`'s else
branch is `skip`, leaving the flag 0, and the body reuses the guard's loaded
elements (`r6`/`r7`) for the swap.
-/
def code (b : BufId) : Stmt w :=
  .memLen 1 b ;;
  .imm 0 1 ;;
  .whileNZ (.bin .ult 2 0 1) 2
    (.mov 3 0 ;;
     .whileNZ
       (.un .isNonZero 8 3 ;;
        .ifNZ 8
          (.imm 4 1 ;;
           .bin .sub 5 3 4 ;;
           .memLoad 6 b 5 ;;
           .memLoad 7 b 3 ;;
           .bin .ult 8 7 6)
          .skip)
       8
       (.memStore b 5 7 ;;
        .memStore b 3 6 ;;
        .imm 4 1 ;;
        .bin .sub 3 3 4) ;;
     .imm 4 1 ;;
     .bin .add 0 0 4)

/-- Sort a length-6 buffer, returning `(contents, time, net, peak)`. -/
def runOn (arr : Array (Word 64)) : Option (Array (Word 64) × ℕ × ℤ × ℤ) :=
  (run .unit 100000 (code 0)
      { State.init 64 with
        bufs := fun b => if b = 0 then arr else #[]
        caps := fun b => if b = 0 then arr.size else 0 }).map
    fun (s, t, d, p) => (s.bufs 0, t, d, p)

/- Shuffled input. -/
/-- info: some (#[1#64, 2#64, 3#64, 4#64, 5#64, 6#64], 167, 0, 0) -/
#guard_msgs in
#eval runOn #[5, 2, 4, 6, 1, 3]

/- Already sorted: the inner loop never fires, the cheap case. -/
/-- info: some (#[1#64, 2#64, 3#64, 4#64, 5#64, 6#64], 69, 0, 0) -/
#guard_msgs in
#eval runOn #[1, 2, 3, 4, 5, 6]

/- Reverse sorted: every inner iteration fires, the worst case. -/
/-- info: some (#[1#64, 2#64, 3#64, 4#64, 5#64, 6#64], 224, 0, 0) -/
#guard_msgs in
#eval runOn #[6, 5, 4, 3, 2, 1]

/-- info: 9 -/
#guard_msgs in
#eval (code (w := 64) 0).regPeak₀

end InsertionSort

/-! ## 3×3 matrix multiply -/

namespace MatMul3

open Build in
/-- `C[i][j] = Σₖ A[3i+k] · B[3k+j]`, row-major, written entirely in the
builder surface: three nested `while_` loops, index arithmetic as compound
expressions, results pushed into `c` in row-major order. -/
def matmulB (a b c : Buf w) : Build w Unit := do
  let i ← var 0
  while_ (var ((i : Exp w) .< 3)) do
    let j ← var 0
    while_ (var ((j : Exp w) .< 3)) do
      let acc ← var 0
      let k ← var 0
      while_ (var ((k : Exp w) .< 3)) do
        let x ← a.load (3 * (i : Exp w) + k)
        let y ← b.load (3 * (k : Exp w) + j)
        acc <~ (acc : Exp w) + (x : Exp w) * y
        k <~ (k : Exp w) + 1
      c.push (acc : Exp w)
      j <~ (j : Exp w) + 1
    i <~ (i : Exp w) + 1

/-- The full program: reserve the 9-word result buffer (buffer 2, immediate capacity,
statically priced), then multiply buffers 0 and 1 into it. -/
def prog : Stmt 64 :=
  (Build.build (w := 64) do
    Build.emit (.memAllocI 2 9)
    matmulB ⟨0⟩ ⟨1⟩ ⟨2⟩).2

/--
```
    ⎡1 2 3⎤   ⎡9 8 7⎤   ⎡ 30  24  18⎤
    ⎢4 5 6⎥ · ⎢6 5 4⎥ = ⎢ 84  69  54⎥
    ⎣7 8 9⎦   ⎣3 2 1⎦   ⎣138 114  90⎦
```
`(result, time, net, peak)`, memory (9, 9): the result buffer, charged once at its
immediate allocation. -/
def demo : Option (Array (Word 64) × ℕ × ℤ × ℤ) :=
  (run .unit 100000 prog
      { State.init 64 with
        bufs := fun b =>
          if b = 0 then #[1, 2, 3, 4, 5, 6, 7, 8, 9]
          else if b = 1 then #[9, 8, 7, 6, 5, 4, 3, 2, 1] else #[]
        caps := fun b => if b = 0 ∨ b = 1 then 9 else 0 }).map
    fun (s, t, d, p) => (s.bufs 2, t, d, p)

/--
info: some (#[30#64, 24#64, 18#64, 84#64, 69#64, 54#64, 138#64, 114#64, 90#64], 544, 9, 9)
-/
#guard_msgs in
#eval demo

/- 22 registers: the conservative (fixpoint-free) loop widening of the
liveness analysis keeps every register the three nested loop bodies read
alive across the loop heads, so nearly all of the builder's temporaries
count toward the peak here. -/
/-- info: 22 -/
#guard_msgs in
#eval prog.regPeak₀

end MatMul3

end Caliper.Corpus
