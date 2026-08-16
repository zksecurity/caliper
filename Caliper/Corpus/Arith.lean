import Caliper.Corpus.Util
import Caliper.Liveness
import Caliper.Render

/-!
# Corpus: arithmetic programs

* `DotProduct`: two buffers folded into an accumulator, with a proved `Triple` for
  functional correctness, linear time and zero memory.
* `Gcd`: Euclid's algorithm, a loop whose trip count is data-dependent and whose
  termination measure is the *value* of a register rather than a counter. Proved
  `Triple` with functional spec `Nat.gcd` and a linear-in-`b` time bound.
* `BinExp`: binary exponentiation over a runtime exponent, i.e. loop, branch and
  shifts.
* `Popcount`: shift/mask population count.
* `DivMod`: straight-line div/mod recomposition (`udiv`/`umod`/`mulhi`/`eq`), with
  its exact static time read off the syntax by `staticTime?`.
* `BitTricks`: branchless `min` (`ule`/`neg`/`xor`/`and`), a power-of-two test
  (`isZero`/`isNonZero`), and a 32-bit pack/unpack round trip
  (`shl`/`or`/`shr`/`ne`/`not`), all straight-line with `staticTime?` pins.
-/

namespace Caliper.Corpus

open Caliper

variable {w : ℕ}

/-! ## Dot product -/

namespace DotProduct

/--
```c
acc = 0; i = 0; n = xs.len;
while (i < n) { acc += xs[i] * ys[i]; i += 1; }
```
Registers: `r0` accumulator, `r1` index, `r2` length, `r3` loop flag,
`r4`/`r5` elements, `r6` product, `r7` the constant 1. Read-only on both buffers, so
no separation fact is needed and the two buffer names may even coincide.
-/
def code (xs ys : BufId) : Stmt w :=
  .imm 0 0 ;;
  .imm 1 0 ;;
  .memLen 2 xs ;;
  .whileNZ (.bin .ult 3 1 2) 3
    (.memLoad 4 xs 1 ;;
     .memLoad 5 ys 1 ;;
     .bin .mul 6 4 5 ;;
     .bin .add 0 0 6 ;;
     .imm 7 1 ;;
     .bin .add 1 1 7)

/-- Dot product of the first `n` positions (the specification-side function). -/
def dotTo (xs ys : Array (Word w)) : ℕ → Word w
  | 0 => 0
  | n + 1 => dotTo xs ys n +
      (if h : n < xs.size ∧ n < ys.size then xs[n]'h.1 * ys[n]'h.2 else 0)

/-- Loop invariant, indexed by the remaining-iterations budget `k`. -/
def Inv (xs ys : BufId) (aX aY : Array (Word w)) (k : ℕ) (s : State w) : Prop :=
  s.bufs xs = aX ∧
  s.bufs ys = aY ∧
  s.regs 2 = BitVec.ofNat w aX.size ∧
  (s.regs 1).toNat + k = aX.size ∧
  s.regs 0 = dotTo aX aY (s.regs 1).toNat

/-- Invariant after the guard: additionally `r3` holds the comparison verdict. -/
def InvG (xs ys : BufId) (aX aY : Array (Word w)) (k : ℕ) (s : State w) : Prop :=
  Inv xs ys aX aY k s ∧
  s.regs 3 = if (s.regs 1).toNat < aX.size then 1 else 0

/-- Linear time: 3 setup instructions, `n + 1` guard evaluations, `n` bodies. -/
def timeBound (C : CostModel) (n : ℕ) : ℕ :=
  2 * C.imm + C.memLen + (n + 1) * (C.bin .ult + C.branch)
    + n * (2 * C.memLoad + C.bin .mul + C.bin .add + C.imm + C.bin .add)

/-- The dot product is correct, linear-time and allocation-free: `r0` ends holding
`Σᵢ xs[i] * ys[i]` in wrapping word arithmetic, within `timeBound C n` and memory
(0, 0), for any cost model. -/
theorem spec {C : CostModel} (xs ys : BufId) (aX aY : Array (Word w))
    (hsz : aX.size < 2 ^ w) (hlen : aY.size = aX.size) :
    Triple C (fun s => s.bufs xs = aX ∧ s.bufs ys = aY) (code xs ys)
      (fun s => s.regs 0 = dotTo aX aY aX.size)
      (timeBound C aX.size) 0 0 := by
  have hguard : ∀ k, Triple C (Inv xs ys aX aY k) (.bin .ult 3 1 2)
      (InvG xs ys aX aY k) (C.bin .ult) 0 0 := by
    intro k
    apply Triple.bin
    rintro s ⟨hbx, hby, hn, hik, hacc⟩
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [hbx]
    · simp [hby]
    · simp [hn]
    · simp [hik]
    · simp [hacc]
    · simp [hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz]
  have hpos : ∀ k s, InvG xs ys aX aY k s → s.regs 3 ≠ 0 → ∃ k', k = k' + 1 := by
    rintro k s ⟨⟨hbx, hby, hn, hik, hacc⟩, hflag⟩ hnz
    have hlt := cond_of_flag_ne hflag hnz
    exact ⟨k - 1, by omega⟩
  have hbody : ∀ k, Triple C (fun s => InvG xs ys aX aY (k + 1) s ∧ s.regs 3 ≠ 0)
      (.memLoad 4 xs 1 ;; .memLoad 5 ys 1 ;; .bin .mul 6 4 5 ;;
       .bin .add 0 0 6 ;; .imm 7 1 ;; .bin .add 1 1 7)
      (Inv xs ys aX aY k)
      (C.memLoad + (C.memLoad + (C.bin .mul + (C.bin .add + (C.imm + C.bin .add)))))
      0 0 := by
    rintro k s ⟨⟨⟨hbx, hby, hn, hik, hacc⟩, hflag⟩, hnz⟩
    have hlt : (s.regs 1).toNat < aX.size := cond_of_flag_ne hflag hnz
    have hltx : (s.regs 1).toNat < (s.bufs xs).size := by rw [hbx]; exact hlt
    have hlty : ((s.setReg 4 (s.bufs xs)[(s.regs 1).toNat]).regs 1).toNat
        < ((s.setReg 4 (s.bufs xs)[(s.regs 1).toNat]).bufs ys).size := by
      show (s.regs 1).toNat < (s.bufs ys).size
      rw [hby]
      omega
    refine ⟨_, _, _, _,
      .seq (.memLoad hltx) (.seq (.memLoad hlty) (.seq .bin (.seq .bin (.seq .imm .bin)))),
      ⟨?_, ?_, ?_, ?_, ?_⟩, le_refl _, by omega, by omega⟩
    · simp [hbx]
    · simp [hby]
    · simp [hn]
    · simp [-BitVec.toNat_add]
      rw [toNat_add_ofNat_one hlt hsz]
      omega
    · simp [-BitVec.toNat_add, hbx, hby]
      rw [toNat_add_ofNat_one hlt hsz]
      simp [dotTo, hlt, hlt.trans_le hlen.ge, hacc]
  have h1 : Triple C (fun s => s.bufs xs = aX ∧ s.bufs ys = aY) (.imm 0 0)
      (fun s => s.bufs xs = aX ∧ s.bufs ys = aY ∧ s.regs 0 = 0) C.imm 0 0 :=
    Triple.imm fun s hs => by simp [hs.1, hs.2]
  have h2 : Triple C (fun s => s.bufs xs = aX ∧ s.bufs ys = aY ∧ s.regs 0 = 0)
      (.imm 1 0)
      (fun s => s.bufs xs = aX ∧ s.bufs ys = aY ∧ s.regs 0 = 0 ∧ s.regs 1 = 0)
      C.imm 0 0 :=
    Triple.imm fun s hs => by simp [hs.1, hs.2.1, hs.2.2]
  have h3 : Triple C
      (fun s => s.bufs xs = aX ∧ s.bufs ys = aY ∧ s.regs 0 = 0 ∧ s.regs 1 = 0)
      (.memLen 2 xs) (Inv xs ys aX aY aX.size) C.memLen 0 0 := by
    apply Triple.memLen
    rintro s ⟨hbx, hby, h0, h1'⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [hbx]
    · simp [hby]
    · simp [hbx]
    · simp [h1']
    · simp [h0, h1', dotTo]
  have hW := Triple.whileNZ_measure hguard hpos hbody aX.size
  refine ((h1.seq (h2.seq (h3.seq hW))).conseq (fun _ h => h) ?_
    (le_of_eq (by unfold timeBound; ring)) (by simp) (by simp))
  rintro s ⟨k', ⟨⟨hbx, hby, hn, hik, hacc⟩, hflag⟩, hzero⟩
  by_cases hc : (s.regs 1).toNat < aX.size
  · exfalso
    rw [hflag] at hzero
    exact not_cond_of_flag_zero (by omega) hzero hc
  · have hi : (s.regs 1).toNat = aX.size := by omega
    rw [hacc, hi]

/-- `⟨1,2,3⟩ · ⟨4,5,6⟩ = 32`: `(value, time, net, peak)`, with time
`29 = timeBound .unit 3`, an instance of `spec`. -/
def demo : Option (Word 64 × ℕ × ℤ × ℤ) :=
  (run .unit 1000 (code 0 1)
      { State.init 64 with
        bufs := fun b => if b = 0 then #[1, 2, 3] else if b = 1 then #[4, 5, 6] else #[]
        caps := fun b => if b = 0 ∨ b = 1 then 3 else 0 }).map
    fun (s, t, d, p) => (s.regs 0, t, d, p)

/-- info: some (32#64, 29, 0, 0) -/
#guard_msgs in
#eval demo

/-- info: 8 -/
#guard_msgs in
#eval (code (w := 64) 0 1).regPeak₀

end DotProduct

/-! ## Euclid's gcd -/

namespace Gcd

/--
```c
while (b != 0) { t = a % b; a = b; b = t; }
```
`a` in `r0`, `b` in `r1`; `r2` loop flag, `r3` the remainder. The result
lands in `r0`. The trip count is data-dependent; the termination measure of
the proof is the *value* of `r1`, which `a % b < b` strictly decreases.
-/
def code : Stmt w :=
  .whileNZ (.un .isNonZero 2 1) 2
    (.bin .umod 3 0 1 ;;
     .mov 0 1 ;;
     .mov 1 3)

open Build in
/-- The same program through the builder surface: two `Build.input`s, the first
registers declared (r0 and r1, which the caller preloads), then a structured `while`
with an expression guard. The `#eval` below pins that the sugar compiles to exactly
the hand-written core code. -/
def gcdB : Build w Unit := do
  let a ← Build.input
  let b ← Build.input
  Build.while_ (Build.var (.un .isNonZero (b : Exp w))) do
    let t ← Build.var ((a : Exp w) % (b : Exp w))
    a <~ ((b : Reg) : Exp w)
    b <~ ((t : Reg) : Exp w)

/-- info: true -/
#guard_msgs in
#eval (Build.build (gcdB (w := 64))).2 == code

/-- Loop invariant: the gcd of the register pair is pinned to the input gcd,
and `r1` (the strictly decreasing value) is bounded by the measure `k`. -/
def Inv (a b : Word w) (k : ℕ) (s : State w) : Prop :=
  Nat.gcd (s.regs 1).toNat (s.regs 0).toNat = Nat.gcd b.toNat a.toNat ∧
  (s.regs 1).toNat ≤ k

/-- Invariant after the guard: additionally `r2` holds the nonzero verdict. -/
def InvG (a b : Word w) (k : ℕ) (s : State w) : Prop :=
  Inv a b k s ∧
  s.regs 2 = if s.regs 1 = 0 then 0 else 1

/-- Linear-in-`b` time, a sound but modest bound, the true worst case being
logarithmic: `b + 1` guard evaluations, at most `b` bodies. -/
def timeBound (C : CostModel) (b : ℕ) : ℕ :=
  (b + 1) * (C.un .isNonZero + C.branch) + b * (C.bin .umod + 2 * C.mov)

/-- Euclid terminates with the gcd, in time linear in `b`. The loop rule's measure
is instantiated with the *value* of `r1`: each iteration replaces it by `a % b < b`.
`0 < w` keeps the flag readable, 1 being 0 in a 0-bit word. Time-only judgment; the
memory side is below. -/
theorem time_spec {C : CostModel} (hw : 0 < w) (a b : Word w) :
    TimeTriple C (fun s => s.regs 0 = a ∧ s.regs 1 = b) (code (w := w))
      (fun s => (s.regs 0).toNat = Nat.gcd a.toNat b.toNat)
      (timeBound C b.toNat) := by
  have hguard : ∀ k, TimeTriple C (Inv a b k) (.un .isNonZero 2 1)
      (InvG a b k) (C.un .isNonZero) := by
    intro k
    apply TimeTriple.un
    rintro s ⟨hg, hk⟩
    -- the flag write leaves r0/r1 alone (definitionally), and the flag's
    -- value *is* the `isNonZero` verdict
    exact ⟨⟨hg, hk⟩, rfl⟩
  have hpos : ∀ k (s : State w), InvG a b k s → s.regs 2 ≠ 0 → ∃ k', k = k' + 1 := by
    rintro k s ⟨⟨hg, hk⟩, hflag⟩ hnz
    have hb : s.regs 1 ≠ 0 := by
      intro h0
      rw [h0, if_pos rfl] at hflag
      exact hnz hflag
    have := toNat_ne_zero hb
    exact ⟨k - 1, by omega⟩
  have hbody : ∀ k, TimeTriple C (fun (s : State w) => InvG a b (k + 1) s ∧ s.regs 2 ≠ 0)
      (.bin .umod 3 0 1 ;; .mov 0 1 ;; .mov 1 3)
      (Inv a b k) (C.bin .umod + (C.mov + C.mov)) := by
    rintro k s ⟨⟨⟨hg, hk⟩, hflag⟩, hnz⟩
    have hb : s.regs 1 ≠ 0 := by
      intro h0
      rw [h0, if_pos rfl] at hflag
      exact hnz hflag
    have hbpos : 0 < (s.regs 1).toNat := Nat.pos_of_ne_zero (toNat_ne_zero hb)
    have hmod : (s.regs 0 % s.regs 1).toNat < (s.regs 1).toNat := by
      rw [BitVec.toNat_umod]
      exact Nat.mod_lt _ hbpos
    refine ⟨_, _, _, _, .seq .bin (.seq .mov .mov), ⟨?_, ?_⟩, le_refl _⟩
    -- after `t ← a % b; a ← b; b ← t`, register reads reduce definitionally:
    -- the new (r1, r0) pair is (a % b, b)
    · show Nat.gcd (s.regs 0 % s.regs 1).toNat (s.regs 1).toNat
          = Nat.gcd b.toNat a.toNat
      rw [BitVec.toNat_umod, ← Nat.gcd_rec]
      exact hg
    · show (s.regs 0 % s.regs 1).toNat ≤ k
      omega
  have hW := TimeTriple.whileNZ_measure hguard hpos hbody b.toNat
  refine hW.conseq ?_ ?_ (le_of_eq (by unfold timeBound; ring))
  · rintro s ⟨h0, h1⟩
    exact ⟨by rw [h0, h1], by rw [h1]⟩
  · rintro s ⟨k', ⟨⟨hg, hk⟩, hflag⟩, hzero⟩
    have hb0 : s.regs 1 = 0 := by
      by_contra hb
      rw [if_neg hb] at hflag
      rw [hflag] at hzero
      have h2 : 1 < 2 ^ w := Nat.one_lt_two_pow_iff.mpr (by omega)
      have := congrArg BitVec.toNat hzero
      simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt h2, Nat.zero_mod] at this
      exact one_ne_zero this
    rw [hb0] at hg
    simp at hg
    rw [hg, Nat.gcd_comm]

/-- The full triple: the time proof above recombined, by determinism, with the free
space triple, the code containing no allocation. -/
theorem spec {C : CostModel} (hw : 0 < w) (a b : Word w) :
    Triple C (fun s => s.regs 0 = a ∧ s.regs 1 = b) (code (w := w))
      (fun s => (s.regs 0).toNat = Nat.gcd a.toNat b.toNat)
      (timeBound C b.toNat) 0 0 :=
  (time_spec hw a b).and_space'
    ((time_spec hw a b).space_of_allocFree ⟨trivial, trivial, trivial, trivial⟩)

/-- `gcd 252 105 = 21` in 17 unit steps: 4 guard evaluations, the last seeing
`b = 0`, and 3 bodies. An instance of `spec`. -/
def demo : Option (Word 64 × ℕ × ℤ × ℤ) :=
  (run .unit 1000 (code (w := 64))
      { State.init 64 with
        regs := fun r => if r = 0 then 252 else if r = 1 then 105 else 0 }).map
    fun (s, t, d, p) => (s.regs 0, t, d, p)

/-- info: some (21#64, 17, 0, 0) -/
#guard_msgs in
#eval demo

/- The canonical rendering. -/
/--
info: loop {
  snez r2, r1
  bifz r2
  umod r3, r0, r1
  mov   r0, r1
  mov   r1, r3
}
-/
#guard_msgs in
#eval IO.println (code (w := 64)).renderString

/-- info: 4 -/
#guard_msgs in
#eval (code (w := 64)).regPeak₀

end Gcd

/-! ## Binary exponentiation -/

namespace BinExp

/--
```c
r = 1;
while (e != 0) { if (e & 1) r *= x; x *= x; e >>= 1; }
```
Square-and-multiply over a *runtime* exponent. Registers: `r0` base (squared
in place), `r1` exponent (shifted down), `r2` result, `r3` loop flag, `r4`
the constant 1, `r5` the tested bit. The `ifNZ`'s else-branch is a genuine
`skip`.
-/
def code : Stmt w :=
  .imm 2 1 ;;
  .whileNZ (.un .isNonZero 3 1) 3
    (.imm 4 1 ;;
     .bin .and 5 1 4 ;;
     .ifNZ 5 (.bin .mul 2 2 0) .skip ;;
     .bin .mul 0 0 0 ;;
     .bin .shr 1 1 4)

/-- `3 ^ 13 = 1594323` (word arithmetic): `(result, time, net, peak)`. The
exponent 13 = 0b1101 drives 4 iterations, 3 of them through the multiply branch, so
the time is data-dependent. -/
def demo : Option (Word 64 × ℕ × ℤ × ℤ) :=
  (run .unit 1000 (code (w := 64))
      { State.init 64 with
        regs := fun r => if r = 0 then 3 else if r = 1 then 13 else 0 }).map
    fun (s, t, d, p) => (s.regs 2, t, d, p)

/-- info: some (1594323#64, 34, 0, 0) -/
#guard_msgs in
#eval demo

/-- info: 6 -/
#guard_msgs in
#eval (code (w := 64)).regPeak₀

end BinExp

/-! ## Popcount -/

namespace Popcount

/--
```c
c = 0;
while (x != 0) { c += x & 1; x >>= 1; }
```
Registers: `r0` the word being consumed, `r1` count, `r2` loop flag, `r3` the
constant 1, `r4` the masked bit.
-/
def code : Stmt w :=
  .imm 1 0 ;;
  .whileNZ (.un .isNonZero 2 0) 2
    (.imm 3 1 ;;
     .bin .and 4 0 3 ;;
     .bin .add 1 1 4 ;;
     .bin .shr 0 0 3)

/-- `popcount 0xDEADBEEF = 24`: `(count, time, net, peak)`, 32 iterations, the
position of the highest set bit. -/
def demo : Option (Word 64 × ℕ × ℤ × ℤ) :=
  (run .unit 1000 (code (w := 64))
      { State.init 64 with
        regs := fun r => if r = 0 then 0xDEADBEEF else 0 }).map
    fun (s, t, d, p) => (s.regs 1, t, d, p)

/-- info: some (24#64, 195, 0, 0) -/
#guard_msgs in
#eval demo

/-- info: 5 -/
#guard_msgs in
#eval (code (w := 64)).regPeak₀

end Popcount

/-! ## Straight-line div/mod recomposition -/

namespace DivMod

/--
```c
q = a / b; r = a % b; s = q * b + r; ok = (s == a); h = mulhi(a, b);
```
Registers: `r0` = `a`, `r1` = `b`, `r2` quotient, `r3` remainder, `r4` the
recomposition, `r5` the identity flag, `r6` the high word of the widening product.
Branch-free, so `staticTime?` prices it exactly, including at `b = 0`, where Caliper
defines `a / 0 = 0` and `a % 0 = a`, making the recomposition identity hold there
too.
-/
def code : Stmt w :=
  .bin .udiv 2 0 1 ;;
  .bin .umod 3 0 1 ;;
  .bin .mul 4 2 1 ;;
  .bin .add 4 4 3 ;;
  .bin .eq 5 4 0 ;;
  .bin .mulhi 6 0 1

/- The exact static time: 6 unit instructions, on every input. -/
/-- info: some 6 -/
#guard_msgs in
#eval (code (w := 64)).staticTime? .unit

/-- `a = 2^64 - 1`, `b = 10`: `(q, r, ok, mulhi)`, with the identity flag 1 and the
widening product's high word 9. -/
def demo : Option (Word 64 × Word 64 × Word 64 × Word 64) :=
  (run .unit 100 (code (w := 64))
      { State.init 64 with
        regs := fun r => if r = 0 then 0xFFFFFFFFFFFFFFFF else if r = 1 then 10 else 0 }).map
    fun (s, _, _, _) => (s.regs 2, s.regs 3, s.regs 5, s.regs 6)

/-- info: some (1844674407370955161#64, 5#64, 1#64, 9#64) -/
#guard_msgs in
#eval demo

/-- Division by zero, Caliper semantics: `5 / 0 = 0`, `5 % 0 = 5`, and the
recomposition identity still holds. RISC-V's `DIVU` returns all-ones here, so the
lowering bridges that; `REMU` already matches. -/
def demoZero : Option (Word 64 × Word 64 × Word 64) :=
  (run .unit 100 (code (w := 64))
      { State.init 64 with regs := fun r => if r = 0 then 5 else 0 }).map
    fun (s, _, _, _) => (s.regs 2, s.regs 3, s.regs 5)

/-- info: some (0#64, 5#64, 1#64) -/
#guard_msgs in
#eval demoZero

/-- info: 4 -/
#guard_msgs in
#eval (code (w := 64)).regPeak₀

end DivMod

/-! ## Bit tricks -/

namespace BitTricks

/--
Branchless minimum: `min(a, b) = b ^ ((a ^ b) & -(a ≤ b))`. Registers:
`r0` = `a`, `r1` = `b`, `r2` the `ule` flag, `r3` its arithmetic negation
(all-ones mask iff `a ≤ b`), `r4` scratch, `r5` the minimum.
-/
def minCode : Stmt w :=
  .bin .ule 2 0 1 ;;
  .un .neg 3 2 ;;
  .bin .xor 4 0 1 ;;
  .bin .and 4 4 3 ;;
  .bin .xor 5 1 4

/-- info: some 5 -/
#guard_msgs in
#eval (minCode (w := 64)).staticTime? .unit

/-- `min(1000, 37) = 37` and `min(37, 1000) = 37`: the two orders cost the same 5
instructions, straight-line code being constant-time by construction. -/
def minDemo : Option (Word 64 × Word 64) := do
  let (s₁, _, _, _) ← run .unit 100 (minCode (w := 64))
    { State.init 64 with regs := fun r => if r = 0 then 1000 else if r = 1 then 37 else 0 }
  let (s₂, _, _, _) ← run .unit 100 (minCode (w := 64))
    { State.init 64 with regs := fun r => if r = 0 then 37 else if r = 1 then 1000 else 0 }
  return (s₁.regs 5, s₂.regs 5)

/-- info: some (37#64, 37#64) -/
#guard_msgs in
#eval minDemo

/--
Power-of-two test: `x != 0 && (x & (x - 1)) == 0`, branch-free. Registers:
`r0` = `x`, `r1` the constant 1, `r2` = `x - 1`, `r3` = `x & (x - 1)`,
`r4` its zero flag, `r5` the verdict.
-/
def isPow2Code : Stmt w :=
  .imm 1 1 ;;
  .bin .sub 2 0 1 ;;
  .bin .and 3 0 2 ;;
  .un .isZero 4 3 ;;
  .un .isNonZero 5 0 ;;
  .bin .and 5 4 5

/-- `(isPow2 64, isPow2 96, isPow2 0)` = `(1, 0, 0)`. -/
def isPow2Demo : Option (Word 64 × Word 64 × Word 64) := do
  let go (x : Word 64) : Option (Word 64) :=
    (run .unit 100 (isPow2Code (w := 64))
      { State.init 64 with regs := fun r => if r = 0 then x else 0 }).map
      fun (s, _, _, _) => s.regs 5
  return (← go 64, ← go 96, ← go 0)

/-- info: some (1#64, 0#64, 0#64) -/
#guard_msgs in
#eval isPow2Demo

/--
Pack two 32-bit halves and check the round trip:
`p = (hi << 32) | lo; ok' = ~(hi != (p >> 32))`. Registers: `r0` = `hi`,
`r1` = `lo`, `r2` the constant 32, `r3` the shifted half, `r4` the packed
word, `r5` the recovered half, `r6` the `ne` flag, `r7` its complement
(all-ones iff the round trip held).
-/
def packCode : Stmt w :=
  .imm 2 32 ;;
  .bin .shl 3 0 2 ;;
  .bin .or 4 3 1 ;;
  .bin .shr 5 4 2 ;;
  .bin .ne 6 5 0 ;;
  .un .not 7 6

/-- `(packed, ok')` for `hi = 0xDEAD`, `lo = 0xBEEF`. -/
def packDemo : Option (Word 64 × Word 64) :=
  (run .unit 100 (packCode (w := 64))
      { State.init 64 with
        regs := fun r => if r = 0 then 0xDEAD else if r = 1 then 0xBEEF else 0 }).map
    fun (s, _, _, _) => (s.regs 4, s.regs 7)

/-- info: some (244834610757359#64, 18446744073709551615#64) -/
#guard_msgs in
#eval packDemo

/-- info: some 6 -/
#guard_msgs in
#eval (packCode (w := 64)).staticTime? .unit

/-- info: 3 -/
#guard_msgs in
#eval (minCode (w := 64)).regPeak₀

end BitTricks

end Caliper.Corpus
