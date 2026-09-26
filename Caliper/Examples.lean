import Caliper.Triple
import Caliper.Builder
import Caliper.Render

/-!
# Worked examples

The worked programs, in increasing order of interest:

1. `swapCode`: straight-line code, with a functional spec, *exact* constant time
   from the syntax alone, and the data-independence corollary.
2. `SumBuf`: a loop reading a buffer, with functional correctness, a linear *upper
   bound* on time, and zero memory.
3. `Iota`: a loop that allocates, with net and peak memory growing linearly.
4. `ScratchLoop`: a loop that *reuses* memory. Each iteration writes a word and reads it back, so
   the peak is 1 word regardless of the trip count, which is what the (net, peak)
   profile buys over counting allocations.
5. `SumTwo`: composition of two `SumBuf` calls, where the separation reasoning is
   `simp` on syntactic footprints (`Writes`/`Touches`).
6. `CountUp`/`Drain`: decoupled judgments via `TimeTriple`/`SpaceTriple`, a time
   bound proved without touching memory algebra, and a space bound for a loop whose
   trip count admits no uniform time bound.
7. `ScopedSumSq`: register temporaries dying early. A sum of squares names 5
   registers, of which at most 2 are ever live at once. The dynamic profile is
   buffers-only, here (0, 0); the register footprint is the statically inferred peak
   `Stmt.regPeak₀`, pinned in `Liveness.lean` alongside the combined `SpaceBound`
   statement.

At the end, the builder surface is connected to the hand-written core syntax by
evaluation, and `#eval` runs the reference interpreter against the proved bounds.
-/

namespace Caliper.Examples

open Caliper

variable {w : ℕ}

/-! ## BitVec helpers

The two facts about wrap-around that every loop proof needs. Both take the bound that
makes the wrap dead (`n < 2 ^ w` from the loop's own precondition), which is exactly
the pattern of `u64Wrap` in the witness IR. -/

private theorem toNat_add_ofNat_one {x : BitVec w} {n : ℕ}
    (hx : x.toNat < n) (hn : n < 2 ^ w) : (x + BitVec.ofNat w 1).toNat = x.toNat + 1 := by
  have h2 : 1 < 2 ^ w := by omega
  have h1 : (BitVec.ofNat w 1).toNat = 1 := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt h2
  rw [BitVec.toNat_add, h1]
  exact Nat.mod_eq_of_lt (by omega)

/-- A comparison flag `if c then 1 else 0` that is nonzero certifies `c`. -/
private theorem cond_of_flag_ne {c : Prop} [Decidable c] {f : BitVec w}
    (hf : f = if c then 1 else 0) (hnz : f ≠ 0) : c := by
  by_cases hc : c
  · exact hc
  · rw [if_neg hc] at hf
    exact absurd hf hnz

/-- A zero comparison flag refutes `c`, provided the word size can distinguish 1
from 0 (`1 < 2 ^ w`), which each call site derives from its own bounds. -/
private theorem not_cond_of_flag_zero {c : Prop} [Decidable c]
    (h2 : 1 < 2 ^ w) (hf : (if c then (1 : BitVec w) else 0) = 0) : ¬ c := by
  intro hc
  rw [if_pos hc] at hf
  have h := congrArg BitVec.toNat hf
  simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat] at h
  rw [Nat.mod_eq_of_lt h2, Nat.zero_mod] at h
  exact one_ne_zero h

/-! ## Example 1: straight-line code is constant time

Swap `r0` and `r1` through the scratch register `r2`. -/

/-- `r2 ← r0; r0 ← r1; r1 ← r2` -/
def swapCode : Stmt w := .mov 2 0 ;; .mov 0 1 ;; .mov 1 2

/-- Functional spec with time and memory bounds. Note the time bound `3 * C.mov` holds
for every input. -/
theorem swapCode_spec {C : CostModel} (a b : Word w) :
    Triple C Caliper.RandomTape.zero (fun s => s.regs 0 = a ∧ s.regs 1 = b) (swapCode (w := w))
      (fun s => s.regs 0 = b ∧ s.regs 1 = a) (3 * C.mov) 0 0 := by
  have h1 : Triple C Caliper.RandomTape.zero (fun s => s.regs 0 = a ∧ s.regs 1 = b) (.mov 2 0)
      (fun s => s.regs 1 = b ∧ s.regs 2 = a) C.mov 0 0 :=
    Triple.mov fun s hs => by simp [hs.1, hs.2]
  have h2 : Triple C Caliper.RandomTape.zero (fun s => s.regs 1 = b ∧ s.regs 2 = a) (.mov 0 1)
      (fun s => s.regs 0 = b ∧ s.regs 2 = a) C.mov 0 0 :=
    Triple.mov fun s hs => by simp [hs.1, hs.2]
  have h3 : Triple C Caliper.RandomTape.zero (fun s => s.regs 0 = b ∧ s.regs 2 = a) (.mov 1 2)
      (fun s => s.regs 0 = b ∧ s.regs 1 = a) C.mov 0 0 :=
    Triple.mov fun s hs => by simp [hs.1, hs.2]
  exact (h1.seq (h2.seq h3)).conseq (fun _ h => h) (fun _ h => h)
    (le_of_eq (by ring)) (by omega) (by omega)

/-- The time is not merely bounded; it is *equal* to the syntactic constant, on every
input. This is what gives "unit time per instruction" its meaning. -/
theorem swapCode_time {C : CostModel} {s s' : State w} {t : ℕ} {d p : ℤ}
    (h : Exec C Caliper.RandomTape.zero swapCode s s' t d p) : t = 3 * C.mov := by
  have := h.straight_time_eq ⟨trivial, trivial, trivial⟩
  simp only [swapCode, Stmt.staticTime] at this
  omega

/-- Constant-time in the side-channel sense: two runs on unrelated inputs cost the
same. -/
theorem swapCode_data_independent {C : CostModel} {s₁ s₁' s₂ s₂' : State w}
    {t₁ t₂ : ℕ} {d₁ p₁ d₂ p₂ : ℤ} (h₁ : Exec C Caliper.RandomTape.zero swapCode s₁ s₁' t₁ d₁ p₁)
    (h₂ : Exec C Caliper.RandomTape.zero swapCode s₂ s₂' t₂ d₂ p₂) : t₁ = t₂ :=
  h₁.straight_data_independent h₂ ⟨trivial, trivial, trivial⟩

/-- `mulhi` sanity check: the high word of `2^63 * 4` is `2`. -/
example : BinOp.eval .mulhi (0x8000000000000000#64) (4#64) = 2#64 := by decide

/-! ## Example 2: summing a buffer, linear time, zero allocation

Register conventions: `r0` accumulator, `r1` index, `r2` length, `r3` loop flag,
`r4` element scratch, `r5` the constant 1. The buffer name `xs` is a parameter, so
the code is generic in *which* buffer it sums, and the registers are concrete
numerals so that all framing side conditions compute. -/

namespace SumBuf

/--
```c
acc = 0; i = 0; n = xs.len;
while (i < n) { acc += xs[i]; i += 1; }
```
-/
def code (xs : BufId) : Stmt w :=
  .imm 0 0 ;;
  .imm 1 0 ;;
  .memLen 2 xs ;;
  .whileNZ (.bin .ult 3 1 2) 3
    (.memLoad 4 xs 1 ;;
     .bin .add 0 0 4 ;;
     .imm 5 1 ;;
     .bin .add 1 1 5)

/-- Sum of the first `n` elements (the specification-side function). -/
def sumTo (arr : Array (Word w)) : ℕ → Word w
  | 0 => 0
  | n + 1 => sumTo arr n + if h : n < arr.size then arr[n] else 0

/-- Loop invariant, indexed by the remaining-iterations budget `k`. -/
def Inv (xs : BufId) (arr : Array (Word w)) (k : ℕ) (s : State w) : Prop :=
  s.bufs xs = arr ∧
  s.regs 2 = BitVec.ofNat w arr.size ∧
  (s.regs 1).toNat + k = arr.size ∧
  s.regs 0 = sumTo arr (s.regs 1).toNat

/-- Invariant after the guard: additionally, `r3` holds the comparison verdict. -/
def InvG (xs : BufId) (arr : Array (Word w)) (k : ℕ) (s : State w) : Prop :=
  Inv xs arr k s ∧
  s.regs 3 = if (s.regs 1).toNat < arr.size then 1 else 0

/-- The linear time bound: 3 setup instructions, `n + 1` guard evaluations,
`n` loop bodies. -/
def timeBound (C : CostModel) (n : ℕ) : ℕ :=
  2 * C.imm + C.memLen + (n + 1) * (C.bin .ult + C.branch)
    + n * (C.memLoad + 2 * C.bin .add + C.imm)

/-- `code xs` sums the buffer `xs` into `r0`, in time `O(n)` with zero allocation,
for any cost model. The `arr.size < 2 ^ w` assumption is what makes the index
increment wrap-free. -/
theorem spec {C : CostModel} (xs : BufId) (arr : Array (Word w))
    (hsz : arr.size < 2 ^ w) :
    Triple C Caliper.RandomTape.zero (fun s => s.bufs xs = arr) (code xs)
      (fun s => s.regs 0 = sumTo arr arr.size)
      (timeBound C arr.size) 0 0 := by
  -- the guard: one `ult`, leaving the verdict in r3
  have hguard : ∀ k, Triple C Caliper.RandomTape.zero (Inv xs arr k) (.bin .ult 3 1 2) (InvG xs arr k)
      (C.bin .ult) 0 0 := by
    intro k
    apply Triple.bin
    rintro s ⟨hb, hlen, hik, hacc⟩
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [hb]
    · simp [hlen]
    · simp [hik]
    · simp [hacc]
    · simp [hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz]
  -- a raised flag means iterations remain
  have hpos : ∀ k s, InvG xs arr k s → s.regs 3 ≠ 0 → ∃ k', k = k' + 1 := by
    rintro k s ⟨⟨hb, hlen, hik, hacc⟩, hflag⟩ hnz
    have hlt := cond_of_flag_ne hflag hnz
    exact ⟨k - 1, by omega⟩
  -- the body: read, accumulate, increment
  have hbody : ∀ k, Triple C Caliper.RandomTape.zero (fun s => InvG xs arr (k + 1) s ∧ s.regs 3 ≠ 0)
      (.memLoad 4 xs 1 ;; .bin .add 0 0 4 ;; .imm 5 1 ;; .bin .add 1 1 5)
      (Inv xs arr k)
      (C.memLoad + (C.bin .add + (C.imm + C.bin .add))) 0 0 := by
    rintro k s ⟨⟨⟨hb, hlen, hik, hacc⟩, hflag⟩, hnz⟩
    have hlt : (s.regs 1).toNat < arr.size := cond_of_flag_ne hflag hnz
    have hltb : (s.regs 1).toNat < (s.bufs xs).size := by rw [hb]; exact hlt
    refine ⟨_, _, _, _, .seq (.memLoad hltb) (.seq .bin (.seq .imm .bin)),
      ⟨?_, ?_, ?_, ?_⟩, le_refl _, by omega, by omega⟩
    · simp [hb]
    · simp [hlen]
    · simp [-BitVec.toNat_add]
      rw [toNat_add_ofNat_one hlt hsz]
      omega
    · simp [-BitVec.toNat_add, hb]
      rw [toNat_add_ofNat_one hlt hsz]
      simp [sumTo, hlt, hacc]
  -- prologue
  have h1 : Triple C Caliper.RandomTape.zero (fun s => s.bufs xs = arr) (.imm 0 0)
      (fun s => s.bufs xs = arr ∧ s.regs 0 = 0) C.imm 0 0 :=
    Triple.imm fun s hs => by simp [hs]
  have h2 : Triple C Caliper.RandomTape.zero (fun s => s.bufs xs = arr ∧ s.regs 0 = 0) (.imm 1 0)
      (fun s => s.bufs xs = arr ∧ s.regs 0 = 0 ∧ s.regs 1 = 0) C.imm 0 0 :=
    Triple.imm fun s hs => by simp [hs.1, hs.2]
  have h3 : Triple C Caliper.RandomTape.zero (fun s => s.bufs xs = arr ∧ s.regs 0 = 0 ∧ s.regs 1 = 0)
      (.memLen 2 xs) (Inv xs arr arr.size) C.memLen 0 0 := by
    apply Triple.memLen
    rintro s ⟨hb, h0, h1'⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [hb]
    · simp [hb]
    · simp [h1']
    · simp [h0, h1', sumTo]
  -- assemble
  have hW := Triple.whileNZ_measure hguard hpos hbody arr.size
  refine ((h1.seq (h2.seq (h3.seq hW))).conseq (fun _ h => h) ?_
    (le_of_eq (by unfold timeBound; ring)) (by simp) (by simp))
  -- exit: flag down means the index reached the length
  rintro s ⟨k', ⟨⟨hb, hlen, hik, hacc⟩, hflag⟩, hzero⟩
  by_cases hc : (s.regs 1).toNat < arr.size
  · exfalso
    rw [hflag] at hzero
    exact not_cond_of_flag_zero (by omega) hzero hc
  · have hi : (s.regs 1).toNat = arr.size := by omega
    rw [hacc, hi]

/-- The bound specialized to the uniform cost model: `6n + 5` steps. -/
theorem spec_unit (xs : BufId) (arr : Array (Word w)) (hsz : arr.size < 2 ^ w) :
    Triple .unit Caliper.RandomTape.zero (fun s => s.bufs xs = arr) (code xs)
      (fun s => s.regs 0 = sumTo arr arr.size) (6 * arr.size + 5) 0 0 :=
  (spec xs arr hsz).weaken
    (by unfold timeBound CostModel.unit; simp; omega) (le_refl _) (le_refl _)

end SumBuf

/-! ## Example 3: filling a buffer, the allocation bound

`iota n`: resize the buffer to length `n` (new words read 0), then store
`0, 1, ..., n-1` through an explicit fill index. The words are charged at the
`memResize` (net at most `n`, peak `n`); every store is then memory-free and unit
time, its in-range obligation discharged from the invariant. Whatever the buffer
held before is overwritten, so the spec assumes nothing about it.

Register conventions: `r0` index, `r1` flag, `r2` the limit `n`, `r3` the constant 1. -/

namespace Iota

/--
```c
b = realloc(b, n); i = 0;
while (i < n) { b[i] = i; i += 1; }
```
`n` is passed in `r2`. -/
def code (b : BufId) : Stmt w :=
  .memResize b 2 ;;
  .imm 0 0 ;;
  .whileNZ (.bin .ult 1 0 2) 1
    (.memStore b 0 0 ;;
     .imm 3 1 ;;
     .bin .add 0 0 3)

/-- The intended buffer contents. -/
def iotaTo (w : ℕ) : ℕ → Array (Word w)
  | 0 => #[]
  | n + 1 => (iotaTo w n).push (BitVec.ofNat w n)

private theorem iotaTo_size (w n : ℕ) : (iotaTo w n).size = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iotaTo, ih]

private theorem getElem?_iotaTo (w n j : ℕ) :
    (iotaTo w n)[j]? = if j < n then some (BitVec.ofNat w j) else none := by
  induction n with
  | zero => simp [iotaTo]
  | succ n ih =>
    rw [iotaTo, Array.getElem?_push, iotaTo_size, ih]
    by_cases h1 : j = n
    · subst h1; simp
    · by_cases h2 : j < n
      · simp [h1, h2, show j < n + 1 by omega]
      · simp [h1, h2, show ¬ j < n + 1 by omega]

/-- Loop invariant: `k` iterations remain, `b` has length `n`, and the words below
the index hold their final values. -/
def Inv (b : BufId) (n : ℕ) (k : ℕ) (s : State w) : Prop :=
  s.regs 2 = BitVec.ofNat w n ∧
  (s.regs 0).toNat + k = n ∧
  (s.bufs b).size = n ∧
  ∀ j, j < (s.regs 0).toNat → (s.bufs b)[j]? = some (BitVec.ofNat w j)

def InvG (b : BufId) (n : ℕ) (k : ℕ) (s : State w) : Prop :=
  Inv b n k s ∧
  s.regs 1 = if (s.regs 0).toNat < n then 1 else 0

def timeBound (C : CostModel) (n : ℕ) : ℕ :=
  C.memResize + n * C.allocPerWord + C.imm + (n + 1) * (C.bin .ult + C.branch)
    + n * (C.memStore + C.imm + C.bin .add)

/-- `code b` fills `b` with `0..n-1`. Time is linear; memory is charged once, at the
resize: net and peak at most `n`. The length is *dynamic* (read from `r2`), so the
resize's per-word time charge is data-dependent and enters the bound as
`n * C.allocPerWord` through the length bound of `Triple.memResize`. -/
theorem spec {C : CostModel} (b : BufId) (n : ℕ) (hn : n < 2 ^ w) :
    Triple C Caliper.RandomTape.zero (fun s => s.regs 2 = BitVec.ofNat w n) (code b)
      (fun s => s.bufs b = iotaTo w n)
      (timeBound C n) n n := by
  have hguard : ∀ k, Triple C Caliper.RandomTape.zero (Inv (w := w) b n k) (.bin .ult 1 0 2)
      (InvG (w := w) b n k) (C.bin .ult) 0 0 := by
    intro k
    apply Triple.bin
    rintro s ⟨hlim, hik, hsz, hfill⟩
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [hlim]
    · simp [hik]
    · simp [hsz]
    · simpa using hfill
    · simp [hlim, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have hpos : ∀ k (s : State w), InvG b n k s → s.regs 1 ≠ 0 → ∃ k', k = k' + 1 := by
    rintro k s ⟨⟨hlim, hik, hsz, hfill⟩, hflag⟩ hnz
    have hlt := cond_of_flag_ne hflag hnz
    exact ⟨k - 1, by omega⟩
  have hbody : ∀ k, Triple C Caliper.RandomTape.zero
      (fun (s : State w) => InvG b n (k + 1) s ∧ s.regs 1 ≠ 0)
      (.memStore b 0 0 ;; .imm 3 1 ;; .bin .add 0 0 3)
      (Inv b n k)
      (C.memStore + (C.imm + C.bin .add)) 0 0 := by
    rintro k s ⟨⟨⟨hlim, hik, hsz, hfill⟩, hflag⟩, hnz⟩
    have hlt : (s.regs 0).toNat < n := cond_of_flag_ne hflag hnz
    have hst : (s.regs 0).toNat < (s.bufs b).size := by rw [hsz]; exact hlt
    refine ⟨_, _, _, _, .seq (.memStore hst) (.seq .imm .bin),
      ⟨?_, ?_, ?_, ?_⟩, le_refl _, by omega, by omega⟩
    · simp [hlim]
    · simp [-BitVec.toNat_add]
      rw [toNat_add_ofNat_one hlt hn]
      omega
    · simp [hsz]
    · intro j hj
      simp [-BitVec.toNat_add] at hj ⊢
      rw [toNat_add_ofNat_one hlt hn] at hj
      rw [Array.getElem?_set]
      by_cases hij : (s.regs 0).toNat = j
      · subst hij; simp
      · rw [if_neg hij]; exact hfill j (by omega)
  have h1 : Triple C Caliper.RandomTape.zero (fun s => s.regs 2 = BitVec.ofNat w n)
      (.memResize b 2)
      (fun s => s.regs 2 = BitVec.ofNat w n ∧ (s.bufs b).size = n)
      (C.memResize + n * C.allocPerWord) n n := by
    apply Triple.memResize
    intro s hs
    have hval : (s.regs 2).toNat = n := by
      rw [hs, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hn
    exact ⟨by omega, by rw [hval]; omega, by simp [hs], by simp [hval]⟩
  have h2 : Triple C Caliper.RandomTape.zero
      (fun s => s.regs 2 = BitVec.ofNat w n ∧ (s.bufs b).size = n)
      (.imm 0 0) (Inv b n n) C.imm 0 0 := by
    apply Triple.imm
    rintro s ⟨hlim, hsz⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [hlim]
    · simp
    · simp [hsz]
    · intro j hj; simp at hj
  have hW := Triple.whileNZ_measure hguard hpos hbody n
  refine ((h1.seq (h2.seq hW)).conseq (fun _ h => h) ?_
    (le_of_eq (by unfold timeBound; ring)) (by simp) (by simp))
  rintro s ⟨k', ⟨⟨hlim, hik, hsz, hfill⟩, hflag⟩, hzero⟩
  by_cases hc : (s.regs 0).toNat < n
  · exfalso
    rw [hflag] at hzero
    exact not_cond_of_flag_zero (by omega) hzero hc
  · have hi : (s.regs 0).toNat = n := by omega
    apply Array.ext_getElem?
    intro j
    rw [getElem?_iotaTo]
    by_cases hj : j < n
    · rw [if_pos hj]; exact hfill j (by omega)
    · rw [if_neg hj, Array.getElem?_eq_none (by omega)]

end Iota

/-! ## Example 4: memory reuse, peak 1 regardless of trip count

A one-word scratch buffer is allocated once, each of the `n` iterations writes a
word into it and reads it back, so every access is memory-free, and the buffer is
freed at the end. Net memory 0, peak 1, for any `n`, where a total-allocation
counter would report `n`. The free `memResizeI sb 0`, with the known length 1,
credits the word back so the whole program nets to zero.

Registers: `r0` index, `r1` flag, `r2` the limit `n`, `r3` the constant 1, `r4` the
scratch index 0, `r5` the word read back. -/

namespace ScratchLoop

/--
```c
s = realloc(s, 1); i = 0;
while (i < n) { s[0] = i; x = s[0]; i += 1; }
s = realloc(s, 0);          // free
```
`n` is passed in `r2`. The one-word length is known at generation time, so the
allocation uses the statically priced `memResizeI`: no register setup, and the
per-word charge is the syntactic constant `1 * C.allocPerWord`. -/
def code (sb : BufId) : Stmt w :=
  .memResizeI sb 1 ;;
  .imm 0 0 ;;
  .whileNZ (.bin .ult 1 0 2) 1
    (.imm 4 0 ;;
     .memStore sb 4 0 ;;
     .memLoad 5 sb 4 ;;
     .imm 3 1 ;;
     .bin .add 0 0 3) ;;
  .memResizeI sb 0

def Inv (sb : BufId) (n : ℕ) (k : ℕ) (s : State w) : Prop :=
  s.regs 2 = BitVec.ofNat w n ∧
  (s.regs 0).toNat + k = n ∧
  (s.bufs sb).size = 1

def InvG (sb : BufId) (n : ℕ) (k : ℕ) (s : State w) : Prop :=
  Inv sb n k s ∧
  s.regs 1 = if (s.regs 0).toNat < n then 1 else 0

def timeBound (C : CostModel) (n : ℕ) : ℕ :=
  C.memResize + C.allocPerWord + C.memResize + C.imm + (n + 1) * (C.bin .ult + C.branch)
    + n * (C.imm + C.memStore + C.memLoad + C.imm + C.bin .add)

/-- Linear time, net memory 0 and peak memory 1, for any `n`. -/
theorem spec {C : CostModel} (sb : BufId) (n : ℕ) (hn : n < 2 ^ w) :
    Triple C Caliper.RandomTape.zero (fun s => s.regs 2 = BitVec.ofNat w n) (code sb)
      (fun s => s.bufs sb = #[])
      (timeBound C n) 0 1 := by
  have hguard : ∀ k, Triple C Caliper.RandomTape.zero (Inv (w := w) sb n k) (.bin .ult 1 0 2)
      (InvG (w := w) sb n k) (C.bin .ult) 0 0 := by
    intro k
    apply Triple.bin
    rintro s ⟨hlim, hik, hsz⟩
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · simp [hlim]
    · simp [hik]
    · simp [hsz]
    · simp [hlim, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have hpos : ∀ k (s : State w), InvG sb n k s → s.regs 1 ≠ 0 → ∃ k', k = k' + 1 := by
    rintro k s ⟨⟨hlim, hik, hsz⟩, hflag⟩ hnz
    have hlt := cond_of_flag_ne hflag hnz
    exact ⟨k - 1, by omega⟩
  have hbody : ∀ k, Triple C Caliper.RandomTape.zero
      (fun (s : State w) => InvG sb n (k + 1) s ∧ s.regs 1 ≠ 0)
      (.imm 4 0 ;; .memStore sb 4 0 ;; .memLoad 5 sb 4 ;; .imm 3 1 ;; .bin .add 0 0 3)
      (Inv sb n k)
      (C.imm + (C.memStore + (C.memLoad + (C.imm + C.bin .add)))) 0 0 := by
    rintro k s ⟨⟨⟨hlim, hik, hsz⟩, hflag⟩, hnz⟩
    have hlt : (s.regs 0).toNat < n := cond_of_flag_ne hflag hnz
    refine ⟨_, _, _, _,
      .seq .imm (.seq (.memStore (by simp [hsz])) (.seq (.memLoad (by simp [hsz]))
        (.seq .imm .bin))),
      ⟨?_, ?_, ?_⟩, le_refl _, by omega, by omega⟩
    · simp [hlim]
    · simp [-BitVec.toNat_add]
      rw [toNat_add_ofNat_one hlt hn]
      omega
    · simp [hsz]
  have h1 : Triple C Caliper.RandomTape.zero
      (fun s => s.regs 2 = BitVec.ofNat w n)
      (.memResizeI sb 1)
      (fun s => s.regs 2 = BitVec.ofNat w n ∧ (s.bufs sb).size = 1)
      (C.memResize + 1 * C.allocPerWord) 1 1 := by
    apply Triple.memResizeI
    intro s hlim
    exact ⟨by omega, by simp [hlim], by simp⟩
  have h2 : Triple C Caliper.RandomTape.zero
      (fun s => s.regs 2 = BitVec.ofNat w n ∧ (s.bufs sb).size = 1)
      (.imm 0 0) (Inv sb n n) C.imm 0 0 := by
    apply Triple.imm
    rintro s ⟨hlim, hsz⟩
    exact ⟨by simp [hlim], by simp, by simp [hsz]⟩
  have hW := Triple.whileNZ_measure hguard hpos hbody n
  have hF : Triple C Caliper.RandomTape.zero
      (fun s => ∃ k', InvG (w := w) sb n k' s ∧ s.regs 1 = 0)
      (.memResizeI sb 0) (fun s => s.bufs sb = #[])
      (C.memResize + 0 * C.allocPerWord) (-(1 : ℤ)) ((0 : ℕ) : ℤ) := by
    apply Triple.memResizeI
    rintro s ⟨k', ⟨⟨hlim, hik, hsz⟩, hflag⟩, hzero⟩
    exact ⟨by rw [hsz]; omega, by simp⟩
  refine ((h1.seq (h2.seq (hW.seq hF))).conseq (fun _ h => h)
    (fun _ h => h) (le_of_eq (by unfold timeBound; ring)) (by simp) (by simp))

end ScratchLoop

/-! ## Example 5: composition, subroutine calls without separation logic

`SumBuf.code` is used twice, on two different buffers, and the two results are added.
The proof composes the two `SumBuf.spec` instances; the only "separation" facts are

* the first sum does not *touch* buffer `ys` (`Stmt.Touches`, closed by `simp`), and
* the second sum does not *write* register `r6` (`Stmt.Writes`, closed by `simp`),

both purely syntactic. This is the buffer-model replacement for framing. -/

namespace SumTwo

/-- `r0 ← Σ xs; r6 ← r0; r0 ← Σ ys; r0 ← r0 + r6` -/
def code (xs ys : BufId) : Stmt w :=
  SumBuf.code xs ;; .mov 6 0 ;; SumBuf.code ys ;; .bin .add 0 0 6

theorem spec {C : CostModel} (xs ys : BufId)
    (arrX arrY : Array (Word w))
    (hx : arrX.size < 2 ^ w) (hy : arrY.size < 2 ^ w) :
    Triple C Caliper.RandomTape.zero (fun s => s.bufs xs = arrX ∧ s.bufs ys = arrY) (code xs ys)
      (fun s => s.regs 0 = SumBuf.sumTo arrY arrY.size + SumBuf.sumTo arrX arrX.size)
      (SumBuf.timeBound C arrX.size + SumBuf.timeBound C arrY.size
        + C.mov + C.bin .add) 0 0 := by
  -- first sum; buffer `ys` framed across it (SumBuf.code touches no buffer at all)
  have h1 := (SumBuf.spec (C := C) xs arrX hx).frame_buf (b := ys) (arr := arrY)
    (by simp [SumBuf.code, Stmt.Touches])
  -- save the result
  have h2 : Triple C Caliper.RandomTape.zero
      (fun s => s.regs 0 = SumBuf.sumTo arrX arrX.size ∧ s.bufs ys = arrY)
      (.mov 6 0)
      (fun s => s.bufs ys = arrY ∧ s.regs 6 = SumBuf.sumTo arrX arrX.size)
      C.mov 0 0 :=
    Triple.mov fun s hs => by simp [hs.1, hs.2]
  -- second sum; the saved register framed across it (r6 is never written)
  have h3 := (SumBuf.spec (C := C) ys arrY hy).frame_reg (r := 6)
    (v := SumBuf.sumTo arrX arrX.size) (by simp [SumBuf.code, Stmt.Writes])
  -- combine
  have h4 : Triple C Caliper.RandomTape.zero
      (fun s => s.regs 0 = SumBuf.sumTo arrY arrY.size
        ∧ s.regs 6 = SumBuf.sumTo arrX arrX.size)
      (.bin .add 0 0 6)
      (fun s => s.regs 0 = SumBuf.sumTo arrY arrY.size
        + SumBuf.sumTo arrX arrX.size)
      (C.bin .add) 0 0 :=
    Triple.bin fun s hs => by simp [hs.1, hs.2]
  exact ((h1.seq (h2.seq (h3.seq h4))).conseq (fun _ h => h) (fun _ h => h)
    (le_of_eq (by ring)) (by omega) (by omega))

end SumTwo

/-! ## Example 6: decoupled judgments, time without memory and back

`TimeTriple`/`SpaceTriple` (see `Triple.lean`) bound one resource in isolation.

* `CountUp` proves a `SumBuf`-shaped loop bound as a `TimeTriple`: no net, no peak,
  no `max` profile algebra appears anywhere in the proof.
* `Drain` counts a buffer's length down to zero. Its trip count is the *runtime* buffer
  length, unbounded over the trivial precondition, so no uniform time bound exists
  (`Drain.no_time_bound`), yet the space bound net 0 / peak 0 is provable
  independent of the trip count (`Drain.space_spec`).

When both bounds do exist, determinism recombines separately proved judgments into a
full `Triple` (`TimeTriple.and_space`); `CountUp.spec` below glues its time-only
proof to a space triple obtained for free from alloc-freeness. -/

namespace CountUp

/--
```c
i = 0; while (i < n) { i += 1; }
```
`n` is passed in `r2`; `r0` index, `r1` flag, `r3` the constant 1. -/
def code : Stmt w :=
  .imm 0 0 ;;
  .whileNZ (.bin .ult 1 0 2) 1
    (.imm 3 1 ;; .bin .add 0 0 3)

def Inv (n k : ℕ) (s : State w) : Prop :=
  s.regs 2 = BitVec.ofNat w n ∧ (s.regs 0).toNat + k = n

def InvG (n k : ℕ) (s : State w) : Prop :=
  Inv n k s ∧ s.regs 1 = if (s.regs 0).toNat < n then 1 else 0

def timeBound (C : CostModel) (n : ℕ) : ℕ :=
  C.imm + (n + 1) * (C.bin .ult + C.branch) + n * (C.imm + C.bin .add)

/-- A pure running-time bound: the same measure-indexed loop argument as
`SumBuf.spec`, through `TimeTriple`, with no memory quantity mentioned anywhere. -/
theorem time_spec {C : CostModel} (n : ℕ) (hn : n < 2 ^ w) :
    TimeTriple C Caliper.RandomTape.zero (fun s => s.regs 2 = BitVec.ofNat w n) (code (w := w))
      (fun s => (s.regs 0).toNat = n) (timeBound C n) := by
  have hguard : ∀ k, TimeTriple C Caliper.RandomTape.zero (Inv (w := w) n k) (.bin .ult 1 0 2)
      (InvG (w := w) n k) (C.bin .ult) := by
    intro k
    refine (Triple.bin fun s ⟨hlim, hik⟩ => ⟨⟨?_, ?_⟩, ?_⟩).time
    · simp [hlim]
    · simp [hik]
    · simp [hlim, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have hpos : ∀ k (s : State w), InvG n k s → s.regs 1 ≠ 0 → ∃ k', k = k' + 1 := by
    rintro k s ⟨⟨hlim, hik⟩, hflag⟩ hnz
    have hlt := cond_of_flag_ne hflag hnz
    exact ⟨k - 1, by omega⟩
  have hbody : ∀ k, TimeTriple C Caliper.RandomTape.zero (fun (s : State w) => InvG n (k + 1) s ∧ s.regs 1 ≠ 0)
      (.imm 3 1 ;; .bin .add 0 0 3) (Inv n k) (C.imm + C.bin .add) := by
    rintro k s ⟨⟨⟨hlim, hik⟩, hflag⟩, hnz⟩
    have hlt : (s.regs 0).toNat < n := cond_of_flag_ne hflag hnz
    refine ⟨_, _, _, _, .seq .imm .bin, ⟨?_, ?_⟩, le_refl _⟩
    · simp [hlim]
    · simp [-BitVec.toNat_add]
      rw [toNat_add_ofNat_one hlt hn]
      omega
  have h1 : TimeTriple C Caliper.RandomTape.zero (fun s => s.regs 2 = BitVec.ofNat w n) (.imm 0 0)
      (Inv n n) C.imm :=
    (Triple.imm fun s hs => ⟨by simp [hs], by simp⟩).time
  have hW := TimeTriple.whileNZ_measure hguard hpos hbody n
  refine (h1.seq hW).conseq (fun _ h => h) ?_ (le_of_eq (by unfold timeBound; ring))
  rintro s ⟨k', ⟨⟨hlim, hik⟩, hflag⟩, hzero⟩
  by_cases hc : (s.regs 0).toNat < n
  · exfalso
    rw [hflag] at hzero
    exact not_cond_of_flag_zero (by omega) hzero hc
  · omega

/-- Recombined: the time-only proof above, and a space triple obtained for free
(`code` acquires no memory), glued into a full `Triple` by determinism. -/
theorem spec {C : CostModel} (n : ℕ) (hn : n < 2 ^ w) :
    Triple C Caliper.RandomTape.zero (fun s => s.regs 2 = BitVec.ofNat w n) (code (w := w))
      (fun s => (s.regs 0).toNat = n) (timeBound C n) 0 0 :=
  (time_spec n hn).and_space'
    ((time_spec n hn).space_of_allocFree ⟨trivial, trivial, trivial, trivial⟩)

end CountUp

namespace Drain

/--
```c
i = b.len; while (i != 0) { i -= 1; }
```
`r0` the counter, `r1` the flag, `r2` the constant 1. The trip count is the buffer's
length, a *runtime* quantity with no static bound. -/
def code (b : BufId) : Stmt w :=
  .memLen 0 b ;;
  .whileNZ (.mov 1 0) 1 (.imm 2 1 ;; .bin .sub 0 0 2)

/-- Decrementing a nonzero word does not wrap. -/
private theorem toNat_sub_one {x : BitVec w} (hx : x.toNat ≠ 0) :
    (x - 1).toNat = x.toNat - 1 := by
  have hlt := x.isLt
  have h1 : (1 : BitVec w).toNat = 1 := by
    show (BitVec.ofNat w 1).toNat = 1
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_sub, h1]
  have : 2 ^ w - 1 + x.toNat = (x.toNat - 1) + 2 ^ w := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

def Inv (k : ℕ) (s : State w) : Prop := (s.regs 0).toNat = k

def InvG (k : ℕ) (s : State w) : Prop := Inv k s ∧ s.regs 1 = s.regs 0

/-- Space-only: net 0, peak 0, from every start state, including those where the
loop runs longer than any given time bound (`no_time_bound`). The measure, the
counter's value, still drives the induction; it never appears in the bounds. -/
theorem space_spec {C : CostModel} (b : BufId) :
    SpaceTriple C Caliper.RandomTape.zero (fun _ => True) (code (w := w) b) (fun _ => True) 0 0 := by
  have hguard : ∀ k, SpaceTriple C Caliper.RandomTape.zero (Inv (w := w) k) (.mov 1 0)
      (InvG (w := w) k) 0 0 := by
    intro k
    exact (Triple.mov fun s hs => ⟨by simpa [Inv] using hs, by simp⟩).space
  have hpos : ∀ k (s : State w), InvG k s → s.regs 1 ≠ 0 → ∃ k', k = k' + 1 := by
    rintro (_ | k) s ⟨hk, h1⟩ hnz
    · exact absurd (h1.trans (BitVec.eq_of_toNat_eq (by simpa [Inv] using hk))) hnz
    · exact ⟨k, rfl⟩
  have hbody : ∀ k, SpaceTriple C Caliper.RandomTape.zero
      (fun (s : State w) => InvG (k + 1) s ∧ s.regs 1 ≠ 0)
      (.imm 2 1 ;; .bin .sub 0 0 2) (Inv k) 0 0 := by
    rintro k s ⟨⟨hk, _⟩, _⟩
    refine ⟨_, _, _, _, .seq .imm .bin, ?_, le_refl _, le_refl _⟩
    simp only [Inv] at hk ⊢
    simp only [BinOp.eval, regs_setReg_self, regs_setReg_ne _ _ (show (0 : ℕ) ≠ 2 by decide)]
    rw [toNat_sub_one (by omega)]
    omega
  intro s _
  obtain ⟨s', t, d, p, hexec, _, hd, hp⟩ :=
    SpaceTriple.whileNZ_measure hguard hpos hbody
      ((s.setReg 0 (BitVec.ofNat w (s.bufs b).size)).regs 0).toNat
      (s.setReg 0 (BitVec.ofNat w (s.bufs b).size)) rfl
  refine ⟨s', _, _, _, .seq .memLen hexec, trivial, ?_, ?_⟩ <;> simp_all

/-- Time lower bound for the countdown loop: from counter value `x`, at least
`x.toNat` steps under the unit cost model. -/
private theorem loop_time_lower {c : Stmt w} {s s' : State w} {t : ℕ}
    {d p : ℤ} (h : Exec .unit Caliper.RandomTape.zero c s s' t d p)
    (hc : c = .whileNZ (.mov 1 0) 1 (.imm 2 1 ;; .bin .sub 0 0 2)) :
    (s.regs 0).toNat ≤ t := by
  induction h with
  | while_done hg hz =>
    obtain ⟨rfl, rfl, rfl⟩ := Stmt.whileNZ.inj hc
    cases hg
    simp only [regs_setReg_self] at hz
    simp [hz]
  | while_step hg hnz hb _ _ _ ihl =>
    obtain ⟨rfl, rfl, rfl⟩ := Stmt.whileNZ.inj hc
    cases hg
    cases hb with
    | seq h₁ h₂ =>
      cases h₁
      cases h₂
      simp only [regs_setReg_self] at hnz
      have hx : (_ : BitVec w).toNat ≠ 0 := fun h0 => hnz (BitVec.eq_of_toNat_eq (by simpa using h0))
      have hlow := ihl rfl
      simp only [BinOp.eval, regs_setReg_self, regs_setReg_ne _ _ (show (0 : ℕ) ≠ 2 by decide),
        regs_setReg_ne _ _ (show (0 : ℕ) ≠ 1 by decide)] at hlow
      rw [toNat_sub_one hx] at hlow
      have e1 : CostModel.unit.mov = 1 := rfl
      have e2 : CostModel.unit.branch = 1 := rfl
      have e3 : CostModel.unit.imm = 1 := rfl
      have e4 : CostModel.unit.bin .sub = 1 := rfl
      omega
  | _ => simp_all

/-- Time lower bound: counting down a buffer of length `m < 2 ^ w` takes at least `m`
steps under the unit cost model. -/
private theorem time_lower {b : BufId} {s s' : State w} {t : ℕ} {d p : ℤ}
    (h : Exec .unit Caliper.RandomTape.zero (code b) s s' t d p)
    (hsz : (s.bufs b).size < 2 ^ w) : (s.bufs b).size ≤ t := by
  cases h with
  | seq h₁ h₂ =>
    cases h₁
    have := loop_time_lower h₂ rfl
    simp only [regs_setReg_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz] at this
    omega

/-- No uniform time bound exists for `Drain.code`: every candidate `T` representable
in a word is beaten by starting with a buffer of length `T + 1`. Contrast
`space_spec`, which holds with bounds `0`/`0` for the same trivial precondition. -/
theorem no_time_bound (b : BufId) (T : ℕ) (hT : T + 1 < 2 ^ w) :
    ¬ TimeTriple .unit Caliper.RandomTape.zero (fun _ => True) (code (w := w) b) (fun _ => True) T := by
  intro h
  obtain ⟨s', t, d, p, hexec, -, ht⟩ := h
    { State.init w with
      bufs := fun b' => if b' = b then Array.replicate (T + 1) 0 else #[] }
    trivial
  have hlow := time_lower hexec (by simp; omega)
  simp at hlow
  omega

end Drain

/-! ## The builder produces the same programs

`sumB` is the buffer-summing loop written in the surface syntax: automatic register
allocation, infix expressions, structured `while`. `freshReg` is a name counter, so
the builder's output is exactly the hand-written `SumBuf.code 0`, and the `#eval`
checks the two coincide. -/

open Build in
/-- `SumBuf.code` through the surface syntax, with the typed buffer handle `Buf w`. -/
def sumB (xs : Buf w) : Build w Reg := do
  let acc ← var 0
  let i ← var 0
  let n ← xs.len
  while_ (var (i .< n)) do
    let tmp ← xs.load i
    acc <~ (acc : Exp w) + tmp
    i <~ (i : Exp w) + 1
  return acc

/-- info: true -/
#guard_msgs in
#eval (Build.build (sumB (w := 64) ⟨0⟩)).2 == SumBuf.code 0

/- The rendering (`Stmt.render`, `Render.lean`) of that program, the listing quoted
in `docs/03-programming.md`. -/
/--
info: imm   r0, 0
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
-/
#guard_msgs in
#eval IO.println (SumBuf.code (w := 64) 0).renderString

/-! ## Example 7: register temporaries die early, inferred rather than declared

`3² + 4²` names five registers, but each stage's literal scratch is dead the moment
its `mul` consumes it, so at most two values ever need slots at once. No instruction
declares a register lifetime, and the dynamic profile meters buffers only; this
program touches none, so its (net, peak) memory is (0, 0). The register footprint is
the statically inferred peak `Stmt.regPeak₀ code = 2`, pinned in `Liveness.lean`
along with the combined `SpaceBound` statement. -/

namespace ScopedSumSq

open Build in
/-- `3² + 4²` through the builder: each stage's scratch is an ordinary temporary,
with no scoping ceremony, lifetimes being inferred rather than declared. -/
def sumSqB : Build 64 Reg := do
  let a ← do
    let x ← var 3
    var ((x : Exp 64) * x)
  let b ← do
    let y ← var 4
    var ((y : Exp 64) * y)
  var ((a : Exp 64) + b)

/-- The generated program, hand-written in core syntax. -/
def code : Stmt 64 :=
  .imm 0 3 ;; .bin .mul 1 0 0 ;;
  .imm 2 4 ;; .bin .mul 3 2 2 ;;
  .bin .add 4 1 3

/-- info: true -/
#guard_msgs in
#eval (Build.build sumSqB).2 == code

/-- The buffers-only profile: net 0, peak 0, from any start state in any cost model,
the program allocating nothing. The register side is the inferred `regPeak₀ = 2`;
the combined statement is `ScopedSumSq.total_space` in `Liveness.lean`. -/
theorem space_spec {C : CostModel} :
    SpaceTriple C Caliper.RandomTape.zero (fun _ => True) code (fun _ => True) 0 0 := by
  intro s _
  refine ⟨_, _, _, _, .seq .imm (.seq .bin (.seq .imm (.seq .bin .bin))),
    trivial, ?_, ?_⟩ <;> simp

/- The canonical rendering: pure ALU work, no register-file instructions. -/
/--
info: imm   r0, 3
mul  r1, r0, r0
imm   r2, 4
mul  r3, r2, r2
add  r4, r1, r3
-/
#guard_msgs in
#eval IO.println code.renderString

/-- Value `3² + 4² = 25`, realized: unit time 5 (five ALU/imm instructions),
buffers-only memory (0, 0). -/
def demo : Option (Word 64 × ℕ × ℤ × ℤ) :=
  (run .unit Caliper.RandomTape.zero 100 code (State.init 64)).map fun (s, t, d, p) => (s.regs 4, t, d, p)

/-- info: some (25#64, 5, 0, 0) -/
#guard_msgs in
#eval demo

end ScopedSumSq

/-! ### A nested temporary, same story

The inner squaring's scratch `r0` dies at the `mul` that consumes it and the stage
result `r1` at the final `add`: 3 names, but each value dies at the instruction
producing its successor, so `Liveness.lean` infers a live peak of 1, its write-point
count being survivors plus the destination. -/

open Build in
/-- A squaring stage whose result is consumed by the enclosing expression. -/
def nestedB : Build 64 Reg := do
  let a ← do
    let x ← var 3
    var ((x : Exp 64) * x)
  var ((a : Exp 64) + a)

/--
info: imm   r0, 3
mul  r1, r0, r0
add  r2, r1, r1
-/
#guard_msgs in
#eval IO.println (Build.build nestedB).2.renderString

/-- Value `3² + 3² = 18`; unit time 3; buffers-only memory (0, 0). -/
def nestedDemo : Option (Word 64 × ℕ × ℤ × ℤ) :=
  (run .unit Caliper.RandomTape.zero 100 (Build.build nestedB).2 (State.init 64)).map
    fun (s, t, d, p) => (s.regs 2, t, d, p)

/-- info: some (18#64, 3, 0, 0) -/
#guard_msgs in
#eval nestedDemo

/-! ## Executable

The interpreter runs the same programs the theorems are about (`run_sound`), so the
numbers below are instances of the proved bounds. Each result is
`(value, time, net memory, peak memory)`: summing a 3-element buffer takes
`23 = 6*3 + 5` unit-cost steps and touches no memory, `iota 5` nets and peaks at 5
words, and the scratch loop runs 100 iterations peaking at 1 word. -/

/-- Initial state with `#[3, 5, 9]` in buffer 0. -/
def demoState : State 64 :=
  { State.init 64 with
    bufs := fun b => if b = 0 then #[3, 5, 9] else #[] }

/-- Sum: expect value 17, time 23, memory (0, 0). -/
def demoSum : Option (Word 64 × ℕ × ℤ × ℤ) :=
  (run .unit Caliper.RandomTape.zero 1000 (SumBuf.code 0) demoState).map fun (s, t, d, p) => (s.regs 0, t, d, p)

/-- Iota 5: expect buffer `#[0,1,2,3,4]`, memory (5, 5). -/
def demoIota : Option (Array (Word 64) × ℕ × ℤ × ℤ) :=
  (run .unit Caliper.RandomTape.zero 1000 (Iota.code 0)
      ((State.init 64).setReg 2 5)).map fun (s, t, d, p) => (s.bufs 0, t, d, p)

/-- Scratch loop, 100 iterations: expect net 0, peak 1. -/
def demoScratch : Option (ℕ × ℤ × ℤ) :=
  (run .unit Caliper.RandomTape.zero 2000 (ScratchLoop.code 0)
      ((State.init 64).setReg 2 100)).map fun (_, t, d, p) => (t, d, p)

/-- info: some (17#64, 23, 0, 0) -/
#guard_msgs in
#eval demoSum

/-- info: some (#[0#64, 1#64, 2#64, 3#64, 4#64], 33, 5, 5) -/
#guard_msgs in
#eval demoIota

/-- info: some (704, 0, 1) -/
#guard_msgs in
#eval demoScratch

/-! ### Product types

`PairBuf` (see `Builder.lean`) is an array-of-structs: one buffer, stride 2. Field
access is compiled index arithmetic, so its cost is ordinary instruction cost. The
demo allocates two zeroed pairs, stores both, reads `fst 1` (= 30) and `snd 0`
(= 20), and returns their sum: value 50, memory (4, 4), the four buffer words
charged at allocation, the stores themselves being memory-free. The 34 register
names the straight-line expression code uses are not in the dynamic profile; their
inferred live peak is pinned in `Liveness.lean`. -/

/-- The pair-demo program, named so `Liveness.lean` can pin its inferred
register peak alongside the buffer numbers below. -/
def pairProg : ℕ × Stmt 64 :=
  Build.build (w := 64) do
    let pb ← Build.mkPairBuf 2
    pb.set 0 10 20
    pb.set 1 30 40
    let x ← pb.fst 1
    let y ← pb.snd 0
    Build.var ((x : Exp 64) + y)

def pairDemo : Option (Word 64 × ℤ × ℤ) :=
  (run .unit Caliper.RandomTape.zero 1000 pairProg.2 (State.init 64)).map
    fun (s, _, d, p) => (s.regs pairProg.1, d, p)

/-- info: some (50#64, 4, 4) -/
#guard_msgs in
#eval pairDemo

end Caliper.Examples
