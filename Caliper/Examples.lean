import Clean.Caliper.Triple
import Clean.Caliper.Builder
import Clean.Caliper.Field
import Clean.Caliper.Render

/-!
# Worked examples

Six programs, in increasing order of interest:

1. `swapCode` — straight-line code: functional spec, *exact* constant time from the
   syntax alone, and the data-independence (constant-time) corollary.
2. `SumBuf` — a loop reading a buffer: functional correctness (the register really
   holds the sum), a linear *upper bound* on time, zero memory.
3. `Iota` — a loop that allocates: net and peak memory grow linearly.
4. `ScratchLoop` — a loop that *reuses* memory: each iteration pushes and pops, so
   the peak is **1 word regardless of the trip count**. This is what the (net, peak)
   memory profile buys over counting allocations.
5. `SumTwo` — composition: two calls of the `SumBuf` subroutine glued together, where
   the "separation" reasoning is `simp` on syntactic footprints (`Writes`/`Touches`) —
   no separation logic.
6. `CountUp`/`Drain` — decoupled judgments via `TimeTriple`/`SpaceTriple`: a time
   bound proved without touching memory algebra, and a space bound for a loop whose
   trip count admits **no** uniform time bound.

At the end, the builder surface syntax is connected to the hand-written core syntax by
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

/-- A zero comparison flag refutes `c` — provided the word size can distinguish 1
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
    Triple C (fun s => s.regs 0 = a ∧ s.regs 1 = b) (swapCode (w := w))
      (fun s => s.regs 0 = b ∧ s.regs 1 = a) (3 * C.mov) 0 0 := by
  have h1 : Triple C (fun s => s.regs 0 = a ∧ s.regs 1 = b) (.mov 2 0)
      (fun s => s.regs 1 = b ∧ s.regs 2 = a) C.mov 0 0 :=
    Triple.mov fun s hs => by simp [hs.1, hs.2]
  have h2 : Triple C (fun s => s.regs 1 = b ∧ s.regs 2 = a) (.mov 0 1)
      (fun s => s.regs 0 = b ∧ s.regs 2 = a) C.mov 0 0 :=
    Triple.mov fun s hs => by simp [hs.1, hs.2]
  have h3 : Triple C (fun s => s.regs 0 = b ∧ s.regs 2 = a) (.mov 1 2)
      (fun s => s.regs 0 = b ∧ s.regs 1 = a) C.mov 0 0 :=
    Triple.mov fun s hs => by simp [hs.1, hs.2]
  exact (h1.seq (h2.seq h3)).conseq (fun _ h => h) (fun _ h => h)
    (le_of_eq (by ring)) (by omega) (by omega)

/-- The time is not merely bounded — it is *equal* to the syntactic constant, on every
input. This is the theorem that gives "unit time per instruction" its meaning. -/
theorem swapCode_time {C : CostModel} {s s' : State w} {t : ℕ} {d p : ℤ}
    (h : Exec C swapCode s s' t d p) : t = 3 * C.mov := by
  have := h.straight_time_eq ⟨trivial, trivial, trivial⟩
  simp only [swapCode, Stmt.staticTime] at this
  omega

/-- Constant-time in the side-channel sense: two runs on unrelated inputs cost the
same. -/
theorem swapCode_data_independent {C : CostModel} {s₁ s₁' s₂ s₂' : State w}
    {t₁ t₂ : ℕ} {d₁ p₁ d₂ p₂ : ℤ} (h₁ : Exec C swapCode s₁ s₁' t₁ d₁ p₁)
    (h₂ : Exec C swapCode s₂ s₂' t₂ d₂ p₂) : t₁ = t₂ :=
  h₁.straight_data_independent h₂ ⟨trivial, trivial, trivial⟩

/-- `mulhi` sanity check: the high word of `2^63 * 4` is `2`. -/
example : BinOp.eval .mulhi (0x8000000000000000#64) (4#64) = 2#64 := by decide

/-! ## Example 2: summing a buffer — linear time, zero allocation

Register conventions: `r0` accumulator, `r1` index, `r2` length, `r3` loop flag,
`r4` element scratch, `r5` the constant 1. The buffer name `xs` is a parameter — the
code is generic in *which* buffer it sums, and the registers are concrete numerals so
that all framing side conditions compute. -/

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

/-- `code xs` sums the buffer `xs` into `r0`, in time `O(n)` and **zero allocation**,
for any cost model. The `arr.size < 2 ^ w` assumption is what makes the index
increment wrap-free. -/
theorem spec {C : CostModel} (xs : BufId) (arr : Array (Word w))
    (hsz : arr.size < 2 ^ w) :
    Triple C (fun s => s.bufs xs = arr) (code xs)
      (fun s => s.regs 0 = sumTo arr arr.size)
      (timeBound C arr.size) 0 0 := by
  -- the guard: one `ult`, leaving the verdict in r3
  have hguard : ∀ k, Triple C (Inv xs arr k) (.bin .ult 3 1 2) (InvG xs arr k)
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
  have hbody : ∀ k, Triple C (fun s => InvG xs arr (k + 1) s ∧ s.regs 3 ≠ 0)
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
  have h1 : Triple C (fun s => s.bufs xs = arr) (.imm 0 0)
      (fun s => s.bufs xs = arr ∧ s.regs 0 = 0) C.imm 0 0 :=
    Triple.imm fun s hs => by simp [hs]
  have h2 : Triple C (fun s => s.bufs xs = arr ∧ s.regs 0 = 0) (.imm 1 0)
      (fun s => s.bufs xs = arr ∧ s.regs 0 = 0 ∧ s.regs 1 = 0) C.imm 0 0 :=
    Triple.imm fun s hs => by simp [hs.1, hs.2]
  have h3 : Triple C (fun s => s.bufs xs = arr ∧ s.regs 0 = 0 ∧ s.regs 1 = 0)
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
    Triple .unit (fun s => s.bufs xs = arr) (code xs)
      (fun s => s.regs 0 = sumTo arr arr.size) (6 * arr.size + 5) 0 0 :=
  (spec xs arr hsz).weaken
    (by unfold timeBound CostModel.unit; simp; omega) (le_refl _) (le_refl _)

end SumBuf

/-! ## Example 3: filling a buffer — the allocation bound

`iota n`: reserve capacity `n`, then push `0, 1, ..., n-1`. The capacity is charged at
`memAlloc` (net and peak `n`); every push is then memory-free and worst-case unit
time. The push rule's capacity obligation is discharged from the invariant.

Register conventions: `r0` index, `r1` flag, `r2` the limit `n`, `r3` the constant 1. -/

namespace Iota

/--
```c
b = alloc(n); i = 0;
while (i < n) { b.push(i); i += 1; }
```
`n` is passed in `r2`. -/
def code (b : BufId) : Stmt w :=
  .memAlloc b 2 ;;
  .imm 0 0 ;;
  .whileNZ (.bin .ult 1 0 2) 1
    (.memPush b 0 ;;
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

def Inv (b : BufId) (n : ℕ) (k : ℕ) (s : State w) : Prop :=
  s.regs 2 = BitVec.ofNat w n ∧
  (s.regs 0).toNat + k = n ∧
  s.bufs b = iotaTo w (s.regs 0).toNat ∧
  s.caps b = n

def InvG (b : BufId) (n : ℕ) (k : ℕ) (s : State w) : Prop :=
  Inv b n k s ∧
  s.regs 1 = if (s.regs 0).toNat < n then 1 else 0

def timeBound (C : CostModel) (n : ℕ) : ℕ :=
  C.memAlloc + n * C.allocPerWord + C.imm + (n + 1) * (C.bin .ult + C.branch)
    + n * (C.memPush + C.imm + C.bin .add)

/-- `code b` fills `b` with `0..n-1`. Time is linear; memory is charged once, at the
allocation: net and peak are both `n`. The capacity is *dynamic* (read from `r2`),
so the allocation's per-word time charge is data-dependent and enters the bound as
`n * C.allocPerWord` through the capacity bound of `Triple.memAlloc`. -/
theorem spec {C : CostModel} (b : BufId) (n : ℕ) (hn : n < 2 ^ w) :
    Triple C (fun s => s.regs 2 = BitVec.ofNat w n) (code b)
      (fun s => s.bufs b = iotaTo w n)
      (timeBound C n) n n := by
  have hguard : ∀ k, Triple C (Inv (w := w) b n k) (.bin .ult 1 0 2)
      (InvG (w := w) b n k) (C.bin .ult) 0 0 := by
    intro k
    apply Triple.bin
    rintro s ⟨hlim, hik, hbuf, hcap⟩
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [hlim]
    · simp [hik]
    · simp [hbuf]
    · simp [hcap]
    · simp [hlim, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have hpos : ∀ k (s : State w), InvG b n k s → s.regs 1 ≠ 0 → ∃ k', k = k' + 1 := by
    rintro k s ⟨⟨hlim, hik, hbuf, hcap⟩, hflag⟩ hnz
    have hlt := cond_of_flag_ne hflag hnz
    exact ⟨k - 1, by omega⟩
  have hbody : ∀ k, Triple C (fun (s : State w) => InvG b n (k + 1) s ∧ s.regs 1 ≠ 0)
      (.memPush b 0 ;; .imm 3 1 ;; .bin .add 0 0 3)
      (Inv b n k)
      (C.memPush + (C.imm + C.bin .add)) 0 0 := by
    rintro k s ⟨⟨⟨hlim, hik, hbuf, hcap⟩, hflag⟩, hnz⟩
    have hlt : (s.regs 0).toNat < n := cond_of_flag_ne hflag hnz
    have hpush : (s.bufs b).size < s.caps b := by
      rw [hbuf, hcap, iotaTo_size]
      exact hlt
    refine ⟨_, _, _, _, .seq (.memPush hpush) (.seq .imm .bin),
      ⟨?_, ?_, ?_, ?_⟩, le_refl _, by omega, by omega⟩
    · simp [hlim]
    · simp [-BitVec.toNat_add]
      rw [toNat_add_ofNat_one hlt hn]
      omega
    · simp [-BitVec.toNat_add, hbuf]
      rw [toNat_add_ofNat_one hlt hn]
      simp [iotaTo]
    · simp [hcap]
  have h1 : Triple C (fun s => s.regs 2 = BitVec.ofNat w n) (.memAlloc b 2)
      (fun s => s.regs 2 = BitVec.ofNat w n ∧ s.caps b = n ∧ s.bufs b = #[])
      (C.memAlloc + n * C.allocPerWord) n n := by
    apply Triple.memAlloc
    intro s hs
    have hval : (s.regs 2).toNat = n := by
      rw [hs, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hn
    refine ⟨by omega, ?_, ?_, ?_⟩
    · simp [hs]
    · simp [hval]
    · simp
  have h2 : Triple C
      (fun s => s.regs 2 = BitVec.ofNat w n ∧ s.caps b = n ∧ s.bufs b = #[])
      (.imm 0 0) (Inv b n n) C.imm 0 0 := by
    apply Triple.imm
    rintro s ⟨hlim, hcap, hbuf⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [hlim]
    · simp
    · simp [hbuf, iotaTo]
    · simp [hcap]
  have hW := Triple.whileNZ_measure hguard hpos hbody n
  refine ((h1.seq (h2.seq hW)).conseq (fun _ h => h) ?_
    (le_of_eq (by unfold timeBound; ring)) (by simp) (by simp))
  rintro s ⟨k', ⟨⟨hlim, hik, hbuf, hcap⟩, hflag⟩, hzero⟩
  by_cases hc : (s.regs 0).toNat < n
  · exfalso
    rw [hflag] at hzero
    exact not_cond_of_flag_zero (by omega) hzero hc
  · have hi : (s.regs 0).toNat = n := by omega
    rw [hbuf, hi]

end Iota

/-! ## Example 4: memory reuse — peak 1 regardless of trip count

A one-slot scratch buffer is allocated once, each of the `n` iterations pushes into it
and pops again (inside the fixed capacity, so both are memory-free), and the buffer is
freed at the end. Net memory 0, **peak 1**, for any `n` — a total-allocation counter
would have reported `n`. `Triple.memFree'` (free with known capacity) credits the
word back so the whole program nets to zero.

Registers: `r0` index, `r1` flag, `r2` the limit `n`, `r3` the constant 1. -/

namespace ScratchLoop

/--
```c
s = alloc(1); i = 0;
while (i < n) { s.push(i); s.pop(); i += 1; }
free(s);
```
`n` is passed in `r2`. The one-word capacity is known at generation time, so the
allocation uses the statically priced `memAllocI` — no register setup, and the
per-word charge is the syntactic constant `1 * C.allocPerWord`. -/
def code (sb : BufId) : Stmt w :=
  .memAllocI sb 1 ;;
  .imm 0 0 ;;
  .whileNZ (.bin .ult 1 0 2) 1
    (.memPush sb 0 ;;
     .memPop sb ;;
     .imm 3 1 ;;
     .bin .add 0 0 3) ;;
  .memFree sb

def Inv (sb : BufId) (n : ℕ) (k : ℕ) (s : State w) : Prop :=
  s.regs 2 = BitVec.ofNat w n ∧
  (s.regs 0).toNat + k = n ∧
  s.bufs sb = #[] ∧
  s.caps sb = 1

def InvG (sb : BufId) (n : ℕ) (k : ℕ) (s : State w) : Prop :=
  Inv sb n k s ∧
  s.regs 1 = if (s.regs 0).toNat < n then 1 else 0

def timeBound (C : CostModel) (n : ℕ) : ℕ :=
  C.memAlloc + C.allocPerWord + C.memFree + C.imm + (n + 1) * (C.bin .ult + C.branch)
    + n * (C.memPush + C.memPop + C.imm + C.bin .add)

/-- Linear time — net memory 0 and **peak memory 1**, for any `n`. -/
theorem spec {C : CostModel} (sb : BufId) (n : ℕ) (hn : n < 2 ^ w) :
    Triple C (fun s => s.regs 2 = BitVec.ofNat w n) (code sb)
      (fun s => s.bufs sb = #[] ∧ s.caps sb = 0)
      (timeBound C n) 0 1 := by
  have hguard : ∀ k, Triple C (Inv (w := w) sb n k) (.bin .ult 1 0 2)
      (InvG (w := w) sb n k) (C.bin .ult) 0 0 := by
    intro k
    apply Triple.bin
    rintro s ⟨hlim, hik, hbuf, hcap⟩
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [hlim]
    · simp [hik]
    · simp [hbuf]
    · simp [hcap]
    · simp [hlim, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have hpos : ∀ k (s : State w), InvG sb n k s → s.regs 1 ≠ 0 → ∃ k', k = k' + 1 := by
    rintro k s ⟨⟨hlim, hik, hbuf, hcap⟩, hflag⟩ hnz
    have hlt := cond_of_flag_ne hflag hnz
    exact ⟨k - 1, by omega⟩
  have hbody : ∀ k, Triple C (fun (s : State w) => InvG sb n (k + 1) s ∧ s.regs 1 ≠ 0)
      (.memPush sb 0 ;; .memPop sb ;; .imm 3 1 ;; .bin .add 0 0 3)
      (Inv sb n k)
      (C.memPush + (C.memPop + (C.imm + C.bin .add))) 0 0 := by
    rintro k s ⟨⟨⟨hlim, hik, hbuf, hcap⟩, hflag⟩, hnz⟩
    have hlt : (s.regs 0).toNat < n := cond_of_flag_ne hflag hnz
    have hpush : (s.bufs sb).size < s.caps sb := by
      rw [hbuf, hcap]
      simp
    refine ⟨_, _, _, _, .seq (.memPush hpush) (.seq .memPop (.seq .imm .bin)),
      ⟨?_, ?_, ?_, ?_⟩, le_refl _, by omega, by omega⟩
    · simp [hlim]
    · simp [-BitVec.toNat_add, hbuf]
      rw [toNat_add_ofNat_one hlt hn]
      omega
    · simp [hbuf]
    · simp [hcap]
  have h1 : Triple C
      (fun s => s.regs 2 = BitVec.ofNat w n)
      (.memAllocI sb 1)
      (fun s => s.regs 2 = BitVec.ofNat w n ∧ s.caps sb = 1 ∧ s.bufs sb = #[])
      (C.memAlloc + 1 * C.allocPerWord) 1 1 := by
    apply Triple.memAllocI
    intro s hlim
    refine ⟨?_, ?_, ?_⟩
    · simp [hlim]
    · simp
    · simp
  have h2 : Triple C
      (fun s => s.regs 2 = BitVec.ofNat w n ∧ s.caps sb = 1 ∧ s.bufs sb = #[])
      (.imm 0 0) (Inv sb n n) C.imm 0 0 := by
    apply Triple.imm
    rintro s ⟨hlim, hcap, hbuf⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [hlim]
    · simp
    · simp [hbuf]
    · simp [hcap]
  have hW := Triple.whileNZ_measure hguard hpos hbody n
  have hF : Triple C (fun s => ∃ k', InvG (w := w) sb n k' s ∧ s.regs 1 = 0)
      (.memFree sb) (fun s => s.bufs sb = #[] ∧ s.caps sb = 0)
      C.memFree (-(1 : ℤ)) 0 := by
    apply Triple.memFree' (K := 1)
    rintro s ⟨k', ⟨⟨hlim, hik, hbuf, hcap⟩, hflag⟩, hzero⟩
    exact ⟨by omega, by simp, by simp⟩
  refine ((h1.seq (h2.seq (hW.seq hF))).conseq (fun _ h => h)
    (fun _ h => h) (le_of_eq (by unfold timeBound; ring)) (by simp) (by simp))

end ScratchLoop

/-! ## Example 5: composition — subroutine calls without separation logic

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
    Triple C (fun s => s.bufs xs = arrX ∧ s.bufs ys = arrY) (code xs ys)
      (fun s => s.regs 0 = SumBuf.sumTo arrY arrY.size + SumBuf.sumTo arrX arrX.size)
      (SumBuf.timeBound C arrX.size + SumBuf.timeBound C arrY.size
        + C.mov + C.bin .add) 0 0 := by
  -- first sum; buffer `ys` framed across it (SumBuf.code touches no buffer at all)
  have h1 := (SumBuf.spec (C := C) xs arrX hx).frame_buf (b := ys) (arr := arrY)
    (by simp [SumBuf.code, Stmt.Touches])
  -- save the result
  have h2 : Triple C
      (fun s => s.regs 0 = SumBuf.sumTo arrX arrX.size ∧ s.bufs ys = arrY)
      (.mov 6 0)
      (fun s => s.bufs ys = arrY ∧ s.regs 6 = SumBuf.sumTo arrX arrX.size)
      C.mov 0 0 :=
    Triple.mov fun s hs => by simp [hs.1, hs.2]
  -- second sum; the saved register framed across it (r6 is never written)
  have h3 := (SumBuf.spec (C := C) ys arrY hy).frame_reg (r := 6)
    (v := SumBuf.sumTo arrX arrX.size) (by simp [SumBuf.code, Stmt.Writes])
  -- combine
  have h4 : Triple C
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

/-! ## Example 6: decoupled judgments — time without memory, memory without time

`TimeTriple`/`SpaceTriple` (see `Triple.lean`) bound one resource in isolation.

* `CountUp` proves a `SumBuf`-shaped loop bound as a `TimeTriple`: no net, no peak,
  no `max` profile algebra appears anywhere in the proof.
* `Drain` pops a buffer until it is empty. Its trip count is the *runtime* buffer
  length — unbounded over the trivial precondition — so **no uniform time bound
  exists** (`Drain.no_time_bound`), yet the space bound net 0 / peak 0 is provable,
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
`SumBuf.spec`, but through `TimeTriple` — not a single memory quantity is
mentioned, bounded, or reasoned about. -/
theorem time_spec {C : CostModel} (n : ℕ) (hn : n < 2 ^ w) :
    TimeTriple C (fun s => s.regs 2 = BitVec.ofNat w n) (code (w := w))
      (fun s => (s.regs 0).toNat = n) (timeBound C n) := by
  have hguard : ∀ k, TimeTriple C (Inv (w := w) n k) (.bin .ult 1 0 2)
      (InvG (w := w) n k) (C.bin .ult) := by
    intro k
    apply TimeTriple.bin
    rintro s ⟨hlim, hik⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp [hlim]
    · simp [hik]
    · simp [hlim, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have hpos : ∀ k (s : State w), InvG n k s → s.regs 1 ≠ 0 → ∃ k', k = k' + 1 := by
    rintro k s ⟨⟨hlim, hik⟩, hflag⟩ hnz
    have hlt := cond_of_flag_ne hflag hnz
    exact ⟨k - 1, by omega⟩
  have hbody : ∀ k, TimeTriple C (fun (s : State w) => InvG n (k + 1) s ∧ s.regs 1 ≠ 0)
      (.imm 3 1 ;; .bin .add 0 0 3) (Inv n k) (C.imm + C.bin .add) := by
    rintro k s ⟨⟨⟨hlim, hik⟩, hflag⟩, hnz⟩
    have hlt : (s.regs 0).toNat < n := cond_of_flag_ne hflag hnz
    refine ⟨_, _, _, _, .seq .imm .bin, ⟨?_, ?_⟩, le_refl _⟩
    · simp [hlim]
    · simp [-BitVec.toNat_add]
      rw [toNat_add_ofNat_one hlt hn]
      omega
  have h1 : TimeTriple C (fun s => s.regs 2 = BitVec.ofNat w n) (.imm 0 0)
      (Inv n n) C.imm :=
    TimeTriple.imm fun s hs => ⟨by simp [hs], by simp⟩
  have hW := TimeTriple.whileNZ_measure hguard hpos hbody n
  refine (h1.seq hW).conseq (fun _ h => h) ?_ (le_of_eq (by unfold timeBound; ring))
  rintro s ⟨k', ⟨⟨hlim, hik⟩, hflag⟩, hzero⟩
  by_cases hc : (s.regs 0).toNat < n
  · exfalso
    rw [hflag] at hzero
    exact not_cond_of_flag_zero (by omega) hzero hc
  · omega

/-- Recombined: the time-only proof above, and a space triple obtained for free
(`code` contains no `memAlloc`), glued into a full `Triple` by determinism. -/
theorem spec {C : CostModel} (n : ℕ) (hn : n < 2 ^ w) :
    Triple C (fun s => s.regs 2 = BitVec.ofNat w n) (code (w := w))
      (fun s => (s.regs 0).toNat = n) (timeBound C n) 0 0 :=
  (time_spec n hn).and_space'
    ((time_spec n hn).space_of_allocFree ⟨trivial, trivial, trivial, trivial⟩)

end CountUp

namespace Drain

/--
```c
while (b.len != 0) { b.pop(); }
```
The flag is `r1`. The trip count is the buffer's length — a *runtime* quantity with
no static bound. -/
def code (b : BufId) : Stmt w :=
  .whileNZ (.memLen 1 b) 1 (.memPop b)

def Inv (b : BufId) (k : ℕ) (s : State w) : Prop := (s.bufs b).size = k

def InvG (b : BufId) (k : ℕ) (s : State w) : Prop :=
  Inv b k s ∧ s.regs 1 = BitVec.ofNat w k

/-- Space-only: net 0, peak 0, from **every** start state — including those where the
loop runs longer than any given time bound (`no_time_bound`). The measure (the
buffer length) still drives the induction; it just never appears in the bounds. -/
theorem space_spec {C : CostModel} (b : BufId) :
    SpaceTriple C (fun _ => True) (code (w := w) b) (fun _ => True) 0 0 := by
  have hguard : ∀ k, SpaceTriple C (Inv (w := w) b k) (.memLen 1 b)
      (InvG (w := w) b k) 0 0 := by
    intro k
    apply SpaceTriple.memLen
    intro s hs
    exact ⟨hs, by simp [show (s.bufs b).size = k from hs]⟩
  have hpos : ∀ k (s : State w), InvG b k s → s.regs 1 ≠ 0 → ∃ k', k = k' + 1 := by
    rintro (_ | k) s ⟨_, hflag⟩ hnz
    · exact absurd (hflag.trans (by simp)) hnz
    · exact ⟨k, rfl⟩
  have hbody : ∀ k, SpaceTriple C (fun (s : State w) => InvG b (k + 1) s ∧ s.regs 1 ≠ 0)
      (.memPop b) (Inv b k) 0 0 := by
    intro k
    apply SpaceTriple.memPop
    rintro s ⟨⟨hsz, _⟩, _⟩
    show ((s.setBuf b (s.bufs b).pop).bufs b).size = k
    simp [show (s.bufs b).size = k + 1 from hsz]
  intro s _
  obtain ⟨s', t, d, p, hexec, _, hd, hp⟩ :=
    SpaceTriple.whileNZ_measure hguard hpos hbody ((s.bufs b).size) s rfl
  refine ⟨s', t, d, p, hexec, trivial, ?_, ?_⟩ <;> simp_all

/-- An `ofNat` below the modulus is zero only if its argument is. -/
private theorem ofNat_eq_zero_iff {n : ℕ} (hn : n < 2 ^ w) :
    BitVec.ofNat w n = 0 ↔ n = 0 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt hn] at this
    exact this
  · rintro rfl
    rfl

/-- Time lower bound: draining a buffer of length `m < 2 ^ w` takes at least `m`
steps under the unit cost model. (The hypothesis keeps the length register from
wrapping; it is preserved as the buffer shrinks.) -/
private theorem time_lower {b : BufId} {c : Stmt w} {s s' : State w} {t : ℕ}
    {d p : ℤ} (h : Exec .unit c s s' t d p)
    (hc : c = .whileNZ (.memLen 1 b) 1 (.memPop b))
    (hsz : (s.bufs b).size < 2 ^ w) : (s.bufs b).size ≤ t := by
  induction h with
  | while_done hg hz =>
    obtain ⟨rfl, rfl, rfl⟩ := Stmt.whileNZ.inj hc
    cases hg
    simp only [regs_setReg_self] at hz
    rw [ofNat_eq_zero_iff hsz] at hz
    omega
  | while_step hg hnz hb _ _ _ ihl =>
    obtain ⟨rfl, rfl, rfl⟩ := Stmt.whileNZ.inj hc
    cases hg
    cases hb
    simp only [regs_setReg_self, ne_eq, ofNat_eq_zero_iff hsz] at hnz
    have hlow := ihl rfl (by simp; omega)
    simp only [bufs_setBuf_self, bufs_setReg, Array.size_pop] at hlow
    have e1 : CostModel.unit.memLen = 1 := rfl
    have e2 : CostModel.unit.branch = 1 := rfl
    have e3 : CostModel.unit.memPop = 1 := rfl
    omega
  | _ => simp_all

/-- **No uniform time bound exists** for `Drain.code`: every candidate `T`
(representable in a word) is beaten by starting with a buffer of length `T + 1`.
Contrast with `space_spec`, which holds with bounds `0`/`0` for the same trivial
precondition — the two resources genuinely decouple. -/
theorem no_time_bound (b : BufId) (T : ℕ) (hT : T + 1 < 2 ^ w) :
    ¬ TimeTriple .unit (fun _ => True) (code (w := w) b) (fun _ => True) T := by
  intro h
  obtain ⟨s', t, d, p, hexec, -, ht⟩ := h
    { State.init w with
      bufs := fun b' => if b' = b then Array.replicate (T + 1) 0 else #[] }
    trivial
  have hlow := time_lower hexec rfl (by simp; omega)
  simp at hlow
  omega

end Drain

/-! ## The builder produces the same programs

`sumB` is `SumBuf.code` written in the surface syntax: automatic register allocation,
infix expressions, structured `while`. The `rfl` below checks the two coincide — the
sugar adds nothing to the trusted surface. -/

open Build in
/-- `SumBuf.code`, ergonomically — note the typed buffer handle `Buf w`. -/
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

/- The canonical rendering (`Stmt.render`, `Render.lean`) of that program — the
listing quoted in `doc/caliper.md`. -/
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

/-! ## Executable

The interpreter runs the same programs the theorems are about (`run_sound`), so the
numbers below are instances of the proved bounds. Each result is
`(value, time, net memory, peak memory)`: summing a 3-element buffer takes
`23 = 6*3 + 5` unit-cost steps and touches no memory; `iota 5` nets and peaks at 5
words; the scratch loop runs 100 iterations and **peaks at 1 word**. -/

/-- Initial state with `#[3, 5, 9]` in buffer 0. -/
def demoState : State 64 :=
  { State.init 64 with
    bufs := fun b => if b = 0 then #[3, 5, 9] else #[]
    caps := fun b => if b = 0 then 3 else 0 }

/-- Sum: expect value 17, time 23, memory (0, 0). -/
def demoSum : Option (Word 64 × ℕ × ℤ × ℤ) :=
  (run .unit 1000 (SumBuf.code 0) demoState).map fun (s, t, d, p) => (s.regs 0, t, d, p)

/-- Iota 5: expect buffer `#[0,1,2,3,4]`, memory (5, 5). -/
def demoIota : Option (Array (Word 64) × ℕ × ℤ × ℤ) :=
  (run .unit 1000 (Iota.code 0)
      ((State.init 64).setReg 2 5)).map fun (s, t, d, p) => (s.bufs 0, t, d, p)

/-- Scratch loop, 100 iterations: expect net 0, **peak 1**. -/
def demoScratch : Option (ℕ × ℤ × ℤ) :=
  (run .unit 2000 (ScratchLoop.code 0)
      ((State.init 64).setReg 2 100)).map fun (_, t, d, p) => (t, d, p)

/-- info: some (17#64, 23, 0, 0) -/
#guard_msgs in
#eval demoSum

/-- info: some (#[0#64, 1#64, 2#64, 3#64, 4#64], 34, 5, 5) -/
#guard_msgs in
#eval demoIota

/-- info: some (606, 0, 1) -/
#guard_msgs in
#eval demoScratch

/-! ### Product types

`PairBuf` (see `Builder.lean`) is an array-of-structs: one buffer, stride 2. Field
access is compiled index arithmetic, so its cost is ordinary instruction cost. The
demo allocates room for two pairs, pushes them, reads `fst 1` (= 30) and `snd 0`
(= 20), and returns their sum: value 50, and memory (4, 4) — the four words charged
at allocation; the pushes themselves are memory-free. -/

def pairDemo : Option (Word 64 × ℤ × ℤ) :=
  let (r, prog) := Build.build (w := 64) do
    let pb ← Build.mkPairBuf 2
    pb.push 10 20
    pb.push 30 40
    let x ← pb.fst 1
    let y ← pb.snd 0
    Build.var ((x : Exp 64) + y)
  (run .unit 1000 prog (State.init 64)).map fun (s, _, d, p) => (s.regs r, d, p)

/-- info: some (50#64, 4, 4) -/
#guard_msgs in
#eval pairDemo

/-! ### Generic field arithmetic, from the modulus alone

`Fp w p` (see `Field.lean`) needs nothing but `p`. Here it is instantiated at
BabyBear: the program computes `5⁻¹` via the generated Fermat ladder (whose exponent
bits Lean computed at generation time) and multiplies back. Expect `5⁻¹ * 5 = 1`. -/

def babybear : ℕ := 2 ^ 31 - 2 ^ 27 + 1

def fieldDemo : Option (Word 64 × Word 64 × ℕ) :=
  let (rs, prog) := Build.build (w := 64) do
    let x : Fp 64 babybear := ⟨← Build.var 5⟩
    let xi ← Fp.inv x
    let chk ← Fp.mul xi x
    return (xi.val, chk.val)
  (run .unit 10000 prog (State.init 64)).map fun (s, t, _, _) =>
    (s.regs rs.1, s.regs rs.2, t)

/-- info: some (1610612737#64, 1#64, 128) -/
#guard_msgs in
#eval fieldDemo

end Caliper.Examples
