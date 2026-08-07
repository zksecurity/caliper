import Clean.LowLevel.Triple
import Clean.LowLevel.Builder

/-!
# Worked examples

Four programs, in increasing order of interest:

1. `swapCode` — straight-line code: functional spec, *exact* constant time from the
   syntax alone, and the data-independence (constant-time) corollary.
2. `SumBuf` — a loop reading a buffer: functional correctness (the register really
   holds the sum), a linear *upper bound* on time, zero allocation.
3. `Iota` — a loop that allocates: the memory bound is the interesting part.
4. `SumTwo` — composition: two calls of the `SumBuf` subroutine glued together, where
   the "separation" reasoning is `simp` on syntactic footprints (`Writes`/`Touches`) —
   no separation logic.

At the end, the builder surface syntax is connected to the hand-written core syntax by
`rfl`, and `#eval` runs the reference interpreter against the proved bounds.
-/

namespace LowLevel.Examples

open LowLevel

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
      (fun s => s.regs 0 = b ∧ s.regs 1 = a) (3 * C.mov) 0 := by
  have h1 : Triple C (fun s => s.regs 0 = a ∧ s.regs 1 = b) (.mov 2 0)
      (fun s => s.regs 1 = b ∧ s.regs 2 = a) C.mov 0 :=
    Triple.mov fun s hs => by simp [hs.1, hs.2]
  have h2 : Triple C (fun s => s.regs 1 = b ∧ s.regs 2 = a) (.mov 0 1)
      (fun s => s.regs 0 = b ∧ s.regs 2 = a) C.mov 0 :=
    Triple.mov fun s hs => by simp [hs.1, hs.2]
  have h3 : Triple C (fun s => s.regs 0 = b ∧ s.regs 2 = a) (.mov 1 2)
      (fun s => s.regs 0 = b ∧ s.regs 1 = a) C.mov 0 :=
    Triple.mov fun s hs => by simp [hs.1, hs.2]
  exact (h1.seq (h2.seq h3)).conseq (fun _ h => h) (fun _ h => h)
    (le_of_eq (by ring)) (le_of_eq (by ring))

/-- The time is not merely bounded — it is *equal* to the syntactic constant, on every
input. This is the theorem that gives "unit time per instruction" its meaning. -/
theorem swapCode_time {C : CostModel} {s s' : State w} {t m : ℕ}
    (h : Exec C swapCode s s' t m) : t = 3 * C.mov := by
  have := h.straight_time_eq ⟨trivial, trivial, trivial⟩
  simp only [swapCode, Stmt.staticTime] at this
  omega

/-- Constant-time in the side-channel sense: two runs on unrelated inputs cost the
same. -/
theorem swapCode_data_independent {C : CostModel} {s₁ s₁' s₂ s₂' : State w}
    {t₁ m₁ t₂ m₂ : ℕ} (h₁ : Exec C swapCode s₁ s₁' t₁ m₁)
    (h₂ : Exec C swapCode s₂ s₂' t₂ m₂) : t₁ = t₂ :=
  (h₁.straight_data_independent h₂ ⟨trivial, trivial, trivial⟩).1

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
  .bufLen 2 xs ;;
  .whileNZ (.bin .ult 3 1 2) 3
    (.bufGet 4 xs 1 ;;
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
  2 * C.imm + C.bufLen + (n + 1) * (C.bin .ult + C.branch)
    + n * (C.bufGet + 2 * C.bin .add + C.imm)

/-- `code xs` sums the buffer `xs` into `r0`, in time `O(n)` and **zero allocation**,
for any cost model. The `arr.size < 2 ^ w` assumption is what makes the index
increment wrap-free. -/
theorem spec {C : CostModel} (xs : BufId) (arr : Array (Word w))
    (hsz : arr.size < 2 ^ w) :
    Triple C (fun s => s.bufs xs = arr) (code xs)
      (fun s => s.regs 0 = sumTo arr arr.size)
      (timeBound C arr.size) 0 := by
  -- the guard: one `ult`, leaving the verdict in r3
  have hguard : ∀ k, Triple C (Inv xs arr k) (.bin .ult 3 1 2) (InvG xs arr k)
      (C.bin .ult) 0 := by
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
      (.bufGet 4 xs 1 ;; .bin .add 0 0 4 ;; .imm 5 1 ;; .bin .add 1 1 5)
      (Inv xs arr k)
      (C.bufGet + (C.bin .add + (C.imm + C.bin .add))) 0 := by
    rintro k s ⟨⟨⟨hb, hlen, hik, hacc⟩, hflag⟩, hnz⟩
    have hlt : (s.regs 1).toNat < arr.size := cond_of_flag_ne hflag hnz
    have hltb : (s.regs 1).toNat < (s.bufs xs).size := by rw [hb]; exact hlt
    refine ⟨_, _, _, .seq (.bufGet hltb) (.seq .bin (.seq .imm .bin)),
      ⟨?_, ?_, ?_, ?_⟩, le_refl _, by omega⟩
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
      (fun s => s.bufs xs = arr ∧ s.regs 0 = 0) C.imm 0 :=
    Triple.imm fun s hs => by simp [hs]
  have h2 : Triple C (fun s => s.bufs xs = arr ∧ s.regs 0 = 0) (.imm 1 0)
      (fun s => s.bufs xs = arr ∧ s.regs 0 = 0 ∧ s.regs 1 = 0) C.imm 0 :=
    Triple.imm fun s hs => by simp [hs.1, hs.2]
  have h3 : Triple C (fun s => s.bufs xs = arr ∧ s.regs 0 = 0 ∧ s.regs 1 = 0)
      (.bufLen 2 xs) (Inv xs arr arr.size) C.bufLen 0 := by
    apply Triple.bufLen
    rintro s ⟨hb, h0, h1'⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [hb]
    · simp [hb]
    · simp [h1']
    · simp [h0, h1', sumTo]
  -- assemble
  have hW := Triple.whileNZ_measure hguard hpos hbody arr.size
  refine ((h1.seq (h2.seq (h3.seq hW))).conseq (fun _ h => h) ?_
    (le_of_eq (by unfold timeBound; ring)) (le_of_eq (by ring)))
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
      (fun s => s.regs 0 = sumTo arr arr.size) (6 * arr.size + 5) 0 :=
  (spec xs arr hsz).weaken
    (by unfold timeBound CostModel.unit; simp; omega) (le_refl _)

end SumBuf

/-! ## Example 3: filling a buffer — the allocation bound

`iota n`: push `0, 1, ..., n-1` into a fresh buffer. Time is linear as before; the new
content is the *memory* bound: exactly one word allocated per iteration, so `M ≤ n`.

Register conventions: `r0` index, `r1` flag, `r2` the limit `n`, `r3` the constant 1. -/

namespace Iota

/--
```c
b = []; i = 0;
while (i < n) { b.push(i); i += 1; }
```
`n` is passed in `r2`. -/
def code (b : BufId) : Stmt w :=
  .bufNew b ;;
  .imm 0 0 ;;
  .whileNZ (.bin .ult 1 0 2) 1
    (.bufPush b 0 ;;
     .imm 3 1 ;;
     .bin .add 0 0 3)

/-- The intended buffer contents. -/
def iotaTo (w : ℕ) : ℕ → Array (Word w)
  | 0 => #[]
  | n + 1 => (iotaTo w n).push (BitVec.ofNat w n)

def Inv (b : BufId) (n : ℕ) (k : ℕ) (s : State w) : Prop :=
  s.regs 2 = BitVec.ofNat w n ∧
  (s.regs 0).toNat + k = n ∧
  s.bufs b = iotaTo w (s.regs 0).toNat

def InvG (b : BufId) (n : ℕ) (k : ℕ) (s : State w) : Prop :=
  Inv b n k s ∧
  s.regs 1 = if (s.regs 0).toNat < n then 1 else 0

def timeBound (C : CostModel) (n : ℕ) : ℕ :=
  C.bufNew + C.imm + (n + 1) * (C.bin .ult + C.branch)
    + n * (C.bufPush + C.imm + C.bin .add)

/-- `code b` fills `b` with `0..n-1`. Time is linear and — the point of this
example — **at most `n` words are ever allocated**. -/
theorem spec {C : CostModel} (b : BufId) (n : ℕ) (hn : n < 2 ^ w) :
    Triple C (fun s => s.regs 2 = BitVec.ofNat w n) (code b)
      (fun s => s.bufs b = iotaTo w n)
      (timeBound C n) n := by
  have hguard : ∀ k, Triple C (Inv (w := w) b n k) (.bin .ult 1 0 2)
      (InvG (w := w) b n k) (C.bin .ult) 0 := by
    intro k
    apply Triple.bin
    rintro s ⟨hlim, hik, hbuf⟩
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · simp [hlim]
    · simp [hik]
    · simp [hbuf]
    · simp [hlim, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have hpos : ∀ k (s : State w), InvG b n k s → s.regs 1 ≠ 0 → ∃ k', k = k' + 1 := by
    rintro k s ⟨⟨hlim, hik, hbuf⟩, hflag⟩ hnz
    have hlt := cond_of_flag_ne hflag hnz
    exact ⟨k - 1, by omega⟩
  have hbody : ∀ k, Triple C (fun (s : State w) => InvG b n (k + 1) s ∧ s.regs 1 ≠ 0)
      (.bufPush b 0 ;; .imm 3 1 ;; .bin .add 0 0 3)
      (Inv b n k)
      (C.bufPush + (C.imm + C.bin .add)) 1 := by
    rintro k s ⟨⟨⟨hlim, hik, hbuf⟩, hflag⟩, hnz⟩
    have hlt : (s.regs 0).toNat < n := cond_of_flag_ne hflag hnz
    refine ⟨_, _, _, .seq .bufPush (.seq .imm .bin),
      ⟨?_, ?_, ?_⟩, le_refl _, by omega⟩
    · simp [hlim]
    · simp [-BitVec.toNat_add]
      rw [toNat_add_ofNat_one hlt hn]
      omega
    · simp [-BitVec.toNat_add, hbuf]
      rw [toNat_add_ofNat_one hlt hn]
      simp [iotaTo]
  have h1 : Triple C (fun s => s.regs 2 = BitVec.ofNat w n) (.bufNew b)
      (fun s => s.regs 2 = BitVec.ofNat w n ∧ s.bufs b = #[]) C.bufNew 0 :=
    Triple.bufNew fun s hs => by simp [hs]
  have h2 : Triple C (fun s => s.regs 2 = BitVec.ofNat w n ∧ s.bufs b = #[])
      (.imm 0 0) (Inv b n n) C.imm 0 := by
    apply Triple.imm
    rintro s ⟨hlim, hbuf⟩
    refine ⟨?_, ?_, ?_⟩
    · simp [hlim]
    · simp
    · simp [hbuf, iotaTo]
  have hW := Triple.whileNZ_measure hguard hpos hbody n
  refine ((h1.seq (h2.seq hW)).conseq (fun _ h => h) ?_
    (le_of_eq (by unfold timeBound; ring)) (le_of_eq (by ring)))
  rintro s ⟨k', ⟨⟨hlim, hik, hbuf⟩, hflag⟩, hzero⟩
  by_cases hc : (s.regs 0).toNat < n
  · exfalso
    rw [hflag] at hzero
    exact not_cond_of_flag_zero (by omega) hzero hc
  · have hi : (s.regs 0).toNat = n := by omega
    rw [hbuf, hi]

end Iota

/-! ## Example 4: composition — subroutine calls without separation logic

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
        + C.mov + C.bin .add) 0 := by
  -- first sum; buffer `ys` framed across it (SumBuf.code touches no buffer at all)
  have h1 := (SumBuf.spec (C := C) xs arrX hx).frame_buf (b := ys) (arr := arrY)
    (by simp [SumBuf.code, Stmt.Touches])
  -- save the result
  have h2 : Triple C
      (fun s => s.regs 0 = SumBuf.sumTo arrX arrX.size ∧ s.bufs ys = arrY)
      (.mov 6 0)
      (fun s => s.bufs ys = arrY ∧ s.regs 6 = SumBuf.sumTo arrX arrX.size)
      C.mov 0 :=
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
      (C.bin .add) 0 :=
    Triple.bin fun s hs => by simp [hs.1, hs.2]
  exact ((h1.seq (h2.seq (h3.seq h4))).conseq (fun _ h => h) (fun _ h => h)
    (le_of_eq (by ring)) (le_of_eq (by ring)))

end SumTwo

/-! ## The builder produces the same programs

`sumB` is `SumBuf.code` written in the surface syntax: automatic register allocation,
infix expressions, structured `while`. The `rfl` below checks the two coincide — the
sugar adds nothing to the trusted surface. -/

open Build in
/-- `SumBuf.code`, ergonomically. -/
def sumB (xs : BufId) : Build w Reg := do
  let acc ← var 0
  let i ← var 0
  let n ← len xs
  while_ (var (i .< n)) do
    let tmp ← get xs i
    acc <~ (acc : Exp w) + tmp
    i <~ (i : Exp w) + 1
  pure acc

/-- info: true -/
#guard_msgs in
#eval (Build.build (sumB (w := 64) 0)).2 == SumBuf.code 0

/-! ## Executable

The interpreter runs the same programs the theorems are about (`run_sound`), so the
numbers below are instances of the proved bounds: summing a 3-element buffer takes
`23 = 6*3 + 5` unit-cost steps and allocates nothing; `iota 5` takes `29 = 5*5 + 4`
steps and allocates exactly 5 words — both bounds are met with equality here. -/

/-- Initial state with `#[3, 5, 9]` in buffer 0. -/
def demoState : State 64 :=
  { State.init 64 with bufs := fun b => if b = 0 then #[3, 5, 9] else #[] }

/-- Sum: expect value 17, time 23, allocation 0. -/
def demoSum : Option (Word 64 × ℕ × ℕ) :=
  (run .unit 1000 (SumBuf.code 0) demoState).map fun (s, t, m) => (s.regs 0, t, m)

/-- Iota 5: expect buffer `#[0,1,2,3,4]`, allocation 5. -/
def demoIota : Option (Array (Word 64) × ℕ × ℕ) :=
  (run .unit 1000 (Iota.code 0)
      ((State.init 64).setReg 2 5)).map fun (s, t, m) => (s.bufs 0, t, m)

/-- info: some (17#64, 23, 0) -/
#guard_msgs in
#eval demoSum

/-- info: some (#[0#64, 1#64, 2#64, 3#64, 4#64], 29, 5) -/
#guard_msgs in
#eval demoIota

end LowLevel.Examples
