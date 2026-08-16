import Caliper.Corpus.Util
import Caliper.Liveness

/-!
# Corpus: buffer-moving programs

Four classic buffer routines, written against the raw `Stmt` syntax so their
proofs and pins read off the code directly:

* `Memcpy`: copy a buffer into a freshly, dynamically allocated one, with a proved
  `Triple` for functional correctness, linear time, and net/peak memory exactly the
  copied length.
* `Memset`: overwrite every element of a buffer in place.
* `Reverse`: reverse a buffer in place with two `memStore`s per step.
* `StackSum`: drain a buffer as a stack (`memLen`/`memLoad`/`memPop`), then release
  it (`memFree`); the sum survives and the memory is credited back.

Each program gets interpreter pins (`#guard_msgs` on a concrete input) and a
pinned statically inferred register peak (`Stmt.regPeak₀`).
-/

namespace Caliper.Corpus

open Caliper

variable {w : ℕ}

/-! ## Memcpy -/

namespace Memcpy

/--
```c
n = src.len; dst = alloc(n); i = 0;
while (i < n) { dst.push(src[i]); i += 1; }
```
Registers: `r0` index, `r1` length, `r2` loop flag, `r3` element, `r4` the
constant 1. The destination capacity comes from a register (`memAlloc`), so the
allocation is the *dynamic* one: its time charge is data-dependent and enters the
bound through `Triple.memAlloc`'s capacity bound.
-/
def code (src dst : BufId) : Stmt w :=
  .memLen 1 src ;;
  .memAlloc dst 1 ;;
  .imm 0 0 ;;
  .whileNZ (.bin .ult 2 0 1) 2
    (.memLoad 3 src 0 ;;
     .memPush dst 3 ;;
     .imm 4 1 ;;
     .bin .add 0 0 4)

/-- The first `n` elements of `arr` as a fresh array (the specification-side
description of the copy's progress). -/
def prefixOf (arr : Array (Word w)) : ℕ → Array (Word w)
  | 0 => #[]
  | n + 1 => (prefixOf arr n).push (if h : n < arr.size then arr[n] else 0)

theorem prefixOf_size (arr : Array (Word w)) (n : ℕ) : (prefixOf arr n).size = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [prefixOf, ih]

theorem prefixOf_getElem (arr : Array (Word w)) {n i : ℕ} (hi : i < n)
    (hia : i < arr.size) :
    (prefixOf arr n)[i]'(by rw [prefixOf_size]; exact hi) = arr[i] := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [prefixOf, Array.getElem_push, prefixOf_size]
    split
    · exact ih (by assumption)
    · have : i = n := by omega
      subst this
      simp [hia]

/-- The full prefix is the array itself. -/
theorem prefixOf_eq_self (arr : Array (Word w)) : prefixOf arr arr.size = arr := by
  apply Array.ext
  · exact prefixOf_size arr arr.size
  · intro i h1 h2
    exact prefixOf_getElem arr (by rwa [prefixOf_size] at h1) h2

/-- Loop invariant: `k` iterations remain, `dst` holds the copied prefix
inside capacity `arr.size`. -/
def Inv (src dst : BufId) (arr : Array (Word w)) (k : ℕ) (s : State w) : Prop :=
  s.bufs src = arr ∧
  s.regs 1 = BitVec.ofNat w arr.size ∧
  (s.regs 0).toNat + k = arr.size ∧
  s.bufs dst = prefixOf arr (s.regs 0).toNat ∧
  s.caps dst = arr.size

/-- Invariant after the guard: additionally `r2` holds the comparison verdict. -/
def InvG (src dst : BufId) (arr : Array (Word w)) (k : ℕ) (s : State w) : Prop :=
  Inv src dst arr k s ∧
  s.regs 2 = if (s.regs 0).toNat < arr.size then 1 else 0

/-- Linear time: the length read, the per-word-priced allocation, one setup
`imm`, `n + 1` guard evaluations, `n` loop bodies. -/
def timeBound (C : CostModel) (n : ℕ) : ℕ :=
  C.memLen + (C.memAlloc + n * C.allocPerWord) + C.imm
    + (n + 1) * (C.bin .ult + C.branch)
    + n * (C.memLoad + C.memPush + C.imm + C.bin .add)

/-- Memcpy is correct, linear-time, and costs exactly its payload in memory: from a
state where `src` holds `arr`, the copy terminates with `dst = arr` and `src`
untouched, in time `timeBound C arr.size`, with net and peak live-memory growth
`arr.size`, the destination's capacity charged once at the dynamic allocation.
`dst ≠ src` is the one separation fact, a statement about buffer *names*. -/
theorem spec {C : CostModel} (src dst : BufId) (hne : dst ≠ src)
    (arr : Array (Word w)) (hsz : arr.size < 2 ^ w) :
    Triple C (fun s => s.bufs src = arr) (code src dst)
      (fun s => s.bufs dst = arr ∧ s.bufs src = arr)
      (timeBound C arr.size) arr.size arr.size := by
  have hne' : src ≠ dst := fun h => hne h.symm
  -- the guard: one `ult`, verdict in r2
  have hguard : ∀ k, Triple C (Inv src dst arr k) (.bin .ult 2 0 1)
      (InvG src dst arr k) (C.bin .ult) 0 0 := by
    intro k
    apply Triple.bin
    rintro s ⟨hsrc, hlen, hik, hdst, hcap⟩
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [hsrc]
    · simp [hlen]
    · simp [hik]
    · simp [hdst]
    · simp [hcap]
    · simp [hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz]
  -- a raised flag means iterations remain
  have hpos : ∀ k s, InvG src dst arr k s → s.regs 2 ≠ 0 → ∃ k', k = k' + 1 := by
    rintro k s ⟨⟨hsrc, hlen, hik, hdst, hcap⟩, hflag⟩ hnz
    have hlt := cond_of_flag_ne hflag hnz
    exact ⟨k - 1, by omega⟩
  -- the body: load, push, increment
  have hbody : ∀ k, Triple C (fun s => InvG src dst arr (k + 1) s ∧ s.regs 2 ≠ 0)
      (.memLoad 3 src 0 ;; .memPush dst 3 ;; .imm 4 1 ;; .bin .add 0 0 4)
      (Inv src dst arr k)
      (C.memLoad + (C.memPush + (C.imm + C.bin .add))) 0 0 := by
    rintro k s ⟨⟨⟨hsrc, hlen, hik, hdst, hcap⟩, hflag⟩, hnz⟩
    have hlt : (s.regs 0).toNat < arr.size := cond_of_flag_ne hflag hnz
    have hltb : (s.regs 0).toNat < (s.bufs src).size := by rw [hsrc]; exact hlt
    have hpush : ((s.setReg 3 (s.bufs src)[(s.regs 0).toNat]).bufs dst).size
        < (s.setReg 3 (s.bufs src)[(s.regs 0).toNat]).caps dst := by
      simp only [bufs_setReg, caps_setReg, hdst, hcap, prefixOf_size]
      exact hlt
    refine ⟨_, _, _, _, .seq (.memLoad hltb) (.seq (.memPush hpush) (.seq .imm .bin)),
      ⟨?_, ?_, ?_, ?_, ?_⟩, le_refl _, by omega, by omega⟩
    · simp [bufs_setBuf_ne _ _ hne', hsrc]
    · simp [hlen]
    · simp [-BitVec.toNat_add]
      rw [toNat_add_ofNat_one hlt hsz]
      omega
    · simp [-BitVec.toNat_add, hdst]
      rw [toNat_add_ofNat_one hlt hsz]
      simp [prefixOf, hlt, hsrc]
    · simp [hcap]
  -- prologue: read the length, allocate, zero the index
  have h1 : Triple C (fun s => s.bufs src = arr) (.memLen 1 src)
      (fun s => s.bufs src = arr ∧ s.regs 1 = BitVec.ofNat w arr.size)
      C.memLen 0 0 :=
    Triple.memLen fun s hs => by simp [hs]
  have h2 : Triple C
      (fun s => s.bufs src = arr ∧ s.regs 1 = BitVec.ofNat w arr.size)
      (.memAlloc dst 1)
      (fun s => s.bufs src = arr ∧ s.regs 1 = BitVec.ofNat w arr.size
        ∧ s.caps dst = arr.size ∧ s.bufs dst = #[])
      (C.memAlloc + arr.size * C.allocPerWord) arr.size arr.size := by
    apply Triple.memAlloc
    rintro s ⟨hsrc, hlen⟩
    have hval : (s.regs 1).toNat = arr.size := by
      rw [hlen, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hsz
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · simp [bufs_allocBuf_ne _ _ hne', hsrc]
    · simp [hlen]
    · simp [hval]
    · simp
  have h3 : Triple C
      (fun s => s.bufs src = arr ∧ s.regs 1 = BitVec.ofNat w arr.size
        ∧ s.caps dst = arr.size ∧ s.bufs dst = #[])
      (.imm 0 0) (Inv src dst arr arr.size) C.imm 0 0 := by
    apply Triple.imm
    rintro s ⟨hsrc, hlen, hcap, hdst⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [hsrc]
    · simp [hlen]
    · simp
    · simp [hdst, prefixOf]
    · simp [hcap]
  -- assemble
  have hW := Triple.whileNZ_measure hguard hpos hbody arr.size
  refine ((h1.seq (h2.seq (h3.seq hW))).conseq (fun _ h => h) ?_
    (le_of_eq (by unfold timeBound; ring)) (by simp) (by simp))
  -- exit: flag down means the index reached the length
  rintro s ⟨k', ⟨⟨hsrc, hlen, hik, hdst, hcap⟩, hflag⟩, hzero⟩
  by_cases hc : (s.regs 0).toNat < arr.size
  · exfalso
    rw [hflag] at hzero
    exact not_cond_of_flag_zero (by omega) hzero hc
  · have hi : (s.regs 0).toNat = arr.size := by omega
    rw [hdst, hi, prefixOf_eq_self]
    exact ⟨rfl, hsrc⟩

/-- Copy `#[7, 11, 13]` from buffer 0 to buffer 1:
`(dst contents, time, net, peak)`, with time `25 = timeBound .unit 3` and memory
`(3, 3)`, instances of `spec`. -/
def demo : Option (Array (Word 64) × ℕ × ℤ × ℤ) :=
  (run .unit 1000 (code 0 1)
      { State.init 64 with
        bufs := fun b => if b = 0 then #[7, 11, 13] else #[]
        caps := fun b => if b = 0 then 3 else 0 }).map
    fun (s, t, d, p) => (s.bufs 1, t, d, p)

/-- info: some (#[7#64, 11#64, 13#64], 25, 3, 3) -/
#guard_msgs in
#eval demo

/-- info: 5 -/
#guard_msgs in
#eval (code (w := 64) 0 1).regPeak₀

end Memcpy

/-! ## Memset -/

namespace Memset

/--
```c
n = b.len; i = 0;
while (i < n) { b[i] = v; i += 1; }
```
Registers: `r0` index, `r1` length, `r2` loop flag, `r3` the constant 1; the
fill value `v` is passed in `r5`. In-place: every write is a `memStore` below
the existing fill level, so the program allocates nothing.
-/
def code (b : BufId) : Stmt w :=
  .memLen 1 b ;;
  .imm 0 0 ;;
  .whileNZ (.bin .ult 2 0 1) 2
    (.memStore b 0 5 ;;
     .imm 3 1 ;;
     .bin .add 0 0 3)

/-- Overwrite `#[1, 2, 3, 4]` with the value 9 from `r5`:
`(contents, time, net, peak)`: zero memory, in place. -/
def demo : Option (Array (Word 64) × ℕ × ℤ × ℤ) :=
  (run .unit 1000 (code 0)
      { State.init 64 with
        regs := fun r => if r = 5 then 9 else 0
        bufs := fun b => if b = 0 then #[1, 2, 3, 4] else #[]
        caps := fun b => if b = 0 then 4 else 0 }).map
    fun (s, t, d, p) => (s.bufs 0, t, d, p)

/-- info: some (#[9#64, 9#64, 9#64, 9#64], 24, 0, 0) -/
#guard_msgs in
#eval demo

/-- info: 5 -/
#guard_msgs in
#eval (code (w := 64) 0).regPeak₀

end Memset

/-! ## Reverse (in place) -/

namespace Reverse

/--
```c
i = 0; j = b.len;
while (i + 1 < j) { j -= 1; t = b[i]; u = b[j]; b[i] = u; b[j] = t; i += 1; }
```
Registers: `r0` = `i`, `r1` = `j`, `r2` the constant 1, `r3` = `i + 1`,
`r4` loop flag, `r5`/`r6` the two elements being swapped. The guard computes
`i + 1 < j`, so its cost (an `imm`, an `add`, an `ult`) is billed on every check;
guards are statements, never free side conditions.
-/
def code (b : BufId) : Stmt w :=
  .imm 0 0 ;;
  .memLen 1 b ;;
  .whileNZ (.imm 2 1 ;; .bin .add 3 0 2 ;; .bin .ult 4 3 1) 4
    (.imm 2 1 ;;
     .bin .sub 1 1 2 ;;
     .memLoad 5 b 0 ;;
     .memLoad 6 b 1 ;;
     .memStore b 0 6 ;;
     .memStore b 1 5 ;;
     .bin .add 0 0 2)

/-- Reverse `#[1, 2, 3, 4, 5]` in place: `(contents, time, net, peak)`. -/
def demo : Option (Array (Word 64) × ℕ × ℤ × ℤ) :=
  (run .unit 1000 (code 0)
      { State.init 64 with
        bufs := fun b => if b = 0 then #[1, 2, 3, 4, 5] else #[]
        caps := fun b => if b = 0 then 5 else 0 }).map
    fun (s, t, d, p) => (s.bufs 0, t, d, p)

/-- info: some (#[5#64, 4#64, 3#64, 2#64, 1#64], 28, 0, 0) -/
#guard_msgs in
#eval demo

/-- info: 7 -/
#guard_msgs in
#eval (code (w := 64) 0).regPeak₀

end Reverse

/-! ## StackSum -/

namespace StackSum

/--
```c
acc = 0;
while (b.len != 0) { acc += b[b.len - 1]; b.pop(); }
free(b);
```
Registers: `r0` accumulator, `r1` length, `r2` loop flag, `r3` the constant
1, `r4` top index, `r5` element. The buffer is consumed as a stack, reading the top
(`memLen`, `sub`, `memLoad`) and then `memPop`, and released at the end (`memFree`),
so the net memory is *negative*: the program gives back the buffer's capacity.
-/
def code (b : BufId) : Stmt w :=
  .imm 0 0 ;;
  .whileNZ (.memLen 1 b ;; .un .isNonZero 2 1) 2
    (.imm 3 1 ;;
     .bin .sub 4 1 3 ;;
     .memLoad 5 b 4 ;;
     .bin .add 0 0 5 ;;
     .memPop b) ;;
  .memFree b

/-- Drain `#[3, 5, 9]`: `(sum, final length, final capacity, time, net, peak)`. The
sum is 17 and the buffer ends empty with its 3-word capacity credited back
(net −3). -/
def demo : Option (Word 64 × ℕ × ℕ × ℕ × ℤ × ℤ) :=
  (run .unit 1000 (code 0)
      { State.init 64 with
        bufs := fun b => if b = 0 then #[3, 5, 9] else #[]
        caps := fun b => if b = 0 then 3 else 0 }).map
    fun (s, t, d, p) => (s.regs 0, (s.bufs 0).size, s.caps 0, t, d, p)

/-- info: some (17#64, 0, 0, 28, -3, 0) -/
#guard_msgs in
#eval demo

/-- info: 6 -/
#guard_msgs in
#eval (code (w := 64) 0).regPeak₀

end StackSum

end Caliper.Corpus
