import Caliper.Corpus.Util
import Caliper.Liveness

/-!
# Corpus: a growable vector

`GrowVec` is the library-level growable vector the machine deliberately leaves
out. A buffer's length is its only size, so the vector keeps its *fill* (the number
of pushed elements) in a register (`r0`) and uses the buffer's length as its
capacity. A push that finds the vector full (`fill = length`) first doubles the
length with a realloc-style `memResize`, which keeps the contents, zeroes the new
words, and is charged its full new length; then it stores at index `fill`.

* `pushCode b`: one push of `r1`, doubling when `fill = length`, with a proved
  `Triple`: the first `fill` words become `xs.push x`, the length `newCap`, time
  `pushTime` (worst case linear in the length, on a doubling push), net memory the
  growth, peak the whole new length on a doubling push.
* `pushAll b ys`: `ys.length` pushes in sequence, with a proved `Triple` whose time
  is the exact per-push sum `pushesTime`.
* The amortized bound: the potential `Φ = (4 · fill - 2 · length) · allocPerWord`
  pays for the doublings (`pushTime_amortized`), so `n` pushes into an empty vector
  of length 1 take at most `n * amortCost C` time (`pushesTime_le`), linear with an
  explicit constant, and `GrowVec.fromOne_spec` states it as a `Triple`.

Registers: `r0` fill, `r1` the element, `r2` length (doubled in place), `r3` the grow
flag, `r4` the constant 1.
-/

namespace Caliper.Corpus

open Caliper

variable {w : ℕ}

namespace GrowVec

/--
```c
n = b.len;
if (fill == n) { n = n + n; b = realloc(b, n); }
b[fill] = x; fill += 1;
```
`fill` lives in `r0`, `x` in `r1`.
-/
def pushCode (b : BufId) : Stmt w :=
  .memLen 2 b ;;
  .bin .eq 3 0 2 ;;
  .ifNZ 3 (.bin .add 2 2 2 ;; .memResize b 2) .skip ;;
  .memStore b 0 1 ;;
  .imm 4 1 ;;
  .bin .add 0 0 4

/-- The length after a push at fill `s` and length `c`. -/
def newCap (s c : ℕ) : ℕ := if s = c then 2 * c else c

/-- Time of the grow step: the doubling `add` and the resize, charged the full new
length; nothing when there is room. -/
def growTime (C : CostModel) (s c : ℕ) : ℕ :=
  if s = c then C.bin .add + (C.memResize + 2 * c * C.allocPerWord) else 0

/-- Peak memory growth of the grow step: a doubling realloc holds the old `c` and
the new `2c` words at once, so its peak above the starting level is the whole new
length `2c`; nothing when there is room. -/
def growPeak (s c : ℕ) : ℕ := if s = c then 2 * c else 0

theorem growPeak_le (s c : ℕ) : growPeak s c + 2 * c ≤ 2 * newCap s c := by
  unfold growPeak newCap; split <;> omega

theorem newCap_le_growPeak (s c : ℕ) : newCap s c ≤ growPeak s c + c := by
  unfold growPeak newCap; split <;> omega

/-- Exact time of one push at fill `s`, length `c`. -/
def pushTime (C : CostModel) (s c : ℕ) : ℕ :=
  C.memLen + (C.bin .eq + ((C.branch + growTime C s c)
    + (C.memStore + (C.imm + C.bin .add))))

/-- The vector state: `b` has length `c`, `r0` holds the fill `xs.size`, and the
first `xs.size` words of `b` are `xs`. -/
def Pre (b : BufId) (xs : Array (Word w)) (c : ℕ) (s : State w) : Prop :=
  (s.bufs b).size = c ∧ s.regs 0 = BitVec.ofNat w xs.size ∧
  ∀ j, j < xs.size → (s.bufs b)[j]? = xs[j]?

/-- Writing a register other than the fill keeps the vector state. -/
theorem Pre.setReg {b : BufId} {xs : Array (Word w)} {c : ℕ} {s : State w} {r : Reg}
    (v : Word w) (hr : r ≠ 0) (h : Pre b xs c s) : Pre b xs c (s.setReg r v) := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by simpa using h1, by rw [regs_setReg_ne _ _ (Ne.symm hr)]; exact h2,
    by simpa using h3⟩

theorem le_newCap (s c : ℕ) : c ≤ newCap s c := by
  unfold newCap; split <;> omega

theorem ofNat_eq_ofNat_iff {a b : ℕ} (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    BitVec.ofNat w a = BitVec.ofNat w b ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this
  · rintro rfl; rfl

/-- The grow step, by cases on whether the vector is full. -/
theorem grow_spec {C : CostModel} (b : BufId) (x : Word w) (xs : Array (Word w)) (c : ℕ)
    (hc1 : 1 ≤ c) (hw : 2 * c < 2 ^ w) :
    Triple C RandomTape.zero
      (fun s => (Pre b xs c s ∧ s.regs 1 = x ∧ s.regs 2 = BitVec.ofNat w c)
        ∧ s.regs 3 = if xs.size = c then 1 else 0)
      (.ifNZ 3 (.bin .add 2 2 2 ;; .memResize b 2) .skip)
      (fun s => Pre b xs (newCap xs.size c) s ∧ s.regs 1 = x)
      (C.branch + growTime C xs.size c)
      ((newCap xs.size c : ℤ) - c) (growPeak xs.size c) := by
  have h2 : 1 < 2 ^ w := by omega
  by_cases hs : xs.size = c
  · have hnew : newCap xs.size c = 2 * c := if_pos hs
    have hT : growTime C xs.size c
        = C.bin .add + (C.memResize + 2 * c * C.allocPerWord) := if_pos hs
    have hP : growPeak xs.size c = 2 * c := if_pos hs
    rw [hnew, hT, hP]
    apply Triple.ifNZ
    · have hadd : Triple C RandomTape.zero
          (fun s => ((Pre b xs c s ∧ s.regs 1 = x ∧ s.regs 2 = BitVec.ofNat w c)
            ∧ s.regs 3 = if xs.size = c then 1 else 0) ∧ s.regs 3 ≠ 0)
          (.bin .add 2 2 2)
          (fun s => Pre b xs c s ∧ s.regs 1 = x ∧ s.regs 2 = BitVec.ofNat w (2 * c))
          (C.bin .add) 0 0 := by
        apply Triple.bin
        rintro s ⟨⟨⟨hpre, h1, h2'⟩, _⟩, _⟩
        refine ⟨hpre.setReg _ (by decide), by simp [h1], ?_⟩
        simp [h2', BitVec.ofNat_add_ofNat, two_mul]
      have hres : Triple C RandomTape.zero
          (fun s => Pre b xs c s ∧ s.regs 1 = x ∧ s.regs 2 = BitVec.ofNat w (2 * c))
          (.memResize b 2)
          (fun s => Pre b xs (2 * c) s ∧ s.regs 1 = x)
          (C.memResize + 2 * c * C.allocPerWord)
          (((2 * c : ℕ) : ℤ) - (c : ℕ)) ((2 * c : ℕ) : ℤ) := by
        apply Triple.memResize'
        rintro s ⟨⟨hsz, h0, hpre⟩, h1, h2'⟩
        have hv : (s.regs 2).toNat = 2 * c := by
          rw [h2', BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
        refine ⟨by omega, by omega, ⟨?_, by simpa using h0, ?_⟩, by simpa using h1⟩
        · simp [hv]
        · intro j hj
          rw [hv, bufs_resizeBuf_self, getElem?_zeroResize_of_lt _ (by omega) (by omega)]
          exact hpre j hj
      exact (hadd.seq hres).weaken (le_refl _) (by push_cast; omega) (by push_cast; omega)
    · rintro s ⟨⟨_, h3⟩, hz⟩
      rw [h3] at hz
      exact absurd hs (not_cond_of_flag_zero h2 hz)
  · have hnew : newCap xs.size c = c := if_neg hs
    have hT : growTime C xs.size c = 0 := if_neg hs
    have hP : growPeak xs.size c = 0 := if_neg hs
    rw [hnew, hT, hP]
    apply Triple.ifNZ
    · rintro s ⟨⟨_, h3⟩, hnz⟩
      exact absurd (cond_of_flag_ne h3 hnz) hs
    · exact (Triple.skip fun s hs => ⟨hs.1.1.1, hs.1.1.2.1⟩).weaken
        (le_refl _) (by simp) (by simp)

/-- One push: the first `xs.size + 1` words become `xs.push x`, length `newCap`,
exact time `pushTime`, memory net the length growth (0, or `c` on a doubling push)
and peak `growPeak` (0, or the whole new length `2c` on a doubling push, old and new
coexisting during the copy). -/
theorem push_spec {C : CostModel} (b : BufId) (x : Word w) (xs : Array (Word w)) (c : ℕ)
    (hc1 : 1 ≤ c) (hsz : xs.size ≤ c) (hw : 2 * c < 2 ^ w) :
    Triple C RandomTape.zero (fun s => Pre b xs c s ∧ s.regs 1 = x) (pushCode b)
      (Pre b (xs.push x) (newCap xs.size c))
      (pushTime C xs.size c)
      ((newCap xs.size c : ℤ) - c) (growPeak xs.size c) := by
  have h1 : Triple C RandomTape.zero (fun s => Pre b xs c s ∧ s.regs 1 = x) (.memLen 2 b)
      (fun s => Pre b xs c s ∧ s.regs 1 = x ∧ s.regs 2 = BitVec.ofNat w c)
      C.memLen 0 0 := by
    apply Triple.memLen
    rintro s ⟨hpre, hx⟩
    exact ⟨hpre.setReg _ (by decide), by simp [hx], by simp [hpre.1]⟩
  have h2 : Triple C RandomTape.zero
      (fun s => Pre b xs c s ∧ s.regs 1 = x ∧ s.regs 2 = BitVec.ofNat w c)
      (.bin .eq 3 0 2)
      (fun s => (Pre b xs c s ∧ s.regs 1 = x ∧ s.regs 2 = BitVec.ofNat w c)
        ∧ s.regs 3 = if xs.size = c then 1 else 0)
      (C.bin .eq) 0 0 := by
    apply Triple.bin
    rintro s ⟨hpre, hx, hl⟩
    refine ⟨⟨hpre.setReg _ (by decide), by simp [hx], by simp [hl]⟩, ?_⟩
    simp [hl, hpre.2.1, ofNat_eq_ofNat_iff (w := w) (a := xs.size) (b := c) (by omega) (by omega)]
  have h3 := grow_spec (C := C) b x xs c hc1 hw
  have hlt : xs.size < newCap xs.size c := by unfold newCap; split <;> omega
  have hsw : xs.size < 2 ^ w := by omega
  have h4 : Triple C RandomTape.zero
      (fun s => Pre b xs (newCap xs.size c) s ∧ s.regs 1 = x)
      (.memStore b 0 1 ;; .imm 4 1 ;; .bin .add 0 0 4)
      (Pre b (xs.push x) (newCap xs.size c))
      (C.memStore + (C.imm + C.bin .add)) 0 0 := by
    rintro s ⟨⟨hsize, h0, hpre⟩, hx⟩
    have hv : (s.regs 0).toNat = xs.size := by
      rw [h0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsw]
    have hst : (s.regs 0).toNat < (s.bufs b).size := by rw [hv, hsize]; exact hlt
    refine ⟨_, _, _, _, .seq (.memStore hst) (.seq .imm .bin), ⟨?_, ?_, ?_⟩,
      le_refl _, le_refl _, le_refl _⟩
    · simp [hsize]
    · simp [h0, Array.size_push, BitVec.ofNat_add]
    · intro j hj
      simp only [Array.size_push] at hj
      simp only [regs_setReg_ne _ _ (show (0 : ℕ) ≠ 4 by decide), bufs_setReg,
        bufs_setBuf_self, Array.getElem?_set, hv, Array.getElem?_push]
      by_cases hjs : j = xs.size
      · subst hjs; simp [hx]
      · rw [if_neg (Ne.symm hjs), if_neg hjs]; exact hpre j (by omega)
  have hle := le_newCap xs.size c
  have hgp := newCap_le_growPeak xs.size c
  exact (h1.seq (h2.seq (h3.seq h4))).weaken (le_refl _) (by omega) (by omega)

/-! ### `n` pushes -/

/-- Push every element of `ys`, in order: load it into `r1`, run `pushCode`. -/
def pushAll (b : BufId) : List (Word w) → Stmt w
  | [] => .skip
  | x :: ys => .imm 1 x ;; pushCode b ;; pushAll b ys

/-- The capacity after `m` pushes starting at size `s`, capacity `c`. -/
def capAfter : ℕ → ℕ → ℕ → ℕ
  | _, c, 0 => c
  | s, c, m + 1 => capAfter (s + 1) (newCap s c) m

/-- Exact time of `m` pushes (each with its element load) starting at size `s`,
capacity `c`. -/
def pushesTime (C : CostModel) : ℕ → ℕ → ℕ → ℕ
  | _, _, 0 => 0
  | s, c, m + 1 => C.imm + pushTime C s c + pushesTime C (s + 1) (newCap s c) m

theorem le_capAfter : ∀ (m s c : ℕ), c ≤ capAfter s c m
  | 0, _, _ => le_refl _
  | m + 1, s, c => (le_newCap s c).trans (le_capAfter m (s + 1) (newCap s c))

/-- `ys.length` pushes append `ys`, in time `pushesTime`, with net memory the total
capacity growth and peak at most twice it (a doubling from `c'` to `2c'` peaks at
`2c'` above its start, and `2c'` is at most the final capacity). The width
hypotheses keep the size, the capacity and its doubling below `2 ^ w`. -/
theorem pushAll_spec {C : CostModel} (b : BufId) :
    ∀ (ys : List (Word w)) (xs : Array (Word w)) (c : ℕ),
      1 ≤ c → xs.size ≤ c → 2 * c < 2 ^ w → 4 * (xs.size + ys.length) ≤ 2 ^ w →
      Triple C RandomTape.zero (Pre b xs c) (pushAll b ys)
        (Pre b (xs ++ ys.toArray) (capAfter xs.size c ys.length))
        (pushesTime C xs.size c ys.length)
        ((capAfter xs.size c ys.length : ℤ) - c)
        (2 * ((capAfter xs.size c ys.length : ℤ) - c))
  | [], xs, c, _, _, _, _ =>
    (Triple.skip fun s hs => by simpa [capAfter] using hs).weaken
      (le_refl _) (by simp [capAfter]) (by simp [capAfter])
  | x :: ys, xs, c, hc1, hsz, hw, hW => by
    have hld : Triple C RandomTape.zero (Pre b xs c) (.imm 1 x)
        (fun s => Pre b xs c s ∧ s.regs 1 = x) C.imm 0 0 := by
      apply Triple.imm
      intro s hpre
      exact ⟨hpre.setReg _ (by decide), by simp⟩
    have hp := push_spec (C := C) b x xs c hc1 hsz hw
    have hnc := le_newCap xs.size c
    have hc1' : 1 ≤ newCap xs.size c := by omega
    have hsz' : (xs.push x).size ≤ newCap xs.size c := by
      simp only [Array.size_push]; unfold newCap; split <;> omega
    have hw' : 2 * newCap xs.size c < 2 ^ w := by
      simp only [List.length_cons] at hW; unfold newCap; split <;> omega
    have hW' : 4 * ((xs.push x).size + ys.length) ≤ 2 ^ w := by
      simp only [Array.size_push, List.length_cons] at hW ⊢; omega
    have ih := pushAll_spec (C := C) b ys (xs.push x) (newCap xs.size c) hc1' hsz' hw' hW'
    have hfin := le_capAfter ys.length (xs.size + 1) (newCap xs.size c)
    have hgp := growPeak_le xs.size c
    simp only [Array.size_push] at ih
    refine (hld.seq (hp.seq ih)).conseq (fun _ h => h) ?_ ?_ ?_ ?_
    · have harr : xs.push x ++ ys.toArray = xs ++ (x :: ys).toArray := by
        apply Array.ext'; simp
      intro s hs
      rw [← harr]
      exact hs
    · simp only [pushesTime, List.length_cons]; omega
    · simp only [capAfter, List.length_cons]; omega
    · simp only [capAfter, List.length_cons]; omega

/-! ### The amortized bound -/

/-- Base cost of one push, the doubling's constant parts included. -/
def amortBase (C : CostModel) : ℕ :=
  C.memLen + C.bin .eq + C.branch + C.bin .add + C.memResize + C.memStore + C.imm
    + C.bin .add

/-- The amortized cost of one push (with its element load): the base, plus four
words' worth of resize charge deposited into the potential. -/
def amortCost (C : CostModel) : ℕ :=
  C.imm + amortBase C + 4 * C.allocPerWord

/-- One push pays for itself against the potential `Φ(s, c) = (4s - 2c) · a`,
stated subtraction-free: `pushTime + Φ(after) ≤ amortBase + 4a + Φ(before)`. A
doubling push at `s = c` costs `2c · a` in resize charge, exactly what the drop of
`Φ` from `2c · a` to `4a` releases. -/
theorem pushTime_amortized (C : CostModel) (s c : ℕ) :
    pushTime C s c + 4 * (s + 1) * C.allocPerWord + 2 * c * C.allocPerWord
      ≤ amortBase C + 4 * C.allocPerWord + 4 * s * C.allocPerWord
        + 2 * newCap s c * C.allocPerWord := by
  unfold pushTime growTime newCap amortBase
  split
  · subst_vars; ring_nf; omega
  · ring_nf; omega

/-- Telescoping the potential over `m` pushes. -/
theorem pushesTime_amortized (C : CostModel) : ∀ (m s c : ℕ),
    pushesTime C s c m + 4 * (s + m) * C.allocPerWord + 2 * c * C.allocPerWord
      ≤ m * amortCost C + 4 * s * C.allocPerWord + 2 * capAfter s c m * C.allocPerWord
  | 0, s, c => by simp [pushesTime, capAfter]
  | m + 1, s, c => by
    have ih := pushesTime_amortized C m (s + 1) (newCap s c)
    have hs := pushTime_amortized C s c
    simp only [pushesTime, capAfter, amortCost] at ih hs ⊢
    nlinarith [ih, hs]

/-- From capacity at most twice the size (or the initial capacity 1), the capacity
stays at most twice the size. -/
theorem capAfter_le : ∀ (m s c : ℕ), 1 ≤ c → s ≤ c → c ≤ max 1 (2 * s) →
    capAfter s c m ≤ max 1 (2 * (s + m))
  | 0, s, c, _, _, h => by simpa [capAfter] using h
  | m + 1, s, c, h1, hs, h => by
    have := capAfter_le m (s + 1) (newCap s c) (by unfold newCap; split <;> omega)
      (by unfold newCap; split <;> omega) (by unfold newCap; split <;> omega)
    simp only [capAfter]
    omega

/-- Amortized linear time: `n` pushes into an empty vector of capacity 1 cost at
most `n * amortCost C`, i.e. `amortBase C + C.imm + 4 · allocPerWord` per push,
however many doublings they trigger. -/
theorem pushesTime_le (C : CostModel) (n : ℕ) : pushesTime C 0 1 n ≤ n * amortCost C := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pushesTime]
  have h := pushesTime_amortized C n 0 1
  have hcap := capAfter_le n 0 1 (le_refl _) (Nat.zero_le _) (by simp)
  have hcap' : 2 * capAfter 0 1 n ≤ 4 * n := by omega
  have := Nat.mul_le_mul_right C.allocPerWord hcap'
  simp only [Nat.zero_add, Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at h
  nlinarith [h, this]

/-- `n` pushes into an empty capacity-1 vector: contents `ys`, amortized linear
time `n * amortCost C`, net memory growth at most `2n` words (the final capacity is
at most `max 1 (2n)`) and peak at most `4n` words (the last doubling's transient
old-plus-new overlap included). -/
theorem fromOne_spec {C : CostModel} (b : BufId) (ys : List (Word w))
    (hW : 4 * (ys.length + 1) ≤ 2 ^ w) :
    Triple C RandomTape.zero (Pre b #[] 1) (pushAll b ys)
      (fun s => ∀ j, j < ys.length → (s.bufs b)[j]? = ys[j]?)
      (ys.length * amortCost C) (2 * ys.length) (4 * ys.length) := by
  have h := pushAll_spec (C := C) b ys #[] 1 (le_refl _) (by simp) (by omega)
    (by simp; omega)
  have hcap := capAfter_le ys.length 0 1 (le_refl _) (Nat.zero_le _) (by simp)
  simp only [List.size_toArray, List.length_nil] at h hcap
  refine h.conseq (fun _ h => h) (fun s hs => by simpa using hs.2.2)
    (pushesTime_le C ys.length) ?_ ?_ <;> omega

/-! ### Pins -/

/-- Resize the empty vector to length 1, zero the fill in `r0`, push `ys`. -/
def demoProg (ys : List (Word w)) : Stmt w :=
  .memResizeI 0 1 ;; .imm 0 0 ;; pushAll 0 ys

/-- Five pushes from length 1: doublings at fills 1, 2 and 4, final length 8, the
last three words still zero. `(buffer, fill, time, net, peak)`: time
`54 = 2 + pushesTime .unit 0 1 5`, net memory 8 and peak 12: the last doubling,
from 4 to 8 words, holds both regions at once on top of the 4 already live. -/
def demo : Option (Array (Word 64) × ℕ × ℕ × ℤ × ℤ) :=
  (run .unit Caliper.RandomTape.zero 1000 (demoProg [10, 20, 30, 40, 50])
      (State.init 64)).map
    fun (s, t, d, p) => (s.bufs 0, (s.regs 0).toNat, t, d, p)

/-- info: some (#[10#64, 20#64, 30#64, 40#64, 50#64, 0#64, 0#64, 0#64], 5, 54, 8, 12) -/
#guard_msgs in
#eval demo

/-- info: 52 -/
#guard_msgs in
#eval pushesTime .unit 0 1 5

/-- The amortized constant in the unit model: 12 per push. -/
example : amortCost .unit = 12 := rfl

#guard pushesTime .unit 0 1 1000 ≤ 1000 * amortCost .unit

/-- info: 4 -/
#guard_msgs in
#eval (pushCode (w := 64) 0).regPeak₀

end GrowVec

end Caliper.Corpus
