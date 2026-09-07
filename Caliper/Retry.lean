import Caliper.ProbTriple
import Caliper.Geometric

/-!
# Unbounded retry on a uniform word tape

`retryZero` samples until it sees zero. It can diverge on a fixed tape, but has
almost-sure safe termination under `uniformTape`. Its specification composes with
other randomized subroutines using `ProbTriple.seq`.
-/

open MeasureTheory
open scoped ENNReal

namespace Caliper

variable {w : ℕ}

/-- Exactly `n` failures followed by the first zero word. -/
def RandomTape.firstZero (n : ℕ) : Set (RandomTape w) :=
  {tape | (∀ i < n, tape i ≠ 0) ∧ tape n = 0}

theorem RandomTape.measurableSet_firstZero (n : ℕ) :
    MeasurableSet (RandomTape.firstZero (w := w) n) := by
  apply RandomTape.measurableSet_of_prefix
  intro tape ht
  refine ⟨n + 1, ?_⟩
  intro other ha
  exact ⟨fun i hi => by rw [ha i (by omega)]; exact ht.1 i hi,
    by rw [ha n (by omega)]; exact ht.2⟩

theorem RandomTape.firstZero_disjoint :
    Pairwise (fun n m => Disjoint (RandomTape.firstZero (w := w) n) (RandomTape.firstZero m)) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro tape hn hm
  rcases lt_or_gt_of_ne hnm with h | h
  · exact hm.1 n h hn.2
  · exact hn.1 m h hm.2

/-- First-hit probabilities are geometric, with success probability `1 / 2^w`. -/
theorem uniformTape_firstZero (n : ℕ) :
    uniformTape w (RandomTape.firstZero n) =
      (1 - ((2 ^ w : ℕ) : ℝ≥0∞)⁻¹) ^ n * ((2 ^ w : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  let S (i : ℕ) : Set (Word w) := if i < n then {0}ᶜ else {0}
  have hS i : MeasurableSet (S i) := by
    dsimp [S]
    split
    · exact (measurableSet_singleton _).compl
    · exact measurableSet_singleton _
  have he : RandomTape.firstZero n = (↑(Finset.range (n + 1)) : Set ℕ).pi S := by
    ext tape
    simp only [RandomTape.firstZero, Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe,
      Finset.mem_range]
    constructor
    · rintro ⟨hn, hz⟩ i hi
      by_cases h : i < n
      · simpa [S, h] using hn i h
      · have : i = n := by omega
        subst i
        simpa [S] using hz
    · intro h
      constructor
      · intro i hi
        simpa [S, hi] using h i (by omega)
      · simpa [S] using h n (by omega)
  rw [he]
  unfold uniformTape
  rw [Measure.infinitePi_pi _ (fun i _ => hS i), Finset.prod_range_succ]
  have hp : ∀ i ∈ Finset.range n,
      (PMF.uniformOfFintype (Word w)).toMeasure (S i) =
        1 - ((2 ^ w : ℕ) : ℝ≥0∞)⁻¹ := by
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [show S i = {0}ᶜ from if_pos hi, measure_compl (measurableSet_singleton _) (measure_ne_top _ _)]
    simp only [measure_univ, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      PMF.uniformOfFintype_apply, Word.card]
  rw [Finset.prod_congr rfl hp]
  simp [S, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Word.card]

/-- Retry until a sampled word equals zero. No instruction reads the attempt count. -/
def retryZero (r : Reg) : Stmt w := .whileNZ (.rand r) r .skip

theorem retryZero_exec (C : CostModel) (r : Reg) (s : State w) (tape : RandomTape w)
    (n : ℕ) (hn : RandomTape.drop s.tapePos tape ∈ RandomTape.firstZero n) :
    Exec C tape (retryZero r) s
      { s.setReg r 0 with tapePos := s.tapePos + n + 1 }
      ((n + 1) * (C.rand + C.branch)) 0 0 := by
  induction n generalizing s with
  | zero =>
    have hz : (s.readRandom tape r).regs r = 0 := by
      simpa [RandomTape.firstZero, RandomTape.drop] using hn.2
    have he := Exec.while_done (C := C) (tape := tape) (b := Stmt.skip) Exec.rand hz
    convert he using 1 <;> simp_all [retryZero, State.readRandom, State.setReg]
  | succ n ih =>
    have hne : (s.readRandom tape r).regs r ≠ 0 := by
      simpa [RandomTape.drop] using hn.1 0 (by omega)
    have hnext : RandomTape.drop (s.readRandom tape r).tapePos tape ∈
        RandomTape.firstZero n := by
      constructor
      · intro i hi
        simpa [RandomTape.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hn.1 (i + 1) (by omega)
      · simpa [RandomTape.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn.2
    have he := Exec.while_step (C := C) (tape := tape) Exec.rand hne Exec.skip
      (ih (s.readRandom tape r) hnext)
    convert he using 1 <;>
      simp [retryZero, State.readRandom, State.setReg,
        Nat.add_assoc, Nat.add_mul, Nat.mul_add]
    · constructor
      · omega
      · funext r'
        by_cases hr : r' = r <;> simp [hr]
    · omega

/-- Every safe execution of retry is witnessed by a finite first-zero event. -/
theorem retryZero_exec_firstZero {C : CostModel} {r : Reg} {s s' : State w}
    {tape : RandomTape w} {t : ℕ} {d p : ℤ}
    (he : Exec C tape (retryZero r) s s' t d p) :
    ∃ n, RandomTape.drop s.tapePos tape ∈ RandomTape.firstZero n ∧
      t = (n + 1) * (C.rand + C.branch) := by
  have aux {c : Stmt w} {s s' : State w} {t : ℕ} {d p : ℤ}
      (he : Exec C tape c s s' t d p) : c = retryZero r →
      ∃ n, RandomTape.drop s.tapePos tape ∈ RandomTape.firstZero n ∧
        t = (n + 1) * (C.rand + C.branch) := by
    induction he with
    | while_done hg hz _ =>
      intro hc
      cases hc
      cases hg
      refine ⟨0, ⟨?_, ?_⟩, by omega⟩
      · intro i hi; omega
      · simpa [RandomTape.drop, State.readRandom, State.setReg] using hz
    | @while_step g c b s s₁ s₂ s₃ tg dg pg tb db pb tl dl pl hg hn hb hl _ _ ihl =>
      intro hc
      cases hc
      cases hg
      cases hb
      obtain ⟨n, hn', ht⟩ := ihl rfl
      refine ⟨n + 1, ⟨?_, ?_⟩, ?_⟩
      · intro i hi
        cases i with
        | zero => simpa [RandomTape.drop, State.readRandom, State.setReg] using hn
        | succ i =>
          simpa [RandomTape.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hn'.1 i (by omega)
      · simpa [RandomTape.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn'.2
      · rw [ht]; ring
    | _ => intro hc; cases hc
  exact aux he rfl

/-- Each finite runtime atom is geometric. Positive per-attempt cost makes attempt
counts distinguishable in the time PMF. -/
theorem retryZero_timePMF (C : CostModel) (r : Reg) (s : State w)
    (hC : 0 < C.rand + C.branch) (n : ℕ) :
    terminationTimePMF C (retryZero r) s (((n + 1) * (C.rand + C.branch) : ℕ) : ℕ∞) =
      (1 - ((2 ^ w : ℕ) : ℝ≥0∞)⁻¹) ^ n * ((2 ^ w : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [terminationTimePMF_apply]
  have he : {tape | terminationTime C (retryZero r) s tape =
      (((n + 1) * (C.rand + C.branch) : ℕ) : ℕ∞)} =
      RandomTape.drop s.tapePos ⁻¹' RandomTape.firstZero n := by
    ext tape
    rw [Set.mem_setOf_eq, terminationTime_eq_coe_iff]
    constructor
    · rintro ⟨s', d, p, hexec⟩
      obtain ⟨m, hm, ht⟩ := retryZero_exec_firstZero hexec
      have : n = m := by nlinarith
      subst m
      exact hm
    · intro hn
      exact ⟨_, 0, 0, retryZero_exec C r s tape n hn⟩
  rw [he, ← Measure.map_apply (RandomTape.measurable_drop _) (RandomTape.measurableSet_firstZero _),
    uniformTape_drop, uniformTape_firstZero]

/-- Almost-sure correctness of unbounded retry, for any word width and starting
cursor. Expected time is at most `2^w` times the sampling-and-branch cost. -/
theorem retryZero_spec (C : CostModel) (r : Reg) :
    ProbTriple C (fun _ : State w => True) (retryZero r) (fun s => s.regs r = 0)
      ((2 ^ w : ℕ) * (C.rand + C.branch) : ℝ≥0∞) 0 0 := by
  let E (s : State w) (n : ℕ) : Set (RandomTape w) := RandomTape.drop s.tapePos ⁻¹' RandomTape.firstZero n
  have hm (s : State w) n : MeasurableSet (E s n) :=
    (RandomTape.measurable_drop s.tapePos) (RandomTape.measurableSet_firstZero n)
  have hmass (s : State w) n : uniformTape w (E s n) =
      (1 - ((2 ^ w : ℕ) : ℝ≥0∞)⁻¹) ^ n * ((2 ^ w : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [show uniformTape w (E s n) =
      ((uniformTape w).map (RandomTape.drop s.tapePos)) (RandomTape.firstZero n) from
      (Measure.map_apply (RandomTape.measurable_drop _) (RandomTape.measurableSet_firstZero _)).symm,
      uniformTape_drop, uniformTape_firstZero]
  apply ProbTriple.of_countable_cases E (fun n => (n + 1) * (C.rand + C.branch)) hm
  · intro s n m hne
    exact (RandomTape.firstZero_disjoint hne).preimage _
  · intro s _
    simp_rw [hmass]
    exact geometric_mass _ (by positivity)
  · intro s _ n tape hn
    exact ⟨_, _, 0, 0, retryZero_exec C r s tape n hn, by simp [State.setReg],
      le_rfl, le_rfl, le_rfl⟩
  · intro s _
    simp_rw [hmass]
    simpa only [Nat.cast_add] using le_of_eq (geometric_cost (2 ^ w) (C.rand + C.branch) (by positivity))

/-- In particular, the infinity atom is zero; this is not an assumption of the model. -/
theorem retryZero_almostSure (C : CostModel) (r : Reg) (s : State w) :
    terminationTimePMF C (retryZero r) s ⊤ = 0 := by
  apply (terminationTimePMF_top_eq_zero_iff C (retryZero r) s).mpr
  filter_upwards [(retryZero_spec C r s trivial).1] with tape ht
  obtain ⟨s', t, d, p, he, _, _, _⟩ := ht
  exact ⟨s', t, d, p, he⟩

/-- Exact expected runtime, derived from the termination-time PMF. -/
theorem retryZero_expect (C : CostModel) (r : Reg) (s : State w)
    (hC : 0 < C.rand + C.branch) :
    (terminationTimePMF C (retryZero r) s).expect ENat.toENNReal =
      ((2 ^ w : ℕ) : ℝ≥0∞) * (C.rand + C.branch) := by
  apply le_antisymm
  · exact (retryZero_spec C r s trivial).2
  · let time (n : ℕ) : ℕ∞ := ((n + 1) * (C.rand + C.branch) : ℕ)
    have hinj : Function.Injective time := by
      intro n m h
      dsimp only [time] at h
      have h' : (n + 1) * (C.rand + C.branch) = (m + 1) * (C.rand + C.branch) := by
        exact_mod_cast h
      nlinarith
    have h := ENNReal.tsum_comp_le_tsum_of_injective hinj
      (fun t => terminationTimePMF C (retryZero r) s t * ENat.toENNReal t)
    simp only [time, retryZero_timePMF C r s hC, ENat.toENNReal_coe] at h
    rw [geometric_cost (2 ^ w) (C.rand + C.branch) (by positivity)] at h
    simpa only [Nat.cast_add, PMF.expect] using h

/-- A tape with no zero never safely terminates, despite almost-sure termination
under the uniform tape measure. -/
theorem retryZero_no_zero {C : CostModel} {r : Reg} {s : State w} {tape : RandomTape w}
    (h : ∀ i, tape i ≠ 0) : terminationTime C (retryZero r) s tape = ⊤ := by
  apply (terminationTime_eq_top_iff tape).mpr
  rintro ⟨s', t, d, p, he⟩
  obtain ⟨n, hn, _⟩ := retryZero_exec_firstZero he
  exact h (s.tapePos + n) hn.2

end Caliper
