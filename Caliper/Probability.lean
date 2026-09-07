import Caliper.Tape
import Caliper.PMF
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.Data.ENat.Lattice

/-!
# Uniform tapes and runtime distributions

Execution remains deterministic. Probability is the product measure on input words.
The induced runtime PMF retains unsuccessful executions as mass at `∞`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Caliper

variable {w : ℕ}

/-- Words have exactly `2^w` possible values. -/
def Word.equivFin : Word w ≃ Fin (2 ^ w) where
  toFun := BitVec.toFin
  invFun := BitVec.ofFin
  left_inv x := by cases x; rfl
  right_inv _ := rfl

instance : Fintype (Word w) := Fintype.ofEquiv (Fin (2 ^ w)) Word.equivFin.symm

@[simp] theorem Word.card : Fintype.card (Word w) = 2 ^ w :=
  (Fintype.card_congr Word.equivFin).trans (Fintype.card_fin _)

instance : MeasurableSpace (Word w) := ⊤
instance : DiscreteMeasurableSpace (Word w) := ⟨fun _ => trivial⟩

/-- Independent uniform words at every tape position. -/
noncomputable def uniformTape (w : ℕ) : Measure (RandomTape w) :=
  Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype (Word w)).toMeasure

instance : IsProbabilityMeasure (uniformTape w) := by
  unfold uniformTape
  infer_instance

/-- Tapes with a prescribed finite prefix. -/
def RandomTape.cylinder {n : ℕ} (xs : Fin n → Word w) : Set (RandomTape w) :=
  {tape | ∀ i : Fin n, tape (i : ℕ) = xs i}

theorem RandomTape.measurableSet_cylinder {n : ℕ} (xs : Fin n → Word w) :
    MeasurableSet (RandomTape.cylinder xs) := by
  unfold cylinder
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun i => (measurable_pi_apply (i : ℕ)) (measurableSet_singleton _)

/-- Any event witnessed by a finite prefix is measurable. -/
theorem RandomTape.measurableSet_of_prefix (E : Set (RandomTape w))
    (hE : ∀ tape ∈ E, ∃ n, ∀ other, (∀ i < n, other i = tape i) → other ∈ E) :
    MeasurableSet E := by
  classical
  have hEq : E = ⋃ n : ℕ, ⋃ xs : Fin n → Word w,
      if RandomTape.cylinder xs ⊆ E then RandomTape.cylinder xs else ∅ := by
    ext tape
    simp only [Set.mem_iUnion]
    constructor
    · intro ht
      obtain ⟨n, hn⟩ := hE tape ht
      refine ⟨n, fun i => tape i, ?_⟩
      have hc : RandomTape.cylinder (fun i : Fin n => tape i) ⊆ E := by
        intro other ho
        apply hn other
        intro i hi
        exact ho ⟨i, hi⟩
      simp only [if_pos hc]
      exact fun _ => rfl
    · rintro ⟨n, xs, hx⟩
      split at hx
      · exact ‹RandomTape.cylinder xs ⊆ E› hx
      · exact hx.elim
  rw [hEq]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro xs
  split
  · exact RandomTape.measurableSet_cylinder xs
  · exact MeasurableSet.empty

/-- A tape coordinate has exactly the uniform word law. -/
theorem uniformTape_eval (i : ℕ) (v : Word w) :
    uniformTape w {tape | tape i = v} = ((2 ^ w : ℕ) : ℝ≥0∞)⁻¹ := by
  have h := congrArg (fun μ : Measure (Word w) => μ {v})
    (Measure.infinitePi_map_eval (fun _ : ℕ => (PMF.uniformOfFintype (Word w)).toMeasure) i)
  rw [Measure.map_apply (measurable_pi_apply i) (measurableSet_singleton v)] at h
  simpa only [uniformTape, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.uniformOfFintype_apply,
    Word.card, Set.preimage, Set.mem_singleton_iff] using h

/-- Distinct tape positions are independent, including after any fixed offset. -/
theorem uniformTape_independent :
    iIndepFun (fun i : ℕ => fun tape : RandomTape w => tape i) (uniformTape w) :=
  iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)

/-- A specified prefix of `n` words has mass `(2^w)^(-n)`. -/
theorem uniformTape_cylinder {n : ℕ} (xs : Fin n → Word w) :
    uniformTape w (RandomTape.cylinder xs) = (((2 ^ w : ℕ) : ℝ≥0∞)⁻¹) ^ n := by
  classical
  let ext : RandomTape w := fun i => if h : i < n then xs ⟨i, h⟩ else 0
  have hset : RandomTape.cylinder xs =
      (↑(Finset.range n) : Set ℕ).pi (fun i => {ext i}) := by
    ext tape
    simp only [RandomTape.cylinder, Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe,
      Finset.mem_range, Set.mem_singleton_iff]
    constructor
    · intro h i hi
      simpa only [ext, dif_pos hi] using h ⟨i, hi⟩
    · intro h i
      simpa only [ext, dif_pos i.isLt] using h i i.isLt
  rw [hset]
  unfold uniformTape
  rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.uniformOfFintype_apply, Word.card,
    Finset.prod_const, Finset.card_range]

variable (C : CostModel) (c : Stmt w) (s : State w)

/-- An arbitrary predicate on terminating results defines a measurable tape event. -/
theorem measurableSet_exec (Q : State w → ℕ → ℤ → ℤ → Prop) :
    MeasurableSet {tape | ∃ s' t d p, Exec C tape c s s' t d p ∧ Q s' t d p} := by
  apply RandomTape.measurableSet_of_prefix
  rintro tape ⟨s', t, d, p, he, hq⟩
  refine ⟨s'.tapePos, ?_⟩
  intro other ha
  exact ⟨s', t, d, p, he.withTape other (fun i _ hi => ha i hi), hq⟩

/-- Cost of safe termination; unsuccessful execution has value `∞`. -/
noncomputable def runTime (tape : RandomTape w) : ℕ∞ :=
  by
    classical
    exact if h : ∃ t, ∃ s' d p, Exec C tape c s s' t d p then
      ((Classical.choose h : ℕ) : ℕ∞) else ⊤

variable {C c s}

theorem runTime_of_exec {tape : RandomTape w} {s' : State w} {t : ℕ} {d p : ℤ}
    (h : Exec C tape c s s' t d p) : runTime C c s tape = (t : ℕ∞) := by
  have ht : ∃ t, ∃ s' d p, Exec C tape c s s' t d p := ⟨t, s', d, p, h⟩
  obtain ⟨s₀, d₀, p₀, h₀⟩ := Classical.choose_spec ht
  have heq := (h₀.deterministic h).2.1
  simp only [runTime, dif_pos ht, heq]

theorem runTime_eq_coe_iff (tape : RandomTape w) (t : ℕ) :
    runTime C c s tape = (t : ℕ∞) ↔ ∃ s' d p, Exec C tape c s s' t d p := by
  constructor
  · intro heq
    unfold runTime at heq
    split at heq
    · have ht := Classical.choose_spec ‹∃ t, ∃ s' d p, Exec C tape c s s' t d p›
      have heq' : Classical.choose ‹∃ t, ∃ s' d p, Exec C tape c s s' t d p› = t := by
        exact_mod_cast heq
      simpa only [heq'] using ht
    · simp at heq
  · rintro ⟨s', d, p, he⟩
    exact runTime_of_exec he

theorem runTime_eq_top_iff (tape : RandomTape w) :
    runTime C c s tape = ⊤ ↔ ¬ ∃ s' t d p, Exec C tape c s s' t d p := by
  constructor
  · intro ht ⟨s', t, d, p, he⟩
    rw [runTime_of_exec he] at ht
    exact ENat.coe_ne_top _ ht
  · intro hn
    apply dif_neg
    rintro ⟨t, s', d, p, he⟩
    exact hn ⟨s', t, d, p, he⟩

variable (C c s)

theorem measurable_runTime : Measurable (runTime C c s) := by
  apply ENat.measurable_iff.mpr
  intro t
  have hm := measurableSet_exec C c s (fun _ t' _ _ => t' = t)
  simpa only [Set.preimage, Set.mem_singleton_iff, runTime_eq_coe_iff,
    exists_and_right, exists_eq_right] using hm

/-- The unconditional PMF of safe termination costs, including an atom at `∞`. -/
noncomputable def runTimePMF : PMF ℕ∞ :=
  letI : IsProbabilityMeasure ((uniformTape w).map (runTime C c s)) :=
    Measure.isProbabilityMeasure_map (measurable_runTime C c s).aemeasurable
  ((uniformTape w).map (runTime C c s)).toPMF

/-- PMF atoms are exactly the corresponding tape-event probabilities. -/
theorem runTimePMF_apply (t : ℕ∞) :
    runTimePMF C c s t = uniformTape w {tape | runTime C c s tape = t} := by
  unfold runTimePMF
  rw [Measure.toPMF_apply, Measure.map_apply (measurable_runTime C c s)
    (measurableSet_singleton t)]
  rfl

/-- Expectations of the PMF agree with integration over tapes for every observable. -/
theorem runTimePMF_expect_eq (f : ℕ∞ → ℝ≥0∞) :
    (runTimePMF C c s).expect f =
      ∫⁻ tape, f (runTime C c s tape) ∂uniformTape w := by
  rw [PMF.expect_eq_lintegral]
  unfold runTimePMF
  rw [Measure.toPMF_toMeasure, lintegral_map (measurable_of_countable f)
    (measurable_runTime C c s)]

/-- Zero mass at infinity is exactly almost-sure safe termination. -/
theorem runTimePMF_top_eq_zero_iff :
    runTimePMF C c s ⊤ = 0 ↔
      ∀ᵐ tape ∂uniformTape w, ∃ s' t d p, Exec C tape c s s' t d p := by
  rw [runTimePMF_apply, ae_iff]
  simp only [runTime_eq_top_iff]

/-- A constant runtime gives a point-mass distribution. -/
theorem runTimePMF_eq_pure (t : ℕ∞)
    (h : ∀ tape, runTime C c s tape = t) :
    runTimePMF C c s = PMF.pure t := by
  classical
  apply PMF.ext
  intro t'
  rw [runTimePMF_apply, PMF.pure_apply]
  simp only [h]
  by_cases ht : t' = t
  · subst t'; simp
  · have ht' : t ≠ t' := Ne.symm ht
    simp [ht, ht']

/-- A random-free terminating computation has the same cost on every tape. -/
theorem runTimePMF_of_randomFree {tape : RandomTape w} {s' : State w}
    {t : ℕ} {d p : ℤ} (h : Exec C tape c s s' t d p) (hc : c.RandomFree) :
    runTimePMF C c s = PMF.pure (t : ℕ∞) :=
  runTimePMF_eq_pure C c s t fun other =>
    runTime_of_exec (h.withTape_of_randomFree hc other)

/-- Probability of a property of a safely terminating outcome. -/
noncomputable def resultProb (Q : State w → ℕ → ℤ → ℤ → Prop) : ℝ≥0∞ :=
  uniformTape w {tape | ∃ s' t d p, Exec C tape c s s' t d p ∧ Q s' t d p}

/-- For an explicitly known total execution, outcome probabilities simplify directly. -/
theorem resultProb_of_exec (Q : State w → ℕ → ℤ → ℤ → Prop)
    (out : RandomTape w → State w) (time : RandomTape w → ℕ)
    (net peak : RandomTape w → ℤ)
    (h : ∀ tape, Exec C tape c s (out tape) (time tape) (net tape) (peak tape)) :
    resultProb C c s Q =
      uniformTape w {tape | Q (out tape) (time tape) (net tape) (peak tape)} := by
  unfold resultProb
  congr 1
  ext tape
  constructor
  · rintro ⟨s', t, d, p, he, hq⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he.deterministic (h tape)
    exact hq
  · intro hq
    exact ⟨_, _, _, _, h tape, hq⟩

end Caliper
