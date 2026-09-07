import Caliper.Outcome
import Caliper.Triple

/-!
# Probabilistic resource triples

The postcondition and buffer bounds hold on almost every uniform tape. Time is
bounded in expectation using the runtime PMF. Fixed-tape triples remain
available for proofs that cover every supplied tape.
-/

open MeasureTheory
open scoped ENNReal

namespace Caliper

variable {w : ℕ} {C : CostModel}

/-- Almost-sure safe correctness and memory bounds, with an expected-time bound. -/
def ProbTriple (C : CostModel) (P : State w → Prop) (c : Stmt w) (Q : State w → Prop)
    (T : ℝ≥0∞) (D M : ℤ) : Prop :=
  ∀ s, P s →
    (∀ᵐ tape ∂uniformTape w, ∃ s' t d p,
      Exec C tape c s s' t d p ∧ Q s' ∧ d ≤ D ∧ p ≤ M) ∧
    (runTimePMF C c s).expect ENat.toENNReal ≤ T

/-- Bound a PMF expectation by an almost-everywhere bound on witnessed executions. -/
theorem runTimePMF_expect_le {c : Stmt w} {s : State w}
    (f : RandomTape w → ℝ≥0∞)
    (h : ∀ᵐ tape ∂uniformTape w, ∃ s' t d p,
      Exec C tape c s s' t d p ∧ (t : ℝ≥0∞) ≤ f tape) :
    (runTimePMF C c s).expect ENat.toENNReal ≤ ∫⁻ tape, f tape ∂uniformTape w := by
  rw [runTimePMF_expect_eq]
  apply lintegral_mono_ae
  filter_upwards [h] with tape ht
  obtain ⟨s', t, d, p, he, ht⟩ := ht
  simpa only [runTime_of_exec he, ENat.toENNReal_coe] using ht

namespace ProbTriple

theorem conseq {P P' Q Q' : State w → Prop} {c : Stmt w} {T T' : ℝ≥0∞}
    {D D' M M' : ℤ} (h : ProbTriple C P c Q T D M)
    (hP : ∀ s, P' s → P s) (hQ : ∀ s, Q s → Q' s)
    (hT : T ≤ T') (hD : D ≤ D') (hM : M ≤ M') :
    ProbTriple C P' c Q' T' D' M' := by
  intro s hs
  obtain ⟨ha, ht⟩ := h s (hP s hs)
  refine ⟨?_, ht.trans hT⟩
  filter_upwards [ha] with tape ha
  obtain ⟨s', t, d, p, he, hq, hd, hp⟩ := ha
  exact ⟨s', t, d, p, he, hQ s' hq, hd.trans hD, hp.trans hM⟩

/-- Every all-tape worst-case proof also gives a probabilistic specification. -/
theorem of_forall_triple {P Q : State w → Prop} {c : Stmt w} {T : ℕ} {D M : ℤ}
    (h : ∀ tape, Triple C tape P c Q T D M) : ProbTriple C P c Q T D M := by
  intro s hs
  constructor
  · apply Filter.Eventually.of_forall
    intro tape
    obtain ⟨s', t, d, p, he, hq, _, hd, hp⟩ := h tape s hs
    exact ⟨s', t, d, p, he, hq, hd, hp⟩
  · calc
      _ ≤ ∫⁻ _ : RandomTape w, (T : ℝ≥0∞) ∂uniformTape w :=
        runTimePMF_expect_le _ (Filter.Eventually.of_forall fun tape => by
          obtain ⟨s', t, d, p, he, _, ht, _, _⟩ := h tape s hs
          exact ⟨s', t, d, p, he, by exact_mod_cast ht⟩)
      _ = T := by simp

/-- Deterministic library routines can be called from randomized programs using
an existing fixed-tape specification and a syntactic no-randomness certificate. -/
theorem of_randomFree {P Q : State w → Prop} {c : Stmt w} {T : ℕ} {D M : ℤ}
    {tape : RandomTape w} (h : Triple C tape P c Q T D M) (hc : c.RandomFree) :
    ProbTriple C P c Q T D M :=
  of_forall_triple fun other => h.withTape_of_randomFree hc other

protected theorem skip {P Q : State w → Prop} (h : ∀ s, P s → Q s) :
    ProbTriple C P (.skip (w := w)) Q 0 0 0 := by
  exact_mod_cast of_forall_triple (fun _ => Triple.skip h)

/-- Every possible word must establish the postcondition. -/
protected theorem rand {P Q : State w → Prop} {r : Reg}
    (h : ∀ s, P s → ∀ v : Word w, Q { s.setReg r v with tapePos := s.tapePos + 1 }) :
    ProbTriple C P (.rand r) Q C.rand 0 0 :=
  of_forall_triple fun tape => Triple.rand (fun s hs => h s hs (tape s.tapePos))

/-- Sequential composition uses the unread uniform tail, including when the first
subroutine consumes a variable number of words. Costs add; buffer peaks compose
with the net allocation of the first subroutine. -/
protected theorem seq {P R Q : State w → Prop} {c₁ c₂ : Stmt w} {T₁ T₂ : ℝ≥0∞}
    {D₁ M₁ D₂ M₂ : ℤ}
    (h₁ : ProbTriple C P c₁ R T₁ D₁ M₁) (h₂ : ProbTriple C R c₂ Q T₂ D₂ M₂) :
    ProbTriple C P (c₁ ;; c₂) Q (T₁ + T₂) (D₁ + D₂) (max M₁ (D₁ + M₂)) := by
  classical
  intro s hs
  let good : Set (Outcome w) := {r | r ∈ possibleOutcomes C c₁ s ∧
    R r.1 ∧ r.2.2.1 ≤ D₁ ∧ r.2.2.2 ≤ M₁}
  have hc : good.Countable := (possibleOutcomes_countable C c₁ s).mono (fun _ h => h.1)
  letI : Countable good := hc.to_subtype
  let E (a : good) : Set (RandomTape w) := {tape | HasOutcome C tape c₁ s a.val}
  let f (a : good) (tape : RandomTape w) :=
    ENat.toENNReal (runTime C c₂ a.val.1 tape)
  have hE a : MeasurableSet[RandomTape.prefixSigma a.val.1.tapePos] (E a) :=
    HasOutcome.measurableSet C c₁ s a.val
  have hm a : MeasurableSet (E a) := RandomTape.prefixSigma_le _ _ (hE a)
  have hf a : Measurable[RandomTape.tailSigma a.val.1.tapePos] (f a) :=
    (measurable_of_countable ENat.toENNReal).comp (runTime_tail_measurable C c₂ a.val.1)
  have hfm a : Measurable (f a) := (hf a).mono (RandomTape.tailSigma_le _) le_rfl
  have hd : Pairwise (fun a b => Disjoint (E a) (E b)) := by
    intro a b hab
    exact HasOutcome.disjoint (fun h => hab (Subtype.ext h))
  have hmass : (∑' a, uniformTape w (E a)) ≤ 1 := by
    rw [← measure_iUnion hd hm]
    simpa using (measure_mono (Set.subset_univ (⋃ a, E a)) : uniformTape w (⋃ a, E a) ≤ uniformTape w Set.univ)
  obtain ⟨ha₁, ht₁⟩ := h₁ s hs
  have ha₂ : ∀ᵐ tape ∂uniformTape w, ∀ a : good, ∃ s' t d p,
      Exec C tape c₂ a.val.1 s' t d p ∧ Q s' ∧ d ≤ D₂ ∧ p ≤ M₂ :=
    ae_all_iff.mpr (fun a => (h₂ a.val.1 a.property.2.1).1)
  have ha : ∀ᵐ tape ∂uniformTape w, ∃ a : good, ∃ s' t d p,
      HasOutcome C tape c₁ s a.val ∧ Exec C tape c₂ a.val.1 s' t d p ∧
      Q s' ∧ d ≤ D₂ ∧ p ≤ M₂ := by
    filter_upwards [ha₁, ha₂] with tape h₁t h₂t
    obtain ⟨s₁, t₁, d₁, p₁, he₁, hr, hd₁, hp₁⟩ := h₁t
    let a : good := ⟨(s₁, t₁, d₁, p₁), ⟨⟨tape, he₁⟩, hr, hd₁, hp₁⟩⟩
    obtain ⟨s', t, d, p, he₂, hq, hd₂, hp₂⟩ := h₂t a
    exact ⟨a, s', t, d, p, he₁, he₂, hq, hd₂, hp₂⟩
  constructor
  · filter_upwards [ha] with tape ht
    obtain ⟨a, s', t, d, p, he₁, he₂, hq, hd₂, hp₂⟩ := ht
    have hd₁ := a.property.2.2.1
    have hp₁ := a.property.2.2.2
    exact ⟨s', a.val.2.1 + t, a.val.2.2.1 + d, max a.val.2.2.2 (a.val.2.2.1 + p),
      .seq he₁ he₂, hq, by omega, by omega⟩
  · let future (tape : RandomTape w) := ∑' a : good, (E a).indicator (f a) tape
    have hfuture : (∫⁻ tape, future tape ∂uniformTape w) ≤ T₂ := by
      rw [show (∫⁻ tape, future tape ∂uniformTape w) =
        ∑' a : good, ∫⁻ tape, (E a).indicator (f a) tape ∂uniformTape w from
        lintegral_tsum (fun a => ((hfm a).indicator (hm a)).aemeasurable)]
      simp_rw [lintegral_prefix_indicator_future _ (hE _) _ (hf _)]
      calc
        _ ≤ ∑' a : good, uniformTape w (E a) * T₂ := ENNReal.tsum_le_tsum fun a => by
          apply mul_le_mul_right
          rw [← runTimePMF_expect_eq]
          exact (h₂ a.val.1 a.property.2.1).2
        _ = (∑' a : good, uniformTape w (E a)) * T₂ := ENNReal.tsum_mul_right
        _ ≤ 1 * T₂ := mul_le_mul_left hmass T₂
        _ = T₂ := one_mul _
    calc
      _ ≤ ∫⁻ tape, ENat.toENNReal (runTime C c₁ s tape) + future tape
          ∂uniformTape w := runTimePMF_expect_le _ (by
        filter_upwards [ha] with tape ht
        obtain ⟨a, s', t, d, p, he₁, he₂, _, _, _⟩ := ht
        refine ⟨s', a.val.2.1 + t, _, _, .seq he₁ he₂, ?_⟩
        rw [runTime_of_exec he₁, ENat.toENNReal_coe, Nat.cast_add]
        apply add_le_add_right
        have hterm := ENNReal.le_tsum (f := fun a : good => (E a).indicator (f a) tape) a
        simpa only [Set.indicator_of_mem (show tape ∈ E a from he₁), f,
          runTime_of_exec he₂, ENat.toENNReal_coe] using hterm)
      _ = (runTimePMF C c₁ s).expect ENat.toENNReal +
          ∫⁻ tape, future tape ∂uniformTape w := by
        have hm₁ : Measurable (fun tape => ENat.toENNReal (runTime C c₁ s tape)) :=
          (measurable_of_countable ENat.toENNReal).comp (measurable_runTime C c₁ s)
        rw [lintegral_add_left hm₁, runTimePMF_expect_eq]
      _ ≤ T₁ + T₂ := add_le_add ht₁ hfuture

/-- Branch on a register value; branch selection cannot inspect semantic costs. -/
protected theorem ifNZ {P Q : State w → Prop} {r : Reg} {a b : Stmt w}
    {T : ℝ≥0∞} {D M : ℤ}
    (ha : ProbTriple C (fun s => P s ∧ s.regs r ≠ 0) a Q T D M)
    (hb : ProbTriple C (fun s => P s ∧ s.regs r = 0) b Q T D M) :
    ProbTriple C P (.ifNZ r a b) Q (C.branch + T) D M := by
  intro s hs
  by_cases hz : s.regs r = 0
  · obtain ⟨hc, ht⟩ := hb s ⟨hs, hz⟩
    constructor
    · filter_upwards [hc] with tape he
      obtain ⟨s', t, d, p, he, hq, hd, hp⟩ := he
      exact ⟨s', C.branch + t, d, p, .ifNZ_false hz he, hq, hd, hp⟩
    · calc
        _ ≤ ∫⁻ tape, (C.branch : ℝ≥0∞) + ENat.toENNReal (runTime C b s tape)
            ∂uniformTape w := runTimePMF_expect_le _ (by
          filter_upwards [hc] with tape he
          obtain ⟨s', t, d, p, he, _, _, _⟩ := he
          refine ⟨s', C.branch + t, d, p, .ifNZ_false hz he, ?_⟩
          simp only [runTime_of_exec he, ENat.toENNReal_coe, Nat.cast_add, le_refl])
        _ = C.branch + (runTimePMF C b s).expect ENat.toENNReal := by
          rw [lintegral_add_left measurable_const, runTimePMF_expect_eq]
          simp
        _ ≤ C.branch + T := add_le_add_right ht _
  · obtain ⟨hc, ht⟩ := ha s ⟨hs, hz⟩
    constructor
    · filter_upwards [hc] with tape he
      obtain ⟨s', t, d, p, he, hq, hd, hp⟩ := he
      exact ⟨s', C.branch + t, d, p, .ifNZ_true hz he, hq, hd, hp⟩
    · calc
        _ ≤ ∫⁻ tape, (C.branch : ℝ≥0∞) + ENat.toENNReal (runTime C a s tape)
            ∂uniformTape w := runTimePMF_expect_le _ (by
          filter_upwards [hc] with tape he
          obtain ⟨s', t, d, p, he, _, _, _⟩ := he
          refine ⟨s', C.branch + t, d, p, .ifNZ_true hz he, ?_⟩
          simp only [runTime_of_exec he, ENat.toENNReal_coe, Nat.cast_add, le_refl])
        _ = C.branch + (runTimePMF C a s).expect ENat.toENNReal := by
          rw [lintegral_add_left measurable_const, runTimePMF_expect_eq]
          simp
        _ ≤ C.branch + T := add_le_add_right ht _

/-- A countable collection of terminating cases suffices for unbounded randomized
computations. The masses must sum to one; failed runs are never conditioned away.
The cases can, for example, enumerate the number of iterations of a retry loop. -/
theorem of_countable_cases {α : Type*} [Countable α] {P Q : State w → Prop}
    {c : Stmt w} {T : ℝ≥0∞} {D M : ℤ}
    (E : State w → α → Set (RandomTape w)) (cost : α → ℕ)
    (hm : ∀ s a, MeasurableSet (E s a))
    (hd : ∀ s, Pairwise (fun a b => Disjoint (E s a) (E s b)))
    (hmass : ∀ s, P s → (∑' a, uniformTape w (E s a)) = 1)
    (hexec : ∀ s, P s → ∀ a tape, tape ∈ E s a → ∃ s' t d p,
      Exec C tape c s s' t d p ∧ Q s' ∧ t ≤ cost a ∧ d ≤ D ∧ p ≤ M)
    (htime : ∀ s, P s → (∑' a, uniformTape w (E s a) * (cost a : ℝ≥0∞)) ≤ T) :
    ProbTriple C P c Q T D M := by
  classical
  intro s hs
  have hcover : ∀ᵐ tape ∂uniformTape w, tape ∈ ⋃ a, E s a := by
    apply (mem_ae_iff_prob_eq_one (MeasurableSet.iUnion (hm s))).mpr
    rw [measure_iUnion (hd s) (hm s), hmass s hs]
  constructor
  · filter_upwards [hcover] with tape ht
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp ht
    obtain ⟨s', t, d, p, he, hq, _, hD, hM⟩ := hexec s hs a tape ha
    exact ⟨s', t, d, p, he, hq, hD, hM⟩
  · calc
      _ ≤ ∫⁻ tape, ∑' a, (E s a).indicator (fun _ => (cost a : ℝ≥0∞)) tape
          ∂uniformTape w := runTimePMF_expect_le _ (by
        filter_upwards [hcover] with tape ht
        obtain ⟨a, ha⟩ := Set.mem_iUnion.mp ht
        obtain ⟨s', t, d, p, he, _, hc, _, _⟩ := hexec s hs a tape ha
        refine ⟨s', t, d, p, he, ?_⟩
        calc
          (t : ℝ≥0∞) ≤ cost a := by exact_mod_cast hc
          _ = (E s a).indicator (fun _ => (cost a : ℝ≥0∞)) tape :=
            (Set.indicator_of_mem ha (fun _ => (cost a : ℝ≥0∞))).symm
          _ ≤ _ := ENNReal.le_tsum a)
      _ = ∑' a, uniformTape w (E s a) * (cost a : ℝ≥0∞) := by
        rw [lintegral_tsum (fun a => (measurable_const.indicator (hm s a)).aemeasurable)]
        congr 1
        funext a
        rw [lintegral_indicator (hm s a)]
        simp [mul_comm]
      _ ≤ T := htime s hs

end ProbTriple
end Caliper
