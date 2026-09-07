import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Data.Real.ENatENNReal

/-!
# Expectations of discrete distributions

This API is generic in the PMF and its observable. In particular, Caliper's
termination-time distribution needs no separate program-specific expectation.
-/

open MeasureTheory
open scoped ENNReal

namespace PMF

variable {α β : Type*}

/-- Extended nonnegative expectation; zero mass contributes zero even at `∞`. -/
noncomputable def expect (p : PMF α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' x, p x * f x

@[simp] theorem expect_pure (x : α) (f : α → ℝ≥0∞) :
    (PMF.pure x).expect f = f x := by
  classical
  simp [expect, PMF.pure_apply]

theorem expect_mono (p : PMF α) {f g : α → ℝ≥0∞} (h : ∀ x, f x ≤ g x) :
    p.expect f ≤ p.expect g :=
  ENNReal.tsum_le_tsum fun x => mul_le_mul_right (h x) (p x)

@[simp] theorem expect_const (p : PMF α) (v : ℝ≥0∞) :
    p.expect (fun _ => v) = v := by
  simp only [expect, ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

theorem expect_add (p : PMF α) (f g : α → ℝ≥0∞) :
    p.expect (fun x => f x + g x) = p.expect f + p.expect g := by
  simp only [expect, mul_add, ENNReal.tsum_add]

theorem expect_bind (p : PMF α) (q : α → PMF β) (f : β → ℝ≥0∞) :
    (p.bind q).expect f = p.expect (fun x => (q x).expect f) := by
  simp only [expect, PMF.bind_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp only [← ENNReal.tsum_mul_left, mul_assoc]

theorem expect_map (p : PMF α) (g : α → β) (f : β → ℝ≥0∞) :
    (p.map g).expect f = p.expect (fun x => f (g x)) := by
  change (p.bind (fun x => PMF.pure (g x))).expect f = _
  simp only [expect_bind, expect_pure]

/-- The discrete sum agrees with the measure-theoretic expectation. -/
theorem expect_eq_lintegral [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (f : α → ℝ≥0∞) :
    p.expect f = ∫⁻ x, f x ∂p.toMeasure := by
  simp only [expect, lintegral_countable', PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), mul_comm]

end PMF
