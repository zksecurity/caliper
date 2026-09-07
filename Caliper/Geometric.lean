import Caliper.PMF
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-! Geometric series used to account for unbounded retry costs. -/
open scoped ENNReal

namespace Caliper

/-- The expected attempt count is a double geometric sum. This identity is valid
also at the extended endpoints, with the usual `0 * ∞ = 0` convention. -/
theorem tsum_succ_mul_geometric (r : ℝ≥0∞) :
    (∑' n : ℕ, (n + 1 : ℝ≥0∞) * r ^ n) = (1 - r)⁻¹ * (1 - r)⁻¹ := by
  rw [← ENNReal.tsum_geometric, ← ENNReal.tsum_mul_left]
  simp_rw [← ENNReal.tsum_mul_right]
  rw [← ENNReal.tsum_prod,
    ← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq
      (fun p : ℕ × ℕ => r ^ p.2 * r ^ p.1)]
  change _ = ∑' c : (n : ℕ) × ↥(Finset.antidiagonal n), r ^ c.2.val.2 * r ^ c.2.val.1
  rw [ENNReal.tsum_sigma (fun (n : ℕ) (p : ↥(Finset.antidiagonal n)) => r ^ p.val.2 * r ^ p.val.1)]
  apply tsum_congr
  intro n
  simp only [tsum_fintype, ← pow_add]
  have hpow (p : ↥(Finset.antidiagonal n)) : r ^ (p.val.2 + p.val.1) = r ^ n := by
    rw [Nat.add_comm, Finset.mem_antidiagonal.mp p.property]
  simp_rw [hpow]
  simp [nsmul_eq_mul]

/-- Total mass of a geometric first-hit law with success chance `1/N`. -/
theorem geometric_mass (N : ℕ) (hN : 0 < N) :
    (∑' n : ℕ, (1 - (N : ℝ≥0∞)⁻¹) ^ n * (N : ℝ≥0∞)⁻¹) = 1 := by
  have hq : (N : ℝ≥0∞)⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr (by exact_mod_cast hN)
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric,
    ENNReal.sub_sub_cancel (by simp) hq, inv_inv]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast (Nat.ne_of_gt hN)) (by simp)

/-- Constant cost per attempt gives expected total cost `N*K`. -/
theorem geometric_cost (N K : ℕ) (hN : 0 < N) :
    (∑' n : ℕ, (1 - (N : ℝ≥0∞)⁻¹) ^ n * (N : ℝ≥0∞)⁻¹ *
      (((n + 1) * K : ℕ) : ℝ≥0∞)) = (N : ℝ≥0∞) * K := by
  have hq : (N : ℝ≥0∞)⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr (by exact_mod_cast hN)
  have hzero : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  calc
    _ = (∑' n : ℕ, (n + 1 : ℝ≥0∞) * (1 - (N : ℝ≥0∞)⁻¹) ^ n) *
        (N : ℝ≥0∞)⁻¹ * K := by
      rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro n
      push_cast
      ac_rfl
    _ = _ := by
      rw [tsum_succ_mul_geometric, ENNReal.sub_sub_cancel (by simp) hq, inv_inv]
      rw [mul_assoc (N : ℝ≥0∞) (N : ℝ≥0∞) _, ENNReal.mul_inv_cancel hzero (by simp), mul_one]

end Caliper
