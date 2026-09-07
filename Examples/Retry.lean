import Caliper.Retry

/-!
# A randomized loop with no fixed runtime bound

With one-bit words, retrying until zero takes two attempts on average. Each
attempt costs one sample and one branch, giving expected unit cost four.
-/
open Caliper
open scoped ENNReal

namespace CaliperExamples.Retry

example (n : ℕ) :
    terminationTimePMF .unit (retryZero 0) (State.init 1) ((2 * (n + 1) : ℕ) : ℕ∞) =
      (2⁻¹ : ℝ≥0∞) ^ (n + 1) := by
  have h := retryZero_timePMF .unit 0 (State.init 1) (by decide) n
  norm_num [CostModel.unit, pow_succ, Nat.mul_comm] at h ⊢
  exact h

example : terminationTimePMF .unit (retryZero 0) (State.init 1) ⊤ = 0 :=
  retryZero_almostSure _ _ _

example : (terminationTimePMF .unit (retryZero 0) (State.init 1)).expect ENat.toENNReal = 4 := by
  rw [retryZero_expect _ _ _ (by decide)]
  norm_num [CostModel.unit]

/-- The degenerate zero-bit word always succeeds on the first attempt. -/
example : (terminationTimePMF .unit (retryZero 0) (State.init 0)).expect ENat.toENNReal = 2 := by
  rw [retryZero_expect _ _ _ (by decide)]
  norm_num [CostModel.unit]

example : terminationTime .unit (retryZero 0) (State.init 1) (fun _ => 1) = ⊤ :=
  retryZero_no_zero (fun _ => by decide)

/-- Replay three failures and a success: four attempts, eight cost units. -/
example : (run .unit (fun i => if i < 3 then (1 : Word 1) else 0)
    20 (retryZero 0) (State.init 1)).map
    (fun (s, t, d, p) => (s.regs 0, s.tapePos, t, d, p)) = some (0, 4, 8, 0, 0) := rfl

example : (run .unit RandomTape.zero 3 (retryZero 0) (State.init 64)).map
    (fun (s, t, _, _) => (s.regs 0, s.tapePos, t)) = some (0, 1, 2) := rfl

end CaliperExamples.Retry
