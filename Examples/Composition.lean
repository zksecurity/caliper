import Caliper.Retry

/-!
# Composing randomized subroutines

A retrying caller consumes an unbounded number of words. A callee then samples
from the returned cursor. Its sample remains uniform, and expected costs add.
-/

open Caliper MeasureTheory
open scoped ENNReal

namespace CaliperExamples.Composition

/-- The callee is specified at every initial cursor and every caller output. -/
theorem retry_then_sample :
    ProbTriple .unit (fun _ : State 1 => True) (retryZero 0 ;; .rand 1)
      (fun s => s.regs 0 = 0) 5 0 0 := by
  have hsample : ProbTriple .unit (fun s : State 1 => s.regs 0 = 0) (.rand 1)
      (fun s => s.regs 0 = 0) CostModel.unit.rand 0 0 := by
    apply ProbTriple.rand
    intro s hs v
    simpa [State.setReg] using hs
  have h := (retryZero_spec (w := 1) .unit 0).seq hsample
  norm_num [CostModel.unit] at h
  exact h

/-- The next sample is uniform after a random-length retry, without conditioning
on termination. The caller's almost-sure termination is proved separately. -/
example (s : State 1) (v : Word 1) :
    resultProb .unit (retryZero 0 ;; .rand 1) s (fun s' _ _ _ => s'.regs 1 = v) =
      (2 : ℝ≥0∞)⁻¹ := by
  rw [resultProb_seq_rand]
  have hsuccess : resultProb .unit (retryZero 0) s (fun _ _ _ _ => True) = 1 := by
    apply (mem_ae_iff_prob_eq_one (measurableSet_exec _ _ _ _)).mp
    filter_upwards [(retryZero_spec .unit 0 s trivial).1] with tape ht
    obtain ⟨s', t, d, p, he, _, _, _⟩ := ht
    exact ⟨s', t, d, p, he, trivial⟩
  rw [hsuccess]
  norm_num

/-- Existing fixed-tape specifications remain usable for deterministic callees. -/
example {c : Stmt 1} {Q : State 1 → Prop} {T : ℕ} {D M : ℤ}
    (h : Triple .unit RandomTape.zero (fun s => s.regs 0 = 0) c Q T D M)
    (hc : c.RandomFree) :
    ProbTriple .unit (fun _ : State 1 => True) (retryZero 0 ;; c) Q
      (4 + T) D (max 0 M) := by
  have hseq := (retryZero_spec (w := 1) .unit 0).seq (ProbTriple.of_randomFree h hc)
  norm_num [CostModel.unit] at hseq
  exact hseq

/-- Elapsed time is external accounting: even radically different prices preserve
all state changes and memory usage for the same tape. -/
example {C C' : CostModel} {tape : RandomTape 64} {c : Stmt 64}
    {s s' : State 64} {t : ℕ} {d p : ℤ} (h : Exec C tape c s s' t d p) :
    ∃ t', Exec C' tape c s s' t' d p := h.withCostModel C'

/-- This tape fails twice, succeeds, and supplies a fresh word to the callee. -/
example : (run .unit (fun i => if i = 2 then (0 : Word 1) else 1)
    20 (retryZero 0 ;; .rand 1) (State.init 1)).map
    (fun (s, t, _, _) => (s.regs 0, s.regs 1, s.tapePos, t)) = some (0, 1, 4, 7) := rfl

end CaliperExamples.Composition
