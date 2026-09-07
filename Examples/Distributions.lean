import Caliper.ProbTriple

/-! Probability laws for actual Caliper programs, checked during the CI build. -/
open Caliper MeasureTheory
open scoped ENNReal

namespace CaliperExamples.Distributions

variable {w : ℕ}

/-- A sample is uniform at every starting cursor. -/
example (s : State w) (r : Reg) (v : Word w) :
    resultProb .unit (.rand r) s (fun s' _ _ _ => s'.regs r = v) =
      ((2 ^ w : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [resultProb_of_exec _ _ _ _ (fun tape => s.readRandom tape r)
    (fun _ => 1) (fun _ => 0) (fun _ => 0) (fun _ => Exec.rand)]
  simpa only [regs_readRandom, regs_setReg_self] using uniformTape_eval s.tapePos v

/-- Two independent output words: every ordered pair has mass `2^(-2w)`. -/
example (x y : Word w) :
    resultProb .unit (.rand 0 ;; .rand 1) (State.init w)
      (fun s' _ _ _ => s'.regs 0 = x ∧ s'.regs 1 = y) =
      (((2 ^ w : ℕ) : ℝ≥0∞)⁻¹) ^ 2 := by
  rw [resultProb_of_exec _ _ _ _
    (fun tape => ((State.init w).readRandom tape 0).readRandom tape 1)
    (fun _ => 2) (fun _ => 0) (fun _ => 0) (fun _ => Exec.seq Exec.rand Exec.rand)]
  have he : {tape : RandomTape w |
      (((State.init w).readRandom tape 0).readRandom tape 1).regs 0 = x ∧
      (((State.init w).readRandom tape 0).readRandom tape 1).regs 1 = y} =
      RandomTape.cylinder ![x, y] := by
    ext tape
    simp [RandomTape.cylinder, Fin.forall_fin_two, State.readRandom, State.setReg, State.init]
  rw [he, uniformTape_cylinder]

/-- Random output need not imply random runtime. -/
example (s : State w) : terminationTimePMF .unit (.rand 0) s = PMF.pure 1 :=
  terminationTimePMF_eq_pure _ _ _ _ (fun _ => terminationTime_of_exec Exec.rand)

example (s : State w) :
    (terminationTimePMF .unit (.rand 0) s).expect ENat.toENNReal = 1 := by
  rw [terminationTimePMF_eq_pure _ _ _ _ (fun _ => terminationTime_of_exec Exec.rand)]
  simp only [PMF.expect_pure, ENat.toENNReal_coe]
  norm_num [CostModel.unit]

/-- An invalid load is charged to infinity, even though it fails immediately. -/
example : terminationTimePMF .unit (.memLoad 0 0 0) (State.init 64) = PMF.pure ⊤ := by
  apply terminationTimePMF_eq_pure
  intro tape
  apply (terminationTime_eq_top_iff tape).mpr
  rintro ⟨s', t, d, p, he⟩
  cases he with
  | memLoad h => simp [State.init] at h

/-- A deterministic program has a point-mass runtime under the uniform tape law. -/
example : terminationTimePMF .unit (.imm 0 (7 : Word 64)) (State.init 64) = PMF.pure 1 :=
  terminationTimePMF_of_randomFree _ _ _ (tape := RandomTape.zero) Exec.imm trivial

/-- A sampled one triggers an invalid load; a sampled zero returns safely. -/
def maybeFault : Stmt 1 := .rand 0 ;; .ifNZ 0 (.memLoad 1 0 0) .skip

example : terminationTimePMF .unit maybeFault (State.init 1) ⊤ = (2 : ℝ≥0∞)⁻¹ := by
  rw [terminationTimePMF_apply]
  have he : {tape | terminationTime .unit maybeFault (State.init 1) tape = ⊤} =
      {tape : RandomTape 1 | tape 0 = 0}ᶜ := by
    ext tape
    rw [Set.mem_setOf_eq, terminationTime_eq_top_iff]
    change (¬ ∃ s' t d p, Exec .unit tape maybeFault (State.init 1) s' t d p) ↔ tape 0 ≠ 0
    constructor
    · intro hn hz
      apply hn
      refine ⟨_, 2, 0, 0, Exec.seq Exec.rand (Exec.ifNZ_false ?_ Exec.skip)⟩
      simpa [State.readRandom, State.setReg, State.init] using hz
    · intro hn
      rintro ⟨s', t, d, p, hexec⟩
      cases hexec with
      | seq hr hb =>
        cases hr
        cases hb with
        | ifNZ_false hz _ =>
          exact hn (by simpa [State.readRandom, State.setReg, State.init] using hz)
        | ifNZ_true _ hf =>
          cases hf with
          | memLoad hi => simp [State.readRandom, State.setReg, State.init] at hi
  rw [he, measure_compl (by
    simpa only [Set.preimage, Set.mem_singleton_iff] using
      ((measurable_pi_apply 0 : Measurable (fun tape : RandomTape 1 => tape 0))
        (measurableSet_singleton (0 : Word 1)))) (measure_ne_top _ _), uniformTape_eval]
  norm_num

end CaliperExamples.Distributions
