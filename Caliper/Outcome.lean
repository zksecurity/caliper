import Caliper.TapeMeasure

/-!
# Countable outcomes of a fixed program

Although arbitrary machine states form an uncountable type, a fixed program and
initial state have only countably many terminating outcomes: each is witnessed by
a finite sequence of input words. This fact supports probabilistic composition.
-/

namespace Caliper

open MeasureTheory

variable {w : ℕ}

abbrev Outcome (w : ℕ) := State w × ℕ × ℤ × ℤ

def HasOutcome (C : CostModel) (tape : RandomTape w) (c : Stmt w) (s : State w)
    (r : Outcome w) : Prop := Exec C tape c s r.1 r.2.1 r.2.2.1 r.2.2.2

noncomputable def outcome (C : CostModel) (c : Stmt w) (s : State w)
    (tape : RandomTape w) : Option (Outcome w) := by
  classical
  exact if h : ∃ r, HasOutcome C tape c s r then some (Classical.choose h) else none

theorem outcome_of_exec {C : CostModel} {tape : RandomTape w} {c : Stmt w} {s : State w}
    {r : Outcome w} (he : HasOutcome C tape c s r) : outcome C c s tape = some r := by
  have h : ∃ r, HasOutcome C tape c s r := ⟨r, he⟩
  have hx := Classical.choose_spec h
  obtain ⟨hs, ht, hd, hp⟩ := hx.deterministic he
  have hr : Classical.choose h = r := by
    apply Prod.ext hs
    exact Prod.ext ht (Prod.ext hd hp)
  simp only [outcome, dif_pos h, hr]

/-- Possible terminating outcomes over arbitrary tapes. -/
def possibleOutcomes (C : CostModel) (c : Stmt w) (s : State w) : Set (Outcome w) :=
  {r | ∃ tape, HasOutcome C tape c s r}

theorem possibleOutcomes_countable (C : CostModel) (c : Stmt w) (s : State w) :
    (possibleOutcomes C c s).Countable := by
  classical
  let extend (tr : (n : ℕ) × (Fin n → Word w)) : RandomTape w :=
    fun i => if h : i < tr.1 then tr.2 ⟨i, h⟩ else 0
  let f (tr : (n : ℕ) × (Fin n → Word w)) := outcome C c s (extend tr)
  have hsub : possibleOutcomes C c s ⊆ Option.some ⁻¹' Set.range f := by
    rintro r ⟨tape, he⟩
    let tr : (n : ℕ) × (Fin n → Word w) := ⟨r.1.tapePos, fun i => tape i⟩
    refine ⟨tr, ?_⟩
    apply outcome_of_exec
    apply he.withTape
    intro i _ hi
    simp only [extend, tr, dif_pos hi]
  exact ((Set.countable_range f).preimage (by intro x y h; exact Option.some.inj h)).mono hsub

/-- A particular outcome is a prefix event ending at its final cursor. -/
theorem HasOutcome.measurableSet (C : CostModel) (c : Stmt w) (s : State w)
    (r : Outcome w) :
    MeasurableSet[RandomTape.prefixSigma r.1.tapePos] {tape | HasOutcome C tape c s r} := by
  apply RandomTape.prefix_measurableSet
  intro tape other ha
  constructor
  · intro he
    exact he.withTape tape (fun i _ hi => (ha i hi).symm)
  · intro he
    exact he.withTape other (fun i _ hi => ha i hi)

/-- Distinct outcomes belong to disjoint tape events. -/
theorem HasOutcome.disjoint {C : CostModel} {c : Stmt w} {s : State w}
    {r r' : Outcome w} (hne : r ≠ r') :
    Disjoint {tape | HasOutcome C tape c s r} {tape | HasOutcome C tape c s r'} := by
  apply Set.disjoint_left.mpr
  intro tape h h'
  obtain ⟨hs, ht, hd, hp⟩ := h.deterministic h'
  exact hne (Prod.ext hs (Prod.ext ht (Prod.ext hd hp)))

/-- After any safely terminating subroutine, the unread tape is uniform and
independent of every predicate on its outcome. The probability is unconditional:
if the subroutine terminates only with mass `p`, the joint event has mass `p * μ F`.
Neither elapsed time nor the consumed-word count must be fixed. -/
theorem uniformTape_after_exec (C : CostModel) (c : Stmt w) (s : State w)
    (Q : Outcome w → Prop) {F : Set (RandomTape w)} (hF : MeasurableSet F) :
    uniformTape w {tape | ∃ r, HasOutcome C tape c s r ∧ Q r ∧
      RandomTape.drop r.1.tapePos tape ∈ F} =
    uniformTape w {tape | ∃ r, HasOutcome C tape c s r ∧ Q r} * uniformTape w F := by
  classical
  let A : Set (Outcome w) := {r | r ∈ possibleOutcomes C c s ∧ Q r}
  letI : Countable A := ((possibleOutcomes_countable C c s).mono (fun _ h => h.1)).to_subtype
  let E (a : A) : Set (RandomTape w) := {tape | HasOutcome C tape c s a.val}
  have he : {tape | ∃ r, HasOutcome C tape c s r ∧ Q r} = ⋃ a : A, E a := by
    ext tape
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨r, hr, hq⟩
      exact ⟨⟨r, ⟨⟨tape, hr⟩, hq⟩⟩, hr⟩
    · rintro ⟨a, ha⟩
      exact ⟨a.val, ha, a.property.2⟩
  have hef : {tape | ∃ r, HasOutcome C tape c s r ∧ Q r ∧
      RandomTape.drop r.1.tapePos tape ∈ F} =
      ⋃ a : A, E a ∩ RandomTape.drop a.val.1.tapePos ⁻¹' F := by
    ext tape
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨r, hr, hq, hf⟩
      exact ⟨⟨r, ⟨⟨tape, hr⟩, hq⟩⟩, hr, hf⟩
    · rintro ⟨a, ha, hf⟩
      exact ⟨a.val, ha, a.property.2, hf⟩
  rw [he, hef]
  apply uniformTape_partition_drop (fun a : A => a.val.1.tapePos) E
    (fun a => HasOutcome.measurableSet C c s a.val) _ hF
  intro a b hab
  exact HasOutcome.disjoint (fun h => hab (Subtype.ext h))

/-- Sampling after any subroutine gives a uniform word on each safely returning
run. Success mass is retained, rather than implicitly conditioned to one. -/
theorem resultProb_seq_rand (C : CostModel) (c : Stmt w) (s : State w) (r : Reg) (v : Word w) :
    resultProb C (c ;; .rand r) s (fun s' _ _ _ => s'.regs r = v) =
      resultProb C c s (fun _ _ _ _ => True) * ((2 ^ w : ℕ) : ENNReal)⁻¹ := by
  let F : Set (RandomTape w) := {tape | tape 0 = v}
  have hF : MeasurableSet F := by
    simpa only [F, Set.preimage, Set.mem_singleton_iff] using
      ((measurable_pi_apply 0 : Measurable (fun tape : RandomTape w => tape 0)) (measurableSet_singleton v))
  have he : {tape | ∃ s' t d p, Exec C tape (c ;; .rand r) s s' t d p ∧ s'.regs r = v} =
      {tape | ∃ out, HasOutcome C tape c s out ∧ True ∧
        RandomTape.drop out.1.tapePos tape ∈ F} := by
    ext tape
    constructor
    · rintro ⟨s', t, d, p, hexec, hv⟩
      cases hexec with
      | @seq _ _ _ s₁ _ t₁ d₁ p₁ _ _ _ h₁ h₂ =>
        cases h₂
        exact ⟨(s₁, t₁, d₁, p₁), h₁, trivial,
          by simpa [F, RandomTape.drop, State.readRandom, State.setReg] using hv⟩
    · rintro ⟨out, h₁, _, hv⟩
      exact ⟨_, _, _, _, Exec.seq h₁ Exec.rand,
        by simpa [F, RandomTape.drop, State.readRandom, State.setReg] using hv⟩
  unfold resultProb
  rw [he, uniformTape_after_exec C c s (fun _ => True) hF]
  rw [show uniformTape w F = ((2 ^ w : ℕ) : ENNReal)⁻¹ from uniformTape_eval 0 v]
  congr 1
  congr 1
  ext tape
  constructor
  · rintro ⟨out, he, _⟩
    exact ⟨out.1, out.2.1, out.2.2.1, out.2.2.2, he, trivial⟩
  · rintro ⟨s', t, d, p, he, _⟩
    exact ⟨(s', t, d, p), he, trivial⟩

end Caliper
