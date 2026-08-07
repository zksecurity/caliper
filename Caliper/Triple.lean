import Clean.LowLevel.Core

/-!
# Upper-bound Hoare triples

`Triple C P c Q T M` is total correctness with resource *upper bounds*: from any state
satisfying `P`, the statement terminates (and is memory-safe — an `Exec` derivation
exists), the result satisfies `Q`, and it spends at most `T` time and allocates at most
`M` words. Bounds are `≤` throughout, so specs stay simple (`5*n + 7` rather than the
exact branch-dependent expression) and weakening is free.

The rules below are the complete proof system used by the examples:
* one rule per instruction (the `bufGet`/`bufSet` rules demand the index be in range —
  this is where memory-safety obligations surface),
* `seq`/`conseq`/`ifNZ` structural rules,
* `whileNZ_measure`, the one interesting rule: a loop invariant indexed by an iteration
  budget `k`; the conclusion's bounds are linear in `k`.
* `frame_post`: carry any fact about registers/buffers the statement doesn't touch
  across a triple. The side conditions are decidable (`by decide`), which is the
  buffer-model replacement for a separation-logic frame rule.
-/

namespace LowLevel

variable {w : ℕ} {C : CostModel}

/-- Total-correctness triple with time bound `T` and allocation bound `M`. -/
def Triple (C : CostModel) (P : State w → Prop) (c : Stmt w) (Q : State w → Prop)
    (T M : ℕ) : Prop :=
  ∀ s, P s → ∃ s' t m, Exec C c s s' t m ∧ Q s' ∧ t ≤ T ∧ m ≤ M

namespace Triple

/-- Consequence: strengthen the precondition, weaken the postcondition, raise the
bounds. This is why proving `≤` bounds beats proving exact times: bounds compose
without case splits. -/
theorem conseq {P P' Q Q' : State w → Prop} {c : Stmt w} {T T' M M' : ℕ}
    (h : Triple C P c Q T M) (hP : ∀ s, P' s → P s) (hQ : ∀ s, Q s → Q' s)
    (hT : T ≤ T') (hM : M ≤ M') : Triple C P' c Q' T' M' := by
  intro s hs
  obtain ⟨s', t, m, hexec, hq, ht, hm⟩ := h s (hP s hs)
  exact ⟨s', t, m, hexec, hQ s' hq, ht.trans hT, hm.trans hM⟩

theorem weaken {P Q : State w → Prop} {c : Stmt w} {T T' M M' : ℕ}
    (h : Triple C P c Q T M) (hT : T ≤ T') (hM : M ≤ M') : Triple C P c Q T' M' :=
  h.conseq (fun _ => id) (fun _ => id) hT hM

protected theorem skip {P Q : State w → Prop} (h : ∀ s, P s → Q s) :
    Triple C P (.skip (w := w)) Q 0 0 :=
  fun s hs => ⟨s, 0, 0, .skip, h s hs, le_refl _, le_refl _⟩

protected theorem seq {P R Q : State w → Prop} {c₁ c₂ : Stmt w} {T₁ M₁ T₂ M₂ : ℕ}
    (h₁ : Triple C P c₁ R T₁ M₁) (h₂ : Triple C R c₂ Q T₂ M₂) :
    Triple C P (c₁ ;; c₂) Q (T₁ + T₂) (M₁ + M₂) := by
  intro s hs
  obtain ⟨s₁, t₁, m₁, he₁, hr, ht₁, hm₁⟩ := h₁ s hs
  obtain ⟨s₂, t₂, m₂, he₂, hq, ht₂, hm₂⟩ := h₂ s₁ hr
  exact ⟨s₂, t₁ + t₂, m₁ + m₂, .seq he₁ he₂, hq,
    Nat.add_le_add ht₁ ht₂, Nat.add_le_add hm₁ hm₂⟩

/-! ### Instruction rules

Each takes the "forward" form: the precondition must imply the postcondition of the
updated state. Chained with `seq` these give a weakest-precondition-style calculation. -/

protected theorem imm {P Q : State w → Prop} {d : Reg} {v : Word w}
    (h : ∀ s, P s → Q (s.setReg d v)) : Triple C P (.imm d v) Q C.imm 0 :=
  fun s hs => ⟨_, _, _, .imm, h s hs, le_refl _, le_refl _⟩

protected theorem mov {P Q : State w → Prop} {d a : Reg}
    (h : ∀ s, P s → Q (s.setReg d (s.regs a))) : Triple C P (.mov d a) Q C.mov 0 :=
  fun s hs => ⟨_, _, _, .mov, h s hs, le_refl _, le_refl _⟩

protected theorem un {P Q : State w → Prop} {op : UnOp} {d a : Reg}
    (h : ∀ s, P s → Q (s.setReg d (op.eval (s.regs a)))) :
    Triple C P (.un op d a) Q (C.un op) 0 :=
  fun s hs => ⟨_, _, _, .un, h s hs, le_refl _, le_refl _⟩

protected theorem bin {P Q : State w → Prop} {op : BinOp} {d a b : Reg}
    (h : ∀ s, P s → Q (s.setReg d (op.eval (s.regs a) (s.regs b)))) :
    Triple C P (.bin op d a b) Q (C.bin op) 0 :=
  fun s hs => ⟨_, _, _, .bin, h s hs, le_refl _, le_refl _⟩

protected theorem bufNew {P Q : State w → Prop} {b : BufId}
    (h : ∀ s, P s → Q (s.setBuf b #[])) : Triple C P (.bufNew b) Q C.bufNew 0 :=
  fun s hs => ⟨_, _, _, .bufNew, h s hs, le_refl _, le_refl _⟩

protected theorem bufLen {P Q : State w → Prop} {d : Reg} {b : BufId}
    (h : ∀ s, P s → Q (s.setReg d (BitVec.ofNat w (s.bufs b).size))) :
    Triple C P (.bufLen d b) Q C.bufLen 0 :=
  fun s hs => ⟨_, _, _, .bufLen, h s hs, le_refl _, le_refl _⟩

/-- The in-range obligation `hlt` is the memory-safety proof; there is no rule for the
out-of-range case, so a completed triple entails safety. -/
protected theorem bufGet {P Q : State w → Prop} {d : Reg} {b : BufId} {i : Reg}
    (h : ∀ s, P s → ∃ hlt : (s.regs i).toNat < (s.bufs b).size,
      Q (s.setReg d (s.bufs b)[(s.regs i).toNat])) :
    Triple C P (.bufGet d b i) Q C.bufGet 0 := by
  intro s hs
  obtain ⟨hlt, hq⟩ := h s hs
  exact ⟨_, _, _, .bufGet hlt, hq, le_refl _, le_refl _⟩

protected theorem bufSet {P Q : State w → Prop} {b : BufId} {i src : Reg}
    (h : ∀ s, P s → ∃ hlt : (s.regs i).toNat < (s.bufs b).size,
      Q (s.setBuf b ((s.bufs b).set (s.regs i).toNat (s.regs src) hlt))) :
    Triple C P (.bufSet b i src) Q C.bufSet 0 := by
  intro s hs
  obtain ⟨hlt, hq⟩ := h s hs
  exact ⟨_, _, _, .bufSet hlt, hq, le_refl _, le_refl _⟩

protected theorem bufPush {P Q : State w → Prop} {b : BufId} {src : Reg}
    (h : ∀ s, P s → Q (s.setBuf b ((s.bufs b).push (s.regs src)))) :
    Triple C P (.bufPush b src) Q C.bufPush 1 :=
  fun s hs => ⟨_, _, _, .bufPush, h s hs, le_refl _, le_refl _⟩

protected theorem bufPop {P Q : State w → Prop} {b : BufId}
    (h : ∀ s, P s → Q (s.setBuf b (s.bufs b).pop)) :
    Triple C P (.bufPop b) Q C.bufPop 0 :=
  fun s hs => ⟨_, _, _, .bufPop, h s hs, le_refl _, le_refl _⟩

protected theorem ifNZ {P Q : State w → Prop} {r : Reg} {thn els : Stmt w} {T M : ℕ}
    (ht : Triple C (fun s => P s ∧ s.regs r ≠ 0) thn Q T M)
    (he : Triple C (fun s => P s ∧ s.regs r = 0) els Q T M) :
    Triple C P (.ifNZ r thn els) Q (C.branch + T) M := by
  intro s hs
  by_cases hr : s.regs r = 0
  · obtain ⟨s', t, m, hexec, hq, hT, hM⟩ := he s ⟨hs, hr⟩
    exact ⟨s', C.branch + t, m, .ifNZ_false hr hexec, hq, Nat.add_le_add_left hT _, hM⟩
  · obtain ⟨s', t, m, hexec, hq, hT, hM⟩ := ht s ⟨hs, hr⟩
    exact ⟨s', C.branch + t, m, .ifNZ_true hr hexec, hq, Nat.add_le_add_left hT _, hM⟩

/-- **The loop rule.** `I k` is the invariant before the guard when at most `k`
iterations remain; `J k` is the invariant right after the guard.

* The guard takes `I k` to `J k` within `(Tg, Mg)`.
* If the guard's flag is up, at least one iteration remains (`hpos`), and the body
  takes `J (k+1)` back to `I k` within `(Tb, Mb)`.

The loop then costs at most `(k+1) * (Tg + branch) + k * Tb` time and
`(k+1) * Mg + k * Mb` allocation — guard runs once more than the body. The
postcondition is some `J k'` with the flag down. -/
theorem whileNZ_measure {I J : ℕ → State w → Prop} {g body : Stmt w} {r : Reg}
    {Tg Mg Tb Mb : ℕ}
    (hg : ∀ k, Triple C (I k) g (J k) Tg Mg)
    (hpos : ∀ k s, J k s → s.regs r ≠ 0 → ∃ k', k = k' + 1)
    (hb : ∀ k, Triple C (fun s => J (k + 1) s ∧ s.regs r ≠ 0) body (I k) Tb Mb) :
    ∀ k, Triple C (I k) (.whileNZ g r body)
      (fun s => ∃ k', J k' s ∧ s.regs r = 0)
      ((k + 1) * (Tg + C.branch) + k * Tb)
      ((k + 1) * Mg + k * Mb) := by
  intro k
  induction k with
  | zero =>
    intro s hs
    obtain ⟨s₁, tg, mg, heg, hj, htg, hmg⟩ := hg 0 s hs
    by_cases hr : s₁.regs r = 0
    · refine ⟨s₁, tg + C.branch, mg, .while_done heg hr, ⟨0, hj, hr⟩, ?_, ?_⟩ <;> omega
    · obtain ⟨k', hk'⟩ := hpos 0 s₁ hj hr
      omega
  | succ k ih =>
    intro s hs
    obtain ⟨s₁, tg, mg, heg, hj, htg, hmg⟩ := hg (k + 1) s hs
    by_cases hr : s₁.regs r = 0
    · refine ⟨s₁, tg + C.branch, mg, .while_done heg hr, ⟨k + 1, hj, hr⟩, ?_, ?_⟩
      · calc tg + C.branch ≤ Tg + C.branch := Nat.add_le_add_right htg _
          _ ≤ (k + 2) * (Tg + C.branch) + (k + 1) * Tb := by nlinarith
      · calc mg ≤ Mg := hmg
          _ ≤ (k + 2) * Mg + (k + 1) * Mb := by nlinarith
    · obtain ⟨s₂, tb, mb, heb, hi, htb, hmb⟩ := hb k s₁ ⟨hj, hr⟩
      obtain ⟨s₃, tl, ml, hel, hq, htl, hml⟩ := ih s₂ hi
      refine ⟨s₃, tg + C.branch + tb + tl, mg + mb + ml,
        .while_step heg hr heb hel, hq, ?_, ?_⟩
      · have : (k + 1 + 1) * (Tg + C.branch) + (k + 1) * Tb
            = (Tg + C.branch) + Tb + ((k + 1) * (Tg + C.branch) + k * Tb) := by ring
        omega
      · have : (k + 1 + 1) * Mg + (k + 1) * Mb = Mg + Mb + ((k + 1) * Mg + k * Mb) := by
          ring
        omega

/-! ### Framing

Anything a statement provably doesn't write (a decidable, syntactic check) can be
carried across its triple for free. -/

/-- Carry a fact about an untouched register and an untouched buffer family across a
triple. Instantiate `R` with e.g. `fun s => s.regs 3 = x ∧ s.bufs 0 = arr`; the
`hR` hypothesis is discharged by `Exec.frame_reg`/`Exec.frame_buf` + `decide`. -/
theorem frame_post {P Q R : State w → Prop} {c : Stmt w} {T M : ℕ}
    (h : Triple C P c Q T M)
    (hR : ∀ s s' t m, Exec C c s s' t m → R s → R s') :
    Triple C (fun s => P s ∧ R s) c (fun s => Q s ∧ R s) T M := by
  intro s ⟨hp, hr⟩
  obtain ⟨s', t, m, hexec, hq, hT, hM⟩ := h s hp
  exact ⟨s', t, m, hexec, ⟨hq, hR s s' t m hexec hr⟩, hT, hM⟩

/-- Specialization: a register the statement never writes keeps its value. -/
theorem frame_reg {P Q : State w → Prop} {c : Stmt w} {T M : ℕ} {r : Reg} {v : Word w}
    (h : Triple C P c Q T M) (hw : ¬ c.Writes r) :
    Triple C (fun s => P s ∧ s.regs r = v) c (fun s => Q s ∧ s.regs r = v) T M :=
  h.frame_post fun _ _ _ _ hexec hr => (hexec.frame_reg hw).trans hr

/-- Specialization: a buffer the statement never touches keeps its contents. -/
theorem frame_buf {P Q : State w → Prop} {c : Stmt w} {T M : ℕ} {b : BufId}
    {arr : Array (Word w)} (h : Triple C P c Q T M) (ht : ¬ c.Touches b) :
    Triple C (fun s => P s ∧ s.bufs b = arr) c (fun s => Q s ∧ s.bufs b = arr) T M :=
  h.frame_post fun _ _ _ _ hexec hb => (hexec.frame_buf ht).trans hb

end Triple

end LowLevel
