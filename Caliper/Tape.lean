import Caliper.Core

/-!
# Deterministic execution against a word tape

The input tape is immutable. Only `rand` advances its cursor, so an execution
observes a finite prefix and can be replayed with any tape agreeing on that prefix.
-/

namespace Caliper

variable {w : ℕ} {C : CostModel} {tape : RandomTape w}

/-- Statements that never consume an input-tape word. -/
def Stmt.RandomFree : Stmt w → Prop
  | .rand _ => False
  | .seq a b => a.RandomFree ∧ b.RandomFree
  | .ifNZ _ a b => a.RandomFree ∧ b.RandomFree
  | .whileNZ g _ b => g.RandomFree ∧ b.RandomFree
  | _ => True

instance instDecidableRandomFree : ∀ (c : Stmt w), Decidable c.RandomFree
  | .rand _ => inferInstanceAs (Decidable False)
  | .seq a b | .ifNZ _ a b =>
    have := instDecidableRandomFree a
    have := instDecidableRandomFree b
    inferInstanceAs (Decidable (_ ∧ _))
  | .whileNZ g _ b =>
    have := instDecidableRandomFree g
    have := instDecidableRandomFree b
    inferInstanceAs (Decidable (_ ∧ _))
  | .skip | .imm .. | .mov .. | .un .. | .bin .. | .memResize .. | .memResizeI ..
    | .memLen .. | .memLoad .. | .memStore .. =>
    inferInstanceAs (Decidable True)

/-- Programs cannot observe elapsed time: changing every instruction price
preserves termination, the returned state, and both memory costs. -/
theorem Exec.withCostModel {c : Stmt w} {s s' : State w} {t : ℕ} {d p : ℤ}
    (h : Exec C tape c s s' t d p) (C' : CostModel) :
    ∃ t', Exec C' tape c s s' t' d p := by
  induction h with
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨t₁, h₁⟩ := ih₁
    obtain ⟨t₂, h₂⟩ := ih₂
    exact ⟨_, .seq h₁ h₂⟩
  | ifNZ_true hn _ ih =>
    obtain ⟨t, h⟩ := ih
    exact ⟨_, .ifNZ_true hn h⟩
  | ifNZ_false hz _ ih =>
    obtain ⟨t, h⟩ := ih
    exact ⟨_, .ifNZ_false hz h⟩
  | while_done _ hz ih =>
    obtain ⟨t, h⟩ := ih
    exact ⟨_, .while_done h hz⟩
  | while_step _ hn _ _ ihg ihb ihl =>
    obtain ⟨tg, hg⟩ := ihg
    obtain ⟨tb, hb⟩ := ihb
    obtain ⟨tl, hl⟩ := ihl
    exact ⟨_, .while_step hg hn hb hl⟩
  | skip => exact ⟨_, .skip⟩
  | imm => exact ⟨_, .imm⟩
  | rand => exact ⟨_, .rand⟩
  | mov => exact ⟨_, .mov⟩
  | un => exact ⟨_, .un⟩
  | bin => exact ⟨_, .bin⟩
  | memResize => exact ⟨_, .memResize⟩
  | memResizeI => exact ⟨_, .memResizeI⟩
  | memLen => exact ⟨_, .memLen⟩
  | memLoad h => exact ⟨_, .memLoad h⟩
  | memStore h => exact ⟨_, .memStore h⟩

/-- The input cursor never moves backwards. -/
theorem Exec.tapePos_mono {c : Stmt w} {s s' : State w} {t : ℕ} {d p : ℤ}
    (h : Exec C tape c s s' t d p) : s.tapePos ≤ s'.tapePos := by
  induction h <;> simp_all -failIfUnchanged [State.setReg, State.setBuf, State.resizeBuf, State.readRandom] <;>
    omega

/-- Random-free programs leave the input cursor unchanged. -/
theorem Exec.tapePos_eq_of_randomFree {c : Stmt w} {s s' : State w} {t : ℕ} {d p : ℤ}
    (h : Exec C tape c s s' t d p) (hc : c.RandomFree) : s'.tapePos = s.tapePos := by
  induction h <;> simp_all [Stmt.RandomFree, State.setReg, State.setBuf, State.resizeBuf]

/-- Every terminating derivation is returned by all sufficiently large fuels. -/
theorem Exec.run_eventually {c : Stmt w} {s s' : State w} {t : ℕ} {d p : ℤ}
    (h : Exec C tape c s s' t d p) :
    ∃ n, ∀ f, n ≤ f → run C tape f c s = some (s', t, d, p) := by
  induction h with
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨n₁, ih₁⟩ := ih₁
    obtain ⟨n₂, ih₂⟩ := ih₂
    refine ⟨max n₁ n₂ + 1, ?_⟩
    intro f hf
    cases f with
    | zero => omega
    | succ f => simp [run, ih₁ f (by omega), ih₂ f (by omega)]
  | ifNZ_true hn _ ih =>
    obtain ⟨n, ih⟩ := ih
    refine ⟨n + 1, ?_⟩
    intro f hf
    cases f with
    | zero => omega
    | succ f => simp only [run, if_neg hn, ih f (by omega), Option.bind_eq_bind, Option.bind_some]
  | ifNZ_false hz _ ih =>
    obtain ⟨n, ih⟩ := ih
    refine ⟨n + 1, ?_⟩
    intro f hf
    cases f with
    | zero => omega
    | succ f => simp [run, hz, ih f (by omega)]
  | while_done _ hz ih =>
    obtain ⟨n, ih⟩ := ih
    refine ⟨n + 1, ?_⟩
    intro f hf
    cases f with
    | zero => omega
    | succ f => simp [run, hz, ih f (by omega)]
  | while_step _ hn _ _ ihg ihb ihl =>
    obtain ⟨ng, ihg⟩ := ihg
    obtain ⟨nb, ihb⟩ := ihb
    obtain ⟨nl, ihl⟩ := ihl
    refine ⟨max ng (max nb nl) + 1, ?_⟩
    intro f hf
    cases f with
    | zero => omega
    | succ f => simp only [run, ihg f (by omega), Option.bind_eq_bind, Option.bind_some, if_neg hn,
        ihb f (by omega), ihl f (by omega)]
  | _ =>
    refine ⟨1, ?_⟩
    intro f hf
    cases f <;> simp_all [run]

/-- Interpreter completeness for terminating executions. -/
theorem run_complete {c : Stmt w} {s s' : State w} {t : ℕ} {d p : ℤ}
    (h : Exec C tape c s s' t d p) : ∃ f, run C tape f c s = some (s', t, d, p) := by
  obtain ⟨n, hn⟩ := h.run_eventually
  exact ⟨n, hn n le_rfl⟩

/-- Increasing fuel cannot change or lose a successful interpreter result. -/
theorem run_mono {f g : ℕ} (hfg : f ≤ g) (c : Stmt w) (s : State w)
    {result : State w × ℕ × ℤ × ℤ} (h : run C tape f c s = some result) :
    run C tape g c s = some result := by
  induction f generalizing g c s result with
  | zero => simp [run] at h
  | succ f ih =>
    cases g with
    | zero => omega
    | succ g =>
      have hfg' : f ≤ g := by omega
      cases c with
      | seq c₁ c₂ =>
        simp only [run, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
        obtain ⟨r₁, h₁, r₂, h₂, hr⟩ := h
        exact ⟨r₁, ih hfg' _ _ h₁, r₂, ih hfg' _ _ h₂, hr⟩
      | ifNZ r thn els =>
        simp only [run] at h ⊢
        split at h <;> rename_i hc
        all_goals simp only [hc, ↓reduceIte, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
        all_goals obtain ⟨r', hr', heq⟩ := h; exact ⟨r', ih hfg' _ _ hr', heq⟩
      | whileNZ guard r body =>
        simp only [run, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
        obtain ⟨rg, hg, h⟩ := h
        refine ⟨rg, ih hfg' _ _ hg, ?_⟩
        split at h <;> rename_i hc
        · simp only [hc, ↓reduceIte]; exact h
        · simp only [hc, ↓reduceIte]
          simp only [Option.bind_eq_some_iff] at h ⊢
          obtain ⟨rb, hb, rl, hl, heq⟩ := h
          exact ⟨rb, ih hfg' _ _ hb, rl, ih hfg' _ _ hl, heq⟩
      | _ => exact h

/-- Only tape words consumed by the derivation can affect its outcome. -/
theorem Exec.withTape {c : Stmt w} {s s' : State w} {t : ℕ} {d p : ℤ}
    (h : Exec C tape c s s' t d p) (other : RandomTape w)
    (agree : ∀ i, s.tapePos ≤ i → i < s'.tapePos → other i = tape i) :
    Exec C other c s s' t d p := by
  induction h with
  | @rand d s =>
    have hv := agree _ le_rfl (Nat.lt_succ_self _)
    simpa only [State.readRandom, hv] using (Exec.rand (C := C) (tape := other) (d := d) (s := s))
  | seq h₁ h₂ ih₁ ih₂ =>
    exact .seq (ih₁ fun i hlo hhi => agree i hlo (lt_of_lt_of_le hhi h₂.tapePos_mono))
      (ih₂ fun i hlo hhi => agree i (h₁.tapePos_mono.trans hlo) hhi)
  | ifNZ_true hn _ ih => exact .ifNZ_true hn (ih agree)
  | ifNZ_false hz _ ih => exact .ifNZ_false hz (ih agree)
  | while_done _ hz ih => exact .while_done (ih agree) hz
  | while_step hg hn hb hl ihg ihb ihl =>
    exact .while_step
      (ihg fun i hlo hhi => agree i hlo
        (lt_of_lt_of_le hhi (hb.tapePos_mono.trans hl.tapePos_mono))) hn
      (ihb fun i hlo hhi => agree i (hg.tapePos_mono.trans hlo)
        (lt_of_lt_of_le hhi hl.tapePos_mono))
      (ihl fun i hlo hhi => agree i ((hg.tapePos_mono.trans hb.tapePos_mono).trans hlo) hhi)
  | _ => constructor

/-- Changing the tape cannot change a random-free execution. -/
theorem Exec.withTape_of_randomFree {c : Stmt w} {s s' : State w} {t : ℕ} {d p : ℤ}
    (h : Exec C tape c s s' t d p) (hc : c.RandomFree) (other : RandomTape w) :
    Exec C other c s s' t d p := by
  apply h.withTape other
  intro i hlo hhi
  have := h.tapePos_eq_of_randomFree hc
  omega

end Caliper
