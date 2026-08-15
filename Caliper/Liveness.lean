import Caliper.Examples

/-!
# Static register liveness

A purely syntactic, backward liveness analysis for `Stmt`: which registers hold a
value that some later instruction may still read, and how many are live *at once*.

The analysis computes, for a statement `c` and a set `after` of registers assumed
live after `c`:

* `Stmt.liveBefore c after` — an over-approximation of the registers live before
  `c` (read somewhere in or after `c` before being overwritten);
* `Stmt.regPeak c after` — an upper bound on the number of simultaneously live
  registers at any program point inside `c`.

`Stmt.regPeak₀ c := c.regPeak ∅` is the headline number: the peak register
pressure of a whole program (nothing live at exit). It is the *inferred*
counterpart of the instruction-driven register accounting (`regAlloc`/`regFree`,
`State.regsAlloc`, the register summand of `State.liveMem`): instead of trusting
explicit allocation instructions, the analysis reads the lifetimes off the
data-flow of the program itself. `regAlloc`/`regFree` are treated as no-ops here
(see `Stmt.readsSet`); the plan is for this analysis to *replace* the
instruction-driven accounting, at which point those instructions disappear from
the machine altogether.

Everything is computable (`Finset ℕ`), structural (no fixpoints — the `whileNZ`
case widens conservatively instead of iterating; see `Stmt.liveBefore`), and
conservative: err on the side of counting a register live.

The headline theorem, `Stmt.regPeak_le_card_liveBefore_add_writesTotal`, bounds
the peak by *live-in registers plus register-writing instructions*: every
register live at some point either was live on entry or has been written by one
of the register-writing leaves executed so far. For straight-line code the write
count is at most the unit-model static time
(`Stmt.Straight.writesTotal_le_staticTime_unit`), giving
`Stmt.Straight.regPeak₀_le`: peak register pressure is bounded by live-ins plus
running time — the liveness-side analogue of `Exec.peak_le_time`.
-/

namespace Caliper

variable {w : ℕ}

/-! ## Per-instruction register footprints -/

/-- The registers an instruction *reads*. On compound statements this unions the
whole subtree (which is what the `whileNZ` widening needs — see `Stmt.usesSet`);
the backward dataflow (`Stmt.liveBefore`) only ever consults it at leaves and
drives the composition through its own recursion.

`regAlloc`/`regFree` read **no** registers: they are the legacy accounting
instructions this analysis is built to replace — they change a register's
*allocation status*, never touch its value, and carry no data-flow, so for
liveness they are no-ops. -/
def Stmt.readsSet : Stmt w → Finset ℕ
  | .skip => ∅
  | .seq c₁ c₂ => c₁.readsSet ∪ c₂.readsSet
  | .imm _ _ => ∅
  | .mov _ a => {a}
  | .un _ _ a => {a}
  | .bin _ _ a b => {a, b}
  | .memAlloc _ n => {n}
  | .memAllocI _ _ => ∅
  | .memFree _ => ∅
  | .memLen _ _ => ∅
  | .memLoad _ _ i => {i}
  | .memStore _ i src => {i, src}
  | .memPush _ src => {src}
  | .memPop _ => ∅
  | .regAlloc _ => ∅
  | .regFree _ => ∅
  | .ifNZ c t e => insert c (t.readsSet ∪ e.readsSet)
  | .whileNZ g c b => insert c (g.readsSet ∪ b.readsSet)

/-- The registers an instruction *writes* (assigns a value to). Like
`Stmt.readsSet`, compound statements union the subtree, but the dataflow only
consults leaves. `regAlloc`/`regFree` write no register *value* (exactly the
`Stmt.Writes` distinction), so they kill nothing. -/
def Stmt.writesSet : Stmt w → Finset ℕ
  | .skip => ∅
  | .seq c₁ c₂ => c₁.writesSet ∪ c₂.writesSet
  | .imm d _ => {d}
  | .mov d _ => {d}
  | .un _ d _ => {d}
  | .bin _ d _ _ => {d}
  | .memAlloc _ _ => ∅
  | .memAllocI _ _ => ∅
  | .memFree _ => ∅
  | .memLen d _ => {d}
  | .memLoad d _ _ => {d}
  | .memStore _ _ _ => ∅
  | .memPush _ _ => ∅
  | .memPop _ => ∅
  | .regAlloc _ => ∅
  | .regFree _ => ∅
  | .ifNZ _ t e => t.writesSet ∪ e.writesSet
  | .whileNZ g _ b => g.writesSet ∪ b.writesSet

/-- All registers read anywhere in the subtree — the whole-subtree *use* set the
`whileNZ` widening needs. Since `Stmt.readsSet` already unions over
sub-statements, this coincides with it definitionally; the separate name marks
the role: `usesSet` is quoted only where a whole-subtree union is wanted. -/
def Stmt.usesSet : Stmt w → Finset ℕ := Stmt.readsSet

/-! ## The backward analysis -/

/-- Live registers *before* `c`, given the set `after` live after it.

* Leaves: `(after \ writesSet) ∪ readsSet` — the write kills, the reads gen.
* `seq` composes right to left; `ifNZ` joins the branches and adds the
  condition register.
* `whileNZ g c b` is **conservative — no fixpoint**. Let
  `U := insert c (g.usesSet ∪ b.usesSet)` (everything the loop reads anywhere,
  plus the verdict register). The result is
  `g.liveBefore (after ∪ U) ∪ after`.

  Intended invariant (over-approximation): *every register that any iteration
  may read — in the guard or the body — before writing it is in the result, and
  so is everything in `after`.* Justification: a register live at the
  guard/body branch point is either read later inside some iteration before
  being written (hence in `U`) or live after the loop (hence in `after`), so
  `after ∪ U` over-approximates every live-after set the guard can face — in
  particular the fixpoint a Kildall iteration would converge to. The extra
  `∪ after` is pure inclusion-side conservatism (a guard could kill a member of
  `after` that the exit path never reads; we keep it live anyway). Simplicity
  beats precision: the analysis stays a single structural recursion. -/
def Stmt.liveBefore : Stmt w → Finset ℕ → Finset ℕ
  | .seq c₁ c₂, after => c₁.liveBefore (c₂.liveBefore after)
  | .ifNZ c t e, after => insert c (t.liveBefore after ∪ e.liveBefore after)
  | .whileNZ g c b, after =>
      g.liveBefore (after ∪ insert c (g.usesSet ∪ b.usesSet)) ∪ after
  | c, after => (after \ c.writesSet) ∪ c.readsSet

/-- Peak number of simultaneously live registers at any program point in `c`,
threading the same after-sets as `Stmt.liveBefore`. At a leaf the two candidate
points are *before* the instruction (`|liveBefore|`) and *at the write*
(`|after ∪ writesSet|` — the destination is materialized while everything
live-after persists). `whileNZ` prices the guard and body against the same
widened after-set `after ∪ U` its `liveBefore` uses. -/
def Stmt.regPeak : Stmt w → Finset ℕ → ℕ
  | .seq c₁ c₂, after => max (c₁.regPeak (c₂.liveBefore after)) (c₂.regPeak after)
  | .ifNZ c t e, after =>
      max (insert c (t.liveBefore after ∪ e.liveBefore after)).card
        (max (t.regPeak after) (e.regPeak after))
  | .whileNZ g c b, after =>
      max (g.liveBefore (after ∪ insert c (g.usesSet ∪ b.usesSet)) ∪ after).card
        (max (g.regPeak (after ∪ insert c (g.usesSet ∪ b.usesSet)))
          (b.regPeak (after ∪ insert c (g.usesSet ∪ b.usesSet))))
  | c, after => max ((after \ c.writesSet) ∪ c.readsSet).card (after ∪ c.writesSet).card

/-- Peak register pressure of a whole program: nothing live after it. -/
def Stmt.regPeak₀ (c : Stmt w) : ℕ := c.regPeak ∅

/-! ## Unfolding lemmas (definitional, for calculation) -/

@[simp] theorem Stmt.liveBefore_seq (c₁ c₂ : Stmt w) (after : Finset ℕ) :
    (c₁ ;; c₂).liveBefore after = c₁.liveBefore (c₂.liveBefore after) := rfl

@[simp] theorem Stmt.liveBefore_ifNZ (c : Reg) (t e : Stmt w) (after : Finset ℕ) :
    (Stmt.ifNZ c t e).liveBefore after
      = insert c (t.liveBefore after ∪ e.liveBefore after) := rfl

@[simp] theorem Stmt.regPeak_seq (c₁ c₂ : Stmt w) (after : Finset ℕ) :
    (c₁ ;; c₂).regPeak after
      = max (c₁.regPeak (c₂.liveBefore after)) (c₂.regPeak after) := rfl

@[simp] theorem Stmt.regPeak_ifNZ (c : Reg) (t e : Stmt w) (after : Finset ℕ) :
    (Stmt.ifNZ c t e).regPeak after
      = max ((Stmt.ifNZ c t e).liveBefore after).card
          (max (t.regPeak after) (e.regPeak after)) := rfl

/-! ## Basic lemmas -/

/-- Whatever is live after `c` and not written by `c` is live before `c`:
`liveBefore` never drops a survivor. -/
theorem Stmt.sdiff_writesSet_subset_liveBefore (c : Stmt w) (after : Finset ℕ) :
    after \ c.writesSet ⊆ c.liveBefore after := by
  induction c generalizing after with
  | seq c₁ c₂ ih₁ ih₂ =>
    intro x hx
    simp only [Stmt.writesSet, Finset.mem_sdiff, Finset.mem_union, not_or] at hx
    exact ih₁ _ <| Finset.mem_sdiff.mpr
      ⟨ih₂ _ (Finset.mem_sdiff.mpr ⟨hx.1, hx.2.2⟩), hx.2.1⟩
  | ifNZ c t e iht ihe =>
    intro x hx
    simp only [Stmt.writesSet, Finset.mem_sdiff, Finset.mem_union, not_or] at hx
    exact Finset.mem_insert_of_mem <| Finset.mem_union_left _ <|
      iht _ (Finset.mem_sdiff.mpr ⟨hx.1, hx.2.1⟩)
  | whileNZ g c b ihg ihb =>
    exact fun x hx => Finset.mem_union_right _ (Finset.mem_sdiff.mp hx).1
  | _ => exact fun x hx => Finset.mem_union_left _ hx

/-- `liveBefore` only ever adds registers the statement reads: it is contained
in `after ∪ readsSet`. -/
theorem Stmt.liveBefore_subset (c : Stmt w) (after : Finset ℕ) :
    c.liveBefore after ⊆ after ∪ c.readsSet := by
  induction c generalizing after with
  | seq c₁ c₂ ih₁ ih₂ =>
    intro x hx
    simp only [Stmt.readsSet, Finset.mem_union]
    rcases Finset.mem_union.mp (ih₁ _ hx) with hx₁ | hx₁
    · rcases Finset.mem_union.mp (ih₂ _ hx₁) with hx₂ | hx₂
      · exact Or.inl hx₂
      · exact Or.inr (Or.inr hx₂)
    · exact Or.inr (Or.inl hx₁)
  | ifNZ c t e iht ihe =>
    intro x hx
    simp only [Stmt.readsSet, Finset.mem_union, Finset.mem_insert]
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Or.inr (Or.inl rfl)
    · rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_union.mp (iht _ hx) with hx | hx
        · exact Or.inl hx
        · exact Or.inr (Or.inr (Or.inl hx))
      · rcases Finset.mem_union.mp (ihe _ hx) with hx | hx
        · exact Or.inl hx
        · exact Or.inr (Or.inr (Or.inr hx))
  | whileNZ g c b ihg ihb =>
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp (ihg _ hx) with hx | hx
      · exact hx
      · exact Finset.mem_union_right _
          (Finset.mem_insert_of_mem (Finset.mem_union_left _ hx))
    · exact Finset.mem_union_left _ hx
  | _ =>
    exact fun x hx => Finset.union_subset_union Finset.sdiff_subset
      (Finset.Subset.refl _) hx

/-- **Monotonicity of `liveBefore`** in the after-set — the compositional fact:
enlarging what is assumed live after a statement can only enlarge what is live
before it. -/
theorem Stmt.liveBefore_mono (c : Stmt w) :
    ∀ {a a' : Finset ℕ}, a ⊆ a' → c.liveBefore a ⊆ c.liveBefore a' := by
  induction c with
  | seq c₁ c₂ ih₁ ih₂ => exact fun h => ih₁ (ih₂ h)
  | ifNZ c t e iht ihe =>
    exact fun h =>
      Finset.insert_subset_insert _ (Finset.union_subset_union (iht h) (ihe h))
  | whileNZ g c b ihg ihb =>
    exact fun h => Finset.union_subset_union
      (ihg (Finset.union_subset_union h (Finset.Subset.refl _))) h
  | _ =>
    exact fun h => Finset.union_subset_union
      (Finset.sdiff_subset_sdiff h (Finset.Subset.refl _)) (Finset.Subset.refl _)

/-- **Monotonicity of `regPeak`** in the after-set: pricing a statement against
a larger live-after set can only raise the peak. -/
theorem Stmt.regPeak_mono (c : Stmt w) :
    ∀ {a a' : Finset ℕ}, a ⊆ a' → c.regPeak a ≤ c.regPeak a' := by
  induction c with
  | seq c₁ c₂ ih₁ ih₂ =>
    exact fun h => max_le_max (ih₁ (c₂.liveBefore_mono h)) (ih₂ h)
  | ifNZ c t e iht ihe =>
    exact fun h =>
      max_le_max (Finset.card_le_card ((Stmt.ifNZ c t e).liveBefore_mono h))
        (max_le_max (iht h) (ihe h))
  | whileNZ g c b ihg ihb =>
    intro a a' h
    have hA := Finset.union_subset_union h
      (Finset.Subset.refl (insert c (g.usesSet ∪ b.usesSet)))
    exact max_le_max (Finset.card_le_card ((Stmt.whileNZ g c b).liveBefore_mono h))
      (max_le_max (ihg hA) (ihb hA))
  | _ =>
    exact fun h =>
      max_le_max
        (Finset.card_le_card (Finset.union_subset_union
          (Finset.sdiff_subset_sdiff h (Finset.Subset.refl _)) (Finset.Subset.refl _)))
        (Finset.card_le_card (Finset.union_subset_union h (Finset.Subset.refl _)))

/-! ## The headline bound: peak ≤ live-ins + register-writing instructions -/

/-- The number of *register-writing* leaves (`imm`/`mov`/`un`/`bin`/`memLen`/
`memLoad` — exactly the leaves with nonempty `writesSet`), counted through all
branches and loop bodies. Not an instruction count: memory-only and accounting
instructions do not write a register and are not counted, which is what lets the
straight-line corollary survive 0-cost instructions like `memAllocI _ 0`. -/
def Stmt.writesTotal : Stmt w → ℕ
  | .seq c₁ c₂ => c₁.writesTotal + c₂.writesTotal
  | .imm .. => 1
  | .mov .. => 1
  | .un .. => 1
  | .bin .. => 1
  | .memLen .. => 1
  | .memLoad .. => 1
  | .ifNZ _ t e => t.writesTotal + e.writesTotal
  | .whileNZ g _ b => g.writesTotal + b.writesTotal
  | _ => 0

/-- A statement writes at most `writesTotal` distinct registers. -/
theorem Stmt.card_writesSet_le_writesTotal (c : Stmt w) :
    c.writesSet.card ≤ c.writesTotal := by
  induction c with
  | seq c₁ c₂ ih₁ ih₂ =>
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add ih₁ ih₂)
  | ifNZ c t e iht ihe =>
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add iht ihe)
  | whileNZ g c b ihg ihb =>
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add ihg ihb)
  | _ => simp [Stmt.writesSet, Stmt.writesTotal]

/-- Running a statement backward loses at most `writesTotal` registers from the
live set: `|after| ≤ |liveBefore| + writesTotal`. This is the invariant behind
the headline bound — read forward, every register live at exit was live at
entry or was written along the way. -/
theorem Stmt.card_le_card_liveBefore_add_writesTotal (c : Stmt w) (after : Finset ℕ) :
    after.card ≤ (c.liveBefore after).card + c.writesTotal := by
  have h1 : after.card ≤ (after \ c.writesSet).card + c.writesSet.card :=
    Finset.card_le_card_sdiff_add_card
  have h2 := Finset.card_le_card (c.sdiff_writesSet_subset_liveBefore after)
  have h3 := c.card_writesSet_le_writesTotal
  omega

/-- The leaf shape of the headline bound: at a write point the live set is the
survivors-plus-reads set with the destination re-added, so its card exceeds the
live-before card by at most the (≤ 1) written registers. -/
private theorem leaf_peak_bound {after W R : Finset ℕ} {k : ℕ} (hW : W.card ≤ k) :
    max ((after \ W) ∪ R).card (after ∪ W).card ≤ ((after \ W) ∪ R).card + k := by
  have h1 : after ∪ W ⊆ ((after \ W) ∪ R) ∪ W := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · by_cases hxW : x ∈ W
      · exact Finset.mem_union_right _ hxW
      · exact Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxW⟩))
    · exact Finset.mem_union_right _ hx
  have h2 := (Finset.card_le_card h1).trans (Finset.card_union_le _ _)
  omega

/-- **The headline bound.** The peak live-register count is at most the live-in
count plus the number of register-writing instructions:

    regPeak c after ≤ |liveBefore c after| + writesTotal c

Meaning: at every program point, the live set is contained in (registers live
on entry) ∪ (registers written by the instructions executed so far) — a live
register's value had to come from *somewhere*. Live-in registers (read before
ever written — the program's inputs) genuinely count toward the peak and are
*not* written by the program, which is why the `|liveBefore|` summand cannot be
dropped. -/
theorem Stmt.regPeak_le_card_liveBefore_add_writesTotal (c : Stmt w)
    (after : Finset ℕ) :
    c.regPeak after ≤ (c.liveBefore after).card + c.writesTotal := by
  induction c generalizing after with
  | seq c₁ c₂ ih₁ ih₂ =>
    have h₁ := ih₁ (c₂.liveBefore after)
    have h₂ := ih₂ after
    have hmid := c₁.card_le_card_liveBefore_add_writesTotal (c₂.liveBefore after)
    simp only [Stmt.regPeak_seq, Stmt.liveBefore_seq, Stmt.writesTotal]
    omega
  | ifNZ c t e iht ihe =>
    have ht := iht after
    have he := ihe after
    have hlt : (t.liveBefore after).card
        ≤ (insert c (t.liveBefore after ∪ e.liveBefore after)).card :=
      Finset.card_le_card (Finset.subset_union_left.trans (Finset.subset_insert _ _))
    have hle : (e.liveBefore after).card
        ≤ (insert c (t.liveBefore after ∪ e.liveBefore after)).card :=
      Finset.card_le_card (Finset.subset_union_right.trans (Finset.subset_insert _ _))
    simp only [Stmt.regPeak_ifNZ, Stmt.liveBefore_ifNZ, Stmt.writesTotal]
    omega
  | whileNZ g c b ihg ihb =>
    -- the widened after-set the loop prices everything against
    have hg := ihg (after ∪ insert c (g.usesSet ∪ b.usesSet))
    have hb := ihb (after ∪ insert c (g.usesSet ∪ b.usesSet))
    -- the body's live-before stays inside the widened set: its reads are in `U`
    have hbsub : (b.liveBefore (after ∪ insert c (g.usesSet ∪ b.usesSet))).card
        ≤ (after ∪ insert c (g.usesSet ∪ b.usesSet)).card := by
      refine Finset.card_le_card ((b.liveBefore_subset _).trans
        (Finset.union_subset (Finset.Subset.refl _) fun x hx => ?_))
      exact Finset.mem_union_right _
        (Finset.mem_insert_of_mem (Finset.mem_union_right _ hx))
    -- the widened set is recovered from the guard's live-before plus its writes
    have hA := g.card_le_card_liveBefore_add_writesTotal
      (after ∪ insert c (g.usesSet ∪ b.usesSet))
    have hlg : (g.liveBefore (after ∪ insert c (g.usesSet ∪ b.usesSet))).card
        ≤ (g.liveBefore (after ∪ insert c (g.usesSet ∪ b.usesSet)) ∪ after).card :=
      Finset.card_le_card Finset.subset_union_left
    simp only [Stmt.regPeak, Stmt.liveBefore, Stmt.writesTotal]
    omega
  | _ => exact leaf_peak_bound (Stmt.card_writesSet_le_writesTotal _)

/-! ## The straight-line corollary: peak ≤ live-ins + running time -/

/-- For straight-line code the register-writing leaf count is bounded by the
unit-model static time: every register-writing leaf (`imm`/`mov`/`un`/`bin`/
`memLen`/`memLoad`) costs exactly 1 in `CostModel.unit`, and every other leaf
costs ≥ 0 — including the 0-cost `memAllocI _ 0`, which writes no register and
so is not counted. (`Straight` excludes `ifNZ`/`whileNZ`/dynamic `memAlloc`, so
no `max`/loop shapes arise.) -/
theorem Stmt.Straight.writesTotal_le_staticTime_unit {c : Stmt w} (h : c.Straight) :
    c.writesTotal ≤ c.staticTime CostModel.unit := by
  induction c with
  | seq c₁ c₂ ih₁ ih₂ => exact Nat.add_le_add (ih₁ h.1) (ih₂ h.2)
  | memAlloc | ifNZ | whileNZ => exact h.elim
  | _ => simp [Stmt.writesTotal, Stmt.staticTime, CostModel.unit]

/-- **Straight-line code: peak register pressure ≤ live-ins + running time.**
With nothing live at exit, the peak live-register count of a straight-line
program is bounded by its live-in count (registers the program reads before
ever writing — its inputs, which the program does not pay time to produce) plus
its exact unit-model running time. The liveness-side analogue of
`Exec.peak_le_time`: time bounds space, here read off the syntax alone. -/
theorem Stmt.Straight.regPeak₀_le {c : Stmt w} (h : c.Straight) :
    c.regPeak₀ ≤ (c.liveBefore ∅).card + c.staticTime CostModel.unit :=
  (c.regPeak_le_card_liveBefore_add_writesTotal ∅).trans
    (Nat.add_le_add_left h.writesTotal_le_staticTime_unit _)

/-! ## Demos

Inferred peaks for the existing example programs. These programs (except
`SumBuf.code`) still *contain* `regAlloc`/`regFree` instructions in this run —
the analysis ignores them, so each pin shows the statically inferred peak next
to the instruction-driven accounting number quoted in `Examples.lean`. -/

/- `SumBuf.code 0` (no `regAlloc` at all — the registerless original): inferred
peak 6. The conservative loop widening keeps all six registers live across the
guard/branch point (`r3`'s verdict is materialized while `r0-r2, r4, r5` stay
in `U`), matching the 6 registers the program names. -/

/-- info: 6 -/
#guard_msgs in
#eval (Examples.SumBuf.code (w := 64) 0).regPeak₀

/- The inferred live-*in* set of `SumBuf.code` is `{4, 5}` — an artifact of the
loop widening: `r4`/`r5` are read somewhere in the body, so the analysis
conservatively assumes an iteration might read them before the body's own
writes. (In truth every iteration writes them first; a fixpoint analysis would
infer `∅`. Err on the side of inclusion.) -/

/-- info: [4, 5] -/
#guard_msgs in
#eval ((Examples.SumBuf.code (w := 64) 0).liveBefore ∅).sort (· ≤ ·)

/- `sumBCore` — the builder's output for `sumB`, i.e. `SumBuf.code 0` *with*
explicit `regAlloc` instructions: same inferred peak 6, because the accounting
instructions are liveness no-ops. The instruction-driven accounting also says
peak 6 (all six registers acquired, none freed), so the two agree here. -/

/-- info: 6 -/
#guard_msgs in
#eval (Examples.sumBCore (w := 64)).regPeak₀

/- `ScopedSumSq.code`: the instruction-driven accounting certifies peak **3**
(`ScopedSumSq.space_spec`, and the interpreter pin `(25, 10, 3, 3)`). The
liveness analysis infers peak **2** — strictly sharper: at the point the
accounting counts `{r1, r2, r3}` (stage-1 result, stage-2 scratch, stage-2
result), `r2` is dead the moment `mul r3, r2, r2` consumes it, so at most two
*values* ever need slots simultaneously. This gap is the point of Run 2:
inferred lifetimes beat bracket-shaped `regAlloc`/`regFree` accounting. -/

/-- info: 2 -/
#guard_msgs in
#eval Examples.ScopedSumSq.code.regPeak₀

/-- A temp dying early, hand-written: 4 registers are *named* (`r0`-`r3`), but
`r0`/`r1` die at the first `add` and `r2` is consumed by the last instruction,
so at most 2 are ever live at once — peak < registers mentioned. -/
def tempDies : Stmt 64 :=
  .imm 0 1 ;; .imm 1 2 ;; .bin .add 2 0 1 ;; .bin .add 2 2 2 ;; .un .isZero 3 2

/-- info: 2 -/
#guard_msgs in
#eval tempDies.regPeak₀

end Caliper
