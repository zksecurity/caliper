import Clean.Caliper.Core

/-!
# Upper-bound Hoare triples

`Triple C P c Q T D M` is total correctness with resource *upper bounds*: from any
state satisfying `P`, the statement terminates (and is memory-safe — an `Exec`
derivation exists), the result satisfies `Q`, and

* time `t ≤ T`,
* net live-memory change `d ≤ D` (signed: freeing gives memory back),
* peak live-memory growth `p ≤ M`.

Live memory is the sum of reserved capacities: only the alloc instructions
(`bufAlloc`/`bufAllocI`) charge and only `bufFree` credits; push/pop move the fill
level inside capacity already paid for. Allocation time is charged per word
(`C.bufAlloc + cap * C.allocPerWord`), so the alloc time rules carry a capacity
bound; for the dynamic `bufAlloc` the caller must bound the requested capacity.
Bounding the *pair* (net, peak) is what makes reuse compose: sequencing peaks as
`max M₁ (D₁ + M₂)` means an alloc…free block (net 0, via `bufFree'`) contributes its
peak once, not once per occurrence, and `whileNZ_measure` gives loops whose iteration
net is `≤ 0` a peak bound independent of the trip count.

Bounds are `≤` throughout, so specs stay simple and weakening is free. The rules are
the complete proof system used by the examples: one rule per instruction
(`bufGet`/`bufSet` demand the index in range, `bufPush` demands free capacity —
the memory-safety obligations), `seq`/`conseq`/`ifNZ`, the measure-indexed loop
rule, and decidable-side-condition frame rules replacing separation logic.

Time and memory are also *independently* provable: `TimeTriple` bounds only the
running time, `SpaceTriple` only the (net, peak) memory pair — each with the full
rule set, so neither proof carries the other's algebra — and since the machine is
deterministic the two judgments recombine into a full `Triple`
(`TimeTriple.and_space`).
-/

namespace Caliper

variable {w : ℕ} {C : CostModel}

/-- Total-correctness triple with time bound `T`, net-memory bound `D` and
peak-memory bound `M`. -/
def Triple (C : CostModel) (P : State w → Prop) (c : Stmt w) (Q : State w → Prop)
    (T : ℕ) (D M : ℤ) : Prop :=
  ∀ s, P s → ∃ s' t d p, Exec C c s s' t d p ∧ Q s' ∧ t ≤ T ∧ d ≤ D ∧ p ≤ M

namespace Triple

/-- Consequence: strengthen the precondition, weaken the postcondition, raise the
bounds. This is why proving `≤` bounds beats proving exact costs: bounds compose
without case splits. -/
theorem conseq {P P' Q Q' : State w → Prop} {c : Stmt w} {T T' : ℕ} {D D' M M' : ℤ}
    (h : Triple C P c Q T D M) (hP : ∀ s, P' s → P s) (hQ : ∀ s, Q s → Q' s)
    (hT : T ≤ T') (hD : D ≤ D') (hM : M ≤ M') : Triple C P' c Q' T' D' M' := by
  intro s hs
  obtain ⟨s', t, d, p, hexec, hq, ht, hd, hp⟩ := h s (hP s hs)
  exact ⟨s', t, d, p, hexec, hQ s' hq, ht.trans hT, hd.trans hD, hp.trans hM⟩

theorem weaken {P Q : State w → Prop} {c : Stmt w} {T T' : ℕ} {D D' M M' : ℤ}
    (h : Triple C P c Q T D M) (hT : T ≤ T') (hD : D ≤ D') (hM : M ≤ M') :
    Triple C P c Q T' D' M' :=
  h.conseq (fun _ => id) (fun _ => id) hT hD hM

protected theorem skip {P Q : State w → Prop} (h : ∀ s, P s → Q s) :
    Triple C P (.skip (w := w)) Q 0 0 0 :=
  fun s hs => ⟨s, 0, 0, 0, .skip, h s hs, le_refl _, le_refl _, le_refl _⟩

protected theorem seq {P R Q : State w → Prop} {c₁ c₂ : Stmt w} {T₁ T₂ : ℕ}
    {D₁ M₁ D₂ M₂ : ℤ}
    (h₁ : Triple C P c₁ R T₁ D₁ M₁) (h₂ : Triple C R c₂ Q T₂ D₂ M₂) :
    Triple C P (c₁ ;; c₂) Q (T₁ + T₂) (D₁ + D₂) (max M₁ (D₁ + M₂)) := by
  intro s hs
  obtain ⟨s₁, t₁, d₁, p₁, he₁, hr, ht₁, hd₁, hp₁⟩ := h₁ s hs
  obtain ⟨s₂, t₂, d₂, p₂, he₂, hq, ht₂, hd₂, hp₂⟩ := h₂ s₁ hr
  exact ⟨s₂, t₁ + t₂, d₁ + d₂, max p₁ (d₁ + p₂), .seq he₁ he₂, hq,
    Nat.add_le_add ht₁ ht₂, by omega, by omega⟩

/-! ### Instruction rules

Each takes the "forward" form: the precondition must imply the postcondition of the
updated state. Chained with `seq` these give a weakest-precondition-style calculation. -/

protected theorem imm {P Q : State w → Prop} {d : Reg} {v : Word w}
    (h : ∀ s, P s → Q (s.setReg d v)) : Triple C P (.imm d v) Q C.imm 0 0 :=
  fun s hs => ⟨_, _, _, _, .imm, h s hs, le_refl _, le_refl _, le_refl _⟩

protected theorem mov {P Q : State w → Prop} {d a : Reg}
    (h : ∀ s, P s → Q (s.setReg d (s.regs a))) : Triple C P (.mov d a) Q C.mov 0 0 :=
  fun s hs => ⟨_, _, _, _, .mov, h s hs, le_refl _, le_refl _, le_refl _⟩

protected theorem un {P Q : State w → Prop} {op : UnOp} {d a : Reg}
    (h : ∀ s, P s → Q (s.setReg d (op.eval (s.regs a)))) :
    Triple C P (.un op d a) Q (C.un op) 0 0 :=
  fun s hs => ⟨_, _, _, _, .un, h s hs, le_refl _, le_refl _, le_refl _⟩

protected theorem bin {P Q : State w → Prop} {op : BinOp} {d a b : Reg}
    (h : ∀ s, P s → Q (s.setReg d (op.eval (s.regs a) (s.regs b)))) :
    Triple C P (.bin op d a b) Q (C.bin op) 0 0 :=
  fun s hs => ⟨_, _, _, _, .bin, h s hs, le_refl _, le_refl _, le_refl _⟩

/-- Reserve capacity (dynamic). The caller supplies an upper bound `N` on the
*requested capacity* (the register value); it bounds the memory charge
(`newCap - oldCap ≤ newCap ≤ N`, capacities being nonnegative) **and** the
data-dependent time charge `C.bufAlloc + newCap * C.allocPerWord ≤
C.bufAlloc + N * C.allocPerWord`. -/
protected theorem bufAlloc {P Q : State w → Prop} {b : BufId} {n : Reg} {N : ℕ}
    (h : ∀ s, P s → (s.regs n).toNat ≤ N ∧ Q (s.allocBuf b (s.regs n).toNat)) :
    Triple C P (.bufAlloc b n) Q (C.bufAlloc + N * C.allocPerWord) N N := by
  intro s hs
  obtain ⟨hN, hq⟩ := h s hs
  refine ⟨_, _, _, _, .bufAlloc, hq, ?_, by omega, by omega⟩
  have := Nat.mul_le_mul_right C.allocPerWord hN
  omega

/-- Reserve capacity (immediate): the syntactic capacity `n` prices both time
(exactly) and memory (as a bound, the old capacity being unknown but
nonnegative). -/
protected theorem bufAllocI {P Q : State w → Prop} {b : BufId} {n : ℕ}
    (h : ∀ s, P s → Q (s.allocBuf b n)) :
    Triple C P (.bufAllocI b n) Q (C.bufAlloc + n * C.allocPerWord) n n :=
  fun s hs => ⟨_, _, _, _, .bufAllocI, h s hs, le_refl _, by omega, by omega⟩

/-- Free a buffer: never charges memory. -/
protected theorem bufFree {P Q : State w → Prop} {b : BufId}
    (h : ∀ s, P s → Q (s.allocBuf b 0)) : Triple C P (.bufFree b) Q C.bufFree 0 0 :=
  fun s hs => ⟨_, _, _, _, .bufFree, h s hs, le_refl _, by omega, le_refl _⟩

/-- Free with a known lower bound `K` on the capacity being released: credits `-K`.
This is the rule that makes an alloc…free block's net vanish. -/
protected theorem bufFree' {P Q : State w → Prop} {b : BufId} {K : ℕ}
    (h : ∀ s, P s → K ≤ s.caps b ∧ Q (s.allocBuf b 0)) :
    Triple C P (.bufFree b) Q C.bufFree (-(K : ℤ)) 0 := by
  intro s hs
  obtain ⟨hK, hq⟩ := h s hs
  exact ⟨_, _, _, _, .bufFree, hq, le_refl _, by omega, le_refl _⟩

protected theorem bufLen {P Q : State w → Prop} {d : Reg} {b : BufId}
    (h : ∀ s, P s → Q (s.setReg d (BitVec.ofNat w (s.bufs b).size))) :
    Triple C P (.bufLen d b) Q C.bufLen 0 0 :=
  fun s hs => ⟨_, _, _, _, .bufLen, h s hs, le_refl _, le_refl _, le_refl _⟩

/-- The in-range obligation `hlt` is the memory-safety proof; there is no rule for the
out-of-range case, so a completed triple entails safety. -/
protected theorem bufGet {P Q : State w → Prop} {d : Reg} {b : BufId} {i : Reg}
    (h : ∀ s, P s → ∃ hlt : (s.regs i).toNat < (s.bufs b).size,
      Q (s.setReg d (s.bufs b)[(s.regs i).toNat])) :
    Triple C P (.bufGet d b i) Q C.bufGet 0 0 := by
  intro s hs
  obtain ⟨hlt, hq⟩ := h s hs
  exact ⟨_, _, _, _, .bufGet hlt, hq, le_refl _, le_refl _, le_refl _⟩

protected theorem bufSet {P Q : State w → Prop} {b : BufId} {i src : Reg}
    (h : ∀ s, P s → ∃ hlt : (s.regs i).toNat < (s.bufs b).size,
      Q (s.setBuf b ((s.bufs b).set (s.regs i).toNat (s.regs src) hlt))) :
    Triple C P (.bufSet b i src) Q C.bufSet 0 0 := by
  intro s hs
  obtain ⟨hlt, hq⟩ := h s hs
  exact ⟨_, _, _, _, .bufSet hlt, hq, le_refl _, le_refl _, le_refl _⟩

/-- Push demands free capacity (`size < cap`) — the second memory-safety obligation,
which is what makes push worst-case unit time. Memory-neutral: the word was charged
at `bufAlloc`. -/
protected theorem bufPush {P Q : State w → Prop} {b : BufId} {src : Reg}
    (h : ∀ s, P s → (s.bufs b).size < s.caps b
      ∧ Q (s.setBuf b ((s.bufs b).push (s.regs src)))) :
    Triple C P (.bufPush b src) Q C.bufPush 0 0 := by
  intro s hs
  obtain ⟨hcap, hq⟩ := h s hs
  exact ⟨_, _, _, _, .bufPush hcap, hq, le_refl _, le_refl _, le_refl _⟩

/-- Pop keeps the capacity: memory-neutral. -/
protected theorem bufPop {P Q : State w → Prop} {b : BufId}
    (h : ∀ s, P s → Q (s.setBuf b (s.bufs b).pop)) :
    Triple C P (.bufPop b) Q C.bufPop 0 0 :=
  fun s hs => ⟨_, _, _, _, .bufPop, h s hs, le_refl _, le_refl _, le_refl _⟩

protected theorem ifNZ {P Q : State w → Prop} {r : Reg} {thn els : Stmt w} {T : ℕ}
    {D M : ℤ}
    (ht : Triple C (fun s => P s ∧ s.regs r ≠ 0) thn Q T D M)
    (he : Triple C (fun s => P s ∧ s.regs r = 0) els Q T D M) :
    Triple C P (.ifNZ r thn els) Q (C.branch + T) D M := by
  intro s hs
  by_cases hr : s.regs r = 0
  · obtain ⟨s', t, d, p, hexec, hq, hT, hD, hM⟩ := he s ⟨hs, hr⟩
    exact ⟨s', C.branch + t, d, p, .ifNZ_false hr hexec, hq,
      Nat.add_le_add_left hT _, hD, hM⟩
  · obtain ⟨s', t, d, p, hexec, hq, hT, hD, hM⟩ := ht s ⟨hs, hr⟩
    exact ⟨s', C.branch + t, d, p, .ifNZ_true hr hexec, hq,
      Nat.add_le_add_left hT _, hD, hM⟩

/-- **The loop rule.** `I k` is the invariant before the guard when at most `k`
iterations remain; `J k` is the invariant right after the guard.

* The guard takes `I k` to `J k` within `(Tg, Dg, Mg)`.
* If the guard's flag is up, at least one iteration remains (`hpos`), and the body
  takes `J (k+1)` back to `I k` within `(Tb, Db, Mb)`.

Time is linear in `k` as before. Memory: both net and peak are bounded by
`base + k * max (Dg + Db) 0` — `max` with 0 because the loop may exit early, and
fewer iterations free less. The payoff: when each iteration's net `Dg + Db` is `≤ 0`
(memory reused), **neither net nor peak grows with `k`**. -/
theorem whileNZ_measure {I J : ℕ → State w → Prop} {g body : Stmt w} {r : Reg}
    {Tg Tb : ℕ} {Dg Mg Db Mb : ℤ}
    (hg : ∀ k, Triple C (I k) g (J k) Tg Dg Mg)
    (hpos : ∀ k s, J k s → s.regs r ≠ 0 → ∃ k', k = k' + 1)
    (hb : ∀ k, Triple C (fun s => J (k + 1) s ∧ s.regs r ≠ 0) body (I k) Tb Db Mb) :
    ∀ k, Triple C (I k) (.whileNZ g r body)
      (fun s => ∃ k', J k' s ∧ s.regs r = 0)
      ((k + 1) * (Tg + C.branch) + k * Tb)
      (Dg + k * max (Dg + Db) 0)
      (max Mg (Dg + Mb) + k * max (Dg + Db) 0) := by
  intro k
  induction k with
  | zero =>
    intro s hs
    obtain ⟨s₁, tg, dg, pg, heg, hj, htg, hdg, hpg⟩ := hg 0 s hs
    by_cases hr : s₁.regs r = 0
    · refine ⟨s₁, tg + C.branch, dg, pg, .while_done heg hr, ⟨0, hj, hr⟩,
        ?_, ?_, ?_⟩
      · omega
      · push_cast; omega
      · push_cast; omega
    · obtain ⟨k', hk'⟩ := hpos 0 s₁ hj hr
      omega
  | succ k ih =>
    intro s hs
    have hnn : (0 : ℤ) ≤ (k : ℤ) * max (Dg + Db) 0 :=
      mul_nonneg (Int.natCast_nonneg k) (le_max_right _ _)
    have hsplit : ((k : ℤ) + 1) * max (Dg + Db) 0
        = max (Dg + Db) 0 + (k : ℤ) * max (Dg + Db) 0 := by ring
    obtain ⟨s₁, tg, dg, pg, heg, hj, htg, hdg, hpg⟩ := hg (k + 1) s hs
    by_cases hr : s₁.regs r = 0
    · refine ⟨s₁, tg + C.branch, dg, pg, .while_done heg hr, ⟨k + 1, hj, hr⟩,
        ?_, ?_, ?_⟩
      · calc tg + C.branch ≤ Tg + C.branch := Nat.add_le_add_right htg _
          _ ≤ (k + 1 + 1) * (Tg + C.branch) + (k + 1) * Tb := by nlinarith
      · push_cast; omega
      · push_cast; omega
    · obtain ⟨s₂, tb, db, pb, heb, hi, htb, hdb, hpb⟩ := hb k s₁ ⟨hj, hr⟩
      obtain ⟨s₃, tl, dl, pl, hel, hq, htl, hdl, hpl⟩ := ih s₂ hi
      refine ⟨s₃, tg + C.branch + tb + tl, dg + db + dl,
        max pg (dg + max pb (db + pl)),
        .while_step heg hr heb hel, hq, ?_, ?_, ?_⟩
      · have : (k + 1 + 1) * (Tg + C.branch) + (k + 1) * Tb
            = (Tg + C.branch) + Tb + ((k + 1) * (Tg + C.branch) + k * Tb) := by ring
        omega
      · push_cast at hdl ⊢
        omega
      · push_cast at hpl ⊢
        omega

/-! ### Framing

Anything a statement provably doesn't write (a decidable, syntactic check) can be
carried across its triple for free. -/

/-- Carry a fact about an untouched register and an untouched buffer family across a
triple. Instantiate `R` with e.g. `fun s => s.regs 3 = x ∧ s.bufs 0 = arr`; the
`hR` hypothesis is discharged by `Exec.frame_reg`/`Exec.frame_buf` + `decide`. -/
theorem frame_post {P Q R : State w → Prop} {c : Stmt w} {T : ℕ} {D M : ℤ}
    (h : Triple C P c Q T D M)
    (hR : ∀ s s' t d p, Exec C c s s' t d p → R s → R s') :
    Triple C (fun s => P s ∧ R s) c (fun s => Q s ∧ R s) T D M := by
  intro s ⟨hp, hr⟩
  obtain ⟨s', t, d, p, hexec, hq, hT, hD, hM⟩ := h s hp
  exact ⟨s', t, d, p, hexec, ⟨hq, hR s s' t d p hexec hr⟩, hT, hD, hM⟩

/-- Specialization: a register the statement never writes keeps its value. -/
theorem frame_reg {P Q : State w → Prop} {c : Stmt w} {T : ℕ} {D M : ℤ} {r : Reg}
    {v : Word w} (h : Triple C P c Q T D M) (hw : ¬ c.Writes r) :
    Triple C (fun s => P s ∧ s.regs r = v) c (fun s => Q s ∧ s.regs r = v) T D M :=
  h.frame_post fun _ _ _ _ _ hexec hr => (hexec.frame_reg hw).trans hr

/-- Specialization: a buffer the statement never touches keeps its contents. -/
theorem frame_buf {P Q : State w → Prop} {c : Stmt w} {T : ℕ} {D M : ℤ} {b : BufId}
    {arr : Array (Word w)} (h : Triple C P c Q T D M) (ht : ¬ c.Touches b) :
    Triple C (fun s => P s ∧ s.bufs b = arr) c (fun s => Q s ∧ s.bufs b = arr) T D M :=
  h.frame_post fun _ _ _ _ _ hexec hb => (hexec.frame_buf ht).trans hb

end Triple

/-! ## Decoupled judgments: time-only and space-only triples

A `Triple` carries all three bounds at once, which forces every proof to do the
memory algebra even when only a running-time bound is wanted (and vice versa).
`TimeTriple` and `SpaceTriple` are the two halves: the same total-correctness core —
an `Exec` derivation is exhibited, so termination and memory safety are still
proved — but only one resource is bounded, and the other resource's arithmetic
disappears from the rules entirely (`TimeTriple.seq` has no `max` profile algebra;
`SpaceTriple.whileNZ_measure` has no trip-count time term).

The halves lose nothing: `Triple.time`/`Triple.space` project a full triple, and
because the machine is deterministic (`Exec.deterministic`) the executions exhibited
by a `TimeTriple` and a `SpaceTriple` from the same state are the *same* execution,
so `TimeTriple.and_space` recombines separately proved bounds into a full `Triple`
after the fact. Decoupling is not just convenience: a bound of one kind can exist
while the other provably does not — see `Drain` in `Examples.lean`, a loop with a
trip-count-independent space bound but no uniform time bound. -/

/-- Time-only total-correctness triple: from any state satisfying `P`, the statement
terminates (memory-safely) in a state satisfying `Q` within `t ≤ T` time units. The
execution's memory profile is existentially forgotten. -/
def TimeTriple (C : CostModel) (P : State w → Prop) (c : Stmt w) (Q : State w → Prop)
    (T : ℕ) : Prop :=
  ∀ s, P s → ∃ s' t d p, Exec C c s s' t d p ∧ Q s' ∧ t ≤ T

/-- Space-only total-correctness triple: net live-memory change `d ≤ D` and peak
growth `p ≤ M`. The running time is existentially forgotten — the statement still
*terminates* (an `Exec` derivation is exhibited), there is just no bound on `t`. -/
def SpaceTriple (C : CostModel) (P : State w → Prop) (c : Stmt w) (Q : State w → Prop)
    (D M : ℤ) : Prop :=
  ∀ s, P s → ∃ s' t d p, Exec C c s s' t d p ∧ Q s' ∧ d ≤ D ∧ p ≤ M

/-- Forget the memory bounds of a full triple. -/
theorem Triple.time {P Q : State w → Prop} {c : Stmt w} {T : ℕ} {D M : ℤ}
    (h : Triple C P c Q T D M) : TimeTriple C P c Q T := by
  intro s hs
  obtain ⟨s', t, d, p, hexec, hq, hT, _, _⟩ := h s hs
  exact ⟨s', t, d, p, hexec, hq, hT⟩

/-- Forget the time bound of a full triple. -/
theorem Triple.space {P Q : State w → Prop} {c : Stmt w} {T : ℕ} {D M : ℤ}
    (h : Triple C P c Q T D M) : SpaceTriple C P c Q D M := by
  intro s hs
  obtain ⟨s', t, d, p, hexec, hq, _, hD, hM⟩ := h s hs
  exact ⟨s', t, d, p, hexec, hq, hD, hM⟩

namespace TimeTriple

/-- **Recombination.** The machine is deterministic, so the executions exhibited by a
time-only and a space-only triple from the same state coincide — separately proved
bounds hold of the one real execution, giving back a full `Triple`. -/
theorem and_space {P Q₁ Q₂ : State w → Prop} {c : Stmt w} {T : ℕ} {D M : ℤ}
    (h₁ : TimeTriple C P c Q₁ T) (h₂ : SpaceTriple C P c Q₂ D M) :
    Triple C P c (fun s => Q₁ s ∧ Q₂ s) T D M := by
  intro s hs
  obtain ⟨s', t, d, p, hexec, hq₁, hT⟩ := h₁ s hs
  obtain ⟨s'', t', d', p', hexec', hq₂, hD, hM⟩ := h₂ s hs
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hexec.deterministic hexec'
  exact ⟨s', t, d, p, hexec, ⟨hq₁, hq₂⟩, hT, hD, hM⟩

/-- Recombination when the two judgments share a postcondition. -/
theorem and_space' {P Q : State w → Prop} {c : Stmt w} {T : ℕ} {D M : ℤ}
    (h₁ : TimeTriple C P c Q T) (h₂ : SpaceTriple C P c Q D M) :
    Triple C P c Q T D M :=
  (h₁.and_space h₂).conseq (fun _ => id) (fun _ h => h.1) (le_refl _) (le_refl _)
    (le_refl _)

/-- Code containing no `bufAlloc` gets a space triple for free from a time triple:
the execution the time triple already exhibits satisfies `d ≤ 0 ∧ p ≤ 0` outright
(`Exec.allocFree_space`). -/
theorem space_of_allocFree {P Q : State w → Prop} {c : Stmt w} {T : ℕ}
    (h : TimeTriple C P c Q T) (ha : c.AllocFree) : SpaceTriple C P c Q 0 0 := by
  intro s hs
  obtain ⟨s', t, d, p, hexec, hq, _⟩ := h s hs
  obtain ⟨hd, hp⟩ := hexec.allocFree_space ha
  exact ⟨s', t, d, p, hexec, hq, hd, hp⟩

theorem conseq {P P' Q Q' : State w → Prop} {c : Stmt w} {T T' : ℕ}
    (h : TimeTriple C P c Q T) (hP : ∀ s, P' s → P s) (hQ : ∀ s, Q s → Q' s)
    (hT : T ≤ T') : TimeTriple C P' c Q' T' := by
  intro s hs
  obtain ⟨s', t, d, p, hexec, hq, ht⟩ := h s (hP s hs)
  exact ⟨s', t, d, p, hexec, hQ s' hq, ht.trans hT⟩

theorem weaken {P Q : State w → Prop} {c : Stmt w} {T T' : ℕ}
    (h : TimeTriple C P c Q T) (hT : T ≤ T') : TimeTriple C P c Q T' :=
  h.conseq (fun _ => id) (fun _ => id) hT

protected theorem skip {P Q : State w → Prop} (h : ∀ s, P s → Q s) :
    TimeTriple C P (.skip (w := w)) Q 0 :=
  (Triple.skip h).time

/-- Sequencing time bounds is plain addition — none of `Triple.seq`'s (net, peak)
profile algebra appears. That absence is the point of the decoupled judgment. -/
protected theorem seq {P R Q : State w → Prop} {c₁ c₂ : Stmt w} {T₁ T₂ : ℕ}
    (h₁ : TimeTriple C P c₁ R T₁) (h₂ : TimeTriple C R c₂ Q T₂) :
    TimeTriple C P (c₁ ;; c₂) Q (T₁ + T₂) := by
  intro s hs
  obtain ⟨s₁, t₁, d₁, p₁, he₁, hr, ht₁⟩ := h₁ s hs
  obtain ⟨s₂, t₂, d₂, p₂, he₂, hq, ht₂⟩ := h₂ s₁ hr
  exact ⟨s₂, t₁ + t₂, d₁ + d₂, max p₁ (d₁ + p₂), .seq he₁ he₂, hq,
    Nat.add_le_add ht₁ ht₂⟩

/-! ### Instruction rules

Projections of the corresponding `Triple` rules — except `bufAlloc`, whose full rule
carries a memory obligation that a time bound does not need. -/

protected theorem imm {P Q : State w → Prop} {d : Reg} {v : Word w}
    (h : ∀ s, P s → Q (s.setReg d v)) : TimeTriple C P (.imm d v) Q C.imm :=
  (Triple.imm h).time

protected theorem mov {P Q : State w → Prop} {d a : Reg}
    (h : ∀ s, P s → Q (s.setReg d (s.regs a))) : TimeTriple C P (.mov d a) Q C.mov :=
  (Triple.mov h).time

protected theorem un {P Q : State w → Prop} {op : UnOp} {d a : Reg}
    (h : ∀ s, P s → Q (s.setReg d (op.eval (s.regs a)))) :
    TimeTriple C P (.un op d a) Q (C.un op) :=
  (Triple.un h).time

protected theorem bin {P Q : State w → Prop} {op : BinOp} {d a b : Reg}
    (h : ∀ s, P s → Q (s.setReg d (op.eval (s.regs a) (s.regs b)))) :
    TimeTriple C P (.bin op d a b) Q (C.bin op) :=
  (Triple.bin h).time

/-- Reserve capacity (dynamic). Unlike the other time rules the capacity bound `N`
does **not** disappear: the time charge `C.bufAlloc + newCap * C.allocPerWord` is
data-dependent, so bounding the requested capacity is exactly what a time bound
needs. -/
protected theorem bufAlloc {P Q : State w → Prop} {b : BufId} {n : Reg} {N : ℕ}
    (h : ∀ s, P s → (s.regs n).toNat ≤ N ∧ Q (s.allocBuf b (s.regs n).toNat)) :
    TimeTriple C P (.bufAlloc b n) Q (C.bufAlloc + N * C.allocPerWord) :=
  (Triple.bufAlloc h).time

/-- Reserve capacity (immediate): statically priced, no side obligation. -/
protected theorem bufAllocI {P Q : State w → Prop} {b : BufId} {n : ℕ}
    (h : ∀ s, P s → Q (s.allocBuf b n)) :
    TimeTriple C P (.bufAllocI b n) Q (C.bufAlloc + n * C.allocPerWord) :=
  (Triple.bufAllocI h).time

protected theorem bufFree {P Q : State w → Prop} {b : BufId}
    (h : ∀ s, P s → Q (s.allocBuf b 0)) : TimeTriple C P (.bufFree b) Q C.bufFree :=
  (Triple.bufFree h).time

protected theorem bufLen {P Q : State w → Prop} {d : Reg} {b : BufId}
    (h : ∀ s, P s → Q (s.setReg d (BitVec.ofNat w (s.bufs b).size))) :
    TimeTriple C P (.bufLen d b) Q C.bufLen :=
  (Triple.bufLen h).time

protected theorem bufGet {P Q : State w → Prop} {d : Reg} {b : BufId} {i : Reg}
    (h : ∀ s, P s → ∃ hlt : (s.regs i).toNat < (s.bufs b).size,
      Q (s.setReg d (s.bufs b)[(s.regs i).toNat])) :
    TimeTriple C P (.bufGet d b i) Q C.bufGet :=
  (Triple.bufGet h).time

protected theorem bufSet {P Q : State w → Prop} {b : BufId} {i src : Reg}
    (h : ∀ s, P s → ∃ hlt : (s.regs i).toNat < (s.bufs b).size,
      Q (s.setBuf b ((s.bufs b).set (s.regs i).toNat (s.regs src) hlt))) :
    TimeTriple C P (.bufSet b i src) Q C.bufSet :=
  (Triple.bufSet h).time

protected theorem bufPush {P Q : State w → Prop} {b : BufId} {src : Reg}
    (h : ∀ s, P s → (s.bufs b).size < s.caps b
      ∧ Q (s.setBuf b ((s.bufs b).push (s.regs src)))) :
    TimeTriple C P (.bufPush b src) Q C.bufPush :=
  (Triple.bufPush h).time

protected theorem bufPop {P Q : State w → Prop} {b : BufId}
    (h : ∀ s, P s → Q (s.setBuf b (s.bufs b).pop)) :
    TimeTriple C P (.bufPop b) Q C.bufPop :=
  (Triple.bufPop h).time

protected theorem ifNZ {P Q : State w → Prop} {r : Reg} {thn els : Stmt w} {T : ℕ}
    (ht : TimeTriple C (fun s => P s ∧ s.regs r ≠ 0) thn Q T)
    (he : TimeTriple C (fun s => P s ∧ s.regs r = 0) els Q T) :
    TimeTriple C P (.ifNZ r thn els) Q (C.branch + T) := by
  intro s hs
  by_cases hr : s.regs r = 0
  · obtain ⟨s', t, d, p, hexec, hq, hT⟩ := he s ⟨hs, hr⟩
    exact ⟨s', C.branch + t, d, p, .ifNZ_false hr hexec, hq, Nat.add_le_add_left hT _⟩
  · obtain ⟨s', t, d, p, hexec, hq, hT⟩ := ht s ⟨hs, hr⟩
    exact ⟨s', C.branch + t, d, p, .ifNZ_true hr hexec, hq, Nat.add_le_add_left hT _⟩

/-- The time-only loop rule: the measure-indexed structure of
`Triple.whileNZ_measure` (the measure is what proves termination), with **no**
memory hypotheses and no memory conclusion. Time is linear in `k` as before. -/
theorem whileNZ_measure {I J : ℕ → State w → Prop} {g body : Stmt w} {r : Reg}
    {Tg Tb : ℕ}
    (hg : ∀ k, TimeTriple C (I k) g (J k) Tg)
    (hpos : ∀ k s, J k s → s.regs r ≠ 0 → ∃ k', k = k' + 1)
    (hb : ∀ k, TimeTriple C (fun s => J (k + 1) s ∧ s.regs r ≠ 0) body (I k) Tb) :
    ∀ k, TimeTriple C (I k) (.whileNZ g r body)
      (fun s => ∃ k', J k' s ∧ s.regs r = 0)
      ((k + 1) * (Tg + C.branch) + k * Tb) := by
  intro k
  induction k with
  | zero =>
    intro s hs
    obtain ⟨s₁, tg, dg, pg, heg, hj, htg⟩ := hg 0 s hs
    by_cases hr : s₁.regs r = 0
    · exact ⟨s₁, tg + C.branch, dg, pg, .while_done heg hr, ⟨0, hj, hr⟩, by omega⟩
    · obtain ⟨k', hk'⟩ := hpos 0 s₁ hj hr
      omega
  | succ k ih =>
    intro s hs
    obtain ⟨s₁, tg, dg, pg, heg, hj, htg⟩ := hg (k + 1) s hs
    by_cases hr : s₁.regs r = 0
    · refine ⟨s₁, tg + C.branch, dg, pg, .while_done heg hr, ⟨k + 1, hj, hr⟩, ?_⟩
      calc tg + C.branch ≤ Tg + C.branch := Nat.add_le_add_right htg _
        _ ≤ (k + 1 + 1) * (Tg + C.branch) + (k + 1) * Tb := by nlinarith
    · obtain ⟨s₂, tb, db, pb, heb, hi, htb⟩ := hb k s₁ ⟨hj, hr⟩
      obtain ⟨s₃, tl, dl, pl, hel, hq, htl⟩ := ih s₂ hi
      refine ⟨s₃, tg + C.branch + tb + tl, dg + db + dl,
        max pg (dg + max pb (db + pl)), .while_step heg hr heb hel, hq, ?_⟩
      have : (k + 1 + 1) * (Tg + C.branch) + (k + 1) * Tb
          = (Tg + C.branch) + Tb + ((k + 1) * (Tg + C.branch) + k * Tb) := by ring
      omega

/-! ### Framing -/

theorem frame_post {P Q R : State w → Prop} {c : Stmt w} {T : ℕ}
    (h : TimeTriple C P c Q T)
    (hR : ∀ s s' t d p, Exec C c s s' t d p → R s → R s') :
    TimeTriple C (fun s => P s ∧ R s) c (fun s => Q s ∧ R s) T := by
  intro s ⟨hp, hr⟩
  obtain ⟨s', t, d, p, hexec, hq, hT⟩ := h s hp
  exact ⟨s', t, d, p, hexec, ⟨hq, hR s s' t d p hexec hr⟩, hT⟩

/-- A register the statement never writes keeps its value. -/
theorem frame_reg {P Q : State w → Prop} {c : Stmt w} {T : ℕ} {r : Reg}
    {v : Word w} (h : TimeTriple C P c Q T) (hw : ¬ c.Writes r) :
    TimeTriple C (fun s => P s ∧ s.regs r = v) c (fun s => Q s ∧ s.regs r = v) T :=
  h.frame_post fun _ _ _ _ _ hexec hr => (hexec.frame_reg hw).trans hr

/-- A buffer the statement never touches keeps its contents. -/
theorem frame_buf {P Q : State w → Prop} {c : Stmt w} {T : ℕ} {b : BufId}
    {arr : Array (Word w)} (h : TimeTriple C P c Q T) (ht : ¬ c.Touches b) :
    TimeTriple C (fun s => P s ∧ s.bufs b = arr) c (fun s => Q s ∧ s.bufs b = arr) T :=
  h.frame_post fun _ _ _ _ _ hexec hb => (hexec.frame_buf ht).trans hb

end TimeTriple

namespace SpaceTriple

theorem conseq {P P' Q Q' : State w → Prop} {c : Stmt w} {D D' M M' : ℤ}
    (h : SpaceTriple C P c Q D M) (hP : ∀ s, P' s → P s) (hQ : ∀ s, Q s → Q' s)
    (hD : D ≤ D') (hM : M ≤ M') : SpaceTriple C P' c Q' D' M' := by
  intro s hs
  obtain ⟨s', t, d, p, hexec, hq, hd, hp⟩ := h s (hP s hs)
  exact ⟨s', t, d, p, hexec, hQ s' hq, hd.trans hD, hp.trans hM⟩

theorem weaken {P Q : State w → Prop} {c : Stmt w} {D D' M M' : ℤ}
    (h : SpaceTriple C P c Q D M) (hD : D ≤ D') (hM : M ≤ M') :
    SpaceTriple C P c Q D' M' :=
  h.conseq (fun _ => id) (fun _ => id) hD hM

protected theorem skip {P Q : State w → Prop} (h : ∀ s, P s → Q s) :
    SpaceTriple C P (.skip (w := w)) Q 0 0 :=
  (Triple.skip h).space

/-- Sequencing composes the memory profile exactly as in `Triple.seq` — but with no
time arithmetic anywhere. -/
protected theorem seq {P R Q : State w → Prop} {c₁ c₂ : Stmt w} {D₁ M₁ D₂ M₂ : ℤ}
    (h₁ : SpaceTriple C P c₁ R D₁ M₁) (h₂ : SpaceTriple C R c₂ Q D₂ M₂) :
    SpaceTriple C P (c₁ ;; c₂) Q (D₁ + D₂) (max M₁ (D₁ + M₂)) := by
  intro s hs
  obtain ⟨s₁, t₁, d₁, p₁, he₁, hr, hd₁, hp₁⟩ := h₁ s hs
  obtain ⟨s₂, t₂, d₂, p₂, he₂, hq, hd₂, hp₂⟩ := h₂ s₁ hr
  exact ⟨s₂, t₁ + t₂, d₁ + d₂, max p₁ (d₁ + p₂), .seq he₁ he₂, hq,
    by omega, by omega⟩

/-! ### Instruction rules

All projections of the corresponding `Triple` rules — the dropped time bound never
constrains anything. -/

protected theorem imm {P Q : State w → Prop} {d : Reg} {v : Word w}
    (h : ∀ s, P s → Q (s.setReg d v)) : SpaceTriple C P (.imm d v) Q 0 0 :=
  (Triple.imm h).space

protected theorem mov {P Q : State w → Prop} {d a : Reg}
    (h : ∀ s, P s → Q (s.setReg d (s.regs a))) : SpaceTriple C P (.mov d a) Q 0 0 :=
  (Triple.mov h).space

protected theorem un {P Q : State w → Prop} {op : UnOp} {d a : Reg}
    (h : ∀ s, P s → Q (s.setReg d (op.eval (s.regs a)))) :
    SpaceTriple C P (.un op d a) Q 0 0 :=
  (Triple.un h).space

protected theorem bin {P Q : State w → Prop} {op : BinOp} {d a b : Reg}
    (h : ∀ s, P s → Q (s.setReg d (op.eval (s.regs a) (s.regs b)))) :
    SpaceTriple C P (.bin op d a b) Q 0 0 :=
  (Triple.bin h).space

/-- Reserve capacity (dynamic), charging at most `N`. Since no time bound is
drawn, this rule keeps the finer *charge* bound (`newCap - oldCap ≤ N`, which may
use knowledge of the old capacity and may even be negative) rather than
`Triple.bufAlloc`'s bound on the requested capacity itself — direct, not
projected. -/
protected theorem bufAlloc {P Q : State w → Prop} {b : BufId} {n : Reg} {N : ℤ}
    (h : ∀ s, P s → (((s.regs n).toNat : ℤ) - (s.caps b : ℤ) ≤ N)
      ∧ Q (s.allocBuf b (s.regs n).toNat)) :
    SpaceTriple C P (.bufAlloc b n) Q N (max N 0) := by
  intro s hs
  obtain ⟨hN, hq⟩ := h s hs
  exact ⟨_, _, _, _, .bufAlloc, hq, hN, by omega⟩

/-- Reserve capacity (immediate), charging at most the syntactic capacity `n`. -/
protected theorem bufAllocI {P Q : State w → Prop} {b : BufId} {n : ℕ}
    (h : ∀ s, P s → Q (s.allocBuf b n)) :
    SpaceTriple C P (.bufAllocI b n) Q n n :=
  (Triple.bufAllocI h).space

protected theorem bufFree {P Q : State w → Prop} {b : BufId}
    (h : ∀ s, P s → Q (s.allocBuf b 0)) : SpaceTriple C P (.bufFree b) Q 0 0 :=
  (Triple.bufFree h).space

/-- Free with a known lower bound `K` on the released capacity: credits `-K`. -/
protected theorem bufFree' {P Q : State w → Prop} {b : BufId} {K : ℕ}
    (h : ∀ s, P s → K ≤ s.caps b ∧ Q (s.allocBuf b 0)) :
    SpaceTriple C P (.bufFree b) Q (-(K : ℤ)) 0 :=
  (Triple.bufFree' h).space

protected theorem bufLen {P Q : State w → Prop} {d : Reg} {b : BufId}
    (h : ∀ s, P s → Q (s.setReg d (BitVec.ofNat w (s.bufs b).size))) :
    SpaceTriple C P (.bufLen d b) Q 0 0 :=
  (Triple.bufLen h).space

protected theorem bufGet {P Q : State w → Prop} {d : Reg} {b : BufId} {i : Reg}
    (h : ∀ s, P s → ∃ hlt : (s.regs i).toNat < (s.bufs b).size,
      Q (s.setReg d (s.bufs b)[(s.regs i).toNat])) :
    SpaceTriple C P (.bufGet d b i) Q 0 0 :=
  (Triple.bufGet h).space

protected theorem bufSet {P Q : State w → Prop} {b : BufId} {i src : Reg}
    (h : ∀ s, P s → ∃ hlt : (s.regs i).toNat < (s.bufs b).size,
      Q (s.setBuf b ((s.bufs b).set (s.regs i).toNat (s.regs src) hlt))) :
    SpaceTriple C P (.bufSet b i src) Q 0 0 :=
  (Triple.bufSet h).space

protected theorem bufPush {P Q : State w → Prop} {b : BufId} {src : Reg}
    (h : ∀ s, P s → (s.bufs b).size < s.caps b
      ∧ Q (s.setBuf b ((s.bufs b).push (s.regs src)))) :
    SpaceTriple C P (.bufPush b src) Q 0 0 :=
  (Triple.bufPush h).space

protected theorem bufPop {P Q : State w → Prop} {b : BufId}
    (h : ∀ s, P s → Q (s.setBuf b (s.bufs b).pop)) :
    SpaceTriple C P (.bufPop b) Q 0 0 :=
  (Triple.bufPop h).space

protected theorem ifNZ {P Q : State w → Prop} {r : Reg} {thn els : Stmt w} {D M : ℤ}
    (ht : SpaceTriple C (fun s => P s ∧ s.regs r ≠ 0) thn Q D M)
    (he : SpaceTriple C (fun s => P s ∧ s.regs r = 0) els Q D M) :
    SpaceTriple C P (.ifNZ r thn els) Q D M := by
  intro s hs
  by_cases hr : s.regs r = 0
  · obtain ⟨s', t, d, p, hexec, hq, hD, hM⟩ := he s ⟨hs, hr⟩
    exact ⟨s', C.branch + t, d, p, .ifNZ_false hr hexec, hq, hD, hM⟩
  · obtain ⟨s', t, d, p, hexec, hq, hD, hM⟩ := ht s ⟨hs, hr⟩
    exact ⟨s', C.branch + t, d, p, .ifNZ_true hr hexec, hq, hD, hM⟩

/-- The space-only loop rule: same measure-indexed structure as
`Triple.whileNZ_measure` (the measure is still what proves termination), same memory
bounds — `base + k * max (Dg + Db) 0`, so a memory-reusing iteration (`Dg + Db ≤ 0`)
gives trip-count-independent bounds — but **no time bound** in the conclusion, so no
`Tg`/`Tb` hypotheses are needed. -/
theorem whileNZ_measure {I J : ℕ → State w → Prop} {g body : Stmt w} {r : Reg}
    {Dg Mg Db Mb : ℤ}
    (hg : ∀ k, SpaceTriple C (I k) g (J k) Dg Mg)
    (hpos : ∀ k s, J k s → s.regs r ≠ 0 → ∃ k', k = k' + 1)
    (hb : ∀ k, SpaceTriple C (fun s => J (k + 1) s ∧ s.regs r ≠ 0) body (I k) Db Mb) :
    ∀ k, SpaceTriple C (I k) (.whileNZ g r body)
      (fun s => ∃ k', J k' s ∧ s.regs r = 0)
      (Dg + k * max (Dg + Db) 0)
      (max Mg (Dg + Mb) + k * max (Dg + Db) 0) := by
  intro k
  induction k with
  | zero =>
    intro s hs
    obtain ⟨s₁, tg, dg, pg, heg, hj, hdg, hpg⟩ := hg 0 s hs
    by_cases hr : s₁.regs r = 0
    · refine ⟨s₁, tg + C.branch, dg, pg, .while_done heg hr, ⟨0, hj, hr⟩, ?_, ?_⟩
      · push_cast; omega
      · push_cast; omega
    · obtain ⟨k', hk'⟩ := hpos 0 s₁ hj hr
      omega
  | succ k ih =>
    intro s hs
    have hnn : (0 : ℤ) ≤ (k : ℤ) * max (Dg + Db) 0 :=
      mul_nonneg (Int.natCast_nonneg k) (le_max_right _ _)
    have hsplit : ((k : ℤ) + 1) * max (Dg + Db) 0
        = max (Dg + Db) 0 + (k : ℤ) * max (Dg + Db) 0 := by ring
    obtain ⟨s₁, tg, dg, pg, heg, hj, hdg, hpg⟩ := hg (k + 1) s hs
    by_cases hr : s₁.regs r = 0
    · refine ⟨s₁, tg + C.branch, dg, pg, .while_done heg hr, ⟨k + 1, hj, hr⟩, ?_, ?_⟩
      · push_cast; omega
      · push_cast; omega
    · obtain ⟨s₂, tb, db, pb, heb, hi, hdb, hpb⟩ := hb k s₁ ⟨hj, hr⟩
      obtain ⟨s₃, tl, dl, pl, hel, hq, hdl, hpl⟩ := ih s₂ hi
      refine ⟨s₃, tg + C.branch + tb + tl, dg + db + dl,
        max pg (dg + max pb (db + pl)), .while_step heg hr heb hel, hq, ?_, ?_⟩
      · push_cast at hdl ⊢
        omega
      · push_cast at hpl ⊢
        omega

/-! ### Framing -/

theorem frame_post {P Q R : State w → Prop} {c : Stmt w} {D M : ℤ}
    (h : SpaceTriple C P c Q D M)
    (hR : ∀ s s' t d p, Exec C c s s' t d p → R s → R s') :
    SpaceTriple C (fun s => P s ∧ R s) c (fun s => Q s ∧ R s) D M := by
  intro s ⟨hp, hr⟩
  obtain ⟨s', t, d, p, hexec, hq, hD, hM⟩ := h s hp
  exact ⟨s', t, d, p, hexec, ⟨hq, hR s s' t d p hexec hr⟩, hD, hM⟩

/-- A register the statement never writes keeps its value. -/
theorem frame_reg {P Q : State w → Prop} {c : Stmt w} {D M : ℤ} {r : Reg}
    {v : Word w} (h : SpaceTriple C P c Q D M) (hw : ¬ c.Writes r) :
    SpaceTriple C (fun s => P s ∧ s.regs r = v) c (fun s => Q s ∧ s.regs r = v) D M :=
  h.frame_post fun _ _ _ _ _ hexec hr => (hexec.frame_reg hw).trans hr

/-- A buffer the statement never touches keeps its contents. -/
theorem frame_buf {P Q : State w → Prop} {c : Stmt w} {D M : ℤ} {b : BufId}
    {arr : Array (Word w)} (h : SpaceTriple C P c Q D M) (ht : ¬ c.Touches b) :
    SpaceTriple C (fun s => P s ∧ s.bufs b = arr) c (fun s => Q s ∧ s.bufs b = arr)
      D M :=
  h.frame_post fun _ _ _ _ _ hexec hb => (hexec.frame_buf ht).trans hb

end SpaceTriple

end Caliper
