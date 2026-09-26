import Caliper.Tape

/-!
# Upper-bound Hoare triples

`Triple C tape P c Q T D M` is total correctness with resource *upper bounds*: from any
state satisfying `P`, the statement terminates and is memory-safe, an `Exec`
derivation existing, the result satisfies `Q`, and

* time `t ≤ T`,
* net live-memory change `d ≤ D` (signed: freeing gives memory back),
* peak live-memory growth `p ≤ M`.

Live memory is the sum of buffer lengths: only the resize instructions
(`memResize`/`memResizeI`) change it, charging growth and crediting shrinkage, with
the whole new length as the resize's peak (old and new coexist during a copy);
stores overwrite words already paid for. Resize time is charged per word of the new
length (`C.memResize + len * C.allocPerWord`), so the resize time rules carry a
length bound; for the dynamic `memResize` the caller must bound the requested
length. Bounding the *pair* (net, peak) is what makes reuse compose: sequencing
peaks as `max M₁ (D₁ + M₂)` means an acquire…free block (net 0, the free
`memResizeI b 0` crediting a known length) contributes its peak once, not once per occurrence, and `whileNZ_measure` gives loops whose iteration
net is `≤ 0` a peak bound independent of the trip count.

Bounds are `≤` throughout, so specs stay simple and weakening is free. The rules are
the complete proof system used by the examples: one rule per instruction, with the
memory-safety obligations sitting in `memLoad`/`memStore` (index in range), plus `seq`/`conseq`/`ifNZ`, the measure-indexed loop
rule, and decidable-side-condition frame rules replacing separation logic.

Time and memory are also *independently* provable: `TimeTriple` bounds only the
running time, `SpaceTriple` only the (net, peak) memory pair, each with its own
`seq`/`conseq`/`ifNZ`/loop/frame rules (instructions go through `Triple.time` /
`Triple.space`), so neither proof carries the other's algebra. Since the machine is
deterministic the two judgments recombine into a full `Triple`
(`TimeTriple.and_space`).
-/

namespace Caliper

variable {w : ℕ} {tape : RandomTape w} {C : CostModel}

/-- Total-correctness triple with time bound `T`, net-memory bound `D` and
peak-memory bound `M`. -/
def Triple (C : CostModel) (tape : RandomTape w) (P : State w → Prop) (c : Stmt w) (Q : State w → Prop)
    (T : ℕ) (D M : ℤ) : Prop :=
  ∀ s, P s → ∃ s' t d p, Exec C tape c s s' t d p ∧ Q s' ∧ t ≤ T ∧ d ≤ D ∧ p ≤ M

namespace Triple

/-- Reuse a random-free subroutine's fixed-tape specification on any caller tape. -/
theorem withTape_of_randomFree {P Q : State w → Prop} {c : Stmt w} {T : ℕ} {D M : ℤ}
    (h : Triple C tape P c Q T D M) (hc : c.RandomFree) (other : RandomTape w) :
    Triple C other P c Q T D M := by
  intro s hs
  obtain ⟨s', t, d, p, he, hq, ht, hd, hp⟩ := h s hs
  exact ⟨s', t, d, p, he.withTape_of_randomFree hc other, hq, ht, hd, hp⟩

/-- Consequence: strengthen the precondition, weaken the postcondition, raise the
bounds. This is why proving `≤` bounds beats proving exact costs: bounds compose
without case splits. -/
theorem conseq {P P' Q Q' : State w → Prop} {c : Stmt w} {T T' : ℕ} {D D' M M' : ℤ}
    (h : Triple C tape P c Q T D M) (hP : ∀ s, P' s → P s) (hQ : ∀ s, Q s → Q' s)
    (hT : T ≤ T') (hD : D ≤ D') (hM : M ≤ M') : Triple C tape P' c Q' T' D' M' := by
  intro s hs
  obtain ⟨s', t, d, p, hexec, hq, ht, hd, hp⟩ := h s (hP s hs)
  exact ⟨s', t, d, p, hexec, hQ s' hq, ht.trans hT, hd.trans hD, hp.trans hM⟩

theorem weaken {P Q : State w → Prop} {c : Stmt w} {T T' : ℕ} {D D' M M' : ℤ}
    (h : Triple C tape P c Q T D M) (hT : T ≤ T') (hD : D ≤ D') (hM : M ≤ M') :
    Triple C tape P c Q T' D' M' :=
  h.conseq (fun _ => id) (fun _ => id) hT hD hM

protected theorem skip {P Q : State w → Prop} (h : ∀ s, P s → Q s) :
    Triple C tape P (.skip (w := w)) Q 0 0 0 :=
  fun s hs => ⟨s, 0, 0, 0, .skip, h s hs, le_refl _, le_refl _, le_refl _⟩

protected theorem seq {P R Q : State w → Prop} {c₁ c₂ : Stmt w} {T₁ T₂ : ℕ}
    {D₁ M₁ D₂ M₂ : ℤ}
    (h₁ : Triple C tape P c₁ R T₁ D₁ M₁) (h₂ : Triple C tape R c₂ Q T₂ D₂ M₂) :
    Triple C tape P (c₁ ;; c₂) Q (T₁ + T₂) (D₁ + D₂) (max M₁ (D₁ + M₂)) := by
  intro s hs
  obtain ⟨s₁, t₁, d₁, p₁, he₁, hr, ht₁, hd₁, hp₁⟩ := h₁ s hs
  obtain ⟨s₂, t₂, d₂, p₂, he₂, hq, ht₂, hd₂, hp₂⟩ := h₂ s₁ hr
  exact ⟨s₂, t₁ + t₂, d₁ + d₂, max p₁ (d₁ + p₂), .seq he₁ he₂, hq,
    Nat.add_le_add ht₁ ht₂, by omega, by omega⟩

/-! ### Instruction rules

Each takes the "forward" form: the precondition must imply the postcondition of the
updated state. Chained with `seq` these give a weakest-precondition-style calculation. -/

protected theorem imm {P Q : State w → Prop} {d : Reg} {v : Word w}
    (h : ∀ s, P s → Q (s.setReg d v)) : Triple C tape P (.imm d v) Q C.imm 0 0 :=
  fun s hs => ⟨_, _, _, _, .imm, h s hs, le_refl _, le_refl _, le_refl _⟩

/-- The postcondition is checked against the word at the current tape cursor. -/
protected theorem rand {P Q : State w → Prop} {d : Reg}
    (h : ∀ s, P s → Q (s.readRandom tape d)) :
    Triple C tape P (.rand d) Q C.rand 0 0 :=
  fun s hs => ⟨_, _, _, _, .rand, h s hs, le_refl _, le_refl _, le_refl _⟩

protected theorem mov {P Q : State w → Prop} {d a : Reg}
    (h : ∀ s, P s → Q (s.setReg d (s.regs a))) : Triple C tape P (.mov d a) Q C.mov 0 0 :=
  fun s hs => ⟨_, _, _, _, .mov, h s hs, le_refl _, le_refl _, le_refl _⟩

protected theorem un {P Q : State w → Prop} {op : UnOp} {d a : Reg}
    (h : ∀ s, P s → Q (s.setReg d (op.eval (s.regs a)))) :
    Triple C tape P (.un op d a) Q (C.un op) 0 0 :=
  fun s hs => ⟨_, _, _, _, .un, h s hs, le_refl _, le_refl _, le_refl _⟩

protected theorem bin {P Q : State w → Prop} {op : BinOp} {d a b : Reg}
    (h : ∀ s, P s → Q (s.setReg d (op.eval (s.regs a) (s.regs b)))) :
    Triple C tape P (.bin op d a b) Q (C.bin op) 0 0 :=
  fun s hs => ⟨_, _, _, _, .bin, h s hs, le_refl _, le_refl _, le_refl _⟩

/-- Resize (dynamic). The caller bounds the *requested length*, the register value,
by `N`, which prices the data-dependent time charge and bounds the peak (the whole
new length, which coexists with the old one during a copying realloc), and bounds
the net charge `newLen - oldLen` by `D`, which may use knowledge of the old length
and may be negative. -/
protected theorem memResize {P Q : State w → Prop} {b : BufId} {n : Reg} {N : ℕ} {D : ℤ}
    (h : ∀ s, P s → (s.regs n).toNat ≤ N ∧ ((s.regs n).toNat : ℤ) - (s.bufs b).size ≤ D
      ∧ Q (s.resizeBuf b (s.regs n).toNat)) :
    Triple C tape P (.memResize b n) Q (C.memResize + N * C.allocPerWord) D N := by
  intro s hs
  obtain ⟨hN, hD, hq⟩ := h s hs
  refine ⟨_, _, _, _, .memResize, hq, ?_, hD, by omega⟩
  have := Nat.mul_le_mul_right C.allocPerWord hN
  omega

/-- Resize (immediate): time and peak are the syntactic `C.memResize + n *
C.allocPerWord` and `n`; the net charge `n - oldLen` is bounded by `D`. At `n = 0`
this is the free, crediting whatever lower bound on the old length `D` records. -/
protected theorem memResizeI {P Q : State w → Prop} {b : BufId} {n : ℕ} {D : ℤ}
    (h : ∀ s, P s → (n : ℤ) - (s.bufs b).size ≤ D ∧ Q (s.resizeBuf b n)) :
    Triple C tape P (.memResizeI b n) Q (C.memResize + n * C.allocPerWord) D n :=
  fun s hs => ⟨_, _, _, _, .memResizeI, (h s hs).2, le_refl _, (h s hs).1, le_refl _⟩

protected theorem memLen {P Q : State w → Prop} {d : Reg} {b : BufId}
    (h : ∀ s, P s → Q (s.setReg d (BitVec.ofNat w (s.bufs b).size))) :
    Triple C tape P (.memLen d b) Q C.memLen 0 0 :=
  fun s hs => ⟨_, _, _, _, .memLen, h s hs, le_refl _, le_refl _, le_refl _⟩

/-- The in-range obligation `hlt` is the memory-safety proof; there is no rule for the
out-of-range case, so a completed triple entails safety. -/
protected theorem memLoad {P Q : State w → Prop} {d : Reg} {b : BufId} {i : Reg}
    (h : ∀ s, P s → ∃ hlt : (s.regs i).toNat < (s.bufs b).size,
      Q (s.setReg d (s.bufs b)[(s.regs i).toNat])) :
    Triple C tape P (.memLoad d b i) Q C.memLoad 0 0 := by
  intro s hs
  obtain ⟨hlt, hq⟩ := h s hs
  exact ⟨_, _, _, _, .memLoad hlt, hq, le_refl _, le_refl _, le_refl _⟩

protected theorem memStore {P Q : State w → Prop} {b : BufId} {i src : Reg}
    (h : ∀ s, P s → ∃ hlt : (s.regs i).toNat < (s.bufs b).size,
      Q (s.setBuf b ((s.bufs b).set (s.regs i).toNat (s.regs src) hlt))) :
    Triple C tape P (.memStore b i src) Q C.memStore 0 0 := by
  intro s hs
  obtain ⟨hlt, hq⟩ := h s hs
  exact ⟨_, _, _, _, .memStore hlt, hq, le_refl _, le_refl _, le_refl _⟩

protected theorem ifNZ {P Q : State w → Prop} {r : Reg} {thn els : Stmt w} {T : ℕ}
    {D M : ℤ}
    (ht : Triple C tape (fun s => P s ∧ s.regs r ≠ 0) thn Q T D M)
    (he : Triple C tape (fun s => P s ∧ s.regs r = 0) els Q T D M) :
    Triple C tape P (.ifNZ r thn els) Q (C.branch + T) D M := by
  intro s hs
  by_cases hr : s.regs r = 0
  · obtain ⟨s', t, d, p, hexec, hq, hT, hD, hM⟩ := he s ⟨hs, hr⟩
    exact ⟨s', C.branch + t, d, p, .ifNZ_false hr hexec, hq,
      Nat.add_le_add_left hT _, hD, hM⟩
  · obtain ⟨s', t, d, p, hexec, hq, hT, hD, hM⟩ := ht s ⟨hs, hr⟩
    exact ⟨s', C.branch + t, d, p, .ifNZ_true hr hexec, hq,
      Nat.add_le_add_left hT _, hD, hM⟩

/-- The loop rule. `I k` is the invariant before the guard when at most `k`
iterations remain; `J k` is the invariant right after the guard.

* The guard takes `I k` to `J k` within `(Tg, Dg, Mg)`.
* If the guard's flag is up, at least one iteration remains (`hpos`), and the body
  takes `J (k+1)` back to `I k` within `(Tb, Db, Mb)`.

Time is linear in `k`. Both memory bounds are `base + k * max (Dg + Db) 0`, with
`max` against 0 because the loop may exit early and fewer iterations free less. So
when each iteration's net `Dg + Db` is `≤ 0`, memory being reused, neither net nor
peak grows with `k`. -/
theorem whileNZ_measure {I J : ℕ → State w → Prop} {g body : Stmt w} {r : Reg}
    {Tg Tb : ℕ} {Dg Mg Db Mb : ℤ}
    (hg : ∀ k, Triple C tape (I k) g (J k) Tg Dg Mg)
    (hpos : ∀ k s, J k s → s.regs r ≠ 0 → ∃ k', k = k' + 1)
    (hb : ∀ k, Triple C tape (fun s => J (k + 1) s ∧ s.regs r ≠ 0) body (I k) Tb Db Mb) :
    ∀ k, Triple C tape (I k) (.whileNZ g r body)
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
    (h : Triple C tape P c Q T D M)
    (hR : ∀ s s' t d p, Exec C tape c s s' t d p → R s → R s') :
    Triple C tape (fun s => P s ∧ R s) c (fun s => Q s ∧ R s) T D M := by
  intro s ⟨hp, hr⟩
  obtain ⟨s', t, d, p, hexec, hq, hT, hD, hM⟩ := h s hp
  exact ⟨s', t, d, p, hexec, ⟨hq, hR s s' t d p hexec hr⟩, hT, hD, hM⟩

/-- Specialization: a register the statement never writes keeps its value. -/
theorem frame_reg {P Q : State w → Prop} {c : Stmt w} {T : ℕ} {D M : ℤ} {r : Reg}
    {v : Word w} (h : Triple C tape P c Q T D M) (hw : ¬ c.Writes r) :
    Triple C tape (fun s => P s ∧ s.regs r = v) c (fun s => Q s ∧ s.regs r = v) T D M :=
  h.frame_post fun _ _ _ _ _ hexec hr => (hexec.frame_reg hw).trans hr

/-- Specialization: a buffer the statement never touches keeps its contents. -/
theorem frame_buf {P Q : State w → Prop} {c : Stmt w} {T : ℕ} {D M : ℤ} {b : BufId}
    {arr : Array (Word w)} (h : Triple C tape P c Q T D M) (ht : ¬ c.Touches b) :
    Triple C tape (fun s => P s ∧ s.bufs b = arr) c (fun s => Q s ∧ s.bufs b = arr) T D M :=
  h.frame_post fun _ _ _ _ _ hexec hb => (hexec.frame_buf ht).trans hb

end Triple

/-! ## Decoupled judgments: time-only and space-only triples

A `Triple` carries all three bounds at once, forcing every proof to do the memory
algebra even when only a running-time bound is wanted, and vice versa. `TimeTriple`
and `SpaceTriple` are the two halves. They keep the same total-correctness core, an
`Exec` derivation being exhibited, so termination and memory safety are still
proved, but bound one resource only and drop the other's arithmetic from the rules
entirely: `TimeTriple.seq` has no `max` profile algebra, `SpaceTriple.whileNZ_measure`
no trip-count time term.

The halves lose nothing. `Triple.time`/`Triple.space` project a full triple, and
because the machine is deterministic the executions exhibited by a `TimeTriple` and
a `SpaceTriple` from the same state are the *same* execution, so
`TimeTriple.and_space` recombines separately proved bounds after the fact.
Decoupling is not only convenience: a bound of one kind can exist while the other
provably does not, as with `Drain` in `Examples.lean`, a loop with a
trip-count-independent space bound but no uniform time bound. -/

/-- Time-only total-correctness triple: from any state satisfying `P`, the statement
terminates (memory-safely) in a state satisfying `Q` within `t ≤ T` time units. The
execution's memory profile is existentially forgotten. -/
def TimeTriple (C : CostModel) (tape : RandomTape w) (P : State w → Prop) (c : Stmt w) (Q : State w → Prop)
    (T : ℕ) : Prop :=
  ∀ s, P s → ∃ s' t d p, Exec C tape c s s' t d p ∧ Q s' ∧ t ≤ T

/-- Space-only total-correctness triple: net live-memory change `d ≤ D` and peak
growth `p ≤ M`. The running time is existentially forgotten; the statement still
terminates, an `Exec` derivation being exhibited, but `t` is unbounded. -/
def SpaceTriple (C : CostModel) (tape : RandomTape w) (P : State w → Prop) (c : Stmt w) (Q : State w → Prop)
    (D M : ℤ) : Prop :=
  ∀ s, P s → ∃ s' t d p, Exec C tape c s s' t d p ∧ Q s' ∧ d ≤ D ∧ p ≤ M

/-- Forget the memory bounds of a full triple. -/
theorem Triple.time {P Q : State w → Prop} {c : Stmt w} {T : ℕ} {D M : ℤ}
    (h : Triple C tape P c Q T D M) : TimeTriple C tape P c Q T := by
  intro s hs
  obtain ⟨s', t, d, p, hexec, hq, hT, _, _⟩ := h s hs
  exact ⟨s', t, d, p, hexec, hq, hT⟩

/-- Forget the time bound of a full triple. -/
theorem Triple.space {P Q : State w → Prop} {c : Stmt w} {T : ℕ} {D M : ℤ}
    (h : Triple C tape P c Q T D M) : SpaceTriple C tape P c Q D M := by
  intro s hs
  obtain ⟨s', t, d, p, hexec, hq, _, hD, hM⟩ := h s hs
  exact ⟨s', t, d, p, hexec, hq, hD, hM⟩

namespace TimeTriple

/-- Recombination: the machine is deterministic, so the executions exhibited by a
time-only and a space-only triple from the same state coincide, and separately
proved bounds hold of the one real execution. -/
theorem and_space {P Q₁ Q₂ : State w → Prop} {c : Stmt w} {T : ℕ} {D M : ℤ}
    (h₁ : TimeTriple C tape P c Q₁ T) (h₂ : SpaceTriple C tape P c Q₂ D M) :
    Triple C tape P c (fun s => Q₁ s ∧ Q₂ s) T D M := by
  intro s hs
  obtain ⟨s', t, d, p, hexec, hq₁, hT⟩ := h₁ s hs
  obtain ⟨s'', t', d', p', hexec', hq₂, hD, hM⟩ := h₂ s hs
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hexec.deterministic hexec'
  exact ⟨s', t, d, p, hexec, ⟨hq₁, hq₂⟩, hT, hD, hM⟩

/-- Recombination when the two judgments share a postcondition. -/
theorem and_space' {P Q : State w → Prop} {c : Stmt w} {T : ℕ} {D M : ℤ}
    (h₁ : TimeTriple C tape P c Q T) (h₂ : SpaceTriple C tape P c Q D M) :
    Triple C tape P c Q T D M :=
  (h₁.and_space h₂).conseq (fun _ => id) (fun _ h => h.1) (le_refl _) (le_refl _)
    (le_refl _)

/-- Code acquiring no memory (`Stmt.AllocFree`) gets a space triple for free from a time triple:
the execution the time triple already exhibits satisfies `d ≤ 0 ∧ p ≤ 0` outright
(`Exec.allocFree_space`). -/
theorem space_of_allocFree {P Q : State w → Prop} {c : Stmt w} {T : ℕ}
    (h : TimeTriple C tape P c Q T) (ha : c.AllocFree) : SpaceTriple C tape P c Q 0 0 := by
  intro s hs
  obtain ⟨s', t, d, p, hexec, hq, _⟩ := h s hs
  obtain ⟨hd, hp⟩ := hexec.allocFree_space ha
  exact ⟨s', t, d, p, hexec, hq, hd, hp⟩

theorem conseq {P P' Q Q' : State w → Prop} {c : Stmt w} {T T' : ℕ}
    (h : TimeTriple C tape P c Q T) (hP : ∀ s, P' s → P s) (hQ : ∀ s, Q s → Q' s)
    (hT : T ≤ T') : TimeTriple C tape P' c Q' T' := by
  intro s hs
  obtain ⟨s', t, d, p, hexec, hq, ht⟩ := h s (hP s hs)
  exact ⟨s', t, d, p, hexec, hQ s' hq, ht.trans hT⟩

theorem weaken {P Q : State w → Prop} {c : Stmt w} {T T' : ℕ}
    (h : TimeTriple C tape P c Q T) (hT : T ≤ T') : TimeTriple C tape P c Q T' :=
  h.conseq (fun _ => id) (fun _ => id) hT

/-- Sequencing time bounds is plain addition; none of `Triple.seq`'s (net, peak)
profile algebra appears, which is the point of the decoupled judgment. -/
protected theorem seq {P R Q : State w → Prop} {c₁ c₂ : Stmt w} {T₁ T₂ : ℕ}
    (h₁ : TimeTriple C tape P c₁ R T₁) (h₂ : TimeTriple C tape R c₂ Q T₂) :
    TimeTriple C tape P (c₁ ;; c₂) Q (T₁ + T₂) := by
  intro s hs
  obtain ⟨s₁, t₁, d₁, p₁, he₁, hr, ht₁⟩ := h₁ s hs
  obtain ⟨s₂, t₂, d₂, p₂, he₂, hq, ht₂⟩ := h₂ s₁ hr
  exact ⟨s₂, t₁ + t₂, d₁ + d₂, max p₁ (d₁ + p₂), .seq he₁ he₂, hq,
    Nat.add_le_add ht₁ ht₂⟩

protected theorem ifNZ {P Q : State w → Prop} {r : Reg} {thn els : Stmt w} {T : ℕ}
    (ht : TimeTriple C tape (fun s => P s ∧ s.regs r ≠ 0) thn Q T)
    (he : TimeTriple C tape (fun s => P s ∧ s.regs r = 0) els Q T) :
    TimeTriple C tape P (.ifNZ r thn els) Q (C.branch + T) := by
  intro s hs
  by_cases hr : s.regs r = 0
  · obtain ⟨s', t, d, p, hexec, hq, hT⟩ := he s ⟨hs, hr⟩
    exact ⟨s', C.branch + t, d, p, .ifNZ_false hr hexec, hq, Nat.add_le_add_left hT _⟩
  · obtain ⟨s', t, d, p, hexec, hq, hT⟩ := ht s ⟨hs, hr⟩
    exact ⟨s', C.branch + t, d, p, .ifNZ_true hr hexec, hq, Nat.add_le_add_left hT _⟩

/-- The time-only loop rule: the measure-indexed structure of
`Triple.whileNZ_measure`, the measure being what proves termination, with no memory
hypotheses and no memory conclusion. Time is linear in `k`. -/
theorem whileNZ_measure {I J : ℕ → State w → Prop} {g body : Stmt w} {r : Reg}
    {Tg Tb : ℕ}
    (hg : ∀ k, TimeTriple C tape (I k) g (J k) Tg)
    (hpos : ∀ k s, J k s → s.regs r ≠ 0 → ∃ k', k = k' + 1)
    (hb : ∀ k, TimeTriple C tape (fun s => J (k + 1) s ∧ s.regs r ≠ 0) body (I k) Tb) :
    ∀ k, TimeTriple C tape (I k) (.whileNZ g r body)
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
    (h : TimeTriple C tape P c Q T)
    (hR : ∀ s s' t d p, Exec C tape c s s' t d p → R s → R s') :
    TimeTriple C tape (fun s => P s ∧ R s) c (fun s => Q s ∧ R s) T := by
  intro s ⟨hp, hr⟩
  obtain ⟨s', t, d, p, hexec, hq, hT⟩ := h s hp
  exact ⟨s', t, d, p, hexec, ⟨hq, hR s s' t d p hexec hr⟩, hT⟩

/-- A register the statement never writes keeps its value. -/
theorem frame_reg {P Q : State w → Prop} {c : Stmt w} {T : ℕ} {r : Reg}
    {v : Word w} (h : TimeTriple C tape P c Q T) (hw : ¬ c.Writes r) :
    TimeTriple C tape (fun s => P s ∧ s.regs r = v) c (fun s => Q s ∧ s.regs r = v) T :=
  h.frame_post fun _ _ _ _ _ hexec hr => (hexec.frame_reg hw).trans hr

/-- A buffer the statement never touches keeps its contents. -/
theorem frame_buf {P Q : State w → Prop} {c : Stmt w} {T : ℕ} {b : BufId}
    {arr : Array (Word w)} (h : TimeTriple C tape P c Q T) (ht : ¬ c.Touches b) :
    TimeTriple C tape (fun s => P s ∧ s.bufs b = arr) c (fun s => Q s ∧ s.bufs b = arr) T :=
  h.frame_post fun _ _ _ _ _ hexec hb => (hexec.frame_buf ht).trans hb

end TimeTriple

namespace SpaceTriple

theorem conseq {P P' Q Q' : State w → Prop} {c : Stmt w} {D D' M M' : ℤ}
    (h : SpaceTriple C tape P c Q D M) (hP : ∀ s, P' s → P s) (hQ : ∀ s, Q s → Q' s)
    (hD : D ≤ D') (hM : M ≤ M') : SpaceTriple C tape P' c Q' D' M' := by
  intro s hs
  obtain ⟨s', t, d, p, hexec, hq, hd, hp⟩ := h s (hP s hs)
  exact ⟨s', t, d, p, hexec, hQ s' hq, hd.trans hD, hp.trans hM⟩

theorem weaken {P Q : State w → Prop} {c : Stmt w} {D D' M M' : ℤ}
    (h : SpaceTriple C tape P c Q D M) (hD : D ≤ D') (hM : M ≤ M') :
    SpaceTriple C tape P c Q D' M' :=
  h.conseq (fun _ => id) (fun _ => id) hD hM

/-- Sequencing composes the memory profile exactly as in `Triple.seq`, with no time
arithmetic anywhere. -/
protected theorem seq {P R Q : State w → Prop} {c₁ c₂ : Stmt w} {D₁ M₁ D₂ M₂ : ℤ}
    (h₁ : SpaceTriple C tape P c₁ R D₁ M₁) (h₂ : SpaceTriple C tape R c₂ Q D₂ M₂) :
    SpaceTriple C tape P (c₁ ;; c₂) Q (D₁ + D₂) (max M₁ (D₁ + M₂)) := by
  intro s hs
  obtain ⟨s₁, t₁, d₁, p₁, he₁, hr, hd₁, hp₁⟩ := h₁ s hs
  obtain ⟨s₂, t₂, d₂, p₂, he₂, hq, hd₂, hp₂⟩ := h₂ s₁ hr
  exact ⟨s₂, t₁ + t₂, d₁ + d₂, max p₁ (d₁ + p₂), .seq he₁ he₂, hq,
    by omega, by omega⟩

protected theorem ifNZ {P Q : State w → Prop} {r : Reg} {thn els : Stmt w} {D M : ℤ}
    (ht : SpaceTriple C tape (fun s => P s ∧ s.regs r ≠ 0) thn Q D M)
    (he : SpaceTriple C tape (fun s => P s ∧ s.regs r = 0) els Q D M) :
    SpaceTriple C tape P (.ifNZ r thn els) Q D M := by
  intro s hs
  by_cases hr : s.regs r = 0
  · obtain ⟨s', t, d, p, hexec, hq, hD, hM⟩ := he s ⟨hs, hr⟩
    exact ⟨s', C.branch + t, d, p, .ifNZ_false hr hexec, hq, hD, hM⟩
  · obtain ⟨s', t, d, p, hexec, hq, hD, hM⟩ := ht s ⟨hs, hr⟩
    exact ⟨s', C.branch + t, d, p, .ifNZ_true hr hexec, hq, hD, hM⟩

/-- The space-only loop rule: same measure-indexed structure as
`Triple.whileNZ_measure`, same memory bounds `base + k * max (Dg + Db) 0`, so a
memory-reusing iteration (`Dg + Db ≤ 0`) gives trip-count-independent bounds. No
time bound in the conclusion, hence no `Tg`/`Tb` hypotheses. -/
theorem whileNZ_measure {I J : ℕ → State w → Prop} {g body : Stmt w} {r : Reg}
    {Dg Mg Db Mb : ℤ}
    (hg : ∀ k, SpaceTriple C tape (I k) g (J k) Dg Mg)
    (hpos : ∀ k s, J k s → s.regs r ≠ 0 → ∃ k', k = k' + 1)
    (hb : ∀ k, SpaceTriple C tape (fun s => J (k + 1) s ∧ s.regs r ≠ 0) body (I k) Db Mb) :
    ∀ k, SpaceTriple C tape (I k) (.whileNZ g r body)
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
    (h : SpaceTriple C tape P c Q D M)
    (hR : ∀ s s' t d p, Exec C tape c s s' t d p → R s → R s') :
    SpaceTriple C tape (fun s => P s ∧ R s) c (fun s => Q s ∧ R s) D M := by
  intro s ⟨hp, hr⟩
  obtain ⟨s', t, d, p, hexec, hq, hD, hM⟩ := h s hp
  exact ⟨s', t, d, p, hexec, ⟨hq, hR s s' t d p hexec hr⟩, hD, hM⟩

/-- A register the statement never writes keeps its value. -/
theorem frame_reg {P Q : State w → Prop} {c : Stmt w} {D M : ℤ} {r : Reg}
    {v : Word w} (h : SpaceTriple C tape P c Q D M) (hw : ¬ c.Writes r) :
    SpaceTriple C tape (fun s => P s ∧ s.regs r = v) c (fun s => Q s ∧ s.regs r = v) D M :=
  h.frame_post fun _ _ _ _ _ hexec hr => (hexec.frame_reg hw).trans hr

/-- A buffer the statement never touches keeps its contents. -/
theorem frame_buf {P Q : State w → Prop} {c : Stmt w} {D M : ℤ} {b : BufId}
    {arr : Array (Word w)} (h : SpaceTriple C tape P c Q D M) (ht : ¬ c.Touches b) :
    SpaceTriple C tape (fun s => P s ∧ s.bufs b = arr) c (fun s => Q s ∧ s.bufs b = arr)
      D M :=
  h.frame_post fun _ _ _ _ _ hexec hb => (hexec.frame_buf ht).trans hb

end SpaceTriple

end Caliper
