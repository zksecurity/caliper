# Memory and Resource Bounds

[Documentation](00-overview.md)

## Time and Memory Specifications

`Triple C tape P c Q T D M` is total correctness plus `t ≤ T` (time), `d ≤ D` (net live-memory change, signed) and `p ≤ M` (peak live-memory growth).
Exhibiting the underlying `Exec` derivation also proves memory safety: out-of-range accesses have no derivation, since the `memLoad`/`memStore` rules demand an in-range proof.

The definition in [Triple.lean](../Caliper/Triple.lean) makes each obligation explicit:

```lean
def Triple (C : CostModel) (tape : RandomTape w) (P : State w → Prop) (c : Stmt w) (Q : State w → Prop)
    (T : ℕ) (D M : ℤ) : Prop :=
  ∀ s, P s → ∃ s' t d p, Exec C tape c s s' t d p ∧ Q s' ∧ t ≤ T ∧ d ≤ D ∧ p ≤ M
```

We quantify over every initial state satisfying `P`.
The witness `s'` must satisfy `Q`, and the same execution must meet all three resource bounds.
Here `w` is the surrounding word-width parameter; the definitions below are excerpts from namespace `Caliper`.

## Buffer Memory

Memory gets reused; counting allocations would charge the same scratch space on every loop iteration.
We account for the peak footprint, with two summands (`SpaceBound`, `Liveness.lean`):

    total peak memory = dynamic buffer peak + static register peak

The register file *is* memory; register words are as physical as buffer words.
What differs is the accounting, and the split follows the information: buffer contents are runtime information (lengths are dynamic, indices are data), so buffer length is metered dynamically by the cost semantics; register lifetimes are static information (registers are statically named, never dynamically indexed), so the register footprint is a compile-time constant of the code, the inferred peak live-register count `Stmt.regPeak₀`.
Nothing about the split makes registers cheaper; it makes their accounting exact without runtime instructions.
The dynamic-side principle, in one paragraph:

> Every resize costs one step per word of the *new* length, surviving words included (growing `c → 2c` charges `2c`, not `c`), and those per-word charges price each word's creation and zeroing, any copy, and its eventual destruction; there is no per-object base, since buffer names are static and lengths explicit.
> Holding words is free.
> Releasing it (a resize to 0) is free.

Dynamic live memory is the sum of buffer lengths: `memResize`/`memResizeI` change it by `newLen - oldLen` (a charge when growing, a credit when shrinking), and stores overwrite words already paid for.
Since a buffer's length is its only size, there is no reserved-but-unfilled capacity: every word the metric counts is readable, and every readable word is counted.
The memory profile of a resize is net `newLen - oldLen` and peak `newLen`: a realloc that cannot resize in place allocates the new region, copies, and only then releases the old one, so for a moment both coexist, `oldLen + newLen` words, i.e. `newLen` above the starting footprint.
Charging the whole new length as the peak makes `p` a true high-water mark for every implementation of the realloc contract, in place or copying; a fresh acquisition (`oldLen = 0`) and the free (`newLen = 0`, peak 0) are priced exactly as before.
Releasing is free in *time* as well: the free `memResizeI b 0` costs only the base `C.memResize`, 0 in both tables, since a release only ever shrinks the footprint and every released word was charged by an earlier resize whose per-word charge covers creation and destruction.
That is the only split stable across real allocators, since a buffer's teardown (freelist push, deferred coalescing, `munmap`) is bounded by size-linear work already paid when its words were acquired.
A free of a never-acquired buffer name is statically detectable and elidable by a backend.
Profiles compose like high-water marks:

    seq:  net = d₁ + d₂        peak = max p₁ (d₁ + p₂)

The corresponding proof rule keeps the intermediate postcondition `R` explicit.
This is the complete rule and proof from namespace `Caliper.Triple` in [Triple.lean](../Caliper/Triple.lean),
with surrounding parameters `w`, `C`, and `tape`:

```lean
protected theorem seq {P R Q : State w → Prop} {c₁ c₂ : Stmt w} {T₁ T₂ : ℕ}
    {D₁ M₁ D₂ M₂ : ℤ}
    (h₁ : Triple C tape P c₁ R T₁ D₁ M₁) (h₂ : Triple C tape R c₂ Q T₂ D₂ M₂) :
    Triple C tape P (c₁ ;; c₂) Q (T₁ + T₂) (D₁ + D₂) (max M₁ (D₁ + M₂)) := by
  intro s hs
  obtain ⟨s₁, t₁, d₁, p₁, he₁, hr, ht₁, hd₁, hp₁⟩ := h₁ s hs
  obtain ⟨s₂, t₂, d₂, p₂, he₂, hq, ht₂, hd₂, hp₂⟩ := h₂ s₁ hr
  exact ⟨s₂, t₁ + t₂, d₁ + d₂, max p₁ (d₁ + p₂), .seq he₁ he₂, hq,
    Nat.add_le_add ht₁ ht₂, by omega, by omega⟩
```

Hence a block with net 0 contributes its peak once, not once per occurrence.
The `ScratchLoop` example allocates a one-word scratch buffer, runs `n` iterations that each write a word into it and read it back, and frees it: proved net 0 and peak 1 word, independent of `n`, where an allocation counter would report `n`.
The register-side counterpart is static: `ScopedSumSq` (`3² + 4²`) names five registers and the analysis infers peak 2, since each stage's scratch is dead the moment its `mul` consumes it.

Inference is what keeps the register summand tight.
Explicit alloc/free brackets around register lifetimes, the obvious alternative, can only over-approximate a live range: `SumBuf` uses 6 registers and never releases one, so both accountings agree at `0 + 6 = 6` (`SumBuf.total_space`), but `ScopedSumSq`'s brackets would certify 3 (stage-1 result, stage-2 scratch and stage-2 result coexist as *names*) where inference gives `0 + 2 = 2` (`ScopedSumSq.total_space`), and the array-of-pairs demo, whose builder temporaries are never released, drops from 38 (4 buffer words + 34 register names) to `4 + 3 = 7`.

Invariants `0 ≤ p` and `d ≤ p` hold always; code acquiring no buffer words has `d ≤ 0 ∧ p ≤ 0` (`allocFree_space`, which allows the free `memResizeI b 0`, as it only shrinks the footprint); and `p ≤ t` in any model with `1 ≤ allocPerWord` (`Exec.peak_le_time`), so a time bound subsumes the buffer-peak bound.
The register side has the static analogue `Stmt.Straight.regPeak₀_le`: peak register pressure ≤ live-ins + unit-model static time.
The two bounds do not each consume a running time of their own: on straight code the instructions covering the buffer words (per-word resize charges) and those covering the register slots (register-writing leaves) are disjoint, so buffer peak + register peak ≤ live-ins + `t` for the *single* running time `t` (`Exec.straight_total_footprint_le`).

## Absolute Live Memory

The absolute footprint of buffers `0, …, B - 1` is the sum of their lengths ([Core.lean](../Caliper/Core.lean)):

```lean
def State.liveMem (s : State w) : ℕ → ℕ
  | 0 => 0
  | B + 1 => s.liveMem B + (s.bufs B).size
```

For any bound `B` covering the buffers a program names, `liveMem` changes by exactly `d` (`Exec.liveMem_eq`), and every state the execution passes through stays within `p` of the start (`Exec.reaches_liveMem_le_peak`, `Exec.liveMem_le_peak`), so `p` is a true high-water mark on physical buffer memory.

Keep the two readings apart: a code fragment's quoted peak `p` is growth over its start state, which is what makes Triple-level profiles compose as relative high-water marks, whereas the `liveMem` statements anchor the same indices to absolute live memory.
Quote the absolute form for "this program never holds more than X words" and the relative form for "this fragment adds at most X words".
Either way the user-facing total goes through `SpaceBound`: a buffer-side `SpaceTriple` plus the static `regPeak₀`, summed, so a buffers-only figure can never masquerade as "the memory".
Register *values* are framed by `Stmt.Writes`, as always.

On lowering: the inferred live ranges are exactly what a backend colors.
`Stmt.regPeak₀` bounds the number of simultaneously live registers at any program point, so interval-coloring those ranges renames the unboundedly many fresh names onto `regPeak₀` physical slots; the certified static peak *is* the frame size of a RISC-V lowering's register file.
The claim is sound for arbitrary code, including hand-written `Stmt`: liveness is computed from the reads that actually occur, so a register stays live exactly as long as some later instruction may read it.
What inference costs is precision on loops, since the `whileNZ` case widens by the loop's whole use set instead of iterating to a fixpoint.

## Loops and Independent Bounds

The loop rule `Triple.whileNZ_measure` takes an invariant indexed by a remaining-iterations budget `k`; time is linear in `k`, and both memory bounds have the form `base + k · max (Dg + Db) 0`, with `max` against 0 because the loop may exit early and fewer iterations free less.
When the per-iteration net `Dg + Db ≤ 0`, the peak is independent of the trip count.

Time and memory bounds are also independently provable: `TimeTriple` bounds only the running time and `SpaceTriple` only the (net, peak) pair, each with its own `seq`/`conseq`/`ifNZ`/loop/frame rules (instructions are projected from `Triple` by `Triple.time`/`Triple.space`), so a time proof carries no memory algebra and vice versa.
The `Drain` example has a trip-count-independent space bound even though no uniform time bound exists for it.
For a fixed tape the machine is deterministic, so separately proved judgments recombine into a full `Triple` (`TimeTriple.and_space`).

The separate judgments retain termination and memory safety:

```lean
def TimeTriple (C : CostModel) (tape : RandomTape w) (P : State w → Prop) (c : Stmt w) (Q : State w → Prop)
    (T : ℕ) : Prop :=
  ∀ s, P s → ∃ s' t d p, Exec C tape c s s' t d p ∧ Q s' ∧ t ≤ T

def SpaceTriple (C : CostModel) (tape : RandomTape w) (P : State w → Prop) (c : Stmt w) (Q : State w → Prop)
    (D M : ℤ) : Prop :=
  ∀ s, P s → ∃ s' t d p, Exec C tape c s s' t d p ∧ Q s' ∧ d ≤ D ∧ p ≤ M
```

`TimeTriple` drops the memory inequalities; `SpaceTriple` drops the time inequality.
Both still require an `Exec` derivation.

## The Static Register Metric, in Brief

`Liveness.lean` implements the register summand.
`Stmt.liveBefore c after` over-approximates the registers whose values may still be read (structural recursion, no fixpoint), and `Stmt.regPeak c after` bounds the number of registers simultaneously live at any program point; `Stmt.regPeak₀` is the whole-program peak with nothing live at exit, i.e. the frame size a lowering needs.
The main theorem `Stmt.regPeak_le_card_liveBefore_add_writesTotal` bounds the peak by live-ins plus register-writing instructions, whence `Stmt.Straight.regPeak₀_le` for straight-line code and the disjointness theorem `Exec.straight_total_footprint_le`.
`SpaceBound` packages buffer-`SpaceTriple`-plus-`regPeak₀` as the total, with instances for the example programs.

The register analysis in [Liveness.lean](../Caliper/Liveness.lean) works backwards from a set `after` of registers needed at exit:

```lean
def Stmt.liveBefore : Stmt w → Finset ℕ → Finset ℕ
  | .seq c₁ c₂, after => c₁.liveBefore (c₂.liveBefore after)
  | .ifNZ c t e, after => insert c (t.liveBefore after ∪ e.liveBefore after)
  | .whileNZ g c b, after =>
      g.liveBefore (after ∪ insert c (g.usesSet ∪ b.usesSet)) ∪ after
  | c, after => (after \ c.writesSet) ∪ c.readsSet

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

def Stmt.regPeak₀ (c : Stmt w) : ℕ := c.regPeak ∅
```

`readsSet` and `writesSet` give the registers read and written by the syntax; `usesSet` is the read set.
A sequence passes the second statement's live inputs back to the first.
A loop widens the live set using all of its reads; it does not compute a fixpoint.
For a whole program we take `after = ∅`.

The combined specification adds the inferred register peak to the buffer bound:

```lean
def SpaceBound (C : CostModel) (tape : RandomTape w) (P : State w → Prop) (c : Stmt w)
    (Q : State w → Prop) (M : ℤ) : Prop :=
  ∃ D Mbuf : ℤ, SpaceTriple C tape P c Q D Mbuf ∧ Mbuf + (c.regPeak₀ : ℤ) ≤ M
```

`Mbuf` still bounds *growth* over the initial buffer footprint.
An absolute total-memory claim must also account for the initial buffers; starting with empty buffers makes that baseline zero.
