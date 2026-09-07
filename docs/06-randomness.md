# Random Word Tapes and Composition

[Documentation](00-overview.md)

`RandomTape w` is `ℕ → Word w`.
`Stmt.rand d` copies the word at `State.tapePos` into register `d`, advances that cursor once, and charges `C.rand`.
No other instruction consumes input.
The tape and cursor are external input bookkeeping; they do not contribute to register liveness or allocated-buffer memory.
Neither has a program instruction for inspection, seeking, or rewinding.
Elapsed cost is also unavailable to programs: `Exec.withCostModel` proves that changing prices preserves safe termination, the final state, and both memory costs.

## Tapes

The tape type and the deterministic zero tape are defined in [Core.lean](../Caliper/Core.lean):

```lean
abbrev RandomTape (w : ℕ) := ℕ → Word w

def RandomTape.zero {w : ℕ} : RandomTape w := fun _ => 0
```

The uniform tape measure in [Probability.lean](../Caliper/Probability.lean) samples each position independently:

```lean
noncomputable def uniformTape (w : ℕ) : Measure (RandomTape w) :=
  Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype (Word w)).toMeasure
```

These definitions are excerpts from namespace `Caliper`.
The probability definitions use `MeasureTheory` and the `ENNReal` scope.

All fixed-tape semantics and triples take `tape` explicitly.
`RandomTape.zero` selects deterministic all-zero inputs without disabling the `rand` instruction.
`Stmt.RandomFree` certifies that a program consumes no words; its executions and runtime law are independent of the supplied tape.
Replay uses the returned state, including its cursor.
Fuel is an interpreter limit, not an observable clock; `run_mono` and `run_complete` relate it to unbounded executions.

## Runtime and Result Probabilities

`uniformTape w` is the infinite product of uniform word distributions.
It is a measure, since infinite tapes are not a countable discrete sample space.
The runtime *image* is countable and is exposed as `runTimePMF : PMF ℕ∞`.
Faults and divergence both contribute to infinity, even if a fault happens after a finite instruction count.
`resultProb` counts safe terminating outcomes without conditioning on success.
Generic `PMF.expect`, `PMF.expect_map`, and `PMF.expect_bind` provide expectation and its composition laws.

The runtime law and result probability are defined as follows:

```lean
noncomputable def runTimePMF : PMF ℕ∞ :=
  letI : IsProbabilityMeasure ((uniformTape w).map (runTime C c s)) :=
    Measure.isProbabilityMeasure_map (measurable_runTime C c s).aemeasurable
  ((uniformTape w).map (runTime C c s)).toPMF

noncomputable def resultProb (Q : State w → ℕ → ℤ → ℤ → Prop) : ℝ≥0∞ :=
  uniformTape w {tape | ∃ s' t d p, Exec C tape c s s' t d p ∧ Q s' t d p}
```

The surrounding parameters are `C : CostModel`, `c : Stmt w`, and `s : State w`.
`runTime C c s` maps each tape to a safe termination cost, or $∞$ if there is no safe terminating execution.
`resultProb` measures the tapes admitting an execution whose final state and costs satisfy `Q`.
It does not divide by the probability of termination.

## Sequential Composition

`Exec.withTape` proves finite-prefix locality.
`uniformTape_after_exec` then proves that the unread tail after a safely terminating subroutine is uniform and independent of any predicate on its outcome, including its runtime and consumed-word count.
For a subroutine terminating with probability `p`, an unread-tail event of mass `q` has joint mass `p*q`; no termination assumption is hidden in a conditional probability.
This is essential when a callee follows a caller that consumes a variable-length prefix.
Replaying each component from cursor zero would reuse randomness and does not implement sequential composition.

`ProbTriple C P c Q T D M` gives almost-sure safe correctness and memory bounds, plus expected time at most `T`.
Its sequence rule gives `T₁ + T₂`, `D₁ + D₂`, and `max M₁ (D₁ + M₂)`.
Specifications quantify over initial states, allowing a callee to start at any cursor.
Its input registers may carry random values returned by the caller: the callee's specification must hold for each state satisfying the intermediate postcondition.
`ProbTriple.of_randomFree` lifts an existing fixed-tape deterministic subroutine specification into this logic.
`of_countable_cases` handles unbounded computations by proving countably many terminating cases whose unconditional masses sum to one.

The central specification in [ProbTriple.lean](../Caliper/ProbTriple.lean) is:

```lean
def ProbTriple (C : CostModel) (P : State w → Prop) (c : Stmt w) (Q : State w → Prop)
    (T : ℝ≥0∞) (D M : ℤ) : Prop :=
  ∀ s, P s →
    (∀ᵐ tape ∂uniformTape w, ∃ s' t d p,
      Exec C tape c s s' t d p ∧ Q s' ∧ d ≤ D ∧ p ≤ M) ∧
    (runTimePMF C c s).expect ENat.toENNReal ≤ T
```

`∀ᵐ tape ∂uniformTape w` means that the property holds for almost every tape.
The first conjunct requires safe termination, correctness, and memory bounds; the second bounds expected time.
The specification quantifies over every initial state satisfying `P`, including its tape cursor.

## Unbounded Retry

`retryZero r` repeatedly samples until it sees zero.
Its runtime distribution is geometric with success probability `2^(-w)`, zero mass at infinity, and exact expected cost `2^w * (C.rand + C.branch)` when per-attempt cost is positive.
The proof also covers `w = 0`; a fixed tape without any zero can still diverge.

The loop itself is one line in [Retry.lean](../Caliper/Retry.lean):

```lean
def retryZero (r : Reg) : Stmt w := .whileNZ (.rand r) r .skip
```

With one-bit words, each attempt succeeds with probability $1/2$.
We expect two attempts, each costing one sample and one branch; hence the expected unit cost is four.
The following runnable examples from [Examples/Retry.lean](../Examples/Retry.lean) check both this expectation and a fixed tape with three failures followed by a success:

```lean
import Caliper.Retry

open Caliper
open scoped ENNReal

example : (runTimePMF .unit (retryZero 0) (State.init 1)).expect ENat.toENNReal = 4 := by
  rw [retryZero_expect _ _ _ (by decide)]
  norm_num [CostModel.unit]

example : (run .unit (fun i => if i < 3 then (1 : Word 1) else 0)
    20 (retryZero 0) (State.init 1)).map
    (fun (s, t, d, p) => (s.regs 0, s.tapePos, t, d, p)) = some (0, 4, 8, 0, 0) := rfl
```

The replay returns result zero, advances the cursor to four, takes eight time units, and allocates no buffers.
Its fixed cost and the expected cost answer different questions.

The top-level `Examples` Lake library is a default build target and an explicit CI target.
It checks fixed-tape replay and proves probability and resource statements.
The RV64 differential suite continues to cover the supported deterministic lowering; randomized instructions report an explicit unsupported-backend error.
