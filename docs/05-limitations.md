# Limitations

[Documentation](00-overview.md)

## What Is Not Proved

The theorems stop at the abstract machine.
Stated plainly:

- No verified backend exists.
  There is no verified lowering from `Stmt` to a physical ISA, allocator, or runtime.
  The [Compilation Contract](04-compilation.md) is an engineering argument, made per-instruction and kept inspectable; it is not a theorem.
- Only the Caliper `Stmt` under `Exec` is priced.
  Programs a higher-level language compiles to this machine typically also have other execution engines (a reference semantics, an interpreter).
  The cost theorems price the compiled Caliper artifact only, and the ratio between engines is not a constant: a step count certified here says nothing numerical about any other engine beyond whatever output-equality the compiler's own simulation theorem provides.
- `CostModel` is a parameter, not a fact about hardware.
  Every theorem is generic in `C`.
  The shipped `.unit` and `.cycles` tables are calibration choices, and the `cycles` entries are estimates (`memLoad := 4` assumes an L1 hit, `allocPerWord := 1` a cache-line-amortised first touch); no theorem relates them to any real chip.
- Abstract states are mathematical functions.
  `State` maps registers and buffer names through functions.
  That a backend realizes these as stack slots, machine registers and per-buffer vectors is part of the same informal contract, made credible by the finitely many statically-known names, not proved.
  Each buffer name also carries O(1) descriptor state (pointer, length, and any allocator-side capacity) outside the word-count metric.
- Total semantics at the edges.
  `udiv`/`umod` by zero follow the total `BitVec` semantics: division by zero yields 0.
  A native backend must insert the corresponding checks or establish the corresponding preconditions, which is bounded O(1) work per site, but that obligation lives in the contract, not in the proofs.
- Allocator realities are outside the metric.
  Allocator metadata, alignment, fragmentation, and code size are not measured.
  The peak `p` counts buffer words, made absolute by the `WellFormed`/`liveMem` theorems, but words-to-bytes, headers and padding are the allocator's business.
  The certified peak counts live buffer words, not fragmentation: under a non-reclaiming bump arena, regions left behind by copying reallocs are not reused, so the physical footprint can reach about twice the certified peak.
  A resize's peak is its whole new length, which covers a copying realloc holding the old and the new region at once; an in-place backend is over-approximated by up to the old length for that instant.
- Generation-time staging is unpriced.
  Builder programs, and compilers targeting this machine, unroll at *generation* time, so generated code size is proportional to their static parameters.
  The cost theorems price the runtime of the generated code; the size itself is visible as the instruction count under the unit model, but the generation work is Lean evaluation and carries no bound.
- Time data-independence is not a side-channel proof.
  `straight_time_eq` proves that the abstract time counter is the same on every input.
  It does not cover memory-access addresses (`memLoad b i` costs one unit whatever the data-dependent index `i` is), memory profiles, or faults.
  Resize sizes do show up in the counter, since resizing is charged per word: the dynamic `memResize` is data-dependent and hence excluded from the straight-line fragment, while `memResizeI`'s size is syntactic.

## Trusted Base

Checking the theorems requires trusting the Lean kernel plus the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
Everything in this repository is proved without `native_decide`; the pinned example numbers are `rfl`/`#guard_msgs` evaluations.
Downstream projects may additionally rely on `Lean.ofReduceBool` for their own concrete numerals.
`#print axioms <theorem>` is the audit tool.

We can inspect the axioms of a concrete theorem directly.
For example, this runnable query checks the theorem relating peak buffer growth to running time:

```lean
import Caliper.Core

#print axioms Caliper.Exec.peak_le_time
```

## Caveats / Next Steps

- Natural next steps: a performant runner beyond the reference interpreter, and refining the cost model toward a concrete backend.
- A `Proc` record bundling `code`/`Pre`/`Post`/`time`/`space`/`spec` would package subroutines more tightly; the examples inline this pattern with plain `have`s for now.
- Registers in the examples use fixed conventions (callee-clobbered scratch); a register-window or parameterized-register discipline is mechanical to add (distinctness side conditions close by `decide`).
