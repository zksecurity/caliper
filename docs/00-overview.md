# Caliper

Caliper is a Lean DSL for proving concrete running-time and memory bounds.
Programs use fixed-width words, statically named registers, and independent buffers.
The instruction set is designed around unit-cost operations;
acquiring buffer capacity is charged per word.
It can serve as a compilation target for languages that need certified resource bounds, e.g. witness-generation IRs.

## Documentation

We start with the machine and its resource bounds, then write programs and state what those bounds mean for a real CPU.

1. [Machine Model](01-machine-model.md): words, instructions, states, and execution costs.
2. [Memory](02-memory.md): time and space specifications, buffer capacity, and register liveness.
3. [Programming](03-programming.md): builders, proofs, and the reference interpreter.
4. [Compilation](04-compilation.md): the contract between abstract costs and a 64-bit CPU.
5. [Limitations](05-limitations.md): what is proved, what is assumed, and what remains to be done.
6. [Randomness](06-randomness.md): random tapes, expected time, and sequential composition.

## Files

| File | Contents |
|---|---|
| [Core.lean](../Caliper/Core.lean) | Syntax (`Stmt`), cost models (`CostModel`, `CostModel.Admissible`), big-step cost semantics (`Exec`), determinism, framing (`Writes`/`Touches`), the unit-time theorems, the partial static clock (`staticTime?`), peak memory ≤ running time (`Exec.peak_le_time`), well-formed states and absolute live memory (`State.WellFormed`, `State.liveMem`), reference interpreter (`run`) and its soundness |
| [Render.lean](../Caliper/Render.lean) | Pretty-printer: `Stmt.render`/`Stmt.renderString` emit the `mem.`-qualified assembly dialect used for the listings in the programming chapter |
| [Tape.lean](../Caliper/Tape.lean) | Fixed-tape locality, replay completeness, random-free programs, and independence of program behavior from the cost model |
| [PMF.lean](../Caliper/PMF.lean), [Probability.lean](../Caliper/Probability.lean) | Generic PMF expectation, uniform word tapes, unconditional result probabilities, and runtime distributions |
| [TapeMeasure.lean](../Caliper/TapeMeasure.lean), [Outcome.lean](../Caliper/Outcome.lean) | Independent unread tails after variable-length subroutines and countable terminating outcomes |
| [ProbTriple.lean](../Caliper/ProbTriple.lean) | Almost-sure resource specifications, expected-time sequencing, deterministic callee reuse, branching, and countable terminating cases |
| [Geometric.lean](../Caliper/Geometric.lean), [Retry.lean](../Caliper/Retry.lean) | Unbounded retry, geometric runtime atoms, almost-sure termination, and exact expected time |
| [Triple.lean](../Caliper/Triple.lean) | Upper-bound Hoare triples (`Triple`), one rule per instruction, `seq`/`conseq`/`ifNZ`, the measure-indexed loop rule `whileNZ_measure`, frame rules; time-only and space-only judgments (`TimeTriple`/`SpaceTriple`) with the same rule set, recombinable via determinism (`TimeTriple.and_space`) |
| [Builder.lean](../Caliper/Builder.lean) | Surface syntax: builder monad with fresh register/buffer naming, expression compiler (`Exp`), structured `if_`/`while_`, typed buffer handles (`Buf`), product types (`PairR`, `PairBuf`) |
| [Examples.lean](../Caliper/Examples.lean) | Worked examples with full proofs, builder ↔ core checks, interpreter demos |
| [Liveness.lean](../Caliper/Liveness.lean) | Backward liveness analysis (`Stmt.liveBefore`), inferred peak register pressure (`Stmt.regPeak`/`Stmt.regPeak₀`), the live-ins + writes bound, the combined buffers-plus-registers judgment (`SpaceBound`), and `Exec.straight_total_footprint_le` |
| [W64.lean](../Caliper/W64.lean) | Fixed 64-bit surface: namespace `Caliper64` of reducible `abbrev`s pinning `w := 64` |

## Scope

This repository contains the machine: syntax, cost semantics, program logic, builder surface, renderer, and the fixed 64-bit surface `Caliper64`.
Layers built on top of it, such as a compiler targeting the machine or a gadget library, live in the projects that depend on this one; claims about those layers are stated and proved there, not here.
