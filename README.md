<p align="center">
  <img src="assets/logo.svg" alt="Caliper" width="300">
</p>

Caliper is a deep-embedded imperative language in Lean 4 whose every instruction
runs in constant time: a unit-cost abstract machine with machine-checked upper
bounds on running time and live memory.

Programs are `Stmt` syntax trees with a big-step cost semantics (`Exec`) that
charges each instruction a table entry from a `CostModel`. On top of that sit:

- *Certified Time and Memory.* Upper-bound Hoare triples (`Triple`, `TimeTriple`,
  `SpaceTriple`) with one rule per instruction, frame rules with decidable side
  conditions, and a measure-indexed loop rule. Total memory is two summands quoted
  as one number (`SpaceBound`): a dynamic (net, peak) profile over buffer
  capacities, plus the statically inferred peak register pressure
  (`Stmt.regPeak₀`), since register liveness is static information. Peak buffer
  memory is bounded by running time (`Exec.peak_le_time`), register pressure by
  live-ins plus static time (`Stmt.Straight.regPeak₀_le`), and on straight code the
  two fit in a single running time (`Exec.straight_total_footprint_le`).
- *A Builder Surface.* A monad with fresh register/buffer naming, compound
  expressions, structured control flow, and typed buffer handles, checked equal to
  hand-written core syntax, so the sugar adds nothing to the trusted surface.
- *A Lowering Story.* Every instruction is implementable in O(1) machine
  instructions on a 64-bit CPU (the intended target being RISC-V), so a certified
  unit cost `t` means at most `c · t` cycles. A source language compiles to Caliper
  carrying certified bounds, and Caliper's per-instruction contract carries those
  bounds to the hardware. The contract, and its limits, are in
  [doc/caliper.md](doc/caliper.md).

The fixed 64-bit surface `Caliper64` (`Caliper/W64.lean`) is what programs and
specs should be written against; the core stays generic in the word size.

Caliper was built as the compilation target for the witness-generation IR of the
[Clean](https://github.com/rot256/clean) zk-circuit project, which depends on this
library; the witgen compiler, field gadget library, and `TimedCircuit` budgets live
there.

## Documentation

See [doc/caliper.md](doc/caliper.md) for the machine, ISA, memory model, program
logic, and trust boundary.

## Building

```
lake exe cache get   # fetch Mathlib build artifacts
lake build
```
