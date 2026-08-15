# Caliper

**Caliper** is a deep-embedded imperative language in Lean 4 whose every
instruction runs in constant time — a unit-cost abstract machine with
**machine-checked upper bounds on running time and live memory**.

Programs are `Stmt` syntax trees with a big-step cost semantics (`Exec`) that
charges each instruction a table entry from a `CostModel`. On top of that sit:

- **Certified time and memory.** Upper-bound Hoare triples (`Triple`,
  `TimeTriple`, `SpaceTriple`) with one rule per instruction, frame rules with
  decidable side conditions, and a measure-indexed loop rule. Total memory is
  two summands quoted as one canonical number (`SpaceBound`): a dynamic
  (net, peak) profile over buffer capacities, plus the statically inferred
  peak register pressure (`Stmt.regPeak₀` — register liveness is static
  information, so the register file is counted by analysis, not by runtime
  instructions). Peak buffer memory is bounded by running time
  (`Exec.peak_le_time`), register pressure by live-ins plus static time
  (`Stmt.Straight.regPeak₀_le`), and on straight code the two fit in a single
  running time (`Exec.straight_total_footprint_le`).
- **A builder surface.** A monad with fresh register/buffer naming, compound
  expressions, structured control flow, and typed buffer handles — checked
  equal to hand-written core syntax, so the sugar adds nothing to the trusted
  surface.
- **A lowering story.** Every instruction is implementable in O(1) machine
  instructions on a 64-bit CPU (the intended concrete target being RISC-V), so
  a certified unit cost `t` means at most `c · t` cycles. The lowering happens
  in two steps: a source language compiles to Caliper carrying certified
  bounds, and Caliper's per-instruction contract carries those bounds to the
  hardware. The contract is spelled out — and its limits stated plainly — in
  [doc/caliper.md](doc/caliper.md).

The fixed 64-bit surface `Caliper64` (`Caliper/W64.lean`) is what programs and
specs should be written against; the core stays generic in the word size.

Caliper was built as the compilation target for the witness-generation IR of
the [Clean](https://github.com/rot256/clean) zk-circuit project, which depends
on this library; the witgen compiler, field gadget library, and `TimedCircuit`
budgets live there.

## Documentation

See [doc/caliper.md](doc/caliper.md) for the machine, ISA, memory model,
program logic, and trust boundary.

## Building

```
lake exe cache get   # fetch Mathlib build artifacts
lake build
```

## Test corpus

`Caliper/Corpus/` is a set of complete example programs — memcpy, memset,
buffer reverse, a stack-drain sum, dot product, Euclid's gcd, binary
exponentiation, popcount, div/mod recomposition, branch-free bit tricks,
insertion sort, and a builder-written 3×3 matrix multiply — that together
exercise **every instruction class** of the machine. Each program is pinned
against the reference interpreter (`#guard_msgs` on concrete inputs) and the
static register-liveness analysis (`Stmt.regPeak₀`); straight-line programs
also pin their exact `staticTime?`. Three carry proved bounds as worked
library examples: `Memcpy` (a `Triple` through the dynamic-allocation rule:
linear time, memory = payload), `DotProduct` (linear time, zero memory), and
`Gcd` (functional `Nat.gcd` spec with a *value*-measure loop and a
linear-in-`b` time bound, the space side recovered for free from
alloc-freeness).

## Differential RV64 tests

The `CaliperTest` lake target (deliberately **not** imported by `Caliper` —
user builds never touch it, and nothing in it is proved) contains an RV64IM
encoder and an unverified lowering `Stmt 64 → Array UInt32`: registers map
directly (`rN ↦ x(5+N)`), buffers live in a fixed arena with a length slot
before each data region, and Caliper's semantic edges (`udiv` by zero,
shifts ≥ 64, no-op `memPop`) are bridged by explicit fixup sequences. An
exporter runs the **reference interpreter** over the corpus and emits JSON
vectors with the expected registers/buffers; a Python harness executes the
lowered code on the [Unicorn](https://www.unicorn-engine.org/) emulator and
checks that reality agrees, counting executed instructions.

Run it locally (uv-managed only — no pip):

```
lake build CaliperTest
lake env lean --run CaliperTest/Export.lean   # writes tests/vectors/*.json
cd tests && uv sync && uv run python run_unicorn.py
```

CI runs the same steps on every push. The measured lowering constant
`c` = RV64 instructions / Caliper unit steps, per program (local run,
Unicorn 2.1.4):

| program | caliper | rv64 | c |
| --- | ---: | ---: | ---: |
| binexp | 34 | 57 | 1.68 |
| bittricks_ispow2 | 6 | 6 | 1.00 |
| bittricks_min | 5 | 6 | 1.20 |
| bittricks_min_rev | 5 | 6 | 1.20 |
| bittricks_pack | 6 | 15 | 2.50 |
| divmod | 6 | 11 | 1.83 |
| divmod_zero | 6 | 11 | 1.83 |
| dot_product | 29 | 58 | 2.00 |
| gcd | 17 | 20 | 1.18 |
| insertion_sort | 167 | 363 | 2.17 |
| insertion_sort_rev | 224 | 501 | 2.24 |
| iota | 33 | 71 | 2.15 |
| matmul3 | 544 | 856 | 1.57 |
| memcpy | 25 | 63 | 2.52 |
| memset | 24 | 46 | 1.92 |
| popcount | 195 | 355 | 1.82 |
| reverse | 28 | 64 | 2.29 |
| scoped_sumsq | 5 | 5 | 1.00 |
| scratch_loop | 604 | 1909 | 3.16 |
| stack_sum | 28 | 69 | 2.46 |
| sum_buf | 23 | 40 | 1.74 |

Every Caliper instruction lowers to O(1) RV64 instructions, and the worst
observed program-level constant is ~3.2 (`scratch_loop`, whose loop body is
dominated by `memPush`/`memPop` — each a length-slot read-modify-write in
this naive lowering).

## Provenance

Extracted from [rot256/clean](https://github.com/rot256/clean) with full git
history (the `Clean/LowLevel/` → `Clean/Caliper/` lineage of these files).
