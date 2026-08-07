# The low-level unit-cost DSL (`Clean/LowLevel/`)

A deep-embedded imperative language whose every instruction runs in constant time,
intended as the compilation target for the witness-generation IR
(`Clean/Circuit/WitnessIR.lean`). Programs carry machine-checked **upper bounds** on
running time and on allocated memory. Prototype status: the language, program logic and
worked examples exist; the witgen-IR → DSL compiler does not yet.

## Files

| File | Contents |
|---|---|
| `Core.lean` | Syntax (`Stmt`), cost models (`CostModel`), big-step cost semantics (`Exec`), determinism, framing (`Writes`/`Touches`), the unit-time theorems, reference interpreter (`run`) + soundness |
| `Triple.lean` | Upper-bound Hoare triples (`Triple`), one rule per instruction, `seq`/`conseq`/`ifNZ`, the measure-indexed loop rule `whileNZ_measure`, frame rules |
| `Builder.lean` | Surface syntax: builder monad with fresh register/buffer allocation, expression compiler (`Exp`), structured `if_`/`while_`, product types (`PairR`, `PairBuf`) |
| `Examples.lean` | Worked examples with full proofs (including the `ScratchLoop` memory-reuse bound), builder ↔ core checks, interpreter demos |

## Design decisions

### Buffers instead of a RAM

The machine has an unbounded supply of **named, independent buffers** rather than one
flat address space. Aliasing is impossible by construction: buffer names are part of
the *syntax* (never runtime values), so "these two data structures don't overlap" is
`b₁ ≠ b₂` on `ℕ` — decidable — instead of a separation-logic entailment. The entire
separation theory is the one-line lemma `bufs_setBuf_ne`, and the frame rules
(`Triple.frame_reg` / `Triple.frame_buf`) have *syntactic, decidable* side conditions
(`Stmt.Writes` / `Stmt.Touches`, closed by `simp`). Example 4 (`SumTwo`) composes two
subroutine calls this way; no state-separation proofs appear anywhere.

Buffer *lengths* are fully dynamic; only the set of buffer names is static, and the
builder allocates names automatically so this is invisible when writing programs.

### What "unit time" means

Costs come from a `CostModel`: a table indexed by the *instruction*, never by the
state. `Exec C c s s' t m` charges each instruction its table entry, so:

- `Exec.straight_time_eq`: a branch-free program's running time is a syntactic
  constant — the formal content of "every operation is unit time", and a constant-time
  (side-channel) statement for free.
- Bounds proved for a generic `C` instantiate to any concrete table: `CostModel.unit`
  (all 1) or `CostModel.cycles` (a rough modern-CPU latency table). This is where
  "roughly a cycle on a modern CPU" lives: the *shape* of the machine guarantees
  state-independence, the *table* calibrates it.

Consequences for the instruction set:

- No `alloc n` / `memset`: buffers are created empty and grown one `bufPush` at a
  time, so building an `n`-element structure visibly costs `n`.
- `bufPush` is unit-cost in the *amortised* sense (doubling `Vec::push`); it is the
  only amortised instruction.
- `whileNZ` guards are *statements*, not expressions — evaluating a loop condition
  costs emitted instructions, never free side-computation.
- Words are `BitVec w` (fixed at 64 for the witgen backend); all arithmetic wraps,
  mirroring the `U64Expr` sort of the witness IR.

### Upper bounds, not exact times — and memory as a (net, peak) profile

`Triple C P c Q T D M` is total correctness plus `t ≤ T` (time), `d ≤ D` (net
live-memory change, signed) and `p ≤ M` (peak live-memory growth). Exhibiting the
underlying `Exec` derivation also proves **memory safety** (out-of-range accesses have
no derivation — the `bufGet`/`bufSet` rules demand an in-range proof).

Memory is *not* an allocation counter — memory gets reused. `bufPop` and `bufNew`
give words back, and profiles compose like high-water marks:

    seq:  net = d₁ + d₂        peak = max p₁ (d₁ + p₂)

so a block with net 0 (push then pop; reset then refill) contributes its peak once,
not once per occurrence. The `ScratchLoop` example runs `n` iterations that each push
and pop a word: its proved peak bound is **1 word, independent of `n`** (an
allocation counter would report `n`). Invariants `0 ≤ p` and `d ≤ p` hold always.

The loop rule `Triple.whileNZ_measure` takes an invariant indexed by a
remaining-iterations budget `k`; time is linear in `k`, and both memory bounds have
the form `base + k · max (Dg + Db) 0` — `max` with 0 because the loop may exit early
and fewer iterations free less. When the per-iteration net `Dg + Db ≤ 0`, the peak is
independent of the trip count. Everything downstream is `ℕ`/`ℤ` arithmetic that
`omega`/`ring` close.

### Executable

`run C fuel c s` is a fuel-based reference interpreter; `run_sound` proves anything it
returns is a genuine `Exec` derivation *with the same costs*, so `#eval` numbers are
instances of the proved bounds (the examples check this with `#guard_msgs`).

### Ergonomics

Programs can be written against the raw constructors (assembly-flavoured, what proofs
are stated over) or through `Builder.lean`: a monad with `freshReg`/`freshBuf`,
compound expressions (`x + y * z` compiling through fresh temporaries), `while_`/`if_`,
and subroutines as ordinary Lean functions. Builder output is checked equal to the
hand-written core syntax in the examples, so the sugar adds nothing to the trusted
surface. Subroutine *specs* are ordinary Lean theorems about the generated code
(`SumBuf.spec`), reused at every call site — the same composition discipline as
`FormalCircuit`, one level down.

## The compilation contract — why DSL cost `n` means `c · n` CPU time

The guarantee this machine is designed around is *not* a statement about Turing
machines. It is: **every `Stmt` instruction is implementable in a constant number of
machine instructions on a 64-bit CPU**, so an `Exec` derivation of cost `t` (unit
model) corresponds to a real execution of at most `c · t` cycles, with `c` the maximum
over the per-instruction table. Since every `Exec` rule charges a syntactic constant
and the table is 13 entries, the trusted argument is a per-instruction inspection:

| Instruction | Real implementation | Cost |
|---|---|---|
| `imm`, `mov` | load-immediate / register move | 1 instr |
| `un`, `bin` | one ALU op (`udiv`/`umod` ≈ 20–40 cycles — a *constant*, tabulated in `CostModel.cycles`) | 1 instr |
| `shl`, `shr` | shift + compare/mask for the `≥ w ⇒ 0` convention (x86/ARM mask the amount) | 2–3 instr |
| `bufGet`, `bufSet` | one load/store at `base + 8·i`; the in-range proof carried by the `Exec` rule means bounds checks can be elided | 1–2 instr |
| `bufLen`, `bufPop` | load / decrement of the length field | 1 instr |
| `bufNew` | reset to empty; freeing a `u64` vector has no per-element work | O(1) |
| `bufPush` | `Vec::push` with doubling — **amortized** O(1); sound here because `Triple` bounds *total* time: `m` pushes cost O(`m`) real time | amortized O(1) |

For the **peak-memory** bound to transfer with a constant factor, the backend's
dynamic arrays must shrink: pop with a halve-at-quarter-occupancy policy (and free on
`bufNew`). That keeps push/pop amortized O(1) *and* physical footprint ≤ 4× the
logical live size — the standard dynamic-array result. A backend that never shrinks
still satisfies the *time* contract, but its real memory tracks the high-water mark
of each buffer instead of the proved peak.
| `ifNZ`, `whileNZ` guard | test + branch | 2 instr |

Supporting facts, all discharged by the machine's design rather than by proof:

- The syntax of any program mentions finitely many registers and buffer names, both
  known statically. Registers become stack slots (L1-resident) or machine registers;
  each buffer becomes its own `Vec<u64>`. No dynamic name ever needs resolving.
- Words are exactly `u64`; no bignum arithmetic can hide inside an instruction (this
  is why the DSL exists instead of measuring Lean's GMP-backed `Nat`).
- No instruction's semantics does work proportional to the state (`bufNew` creates
  *empty* buffers precisely so that no hidden `memset` exists).

Two honest qualifications. `bufPush`'s amortization means *individual* operations are
not real-time bounded — irrelevant for total-time upper bounds, relevant only if
per-step latency claims are ever wanted (then pre-size buffers with a push-loop, which
the cost model prices correctly). And `c` is uniform over the memory hierarchy — a
`bufGet` costs the same whether it hits L1 or DRAM; the *count* of memory accesses is
exact, and sensitivity to their unit price is a `CostModel` calibration question, not
a soundness one.

## Caveats / next steps
- The witgen-IR compiler (`WitgenIR → Stmt`) plus a cost theorem per IR node is the
  actual goal; this layer is the target it needs.
- A `Proc` record bundling `code`/`Pre`/`Post`/`time`/`space`/`spec` (mirroring
  `FormalCircuit`) would package subroutines more tightly; the examples inline this
  pattern with plain `have`s for now.
- Registers in the examples use fixed conventions (callee-clobbered scratch); a
  register-window or parameterized-register discipline is mechanical to add
  (distinctness side conditions close by `decide`).
