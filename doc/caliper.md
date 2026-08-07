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
| `Builder.lean` | Surface syntax: builder monad with fresh register/buffer allocation, expression compiler (`Exp`), structured `if_`/`while_` |
| `Examples.lean` | Worked examples with full proofs, builder ↔ core `rfl`/`#eval` checks, interpreter demos |

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

### Upper bounds, not exact times

`Triple C P c Q T M` is total correctness plus `t ≤ T` and `m ≤ M`. Exhibiting the
underlying `Exec` derivation also proves **memory safety** (out-of-range accesses have
no derivation — the `bufGet`/`bufSet` rules demand an in-range proof). The allocation
count `m` only ever grows, so it bounds peak memory with no high-water-mark
bookkeeping.

The loop rule `Triple.whileNZ_measure` takes an invariant indexed by a
remaining-iterations budget `k` and yields bounds linear in `k`:
`(k+1)·(guard + branch) + k·body`. Everything downstream is `ℕ` arithmetic that
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

## Caveats / next steps

- **Relative yardstick.** Bounds are relative to the `CostModel`; there is no
  reasonableness theorem tying the machine to TMs/RAM. Fine for upper-bound and
  order-of-growth claims about witgen; not for absolute complexity-class claims.
- Shift semantics: shift amounts `≥ w` yield 0 (`BitVec` convention); a backend
  targeting x86/ARM masked shifts must emit an explicit mask.
- The witgen-IR compiler (`WitgenIR → Stmt`) plus a cost theorem per IR node is the
  actual goal; this layer is the target it needs.
- A `Proc` record bundling `code`/`Pre`/`Post`/`time`/`space`/`spec` (mirroring
  `FormalCircuit`) would package subroutines more tightly; the examples inline this
  pattern with plain `have`s for now.
- Registers in the examples use fixed conventions (callee-clobbered scratch); a
  register-window or parameterized-register discipline is mechanical to add
  (distinctness side conditions close by `decide`).
