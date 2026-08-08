# Caliper: the low-level unit-cost DSL (`Clean/Caliper/`)

**Caliper** is a deep-embedded imperative language whose every instruction runs in constant time,
intended as the compilation target for the witness-generation IR
(`Clean/Circuit/WitnessIR.lean`). Programs carry machine-checked **upper bounds** on
running time and on allocated memory. The pipeline is complete through the witgen-IR
compiler, including a verified lowering: programs written in Clean's witness IR
compile to this machine, carry certified concrete step-count bounds, and provably
compute the reference `WitgenIR.eval` output (see "The witgen pipeline" below).

## Files

| File | Contents |
|---|---|
| `Core.lean` | Syntax (`Stmt`), cost models (`CostModel`), big-step cost semantics (`Exec`), determinism, framing (`Writes`/`Touches`), the unit-time theorems, reference interpreter (`run`) + soundness |
| `Triple.lean` | Upper-bound Hoare triples (`Triple`), one rule per instruction, `seq`/`conseq`/`ifNZ`, the measure-indexed loop rule `whileNZ_measure`, frame rules; decoupled time-only/space-only judgments (`TimeTriple`/`SpaceTriple`) with the same rule set, recombinable into a full `Triple` via determinism (`TimeTriple.and_space`) |
| `Builder.lean` | Surface syntax: builder monad with fresh register/buffer allocation, expression compiler (`Exp`), structured `if_`/`while_`, typed buffer handles (`Buf`), product types (`PairR`, `PairBuf`) |
| `Field.lean` | Generic prime-field arithmetic from the modulus alone (`Fp w p`): 3-instruction add/mul via native `umod` with proved `ZMod`-correctness specs, Fermat inverse generated from the bits of `p - 2` at generation time |
| `Examples.lean` | Worked examples with full proofs (including the `ScratchLoop` memory-reuse bound), builder ↔ core checks, interpreter demos, BabyBear field demo |
| `W64.lean` | Fixed 64-bit surface: namespace `Caliper64` of reducible `abbrev`s pinning `w := 64` (`Word`, `Stmt`, `State`, `Exec`, `run`, `Triple`, `TimeTriple`, `SpaceTriple`, `Build`, `Exp`, `Buf`, `build`, `Fp p`), plus a short demo where `w` never appears |
| `WitgenCompile.lean` | **Phase 1**: the witgen-IR → `Stmt` compiler (Expression/FExpr/U64Expr/BExpr, let-steps, VExpr), generic over `FiniteField`; straight-line by design (mask-select `ite`, unrolled `mapRange`/`envRange`/`bitsOf`); decidable `compilable`/`envBound` checks and the **checked entry point `compile`**; differential and trust-boundary regression tests against `WitgenIR.eval` at BabyBear |
| `WitgenCost.lean` | **Phase 2**: straightness/alloc-freeness of all compiled code; `compile_time_eq` (every execution takes *exactly* `staticTime` — data-independent, `compile_time_data_independent`), `compile_space_le` (memory ≤ output length), and concrete certified bounds: `isZero_witgen_lt_2_40` |
| `WitgenSim.lean` + `WitgenSimExpr.lean` + `WitgenSimIR.lean` | **Phase 3**: verified lowering, end to end — encodings (`encF`/`encU`/`encB`), state relations, Fermat-ladder correctness, the scalar-expression simulation theorems, and the program-level simulation `compile_sim`: every witness program accepted by `compile` has an execution ending with the output buffer holding exactly the encoded `WitgenIR.eval` output (which doubles as memory safety); combined with phase 2 in `isZero_witgen_correct_140` |

## The witgen pipeline: `witgen in < 2^N steps`, machine-checked

The end-to-end story the five `Witgen*` files deliver: a witness-generation program in
Clean's IR compiles to straight-line machine code that provably **computes the right
answer** and whose running time is a *syntactic constant* — the same number on every
input (also a constant-time/side-channel statement), computable by `#eval` and
certified by evaluation.

**The entry point** is `compile` (`WitgenCompile.lean`):

    compile (N : ℕ) (ir : WitgenIR F m) : Option (Stmt 64)

with `N` the environment size. It returns `some code` only when every
generation-time check passes — `ir` is a structured `.ir` program (no `native`
closure), `WitgenIR.compilable ir` (no `listGet`/`dataGet`/`hintGet`, well-sorted
`localVar`s), `WitgenIR.envBound N ir` (every environment read below `N`), and
`N ≤ 2^64`, `m < 2^64` (indices and the output length survive their 64-bit
immediates) — and it computes the local-register count from the program itself
(`L := steps.length`), so no caller-supplied `L` can corrupt the register layout.
The raw compiler `compileIR` is internal and unchecked; it exists as the object the
proofs do induction over. All user-facing theorems are stated about `compile`.

What cannot be decided at generation time for a generic `FiniteField` — `p` prime,
`2 < p`, `p * p ≤ 2^64` (single-word moduli) — is not checked but carried as
hypotheses of the correctness theorems: `compile`'s output is verified exactly under
the field side conditions those theorems state.

The simulation is end to end: `compile_sim` (`WitgenSimIR.lean`) proves that for
every witness program the checked entry accepts, from any start state whose
buffer `0` encodes the environment, the compiled code has an execution ending with
the output buffer holding exactly the encoded reference output `WitgenIR.eval`
(elementwise canonical words) — `compile ... = some code` already carries the
compilability, environment-bound and size facts, so no separate side conditions
remain beyond the field hypotheses and the environment encoding. Because
out-of-range buffer accesses have no `Exec` derivation, that existence theorem is
simultaneously a memory-safety proof; by determinism, its costs and output are
those of *every* execution.

Concretely, for the BabyBear `IsZeroField` witness, correctness and the phase-2 cost
bounds combine into the headline corollary

    theorem isZero_witgen_correct_140
        (henv : EnvEnc env N envArr) (hN0 : 0 < N) (hN : N ≤ 2 ^ 64)
        (hbuf : s.bufs 0 = envArr) :
        ∃ s' d pp, Exec .unit isZeroCompiled s s' 140 d pp ∧
          s'.bufs 1 = (Vector.map encF (testIsZero.eval env)).toArray ∧
          pp ≤ 1

— an execution computing the **correct encoded witness output** in **exactly 140
unit-cost steps** (2090 under the calibrated cycles table; both far below `2^40`,
see `isZero_witgen_correct_lt_2_40`) with **peak memory 1 word**.

Costs scale linearly in circuit size (each IR node compiles to O(1) instructions,
`mapRange n` to n copies of its body, field inverse to ~2·log p multiply-reduce
steps), so full-circuit witgen bounds are sums of per-gadget constants — evaluated,
not estimated. Exclusions: `.native` closures (not compilable, by construction),
`dataGet`/`hintGet` prover-data reads and `listGet` (deferred; they are additional
buffers/select-chains, no new machinery).

## Design decisions

### Buffers instead of a RAM

The machine has an unbounded supply of **named, independent buffers** rather than one
flat address space. Aliasing is impossible by construction: buffer names are part of
the *syntax* (never runtime values), so "these two data structures don't overlap" is
`b₁ ≠ b₂` on `ℕ` — decidable — instead of a separation-logic entailment. The entire
separation theory is the one-line lemma `bufs_setBuf_ne`, and the frame rules
(`Triple.frame_reg` / `Triple.frame_buf`) have *syntactic, decidable* side conditions
(`Stmt.Writes` / `Stmt.Touches`, closed by `simp`). Example 5 (`SumTwo`) composes two
subroutine calls this way; no state-separation proofs appear anywhere.

Buffer *lengths* are fully dynamic; only the set of buffer names is static, and the
builder allocates names automatically so this is invisible when writing programs.

### What "unit time" means

Costs come from a `CostModel`: a table indexed by the *instruction*, never by the
state. `Exec C c s s' t d p` charges each instruction its table entry, so:

- `Exec.straight_time_eq`: a branch-free program's running time is a syntactic
  constant — the formal content of "every operation is unit time", and a constant-time
  (side-channel) statement for free.
- Bounds proved for a generic `C` instantiate to any concrete table: `CostModel.unit`
  (all 1) or `CostModel.cycles` (a rough modern-CPU latency table). This is where
  "roughly a cycle on a modern CPU" lives: the *shape* of the machine guarantees
  state-independence, the *table* calibrates it.

Consequences for the instruction set:

- Memory is *reserved*, not initialised: `bufAlloc b n` reserves capacity for `n`
  words in O(1) — a `malloc` without `memset`. Reads are only allowed below the
  filled length, so uninitialised capacity is unobservable; initialisation is paid
  for by the pushes/stores that perform it.
- `bufPush` requires free capacity (a proof obligation, like the in-range obligation
  of `bufGet`) and is therefore **worst-case** unit time — no doubling, no
  amortisation anywhere in the machine. A growable vector is a *library* on top,
  its realloc-copy loop costing what it visibly costs, its amortised spec proved in
  the program logic rather than trusted in the machine.
- `whileNZ` guards are *statements*, not expressions — evaluating a loop condition
  costs emitted instructions, never free side-computation.
- Words are `BitVec w` (fixed at 64 for the witgen backend); all arithmetic wraps,
  mirroring the `U64Expr` sort of the witness IR.

### Upper bounds, not exact times — and memory as a (net, peak) profile

`Triple C P c Q T D M` is total correctness plus `t ≤ T` (time), `d ≤ D` (net
live-memory change, signed) and `p ≤ M` (peak live-memory growth). Exhibiting the
underlying `Exec` derivation also proves **memory safety** (out-of-range accesses have
no derivation — the `bufGet`/`bufSet` rules demand an in-range proof).

Memory is *not* an allocation counter — memory gets reused. Live memory is the sum
of reserved capacities: only `bufAlloc` charges (`newCap - oldCap`), only `bufFree`
credits, and push/pop move the fill level inside capacity already paid for. Profiles
compose like high-water marks:

    seq:  net = d₁ + d₂        peak = max p₁ (d₁ + p₂)

so a block with net 0 (an alloc…free pair, or work inside fixed capacity)
contributes its peak once, not once per occurrence. The `ScratchLoop` example
allocates a one-slot scratch buffer, runs `n` iterations that each push and pop a
word inside it, and frees it: proved net 0 and peak **1 word, independent of `n`**
(an allocation counter would report `n`). Invariants `0 ≤ p` and `d ≤ p` hold
always, and code containing no `bufAlloc` has `d ≤ 0 ∧ p ≤ 0` (`allocFree_space`).

These indices are anchored to *absolute* live memory, not just to an arbitrary
baseline. `State.WellFormed` (every buffer's fill within its reserved capacity,
finitely many buffers reserved) holds for `State.init` and is preserved by every
execution (`Exec.wellFormed_preserved`), which rules out adversarial states with
phantom capacity — a fabricated `caps b` that a `bufFree` could turn into credit
funding a huge allocation at certified peak 0 — or with stored data the metric never
charged. Over such states the absolute footprint `State.liveMem` changes by *exactly*
`d` (`Exec.liveMem_eq`), a free credits only genuinely live capacity
(`Exec.bufFree_credit_le`), and every state the execution passes through stays within
`p` of the start (`Exec.reaches_liveMem_le_peak`, `Exec.liveMem_le_peak`) — so `p` is
a true high-water mark on physical memory, not merely relative growth.

The loop rule `Triple.whileNZ_measure` takes an invariant indexed by a
remaining-iterations budget `k`; time is linear in `k`, and both memory bounds have
the form `base + k · max (Dg + Db) 0` — `max` with 0 because the loop may exit early
and fewer iterations free less. When the per-iteration net `Dg + Db ≤ 0`, the peak is
independent of the trip count. Everything downstream is `ℕ`/`ℤ` arithmetic that
`omega`/`ring` close.

Time and memory bounds are also *independently* provable: `TimeTriple` bounds only
the running time and `SpaceTriple` only the (net, peak) pair, each with the full rule
set (including a measure-indexed loop rule), so a time proof carries no memory
algebra and vice versa — the `Drain` example has a trip-count-independent space bound
even though no uniform time bound exists for it. Since the machine is deterministic,
separately proved judgments recombine into a full `Triple` (`TimeTriple.and_space`).

### Executable

`run C fuel c s` is a fuel-based reference interpreter; `run_sound` proves anything it
returns is a genuine `Exec` derivation *with the same costs*, so `#eval` numbers are
instances of the proved bounds (the examples check this with `#guard_msgs`).

### Ergonomics

Programs can be written against the raw constructors (assembly-flavoured, what proofs
are stated over) or through `Builder.lean`: a monad with `freshReg`/`freshBuf`,
compound expressions (`x + y * z` compiling through fresh temporaries), `while_`/`if_`,
and subroutines as ordinary Lean functions. At the surface, buffers are the newtype
`Buf w`, produced only by `Build.alloc` — in the core both `Reg` and `BufId` are
`ℕ` (numeral-friendly proof goals), so the wrapper is what stops a buffer handle
being confused with a register or an index. Builder output is checked equal to the
hand-written core syntax in the examples, so the sugar adds nothing to the trusted
surface. Subroutine *specs* are ordinary Lean theorems about the generated code
(`SumBuf.spec`), reused at every call site — the same composition discipline as
`FormalCircuit`, one level down.

### Fixed 64-bit surface (`Caliper64`)

The core stays generic in the word size `w`, but for practical use `w = 64` — the
word size of the witgen backend. `W64.lean` provides the namespace `Caliper64`: thin
reducible `abbrev`s fixing `w := 64` for the types and entry points a program or
spec author touches (`Word`, `Stmt`, `State`, `State.init`, `Exec`, `run`, `Triple`,
`TimeTriple`, `SpaceTriple`, `Build`, `Exp`, `Buf`, `build`, `Fp p`). Import
`Clean.Caliper.W64` and write against `Caliper64`; because the abbreviations are
reducible, every generic theorem and proof rule applies definitionally — nothing is
redefined or restated. Names that infer `w` from their arguments (the `Build`
combinators, the `Triple` rules, `CostModel`, `Reg`, `BufId`, …) are used from
`Caliper` unchanged. The generic `w` remains in the core; the witgen pipeline
already fixes 64.

## The compilation contract — why DSL cost `n` means `c · n` CPU time

The guarantee this machine is designed around is *not* a statement about Turing
machines. It is: **every `Stmt` instruction is implementable in a constant number of
machine instructions on a 64-bit CPU**, so an `Exec` derivation of cost `t` (unit
model) corresponds to a real execution of at most `c · t` cycles, with `c` the maximum
over the per-instruction table. Since every `Exec` rule charges a syntactic constant
and the table has a dozen entries, the trusted argument is a per-instruction inspection:

| Instruction | Real implementation | Cost |
|---|---|---|
| `imm`, `mov` | load-immediate / register move | 1 instr |
| `un`, `bin` | one ALU op (`udiv`/`umod` ≈ 20–40 cycles — a *constant*, tabulated in `CostModel.cycles`) | 1 instr |
| `bin .mulhi` | high word of the widening multiply: `MULHU` (RISC-V M — required by the RVA application profiles), `UMULH` (AArch64), the `RDX` half of `MUL` (x86-64). With `.mul`, the full `2w`-bit product in 2 instructions (the RISC-V-blessed fused idiom) — the primitive field reduction needs | 1 instr |
| `shl`, `shr` | shift + compare/mask for the `≥ w ⇒ 0` convention (x86/ARM mask the amount) | 2–3 instr |
| `bufGet`, `bufSet` | one load/store at `base + 8·i`; the in-range proof carried by the `Exec` rule means bounds checks can be elided | 1–2 instr |
| `bufLen`, `bufPop` | load / decrement of the length field | 1 instr |
| `bufAlloc` | `malloc(8n)` — reserve, don't initialise. O(1): no `memset`, and lazy page mapping attributes first-touch cost to the writes we already charge | O(1) |
| `bufFree` | `free` — no per-element work for a `u64` buffer | O(1) |
| `bufPush` | length-check-free store at `base + 8·len` + length increment (capacity proved sufficient) — **worst-case** O(1), no doubling | 1–2 instr |
| `ifNZ`, `whileNZ` guard | test + branch | 2 instr |

The peak-memory bound transfers directly: physical footprint = sum of reserved
capacities = exactly what the model charges, up to allocator metadata and
fragmentation (a small constant for the few, long-lived, word-aligned buffers this
machine uses). No shrinking policy or amortization argument is needed — capacity
changes only at `bufAlloc`/`bufFree`.

Supporting facts, all discharged by the machine's design rather than by proof:

- The syntax of any program mentions finitely many registers and buffer names, both
  known statically. Registers become stack slots (L1-resident) or machine registers;
  each buffer becomes its own `Vec<u64>`. No dynamic name ever needs resolving.
- Words are exactly `u64`; no bignum arithmetic can hide inside an instruction (this
  is why the DSL exists instead of measuring Lean's GMP-backed `Nat`).
- No instruction's semantics does work proportional to the state (`bufAlloc`
  reserves without initialising precisely so that no hidden `memset` exists;
  freeing a `u64` buffer has no per-element work).

One honest qualification remains: `c` is uniform over the memory hierarchy — a
`bufGet` costs the same whether it hits L1 or DRAM; the *count* of memory accesses is
exact, and sensitivity to their unit price is a `CostModel` calibration question, not
a soundness one. (The former second qualification — amortized `bufPush` latency — is
gone: with explicit capacity, every instruction is worst-case constant time.)

## Caveats / next steps
- The witgen-IR compiler (`WitgenIR → Stmt`) plus a cost theorem per IR node is the
  actual goal; this layer is the target it needs.
- A `Proc` record bundling `code`/`Pre`/`Post`/`time`/`space`/`spec` (mirroring
  `FormalCircuit`) would package subroutines more tightly; the examples inline this
  pattern with plain `have`s for now.
- Registers in the examples use fixed conventions (callee-clobbered scratch); a
  register-window or parameterized-register discipline is mechanical to add
  (distinctness side conditions close by `decide`).
