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
| `Core.lean` | Syntax (`Stmt`), cost models (`CostModel`, including the per-word allocation charge `allocPerWord`), big-step cost semantics (`Exec`), determinism, framing (`Writes`/`Touches`), the unit-time theorems and the partial static clock (`staticTime?`), **peak memory ≤ running time** (`Exec.peak_le_time`), well-formed states and absolute live memory (`State.WellFormed`, `State.liveMem`), reference interpreter (`run`) + soundness |
| `Render.lean` | Canonical pretty-printer: `Stmt.render`/`Stmt.renderString` emit the `mem.`-qualified assembly dialect (`mem.load r4, b0[r1]`, `loop { … bifz r<c> … }`), one instruction per line — the notation used for the instruction listing in this document |
| `Triple.lean` | Upper-bound Hoare triples (`Triple`), one rule per instruction, `seq`/`conseq`/`ifNZ`, the measure-indexed loop rule `whileNZ_measure`, frame rules; decoupled time-only/space-only judgments (`TimeTriple`/`SpaceTriple`) with the same rule set, recombinable into a full `Triple` via determinism (`TimeTriple.and_space`) |
| `Builder.lean` | Surface syntax: builder monad with fresh register/buffer allocation, expression compiler (`Exp`), structured `if_`/`while_`, typed buffer handles (`Buf`), product types (`PairR`, `PairBuf`) |
| `Field.lean` | Generic prime-field arithmetic from the modulus alone (`Fp w p`): 3-instruction add/mul via native `umod` with proved `ZMod`-correctness specs, Fermat inverse generated from the bits of `p - 2` at generation time |
| `Examples.lean` | Worked examples with full proofs (including the `ScratchLoop` memory-reuse bound), builder ↔ core checks, interpreter demos, BabyBear field demo |
| `W64.lean` | Fixed 64-bit surface: namespace `Caliper64` of reducible `abbrev`s pinning `w := 64` (`Word`, `Stmt`, `State`, `Exec`, `run`, `Triple`, `TimeTriple`, `SpaceTriple`, `Build`, `Exp`, `Buf`, `build`, `Fp p`), plus a short demo where `w` never appears |
| `WitgenCompile.lean` | **Phase 1**: the witgen-IR → `Stmt` compiler (Expression/FExpr/U64Expr/BExpr, let-steps, VExpr), generic over `FiniteField`; straight-line by design (mask-select `ite`, unrolled `mapRange`/`envRange`/`bitsOf`); decidable `compilable`/`envBound` checks and the **checked entry point `compile`**; differential and trust-boundary regression tests against `WitgenIR.eval` at BabyBear; the headline program `testIsZero` is proved to be the witness IR extracted from the Clean circuit `Gadgets.IsZeroField.circuit` (`isZeroCircuitIR_eq_testIsZero`); certified native witnesses compile as their IR reimplementation (`compile_certified_eq_ir`), demonstrated on `isZeroCertified` = the closure `isZeroNative` + `testIsZero`'s IR + equivalence proof |
| `WitgenCost.lean` | **Phase 2**: straightness/alloc-freeness of all compiled code; `compile_time_eq` (every execution takes *exactly* `staticTime` — data-independent, `compile_time_data_independent`), the Option-valued static clock `witgenTime` (defined through `staticTime?`, so it cannot quote a number for loopy code), `compile_space_le` (memory ≤ output length), and concrete certified bounds: `isZero_witgen_lt_2_40`, plus the certified-native pins `compile_isZeroCertified` / `isZeroCertified_witgen_lt_2_40` (the same 140 steps, now for a witness whose prover-side evaluation is a native closure) |
| `WitgenSim.lean` + `WitgenSimExpr.lean` + `WitgenSimIR.lean` | **Phase 3**: verified lowering, end to end — encodings (`encF`/`encU`/`encB`), state relations, Fermat-ladder correctness, the scalar-expression simulation theorems, and the program-level simulation `compile_sim`: every witness program accepted by `compile` has an execution ending with the output buffer holding exactly the encoded IR reference output `WitgenIR.irEval` (= `eval` on `.ir` programs; doubles as memory safety); on certified programs the equivalence transports this to the native closure itself (`compile_sim_certified`); combined with phase 2 in `isZero_witgen_correct_140` and `isZeroCertified_witgen_correct_140` |
| `WitgenComputable.lean` | **The checks → circuit-layer bridge**: `compilable` + `envBound N` imply `ProverEnvironment.OnlyAccessedBelow N` (`WitgenIR.onlyAccessedBelow_of_checks`; `onlyAccessedBelow_of_ir_equiv` / `onlyAccessedBelow_certified` for native closures with a certified IR equivalent — covering `WitgenIR.certified` witnesses, whose `eval` is the closure), lifted per-offset to whole circuits (`circuit_computableWitnesses_of_checks`) so that `Circuit.ComputableWitnesses` obligations discharge by one boolean evaluation — demonstrated on the instantiated `IsZeroField` and `Addition8FullCarry` circuits and on the bare closure `isZeroNative` by `native_decide` |
| `TimedCircuit.lean` | **`TimedCircuit`: budgeted witgen as a type** — per-operation certified cost (`FlatOperation.witgenCost`), the offset-threaded whole-circuit fold (`FlatOperation.witgenTime`), its per-generator meaning theorem (`WitnessCosts`, `witgenTime_sound`, `WitnessCosts.forAll_exec`), and the `TimedCircuit` structure whose `witgen_bounded` obligation is one `native_decide`; demonstrated on `IsZeroField` (`isZeroTimed`, pinned total 159) |

## The witgen pipeline: `witgen in < 2^N steps`, machine-checked

The end-to-end story the five `Witgen*` files deliver: a witness-generation program in
Clean's IR compiles to straight-line machine code that provably **computes the right
answer** and whose running time is a *syntactic constant* — the same number on every
input, computable by `#eval` and certified by evaluation. (That data-independence is
a statement about the abstract time counter; what it does and does not say about
side channels is spelled out in "What is NOT proved" below.)

**The entry point** is `compile` (`WitgenCompile.lean`):

    compile (N : ℕ) (ir : WitgenIR F m) : Option (Stmt 64)

with `N` the environment size. It returns `some code` only when every
generation-time check passes — `ir` carries structured IR (a `.ir` program, or a
`.certified` program compiled as its IR reimplementation; bare `native` closures →
`none`), `WitgenIR.compilable ir` (no `listGet`/`dataGet`/`hintGet`, well-sorted
`localVar`s), `WitgenIR.envBound N ir` (every environment read below `N`), and
`N ≤ 2^64`, `m < 2^64` (environment indices and per-output-element immediates
survive their 64-bit encodings; the output buffer's capacity itself is a
`memAllocI` immediate — a bare `ℕ`, so the capacity *accounting* never wraps,
while `memLen` exactness on the output buffer needs the same `m < 2^64`) — and it
computes the
local-register count from the program itself
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

The witness program is not a hand-written fixture: Clean circuits embed their
witness generators structurally (each `witness` is a `FlatOperation.witness m ir`
carrying its `WitgenIR` payload), and `testIsZero` is the payload extracted from
the bundled circuit `Gadgets.IsZeroField.circuit` itself. `isZeroCircuitIR`
(`WitgenCompile.lean`) is that extraction — via `FlatOperation.witnessOperations`
on the circuit's flat operations at input `var ⟨0⟩` — and
`isZeroCircuitIR_eq_testIsZero` proves the two are definitionally equal (`rfl`), so
the headline is a theorem about the circuit's own witness program; the
circuit-anchored statement is `isZero_witgen_correct_140_circuit`
(`WitgenSimIR.lean`). The circuit's only other witness generator is the trivial
`<==` copy for its output `b`; `isZeroCircuit_witnessIRs` certifies these two are
*all* of its witness operations (the equality-assertion subcircuits carry none).
That copy generator is priced too (`isZeroCopyCompiled`, exactly 19 unit steps /
169 cycles), and `isZeroCircuit_total_witgen_time_unit` (`WitgenCost.lean`) sums the
two into `140 + 19 = 159` unit steps with the `< 2^40` corollary
`isZeroCircuit_total_witgen_lt_2_40` — so the headline now covers the circuit's
complete witness list.

Costs scale linearly in circuit size (each IR node compiles to O(1) instructions,
`mapRange n` to n copies of its body, field inverse to ~2·log p multiply-reduce
steps), so full-circuit witgen bounds are sums of per-gadget constants — evaluated,
not estimated. Exclusions: `.native` closures (not compilable, by construction —
but see "Certified native witnesses" below for the sanctioned way to keep a native
closure *and* get certified compilation), `dataGet`/`hintGet` prover-data reads and
`listGet` (deferred; they are additional buffers/select-chains, no new machinery).

### Certified native witnesses

`compile` rejects `WitgenIR.native` closures for a fundamental reason, not an
implementation gap: a cost bound is a claim about *how* a value is computed, but a
Lean function is only its input-output graph — functions are extensional, cost is
intensional. A "running time of this closure" is not even expressible, let alone
provable.

The sanctioned path for witnesses that want native Lean evaluation is a
**reimplementation in the IR plus a proof of equivalence**:
`WitgenIR.certified f steps out h` (smart constructor `WitgenIR.certify`;
provable-value form `WitgenIR.certifiedValue`, mirroring `nativeValue`) bundles

* the native closure `f` — kept as the evaluation fast path:
  `eval (certified f ..) = f` holds definitionally, so the Lean prover still runs
  the closure, never the IR interpreter;
* an IR reimplementation (`steps`, `out`, carried directly, so no nested-`WitgenIR`
  junk terms exist); and
* the equivalence proof `h : ∀ env, f env = (WitgenIR.ir steps out).eval env` — a
  pure-function lemma, typically by `funext`/`Vector.ext` plus `simp` over the
  evaluators.

Compilation, cost, export and the computability checks all go through the IR
fields; the equivalence transports each guarantee to the closure:

* **compilation** — `compile` accepts a certified program iff it accepts its IR
  reimplementation, and emits literally the same code (`compile_certified_eq_ir`,
  definitional);
* **cost** — `compile_time_eq`, `witgenTime`, `compile_space_le` apply unchanged:
  the certified program's step count is the syntactic constant of its IR's code;
* **correctness against the closure itself** — `compile_sim` is stated in terms of
  the IR reference semantics `WitgenIR.irEval` (definitionally `eval` on `.ir`
  programs); on a certified program the packed equivalence rewrites `irEval` to
  `f`, giving `compile_sim_certified`: the machine's output buffer provably holds
  the encoded output **of the native closure** — the guarantee a bare `.native f`
  can never have;
* **computability** — the decidable checks discharge
  `ProverEnvironment.OnlyAccessedBelow N f` for the bare closure
  (`onlyAccessedBelow_certified` / `onlyAccessedBelow_of_ir_equiv`), and
  `computableChecks` / `circuit_computableWitnesses_of_checks` accept certified
  witness operations for free;
* **export** — `#assert_exportable` / `#witgen_json` (`WitnessExport.lean`)
  serialize the IR reimplementation, which computes exactly what the closure the
  Lean prover runs computes.

Worked instance, end to end: `isZeroNative` — the `IsZeroField` conditional-inverse
witness written as an ordinary Lean closure — is certified against `testIsZero`'s
IR program as `isZeroCertified` (`WitgenCompile.lean`, equivalence lemma
`isZeroNative_eq_testIsZero`). The differential test compares the machine against
the *closure*; `compile` emits `isZeroCompiled` with the pinned 140-unit-step /
2090-cycle cost (`compile_isZeroCertified`, `isZeroCertified_witgen_time_unit`,
`WitgenCost.lean`); the machine provably computes the closure's own output in
exactly 140 steps with peak memory ≤ 1 word (`isZeroCertified_witgen_correct_140`,
`WitgenSimIR.lean`); and `OnlyAccessedBelow 1 isZeroNative` discharges by
`native_decide` (`WitgenComputable.lean`).

Bare `.native` remains the visibly-uncertified escape hatch: `compile`, the export
commands and the computability checks all reject it, so an uncertified closure can
never silently acquire a cost claim.

## TimedCircuit: budgeted witgen as a type

`TimedCircuit.lean` turns the pipeline's cost story into a *type*: a
`TimedCircuit F Input Output` is a `FormalCircuit` that cannot be constructed
without a machine-checked bound on its witness-generation cost.

    structure TimedCircuit ... extends FormalCircuit F Input Output where
      costModel : CostModel := .unit
      witgenBudget : ℕ := 2 ^ 40
      witgen_bounded : underBudget costModel (size Input) witgenBudget
        ((main (varFromOffset Input 0)).operations (size Input)).toFlat = true

**The obligation is decidable.** `FlatOperation.witgenTime` folds
`FlatOperation.witgenCost` — `compile` followed by the honest partial clock
`staticTime?` — over the circuit's flat operations, threading the offset exactly
like `FlatOperation.localLength` and `computableChecks`: each generator is priced,
and its `envBound` checked, at its own accumulated offset. `underBudget` is one
boolean, so at a concrete circuit `witgen_bounded := by native_decide` (the default
field tactic) is the entire proof. `IsZeroField` upgrades to `isZeroTimed` this
way, with pinned total `140 + 19 = 159` unit steps.

**The number carries meaning.** `witgenTime_sound` reifies `witgenTime = some T`
into a per-generator certificate (`WitnessCosts`): every witness generator, at its
own offset, is accepted by `compile` with a static time `tᵢ`, and `Σ tᵢ = T`. Via
the phase-2/3 machinery, each certified `tᵢ` is the exact running time of every
execution of that generator's compiled code, with live-memory peak `≤ tᵢ`
(`WitnessCosts.forAll_exec`, citing `Exec.staticTime?_time_eq` and
`Exec.peak_le_time`), and `compile_sim` supplies the execution computing the
encoded reference output. `TimedCircuit.witgen_lt_budget` packages this: every
generator of a `TimedCircuit` runs in exactly its certified time, strictly below
the budget.

**`.native` makes the type unattainable; `.certified` restores it.** `compile`
rejects bare native closures, so one uncertified witness poisons `witgenTime` to
`none` and no budget check can pass. Certifying the closure against an IR
reimplementation (`WitgenIR.certified`) re-admits it — and the cost certificate
then applies to the very closure the prover runs.

**Scope.** The obligation is stated at the canonical instantiation (fresh input
variables `varFromOffset Input 0`, witnesses from offset `size Input`): compiled
cost depends on the syntactic shape of embedded input expressions, so a single
number cannot cover arbitrary compound-expression instantiations. Future work:
input-congruence over variable-only instantiations, and whole-circuit sequential
composition — budgets already sum over composition by construction (the fold of an
append is the sum), but the composed machine-level run is not yet stated.

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
  constant — the formal content of "every operation is unit time". The proved
  statement is data-independence of the *abstract time counter*: every input yields
  the same `t`. That is a useful ingredient of a constant-time argument (the
  instruction trace of straight-line code is input-independent), but it does not
  cover memory-access addresses, allocation sizes, memory profiles, or faults, and
  is not by itself a side-channel security statement — see "What is NOT proved".
- One deliberate exception: **allocation is charged per word**. `memAlloc`(`I`)
  costs `C.memAlloc + cap * C.allocPerWord` — a base cost plus at least one tick
  per word of capacity acquired — so no instruction can acquire `n` words in
  `o(n)` time. For `memAllocI` the capacity is an *immediate* in the syntax, so
  the charge is still a pure function of the instruction and static pricing is
  untouched; the *dynamic* `memAlloc` reads its capacity from a register, so its
  time is data-dependent **by design** and it is excluded from `Stmt.Straight`
  (like a loop). The payoff is the standing theorem `Exec.peak_le_time`: in any
  model with `1 ≤ C.allocPerWord` (both shipped tables), every execution satisfies
  `p ≤ t` — peak live memory is bounded by running time, so **one time certificate
  bounds both resources**.
- `Stmt.staticTime?` is the safe way to *quote* a static time: `some n` iff the
  code is straight-line with static time `n` (`staticTime?_eq_some`), in which case
  every execution takes exactly `n` (`Exec.staticTime?_time_eq`); `none` for
  anything containing `ifNZ`/`whileNZ` or a dynamic `memAlloc`. The raw
  `staticTime` returns 0 on loops, under-reports the dynamic `memAlloc` (it quotes
  only the base cost — the per-word charge depends on the runtime capacity), and
  is only meaningful under a `Stmt.Straight` proof — or, for branching but
  loop-free code (`Stmt.LoopFree`, which also excludes dynamic `memAlloc`), as a
  proved *upper bound*: `Exec.time_le_staticTime_of_loopFree` shows the `ifNZ`
  arm's `branch + max` shape bounds every execution.
- Bounds proved for a generic `C` instantiate to any concrete table: `CostModel.unit`
  (all 1) or `CostModel.cycles` (a rough modern-CPU latency table). This is where
  "roughly a cycle on a modern CPU" lives: the *shape* of the machine guarantees
  state-independence, the *table* calibrates it.

Consequences for the instruction set:

- Memory is *reserved*, not initialised: `memAlloc`/`memAllocI` reserve capacity
  for `n` words — a `malloc` without `memset`. Reads are only allowed below the
  filled length, so uninitialised capacity is unobservable; initialisation is paid
  for by the pushes/stores that perform it. Acquisition itself is charged per word
  (`allocPerWord`), never in one tick — that is what makes `p ≤ t` a theorem.
- `memPush` requires free capacity (a proof obligation, like the in-range obligation
  of `memLoad`) and is therefore **worst-case** unit time — no doubling, no
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
no derivation — the `memLoad`/`memStore` rules demand an in-range proof).

Memory is *not* an allocation counter — memory gets reused. Live memory is the sum
of reserved capacities: only `memAlloc`/`memAllocI` charge (`newCap - oldCap`), only
`memFree` credits, and push/pop move the fill level inside capacity already paid
for. Profiles compose like high-water marks:

    seq:  net = d₁ + d₂        peak = max p₁ (d₁ + p₂)

so a block with net 0 (an alloc…free pair, or work inside fixed capacity)
contributes its peak once, not once per occurrence. The `ScratchLoop` example
allocates a one-slot scratch buffer, runs `n` iterations that each push and pop a
word inside it, and frees it: proved net 0 and peak **1 word, independent of `n`**
(an allocation counter would report `n`). Invariants `0 ≤ p` and `d ≤ p` hold
always, code containing no allocation has `d ≤ 0 ∧ p ≤ 0` (`allocFree_space`),
and — because acquiring capacity costs at least a tick per word — `p ≤ t` in any
model with `1 ≤ allocPerWord` (`Exec.peak_le_time`): a time bound subsumes a
peak-memory bound, one certificate for both resources.

These indices are anchored to *absolute* live memory, not just to an arbitrary
baseline. `State.WellFormed` (every buffer's fill within its reserved capacity,
finitely many buffers reserved) holds for `State.init` and is preserved by every
execution (`Exec.wellFormed_preserved`), which rules out adversarial states with
phantom capacity — a fabricated `caps b` that a `memFree` could turn into credit
funding a huge allocation at certified peak 0 — or with stored data the metric never
charged. Over such states the absolute footprint `State.liveMem` changes by *exactly*
`d` (`Exec.liveMem_eq`), a free credits only genuinely live capacity
(`Exec.memFree_credit_le`), and every state the execution passes through stays within
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

`run` is a *reference semantics* — it exists for differential testing and for
producing `Exec` derivations — **not** a performance-realizing implementation. Its
`State` maps registers and buffer names through Lean functions, so every `setReg`
stacks another closure and lookups walk the chain (individual buffers are real
`Array`s, but the maps around them are functional); the interpreter's own wall-clock
time and heap usage are therefore unrelated to the abstract cost `t` and profile
`(d, p)` it computes. A performant runner — array-backed registers, native buffers —
would be a separate artifact with its own refinement proof against `Exec`.

### Ergonomics

Programs can be written against the raw constructors (assembly-flavoured, what proofs
are stated over) or through `Builder.lean`: a monad with `freshReg`/`freshBuf`,
compound expressions (`x + y * z` compiling through fresh temporaries), `while_`/`if_`,
and subroutines as ordinary Lean functions. At the surface, buffers are the newtype
`Buf w`, produced only by `Mem.alloc` (dynamic capacity) / `Mem.allocI`
(immediate capacity, statically priced); reads, writes, pushes, pops, length and
free are methods on the handle (`b.load i`, `b.store i e`, `b.push e`, `b.pop`,
`b.len`, `b.free`) — in the core both `Reg` and `BufId` are
`ℕ` (numeral-friendly proof goals), so the wrapper is what stops a buffer handle
being confused with a register or an index. Builder output is checked equal to the
hand-written core syntax in the examples, so the sugar adds nothing to the trusted
surface. Subroutine *specs* are ordinary Lean theorems about the generated code
(`SumBuf.spec`), reused at every call site — the same composition discipline as
`FormalCircuit`, one level down.

Generated programs are inspectable through the canonical pretty-printer
(`Stmt.render`, `Render.lean`), which prints the machine's assembly dialect: memory
instructions carry the `mem.` qualifier (their Lean constructors are `memLoad`,
`memStore`, `memPush`, `memPop`, `memLen`, `memAlloc`, `memAllocI`, `memFree` —
identifiers cannot contain dots), register-file instructions of a future phase will
carry `reg.`, and `whileNZ` prints as a `loop { … }` whose guard ends in `bifz r<c>`
(break-if-zero on the verdict register). The buffer-summing builder program `sumB`
(= `SumBuf.code`, `Examples.lean`) renders as (pinned there by `#guard_msgs`):

    imm   r0, 0
    imm   r1, 0
    mem.len   r2, b0
    loop {
      ult  r3, r1, r2
      bifz r3
      mem.load  r4, b0[r1]
      add  r0, r0, r4
      imm   r5, 1
      add  r1, r1, r5
    }

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
| `memLoad`, `memStore` | one load/store at `base + 8·i`; the in-range proof carried by the `Exec` rule means bounds checks can be elided | 1–2 instr |
| `memLen`, `memPop` | load / decrement of the length field | 1 instr |
| `memAlloc`, `memAllocI` | `malloc(8n)` — reserve, don't initialise: no `memset`. The model charges `memAlloc + n·allocPerWord` — deliberately **at least a tick per word**, an over-provision for the allocator's O(1) fast path that also absorbs lazy page-mapping / first-touch costs, and the price of the `p ≤ t` theorem | O(1) real, O(n) charged |
| `memFree` | `free` — no per-element work for a `u64` buffer | O(1) |
| `memPush` | length-check-free store at `base + 8·len` + length increment (capacity proved sufficient) — **worst-case** O(1), no doubling | 1–2 instr |
| `ifNZ`, `whileNZ` guard | test + branch | 2 instr |

The peak-memory bound transfers directly: physical footprint = sum of reserved
capacities = exactly what the model charges, up to allocator metadata and
fragmentation (a small constant for the few, long-lived, word-aligned buffers this
machine uses). No shrinking policy or amortization argument is needed — capacity
changes only at `memAlloc`/`memFree`. On the model side this identification is
backed by the `State.WellFormed`/`State.liveMem` theorems (see the memory-profile
section above): over every state reachable from an honest start, `d` is the exact
change and `p` a true high-water mark of the *absolute* footprint — not growth
relative to an arbitrary baseline — so "sum of reserved capacities" is a
well-defined quantity the profile really tracks.

Supporting facts, all discharged by the machine's design rather than by proof:

- The syntax of any program mentions finitely many registers and buffer names, both
  known statically. Registers become stack slots (L1-resident) or machine registers;
  each buffer becomes its own `Vec<u64>`. No dynamic name ever needs resolving.
- Words are exactly `u64`; no bignum arithmetic can hide inside an instruction (this
  is why the DSL exists instead of measuring Lean's GMP-backed `Nat`).
- No instruction does hidden work the model fails to charge (`memAlloc`
  reserves without initialising precisely so that no hidden `memset` exists;
  freeing a `u64` buffer has no per-element work; allocation's per-word charge
  *over*-states the allocator's O(1) reservation, never under-states it).

One honest qualification remains: `c` is uniform over the memory hierarchy — a
`memLoad` costs the same whether it hits L1 or DRAM; the *count* of memory accesses is
exact, and sensitivity to their unit price is a `CostModel` calibration question, not
a soundness one. (The former second qualification — amortized `memPush` latency — is
gone: with explicit capacity, every instruction is worst-case constant time.)

## What is NOT proved

The theorems stop at the abstract machine. Stated plainly:

- **No verified backend exists.** There is no verified lowering from `Stmt` to a
  physical ISA, allocator, or runtime. The compilation contract above — each
  instruction maps to O(1) machine operations on a modern 64-bit CPU — is an
  engineering argument, made per-instruction and kept inspectable; it is not a
  theorem.
- **`CostModel` is a parameter, not a fact about hardware.** Every theorem is
  generic in `C`. The shipped `.unit` and `.cycles` tables are calibration choices,
  and the `cycles` entries are estimates (`memLoad := 4` assumes an L1 hit,
  `memAlloc := 50` assumes the malloc fast path); no theorem relates them to any
  real chip.
- **Abstract states are mathematical functions.** `State` maps registers and buffer
  names through functions. That a backend realizes these as stack slots, machine
  registers and per-buffer vectors is part of the same informal contract — made
  credible by the finitely many statically-known names, not proved. Each buffer
  name also carries O(1) descriptor state (pointer, length, capacity) outside the
  word-count metric.
- **Total semantics at the edges.** `udiv`/`umod` by zero and `memPop` on an empty
  buffer follow the total `BitVec`/`Array` semantics (division by zero yields 0,
  pop on empty is a no-op). A native backend must insert the corresponding checks
  or establish the corresponding preconditions — bounded, O(1) work per site, but
  that obligation lives in the contract, not in the proofs.
- **Allocator realities are outside the metric.** Allocator metadata, alignment,
  fragmentation, and code size are not measured. The peak `p` counts reserved
  words — the `WellFormed`/`liveMem` theorems make that count absolute over every
  reachable state — but words-to-bytes, headers and padding are the allocator's
  business.
- **Generation-time staging is unpriced.** `mapRange`/`envRange`/`bitsOf` and the
  Fermat inverse ladder unroll at *generation* time, so generated code size is
  proportional to those static parameters. The cost theorems price the runtime of
  the generated code; the size itself is not hidden — it is visible as the
  instruction count / `staticTime` under the unit model — but the generation work
  is Lean evaluation and carries no bound.
- **Time data-independence is not a side-channel proof.** `straight_time_eq` /
  `compile_time_data_independent` prove that the *abstract time counter* is the
  same on every input. They do not cover memory-access addresses (`memLoad b i`
  costs one unit whatever the data-dependent index `i` is), memory profiles, or
  faults. Allocation sizes are no longer a blind spot of the counter: allocation
  is charged per word, so a data-dependent allocation size *shows up in the time*
  — the dynamic `memAlloc` is data-dependent by design and hence excluded from
  the straight-line fragment, while `memAllocI`'s size is syntactic. (The former
  gap — a "constant-time" giant allocation invisible to the counter — is gone.)
  Still, a useful ingredient for a constant-time implementation — the instruction
  trace of straight-line code is input-independent — but not by itself a
  side-channel security statement.

### Trusted base

Checking the theorems requires trusting the Lean kernel plus the three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`). The concrete headline
numerals — BabyBear primality, the `staticTime` numerals like `140`/`2090` —
additionally use `Lean.ofReduceBool` via `native_decide` (trusting the Lean
compiler to evaluate closed booleans; needed because `toBits` is well-founded
recursion, which `rfl` cannot reduce). `#print axioms <theorem>` is the audit
tool: it lists exactly which of these any given theorem depends on.

## Caveats / next steps
- The witgen-IR compiler (`WitgenIR → Stmt`, `WitgenCompile.lean`) with its verified
  lowering and per-node cost theorems is complete. Natural next steps: compiling a
  whole circuit's multi-witness computation (not just single witness blocks), a
  performant runner beyond the reference interpreter, and refining the cost model
  toward a concrete backend.
- A `Proc` record bundling `code`/`Pre`/`Post`/`time`/`space`/`spec` (mirroring
  `FormalCircuit`) would package subroutines more tightly; the examples inline this
  pattern with plain `have`s for now.
- Registers in the examples use fixed conventions (callee-clobbered scratch); a
  register-window or parameterized-register discipline is mechanical to add
  (distinctness side conditions close by `decide`).
