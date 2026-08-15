# Caliper: the low-level unit-cost DSL

**Caliper** is a deep-embedded imperative language whose every instruction runs in
constant time, designed as a compilation target for higher-level languages that want
certified resource bounds — in particular the witness-generation IR of the
[Clean](https://github.com/rot256/clean) zk-circuit project, which depends on this
library. Programs carry machine-checked **upper bounds** on running time and on
allocated memory.

## Files

| File | Contents |
|---|---|
| `Core.lean` | Syntax (`Stmt`), cost models (`CostModel`, including the per-word allocation charge `allocPerWord`; the `CostModel.Admissible` predicate — every instruction-pricing entry ≥ 1, with the deliberate free-is-free exemptions for the release `memFree` and the alloc base `memAlloc` — with both shipped tables proved admissible), big-step cost semantics (`Exec`), determinism, framing (`Writes`/`Touches`), the unit-time theorems and the partial static clock (`staticTime?`), **peak memory ≤ running time** (`Exec.peak_le_time`), well-formed states and absolute live memory (`State.WellFormed`, `State.liveMem` — the sum of reserved buffer capacities), reference interpreter (`run`) + soundness |
| `Render.lean` | Canonical pretty-printer: `Stmt.render`/`Stmt.renderString` emit the `mem.`-qualified assembly dialect (`mem.load r4, b0[r1]`, `loop { … bifz r<c> … }`), one instruction per line — the notation used for the instruction listing in this document |
| `Triple.lean` | Upper-bound Hoare triples (`Triple`), one rule per instruction, `seq`/`conseq`/`ifNZ`, the measure-indexed loop rule `whileNZ_measure`, frame rules; decoupled time-only/space-only judgments (`TimeTriple`/`SpaceTriple`) with the same rule set, recombinable into a full `Triple` via determinism (`TimeTriple.and_space`) |
| `Builder.lean` | Surface syntax: builder monad with fresh register/buffer *naming* (`freshReg`/`freshBuf` — pure counters, no emitted code), expression compiler (`Exp`), structured `if_`/`while_`, typed buffer handles (`Buf`), product types (`PairR`, `PairBuf`) |
| `Examples.lean` | Worked examples with full proofs (including the `ScratchLoop` memory-reuse bound and the `ScopedSumSq` register-lifetime demo), builder ↔ core checks, interpreter demos |
| `Liveness.lean` | The static register metric: backward liveness analysis (`Stmt.liveBefore`), inferred peak register pressure (`Stmt.regPeak`/`Stmt.regPeak₀`), the live-ins + writes bound (`Stmt.regPeak_le_card_liveBefore_add_writesTotal`, `Stmt.Straight.regPeak₀_le`), the canonical combined buffers-plus-registers judgment (`SpaceBound`) and the total time ≥ total memory theorem for straight code (`Exec.straight_total_footprint_le`), plus pinned inferred peaks for the example programs |
| `W64.lean` | Fixed 64-bit surface: namespace `Caliper64` of reducible `abbrev`s pinning `w := 64` (`Word`, `Stmt`, `State`, `Exec`, `run`, `Triple`, `TimeTriple`, `SpaceTriple`, `Build`, `Exp`, `Buf`, `build`), plus a short demo where `w` never appears |

## Where the rest of the pipeline lives

This repository contains the machine itself: syntax, cost semantics, program
logic, builder surface, renderer, and the fixed 64-bit surface `Caliper64`. The
layers built on top of it — the witness-generation compiler (witgen-IR → `Stmt`,
with its verified lowering and per-node cost theorems), the generic prime-field
gadget library (`Fp w p`), and the `TimedCircuit` budgeted-witgen structure —
live in the [Clean](https://github.com/rot256/clean) project, which depends on
this library. Claims about those layers (certified compilation, concrete
step-count pins, budget obligations) are stated and proved there, not here.

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
- One deliberate exception: **acquiring live memory is charged per word**.
  `memAlloc`(`I`) costs `C.memAlloc + cap * C.allocPerWord` — a base (0 in both
  shipped tables: buffer names are static and capacities explicit, so an
  arena/bump allocator serves them and object creation is a pointer bump
  amortized into the per-word charge) plus at least one tick per word of
  capacity acquired — so no instruction can acquire `n` words in `o(n)` time.
  For `memAllocI` the capacity is an *immediate* in the syntax, so the charge
  is still a pure function of the instruction and static pricing is untouched;
  the *dynamic* `memAlloc` reads its capacity from a register, so its time is
  data-dependent **by design** and it is excluded from `Stmt.Straight` (like a
  loop). The payoff is the standing theorem `Exec.peak_le_time`: in any model
  with `1 ≤ C.allocPerWord` (both shipped tables), every execution satisfies
  `p ≤ t` — peak live (buffer) memory is bounded by running time, so one time
  certificate bounds both resources. The register file has its own, *static*
  time ≥ memory theorem (`Stmt.Straight.regPeak₀_le`, and the combined
  `Exec.straight_total_footprint_le` — see the memory-model section).
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
- Genericity cuts both ways: a degenerate table (some entry 0) makes cost claims
  vacuous — a model that prices real work at zero certifies any program under any
  budget. `CostModel.Admissible` (`Core.lean`) packages "every table entry
  pricing an instruction ≥ 1, including the per-op `un`/`bin` entries and
  `allocPerWord`" as a predicate; both shipped tables are proved admissible
  (`CostModel.unit.admissible`, `CostModel.cycles.admissible`), so every headline
  number in this document is accounted in a model where no instruction runs for
  free. Two entries are *deliberately* exempt, both instances of the
  free-is-free principle (a release's cost is covered by its acquisition). The
  release instruction `memFree` (0 in both tables — a buffer release's work was
  priced into the acquisition charge that created it) has no `≥ 1` field. And
  the alloc *base* `memAlloc` (also 0) needs none because the full acquisition
  charge `memAlloc + capacity·allocPerWord` is already kept ≥ 1 per acquired
  word by the `allocPerWord` field — an admissible model still acquires no live
  memory in zero time (the only zero-time allocation is the zero-capacity one,
  whose effect is exactly `memFree`'s: a release, free by principle). Under an
  admissible model, `Exec.peak_le_time` applies via
  `Exec.peak_le_time_admissible` (its `1 ≤ allocPerWord` hypothesis is the
  `allocPerWord` field), and the headline claims should be read against
  admissible tables.

Consequences for the instruction set:

- Memory is *reserved*, not initialised: `memAlloc`/`memAllocI` reserve capacity
  for `n` words — an allocation without `memset`. Reads are only allowed below the
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
- Words are `BitVec w` (fixed at 64 by the `Caliper64` surface); all arithmetic
  wraps, mirroring the u64 sort of typical source IRs.

### Upper bounds, not exact times — and memory as a (net, peak) profile

`Triple C P c Q T D M` is total correctness plus `t ≤ T` (time), `d ≤ D` (net
live-memory change, signed) and `p ≤ M` (peak live-memory growth). Exhibiting the
underlying `Exec` derivation also proves **memory safety** (out-of-range accesses have
no derivation — the `memLoad`/`memStore` rules demand an in-range proof).

Memory is *not* an allocation counter — memory gets reused. And "the memory" of
a program is **two summands**, canonically quoted as one total (`SpaceBound`,
`Liveness.lean`):

    total peak memory = dynamic buffer peak + static register peak

The register file **is** memory — register words are as physical as buffer
words. What differs is the *accounting*, and the split follows the information:
buffer contents are **runtime** information (lengths are dynamic, indices are
data), so buffer capacity is metered dynamically by the cost semantics;
register lifetimes are **static** information (registers are statically named,
never dynamically indexed), so the register footprint is a compile-time
constant of the code — the inferred peak live-register count `Stmt.regPeak₀`
(`Liveness.lean`), read off the program's data-flow by a backward liveness
analysis. Nothing about the split makes registers cheaper; it makes their
accounting exact without runtime instructions. The model's dynamic-side
principle, in one paragraph:

> Acquiring a word of buffer capacity costs one step — and that per-word charge
> prices the word's whole lifecycle, creation *and* eventual destruction; there
> is no per-object base (buffer names are static and capacities explicit, so an
> arena/bump allocator serves them: object creation is a pointer bump,
> amortized into the per-word charge). Holding it is free. Releasing it is
> free — always.

Dynamic live memory is the sum of reserved buffer capacities:
`memAlloc`/`memAllocI` charge `newCap - oldCap`, only `memFree` credits, and
push/pop move the fill level inside capacity already paid for. Releasing is
free in *time* as well: `C.memFree = 0` in both shipped tables — the
free-is-free half of the principle, sound for the cost story because a release
only ever shrinks the footprint and its cost is amortized into the acquisition
it pairs with: every release matches a unique earlier acquisition whose charge
covers creation *and* destruction. That lifecycle accounting is the only split
stable across real allocators — a buffer's teardown (freelist push, deferred
coalescing, or `munmap`) is bounded by size-linear work already paid at its
`memAlloc`. A release with no matching acquisition — `free(NULL)`, a `mem.free`
of a never-acquired buffer name — is statically detectable (buffer names are
static) and elidable by a backend. Profiles compose like high-water marks:

    seq:  net = d₁ + d₂        peak = max p₁ (d₁ + p₂)

so a block with net 0 (an alloc…free pair, or work inside fixed capacity)
contributes its peak once, not once per occurrence. The `ScratchLoop` example
allocates a one-slot scratch buffer, runs `n` iterations that each push and pop a
word inside it, and frees it: proved net 0 and peak **1 word, independent of `n`**
(an allocation counter would report `n`). The register-side counterpart is
static: `ScopedSumSq` (`3² + 4²`) names five registers, and the analysis infers
peak **2** — each stage's scratch is dead the moment its `mul` consumes it.

The combined total is the same quantity the previous machine revision metered
dynamically, only sharper. That revision had explicit `reg.alloc`/`reg.free`
instructions and counted allocated registers inside the dynamic profile — but a
program's register liveness is static, so what those instructions metered was
necessarily a constant of the code; the analysis computes the same constant
directly, and where explicit brackets over-approximated a live range, inference
is strictly sharper. Worked arithmetic: `SumBuf` uses 6 registers and never
releases one — the old dynamic total was 0 buffer + 6 register = 6, and the
canonical total (`SumBuf.total_space`) is the same `0 + 6 = 6`. `ScopedSumSq`'s
old brackets certified register peak **3** (stage-1 result + stage-2 scratch +
stage-2 result coexist as *names*), for a dynamic total of 3; the inferred peak
is **2**, so the canonical total (`ScopedSumSq.total_space`) is `0 + 2 = 2`.
And the array-of-pairs demo, whose builder temporaries were never released,
had old dynamic total 22 (4 buffer words + 18 register names); its canonical
total is `4 + 3 = 7` — the 18 names need only 3 slots.

Invariants `0 ≤ p` and `d ≤ p` hold always; code acquiring no buffer capacity
(no `memAlloc`/`memAllocI`) has `d ≤ 0 ∧ p ≤ 0` (`allocFree_space` — `memFree`
is allowed, it only shrinks the footprint); and — because acquiring a word
costs at least a tick — `p ≤ t` in any model with `1 ≤ allocPerWord`
(`Exec.peak_le_time`): a time bound subsumes the buffer-peak bound. The
register side has the *static* time ≥ memory analogue
(`Stmt.Straight.regPeak₀_le`): peak register pressure ≤ live-ins + unit-model
static time. And the two bounds do not each consume a running time of their
own: on straight code the instructions that cover the buffer words (per-word
allocation charges) and those that cover the register slots (register-writing
leaves) are **disjoint**, so buffer peak + register peak ≤ live-ins + `t` for
the *single* running time `t` (`Exec.straight_total_footprint_le`).

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

Presentation note, to keep the two readings apart: a code *fragment's* quoted peak
`p` is **growth over its start state** — that is what makes Triple-level profiles
compose as relative high-water marks. Absolute-**footprint** statements are the
`State.WellFormed`/`liveMem` forms above, which anchor the same indices to
physical live memory over honestly-reachable states; quote those when the claim
is "this program never holds more than X words", and the relative form when the
claim is "this fragment adds at most X words". In either reading, the
user-facing total goes through `SpaceBound` (`Liveness.lean`): an ordinary
buffer-side `SpaceTriple` plus the static `regPeak₀`, summed — so a
buffers-only figure can never masquerade as "the memory". (Register *values*
are framed by `Stmt.Writes`, as always.)

A note on lowering: the inferred live ranges are exactly what a backend
colors. `Stmt.regPeak₀` bounds the number of simultaneously live registers at
any program point, so interval-coloring the inferred ranges renames the
unboundedly many fresh names onto `regPeak₀` physical slots — the certified
static peak *is* the frame size of a RISC-V lowering's register file. And the
claim is **sound for arbitrary code**, not just disciplined code: the previous
revision's bracket-based version of this claim was scoped to builder-generated
programs, because a hand-written `Stmt` could read a register it had "freed"
and invalidate the brackets; inferred intervals have no such hole — liveness is
computed from the reads that actually occur, so a register stays live exactly
as long as some later instruction may read it. That is an upgrade: the
peak-equals-physical-slots transfer now covers every `Stmt`, hand-written or
generated. (What inference costs is precision on loops — the `whileNZ` case
widens by the loop's whole use set instead of iterating to a fixpoint,
erring toward counting a register live.)

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

#### The static register metric, in brief

`Liveness.lean` implements the register summand: `Stmt.liveBefore c after`
over-approximates the registers whose values may still be read (structural
recursion, no fixpoint — `whileNZ` widens by the loop's whole use set), and
`Stmt.regPeak c after` bounds the number of registers *simultaneously live* at
any program point; `Stmt.regPeak₀` is the whole-program peak with nothing live
at exit — the frame size a lowering needs for the register file. The headline
theorem `Stmt.regPeak_le_card_liveBefore_add_writesTotal` bounds the peak by
live-ins plus register-writing instructions, whence for straight-line code
`Stmt.Straight.regPeak₀_le` (peak register pressure ≤ live-ins + unit-model
static time — the liveness-side analogue of `Exec.peak_le_time`) and the
combined disjointness theorem `Exec.straight_total_footprint_le` (buffer peak +
register peak ≤ live-ins + the one running time). `SpaceBound` packages
buffer-`SpaceTriple`-plus-`regPeak₀` as the canonical total, with worked
instances for the example programs.

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
and subroutines as ordinary Lean functions. `freshReg` is a **pure name
counter** — naming a register emits no code and costs nothing; the register
file's footprint is the statically inferred live peak (`Stmt.regPeak₀`), so
there is no scoping ceremony to observe and no lifetime to declare. At the
surface, buffers are the newtype
`Buf w`, produced only by `Mem.alloc` (dynamic capacity) / `Mem.allocI`
(immediate capacity, statically priced); reads, writes, pushes, pops, length and
free are methods on the handle (`b.load i`, `b.store i e`, `b.push e`, `b.pop`,
`b.len`, `b.free`) — in the core both `Reg` and `BufId` are
`ℕ` (numeral-friendly proof goals), so the wrapper is what stops a buffer handle
being confused with a register or an index. Builder output is checked equal to the
hand-written core syntax in the examples, so the sugar adds nothing to the trusted
surface. Subroutine *specs* are ordinary Lean theorems about the generated code
(`SumBuf.spec`), reused at every call site — the same composition discipline as
Clean's `FormalCircuit`, one level down.

Generated programs are inspectable through the canonical pretty-printer
(`Stmt.render`, `Render.lean`), which prints the machine's assembly dialect: memory
instructions carry the `mem.` qualifier (their Lean constructors are `memLoad`,
`memStore`, `memPush`, `memPop`, `memLen`, `memAlloc`, `memAllocI`, `memFree` —
identifiers cannot contain dots), and
`whileNZ` prints as a `loop { … }` whose guard ends in `bifz r<c>` (break-if-zero
on the verdict register). The hand-written buffer-summing program `SumBuf.code`
(`Examples.lean`) renders as (pinned there by `#guard_msgs`) — and the builder
version `sumB` emits exactly this program (checked there by `#eval`):

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
word size of the intended backends. `W64.lean` provides the namespace `Caliper64`: thin
reducible `abbrev`s fixing `w := 64` for the types and entry points a program or
spec author touches (`Word`, `Stmt`, `State`, `State.init`, `Exec`, `run`, `Triple`,
`TimeTriple`, `SpaceTriple`, `Build`, `Exp`, `Buf`, `build`). Import
`Caliper.W64` and write against `Caliper64`; because the abbreviations are
reducible, every generic theorem and proof rule applies definitionally — nothing is
redefined or restated. Names that infer `w` from their arguments (the `Build`
combinators, the `Triple` rules, `CostModel`, `Reg`, `BufId`, …) are used from
`Caliper` unchanged. The generic `w` remains in the core; downstream users (Clean's
witgen pipeline) fix 64.

## The compilation contract — why DSL cost `n` means `c · n` CPU time

The guarantee this machine is designed around is *not* a statement about Turing
machines. It is: **every `Stmt` instruction is implementable in a constant number of
machine instructions on a 64-bit CPU**, so an `Exec` derivation of cost `t` (unit
model) corresponds to a real execution of at most `c · t` cycles, with `c` the maximum
over the per-instruction table.

That claim is **relative to the built word width `w`**: one `w`-word operation is a
constant number of machine operations *for the `w` the code was built at*. The core
is generic in `w`, and nothing stops instantiating it at a million-bit word — but
that is a different machine, whose "unit" add is a million-bit add and whose `c` is
correspondingly enormous; a cost certified at one `w` says nothing about another.
The headline claims of this document are therefore about the fixed 64-bit surface:
`Caliper64` (`W64.lean`) is the machine they are stated for — words are exactly
`u64`, downstream users pin `w = 64` throughout, and the per-instruction table
below is a table about 64-bit hardware. Write programs and read cost claims against
`Caliper64` unless you are deliberately doing generic-`w` metatheory.

Since every `Exec` rule charges a syntactic constant
and the table has a dozen entries, the trusted argument is a per-instruction inspection:

| Instruction | Real implementation | Cost |
|---|---|---|
| `imm`, `mov` | load-immediate / register move | 1 instr |
| `un`, `bin` | one ALU op (`udiv`/`umod` ≈ 20–40 cycles — a *constant*, tabulated in `CostModel.cycles`) | 1 instr |
| `bin .mulhi` | high word of the widening multiply: `MULHU` (RISC-V M — required by the RVA application profiles), `UMULH` (AArch64), the `RDX` half of `MUL` (x86-64). With `.mul`, the full `2w`-bit product in 2 instructions (the RISC-V-blessed fused idiom) — the primitive field reduction needs | 1 instr |
| `shl`, `shr` | shift + compare/mask for the `≥ w ⇒ 0` convention (x86/ARM mask the amount) | 2–3 instr |
| `memLoad`, `memStore` | one load/store at `base + 8·i`; the in-range proof carried by the `Exec` rule means bounds checks can be elided | 1–2 instr |
| `memLen`, `memPop` | load / decrement of the length field | 1 instr |
| `memAlloc`, `memAllocI` | reserve `8n` bytes, don't initialise: no `memset` — an arena/bump-allocator pointer bump, since buffer names are static and capacities explicit; no general-purpose `malloc` is needed. The model charges `memAlloc + n·allocPerWord` with base 0: **at least a tick per word**, an over-provision for the O(1) pointer bump that pays the object's whole lifecycle (creation *and* eventual destruction) and absorbs lazy page-mapping / first-touch costs — the price of the `p ≤ t` theorem | O(1) real, O(n) charged |
| `memFree` | release to the arena — no per-element work for a `u64` buffer, and its O(1) cost was priced into the per-word acquisition charge that created the object. Charged `memFree` = 0; a `mem.free` with no matching acquisition is statically detectable and elidable, like `free(NULL)` | O(1) real, 0 charged |
| `memPush` | length-check-free store at `base + 8·len` + length increment (capacity proved sufficient) — **worst-case** O(1), no doubling | 1–2 instr |
| `ifNZ`, `whileNZ` guard | test + branch | 2 instr |

The peak-memory bound transfers directly, one summand at a time. The buffer
side: physical buffer footprint = sum of reserved capacities = exactly what
the dynamic profile charges, up to allocator metadata and fragmentation (a
small constant for the few, long-lived, word-aligned buffers this machine
uses); no shrinking policy or amortization argument is needed — capacity
changes only at `memAlloc`/`memFree`. The register side: the register file's
physical demand is a frame of `regPeak₀` word slots — interval-coloring the
statically inferred live ranges renames the unboundedly many fresh names onto
that many slots, for arbitrary programs (see the lowering note in the
memory-profile section). On the model side the buffer identification is
backed by the `State.WellFormed`/`State.liveMem` theorems (see the memory-profile
section above): over every state reachable from an honest start, `d` is the exact
change and `p` a true high-water mark of the *absolute* footprint — not growth
relative to an arbitrary baseline — so "sum of reserved capacities" is a
well-defined quantity the profile really tracks.

Supporting facts, all discharged by the machine's design rather than by proof:

- The syntax of any program mentions finitely many registers and buffer names, both
  known statically. Registers become stack slots (L1-resident) or machine registers;
  each buffer becomes its own `Vec<u64>`. No dynamic name ever needs resolving.
  Register slots are reusable by interval coloring of the inferred live
  ranges, so the *certified peak live count* (`Stmt.regPeak₀`) — not the
  number of fresh names — is the physical register/stack demand.
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
- **Only the Caliper `Stmt` under `Exec` is priced.** Programs a higher-level
  language compiles to this machine typically also have other execution engines
  (a reference semantics, an interpreter). The cost theorems price the compiled
  Caliper artifact only, and the ratio between engines is **not a constant** — a
  step count certified here says nothing numerical about any other engine beyond
  whatever output-equality the compiler's own simulation theorem provides (see
  Clean's witgen pipeline for a worked instance).
- **`CostModel` is a parameter, not a fact about hardware.** Every theorem is
  generic in `C`. The shipped `.unit` and `.cycles` tables are calibration choices,
  and the `cycles` entries are estimates (`memLoad := 4` assumes an L1 hit,
  `allocPerWord := 1` assumes a cache-line-amortised first touch); no theorem relates them to any
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
- **Generation-time staging is unpriced.** Builder programs (and compilers
  targeting this machine) unroll at *generation* time, so generated code size is
  proportional to their static parameters. The cost theorems price the runtime of
  the generated code; the size itself is not hidden — it is visible as the
  instruction count / `staticTime` under the unit model — but the generation work
  is Lean evaluation and carries no bound.
- **Time data-independence is not a side-channel proof.** `straight_time_eq`
  proves that the *abstract time counter* is the
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
axioms (`propext`, `Classical.choice`, `Quot.sound`). Everything in this
repository is proved without `native_decide` (the pinned example numbers are
`rfl`/`#guard_msgs` evaluations); downstream projects may additionally rely on
`Lean.ofReduceBool` for their own concrete headline numerals. `#print axioms
<theorem>` is the audit tool: it lists exactly which axioms any given theorem
depends on.

## Caveats / next steps
- Natural next steps: a performant runner beyond the reference interpreter, and
  refining the cost model toward a concrete backend (the RISC-V lowering story
  sketched in the compilation contract above).
- A `Proc` record bundling `code`/`Pre`/`Post`/`time`/`space`/`spec` (mirroring
  Clean's `FormalCircuit`) would package subroutines more tightly; the examples inline this
  pattern with plain `have`s for now.
- Registers in the examples use fixed conventions (callee-clobbered scratch); a
  register-window or parameterized-register discipline is mechanical to add
  (distinctness side conditions close by `decide`).
