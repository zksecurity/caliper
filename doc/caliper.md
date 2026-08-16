# Caliper: the low-level unit-cost DSL

Caliper is a deep-embedded imperative language whose every instruction runs in
constant time, designed as a compilation target for languages that want certified
resource bounds, witness-generation IRs among them. Programs carry machine-checked
upper bounds on running time and on allocated memory.

## Files

| File | Contents |
|---|---|
| `Core.lean` | Syntax (`Stmt`), cost models (`CostModel`, `CostModel.Admissible`), big-step cost semantics (`Exec`), determinism, framing (`Writes`/`Touches`), the unit-time theorems, the partial static clock (`staticTime?`), peak memory ≤ running time (`Exec.peak_le_time`), well-formed states and absolute live memory (`State.WellFormed`, `State.liveMem`), reference interpreter (`run`) and its soundness |
| `Render.lean` | Pretty-printer: `Stmt.render`/`Stmt.renderString` emit the `mem.`-qualified assembly dialect used for the listings in this document |
| `Triple.lean` | Upper-bound Hoare triples (`Triple`), one rule per instruction, `seq`/`conseq`/`ifNZ`, the measure-indexed loop rule `whileNZ_measure`, frame rules; time-only and space-only judgments (`TimeTriple`/`SpaceTriple`) with the same rule set, recombinable via determinism (`TimeTriple.and_space`) |
| `Builder.lean` | Surface syntax: builder monad with fresh register/buffer naming, expression compiler (`Exp`), structured `if_`/`while_`, typed buffer handles (`Buf`), product types (`PairR`, `PairBuf`) |
| `Examples.lean` | Worked examples with full proofs, builder ↔ core checks, interpreter demos |
| `Liveness.lean` | Backward liveness analysis (`Stmt.liveBefore`), inferred peak register pressure (`Stmt.regPeak`/`Stmt.regPeak₀`), the live-ins + writes bound, the combined buffers-plus-registers judgment (`SpaceBound`), and `Exec.straight_total_footprint_le` |
| `W64.lean` | Fixed 64-bit surface: namespace `Caliper64` of reducible `abbrev`s pinning `w := 64` |

## Scope

This repository contains the machine: syntax, cost semantics, program logic,
builder surface, renderer, and the fixed 64-bit surface `Caliper64`. Layers built
on top of it, such as a compiler targeting the machine or a gadget library, live in
the projects that depend on this one; claims about those layers are stated and
proved there, not here.

## Design decisions

### Buffers instead of a RAM

The machine has an unbounded supply of named, independent buffers rather than one
flat address space. Aliasing is impossible by construction: buffer names are part
of the *syntax*, never runtime values, so "these two data structures don't
overlap" is `b₁ ≠ b₂` on `ℕ`, which is decidable. The separation theory is the
one-line lemma `bufs_setBuf_ne`, and the frame rules (`Triple.frame_reg` /
`Triple.frame_buf`) have syntactic, decidable side conditions (`Stmt.Writes` /
`Stmt.Touches`, closed by `simp`). Example 5 (`SumTwo`) composes two subroutine
calls this way; no state-separation proofs appear anywhere.

Buffer *lengths* are fully dynamic; only the set of buffer names is static, and
the builder allocates names automatically.

### What "unit time" means

Costs come from a `CostModel`: a table indexed by the *instruction*, never by the
state. `Exec C c s s' t d p` charges each instruction its table entry, so:

- `Exec.straight_time_eq`: a branch-free program's running time is a syntactic
  constant. The proved statement is data-independence of the *abstract time
  counter*: every input yields the same `t`. It does not cover memory-access
  addresses, allocation sizes, memory profiles, or faults; see "What is NOT
  proved".
- One deliberate exception: acquiring live memory is charged per word.
  `memAlloc`(`I`) costs `C.memAlloc + cap * C.allocPerWord`, i.e. a base (0 in
  both shipped tables, since static names and explicit capacities admit an
  arena/bump allocator) plus at least one tick per word acquired, so no
  instruction can acquire `n` words in `o(n)` time. For `memAllocI` the capacity
  is an immediate, so static pricing still applies; the dynamic `memAlloc` reads
  its capacity from a register, so its time is data-dependent and it is excluded
  from `Stmt.Straight`, like a loop. The consequence is `Exec.peak_le_time`: in
  any model with `1 ≤ C.allocPerWord` every execution satisfies `p ≤ t`, so one
  time certificate bounds both resources. The register file has its own static
  analogue (`Stmt.Straight.regPeak₀_le`, and the combined
  `Exec.straight_total_footprint_le`).
- `Stmt.staticTime?` is the safe way to quote a static time: `some n` iff the code
  is straight-line with static time `n` (`staticTime?_eq_some`), in which case
  every execution takes exactly `n` (`Exec.staticTime?_time_eq`); `none` for
  anything containing `ifNZ`/`whileNZ` or a dynamic `memAlloc`. The raw
  `staticTime` returns 0 on loops and under-reports the dynamic `memAlloc`, so it
  is meaningful only under a `Stmt.Straight` proof, or, for branching but loop-free
  code, as the upper bound `Exec.time_le_staticTime_of_loopFree`.
- Bounds proved for a generic `C` instantiate to any concrete table:
  `CostModel.unit` (all 1) or `CostModel.cycles` (a rough modern-CPU latency
  table). The *shape* of the machine guarantees state-independence, the *table*
  calibrates it.
- Genericity cuts both ways: a degenerate table with a zero entry makes cost
  claims vacuous, since a model that prices real work at zero certifies any
  program under any budget. `CostModel.Admissible` requires every entry pricing an
  instruction to be ≥ 1, including the per-op `un`/`bin` entries and
  `allocPerWord`; both shipped tables are proved admissible. Two entries are
  exempt, both instances of free-is-free: `memFree` (a release's work was priced
  into the acquisition that created the buffer) and the alloc *base* `memAlloc`,
  which needs no bound because `allocPerWord` already keeps the full acquisition
  charge ≥ 1 per word. Under an admissible model `Exec.peak_le_time` applies
  through `Exec.peak_le_time_admissible`.

Consequences for the instruction set:

- Memory is *reserved*, not initialised: `memAlloc`/`memAllocI` reserve capacity
  for `n` words, an allocation without `memset`. Reads are only allowed below the
  filled length, so uninitialised capacity is unobservable and initialisation is
  paid for by the pushes and stores that perform it.
- `memPush` requires free capacity, a proof obligation like the in-range obligation
  of `memLoad`, and is therefore worst-case unit time: no doubling, no amortisation
  anywhere in the machine. A growable vector is a *library* on top, its realloc-copy
  loop costing what it visibly costs.
- `whileNZ` guards are *statements*, not expressions: evaluating a loop condition
  costs emitted instructions, never free side-computation.
- Words are `BitVec w` (fixed at 64 by the `Caliper64` surface); all arithmetic
  wraps, mirroring the u64 sort of typical source IRs.

### Upper bounds, not exact times; memory as a (net, peak) profile

`Triple C P c Q T D M` is total correctness plus `t ≤ T` (time), `d ≤ D` (net
live-memory change, signed) and `p ≤ M` (peak live-memory growth). Exhibiting the
underlying `Exec` derivation also proves memory safety: out-of-range accesses have
no derivation, since the `memLoad`/`memStore` rules demand an in-range proof.

Memory is not an allocation counter; memory gets reused. And "the memory" of a
program is two summands, quoted as one total (`SpaceBound`, `Liveness.lean`):

    total peak memory = dynamic buffer peak + static register peak

The register file *is* memory; register words are as physical as buffer words.
What differs is the accounting, and the split follows the information: buffer
contents are runtime information (lengths are dynamic, indices are data), so
buffer capacity is metered dynamically by the cost semantics; register lifetimes
are static information (registers are statically named, never dynamically
indexed), so the register footprint is a compile-time constant of the code, the
inferred peak live-register count `Stmt.regPeak₀`. Nothing about the split makes
registers cheaper; it makes their accounting exact without runtime instructions.
The dynamic-side principle, in one paragraph:

> Acquiring a word of buffer capacity costs one step, and that per-word charge
> prices the word's whole lifetime, creation and eventual destruction; there is no
> per-object base, since buffer names are static and capacities explicit, so an
> arena/bump allocator serves them. Holding it is free. Releasing it is free.

Dynamic live memory is the sum of reserved buffer capacities:
`memAlloc`/`memAllocI` charge `newCap - oldCap`, only `memFree` credits, and
push/pop move the fill level inside capacity already paid for. Releasing is free
in *time* as well (`C.memFree = 0` in both tables): a release only ever shrinks
the footprint, and every release matches a unique earlier acquisition whose
per-word charge covers creation and destruction. That is the only split stable
across real allocators, since a buffer's teardown (freelist push, deferred
coalescing, `munmap`) is bounded by size-linear work already paid at its
`memAlloc`. A release with no matching acquisition, e.g. a `mem.free` of a
never-acquired buffer name, is statically detectable and elidable by a backend.
Profiles compose like high-water marks:

    seq:  net = d₁ + d₂        peak = max p₁ (d₁ + p₂)

so a block with net 0 contributes its peak once, not once per occurrence. The
`ScratchLoop` example allocates a one-slot scratch buffer, runs `n` iterations
that each push and pop a word inside it, and frees it: proved net 0 and peak 1
word, independent of `n`, where an allocation counter would report `n`. The
register-side counterpart is static: `ScopedSumSq` (`3² + 4²`) names five
registers and the analysis infers peak 2, since each stage's scratch is dead the
moment its `mul` consumes it.

Inference is what keeps the register summand tight. Explicit alloc/free brackets
around register lifetimes, the obvious alternative, can only over-approximate a
live range: `SumBuf` uses 6 registers and never releases one, so both accountings
agree at `0 + 6 = 6` (`SumBuf.total_space`), but `ScopedSumSq`'s brackets would
certify 3 (stage-1 result, stage-2 scratch and stage-2 result coexist as *names*)
where inference gives `0 + 2 = 2` (`ScopedSumSq.total_space`), and the
array-of-pairs demo, whose builder temporaries are never released, drops from 22
(4 buffer words + 18 register names) to `4 + 3 = 7`.

Invariants `0 ≤ p` and `d ≤ p` hold always; code acquiring no buffer capacity has
`d ≤ 0 ∧ p ≤ 0` (`allocFree_space`, which allows `memFree`, as it only shrinks the
footprint); and `p ≤ t` in any model with `1 ≤ allocPerWord`
(`Exec.peak_le_time`), so a time bound subsumes the buffer-peak bound. The
register side has the static analogue `Stmt.Straight.regPeak₀_le`: peak register
pressure ≤ live-ins + unit-model static time. The two bounds do not each consume a
running time of their own: on straight code the instructions covering the buffer
words (per-word allocation charges) and those covering the register slots
(register-writing leaves) are disjoint, so buffer peak + register peak ≤ live-ins
+ `t` for the *single* running time `t` (`Exec.straight_total_footprint_le`).

These indices are anchored to *absolute* live memory, not to an arbitrary
baseline. `State.WellFormed` (every buffer's fill within its reserved capacity,
finitely many buffers reserved) holds for `State.init` and is preserved by every
execution (`Exec.wellFormed_preserved`), which rules out adversarial states with
phantom capacity, e.g. a fabricated `caps b` that a `memFree` could turn into
credit funding a huge allocation at certified peak 0. Over such states the
absolute footprint `State.liveMem` changes by exactly `d` (`Exec.liveMem_eq`), a
free credits only genuinely live capacity (`Exec.memFree_credit_le`), and every
state the execution passes through stays within `p` of the start
(`Exec.reaches_liveMem_le_peak`, `Exec.liveMem_le_peak`), so `p` is a true
high-water mark on physical memory.

Keep the two readings apart: a code fragment's quoted peak `p` is growth over its
start state, which is what makes Triple-level profiles compose as relative
high-water marks, whereas the `State.WellFormed`/`liveMem` statements anchor the
same indices to physical live memory over reachable states. Quote the absolute
form for "this program never holds more than X words" and the relative form for
"this fragment adds at most X words". Either way the user-facing total goes
through `SpaceBound`: a buffer-side `SpaceTriple` plus the static `regPeak₀`,
summed, so a buffers-only figure can never masquerade as "the memory". Register
*values* are framed by `Stmt.Writes`, as always.

On lowering: the inferred live ranges are exactly what a backend colors.
`Stmt.regPeak₀` bounds the number of simultaneously live registers at any program
point, so interval-coloring those ranges renames the unboundedly many fresh names
onto `regPeak₀` physical slots; the certified static peak *is* the frame size of a
RISC-V lowering's register file. The claim is sound for arbitrary code, including
hand-written `Stmt`: liveness is computed from the reads that actually occur, so a
register stays live exactly as long as some later instruction may read it. What
inference costs is precision on loops, since the `whileNZ` case widens by the
loop's whole use set instead of iterating to a fixpoint.

The loop rule `Triple.whileNZ_measure` takes an invariant indexed by a
remaining-iterations budget `k`; time is linear in `k`, and both memory bounds
have the form `base + k · max (Dg + Db) 0`, with `max` against 0 because the loop
may exit early and fewer iterations free less. When the per-iteration net
`Dg + Db ≤ 0`, the peak is independent of the trip count.

Time and memory bounds are also independently provable: `TimeTriple` bounds only
the running time and `SpaceTriple` only the (net, peak) pair, each with the full
rule set, so a time proof carries no memory algebra and vice versa. The `Drain`
example has a trip-count-independent space bound even though no uniform time bound
exists for it. Since the machine is deterministic, separately proved judgments
recombine into a full `Triple` (`TimeTriple.and_space`).

#### The static register metric, in brief

`Liveness.lean` implements the register summand. `Stmt.liveBefore c after`
over-approximates the registers whose values may still be read (structural
recursion, no fixpoint), and `Stmt.regPeak c after` bounds the number of registers
simultaneously live at any program point; `Stmt.regPeak₀` is the whole-program
peak with nothing live at exit, i.e. the frame size a lowering needs. The main
theorem `Stmt.regPeak_le_card_liveBefore_add_writesTotal` bounds the peak by
live-ins plus register-writing instructions, whence `Stmt.Straight.regPeak₀_le`
for straight-line code and the disjointness theorem
`Exec.straight_total_footprint_le`. `SpaceBound` packages
buffer-`SpaceTriple`-plus-`regPeak₀` as the total, with instances for the example
programs.

### Executable

`run C fuel c s` is a fuel-based reference interpreter; `run_sound` proves anything
it returns is a genuine `Exec` derivation with the same costs, so `#eval` numbers
are instances of the proved bounds (the examples check this with `#guard_msgs`).

`run` is a reference semantics, not a performance-realizing implementation. Its
`State` maps registers and buffer names through Lean functions, so every `setReg`
stacks another closure and lookups walk the chain; the interpreter's own
wall-clock time and heap usage are unrelated to the abstract cost `t` and profile
`(d, p)` it computes. A performant runner would be a separate artifact with its own
refinement proof against `Exec`.

### Ergonomics

Programs can be written against the raw constructors (assembly-flavoured, what
proofs are stated over) or through `Builder.lean`: a monad with
`freshReg`/`freshBuf`, compound expressions (`x + y * z` compiling through fresh
temporaries), `while_`/`if_`, and subroutines as ordinary Lean functions.
`freshReg` is a pure name counter: naming a register emits no code and costs
nothing, and the register file's footprint is the statically inferred live peak, so
there is no scoping ceremony and no lifetime to declare. At the surface, buffers
are the newtype `Buf w`, produced only by `Mem.alloc` (dynamic capacity) or
`Mem.allocI` (immediate capacity, statically priced); reads, writes, pushes, pops,
length and free are methods on the handle (`b.load i`, `b.store i e`, `b.push e`,
`b.pop`, `b.len`, `b.free`). In the core both `Reg` and `BufId` are `ℕ`
(numeral-friendly proof goals), so the wrapper is what stops a buffer handle being
confused with a register or an index. Builder output is checked equal to the
hand-written core syntax in the examples, so the sugar adds nothing to the trusted
surface. Subroutine *specs* are ordinary Lean theorems about the generated code
(`SumBuf.spec`), reused at every call site.

Generated programs are inspectable through the pretty-printer (`Stmt.render`,
`Render.lean`), which prints the machine's assembly dialect: memory instructions
carry the `mem.` qualifier, since Lean identifiers cannot contain dots, and
`whileNZ` prints as a `loop { … }` whose guard ends in `bifz r<c>` (break-if-zero
on the verdict register). The hand-written buffer-summing program `SumBuf.code`
renders as follows, pinned in `Examples.lean` by `#guard_msgs`; the builder version
`sumB` emits exactly this program:

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

The core stays generic in the word size `w`, but for practical use `w = 64`, the
word size of the intended backends. `W64.lean` provides the namespace `Caliper64`:
reducible `abbrev`s fixing `w := 64` for the types and entry points a program or
spec author touches (`Word`, `Stmt`, `State`, `State.init`, `Exec`, `run`,
`Triple`, `TimeTriple`, `SpaceTriple`, `Build`, `Exp`, `Buf`, `build`). Import
`Caliper.W64` and write against `Caliper64`; because the abbreviations are
reducible, every generic theorem and proof rule applies definitionally. Names that
infer `w` from their arguments (the `Build` combinators, the `Triple` rules,
`CostModel`, `Reg`, `BufId`) are used from `Caliper` unchanged.

## The compilation contract: why DSL cost `n` means `c · n` CPU time

The guarantee this machine is designed around is not a statement about Turing
machines. It is: every `Stmt` instruction is implementable in a constant number of
machine instructions on a 64-bit CPU, so an `Exec` derivation of cost `t` (unit
model) corresponds to a real execution of at most `c · t` cycles, with `c` the
maximum over the per-instruction table.

That claim is relative to the built word width `w`: one `w`-word operation is a
constant number of machine operations *for the `w` the code was built at*. The
core is generic in `w`, and nothing stops instantiating it at a million-bit word,
but that is a different machine, whose "unit" add is a million-bit add and whose
`c` is correspondingly enormous. The claims of this document are therefore about
the fixed 64-bit surface `Caliper64`: words are exactly `u64`, downstream users pin
`w = 64`, and the table below is a table about 64-bit hardware.

Since every `Exec` rule charges a syntactic constant and the table has a dozen
entries, the trusted argument is a per-instruction inspection:

| Instruction | Real implementation | Cost |
|---|---|---|
| `imm`, `mov` | load-immediate / register move | 1 instr |
| `un`, `bin` | one ALU op (`udiv`/`umod` ≈ 20–40 cycles, a *constant*, tabulated in `CostModel.cycles`) | 1 instr |
| `bin .mulhi` | high word of the widening multiply: `MULHU` (RISC-V M, required by the RVA application profiles), `UMULH` (AArch64), the `RDX` half of `MUL` (x86-64). With `.mul`, the full `2w`-bit product in 2 instructions | 1 instr |
| `shl`, `shr` | shift + compare/mask for the `≥ w ⇒ 0` convention (x86/ARM mask the amount) | 2–3 instr |
| `memLoad`, `memStore` | one load/store at `base + 8·i`; the in-range proof carried by the `Exec` rule means bounds checks can be elided | 1–2 instr |
| `memLen`, `memPop` | load / decrement of the length field | 1 instr |
| `memAlloc`, `memAllocI` | reserve `8n` bytes without initialising: an arena/bump-allocator pointer bump, since buffer names are static and capacities explicit. Charged `memAlloc + n·allocPerWord` with base 0, i.e. at least a tick per word: an over-provision for the O(1) pointer bump that pays the object's whole lifetime and absorbs lazy page-mapping costs, and the price of the `p ≤ t` theorem | O(1) real, O(n) charged |
| `memFree` | release to the arena: no per-element work for a `u64` buffer, and its O(1) cost was priced into the per-word acquisition charge. A `mem.free` with no matching acquisition is statically detectable and elidable, like `free(NULL)` | O(1) real, 0 charged |
| `memPush` | store at `base + 8·len` plus length increment, capacity proved sufficient: worst-case O(1), no doubling | 1–2 instr |
| `ifNZ`, `whileNZ` guard | test + branch | 2 instr |

The peak-memory bound transfers one summand at a time. Buffers: physical footprint
= sum of reserved capacities = exactly what the dynamic profile charges, up to
allocator metadata and fragmentation (a small constant for the few, long-lived,
word-aligned buffers this machine uses); no shrinking policy or amortization
argument is needed, since capacity changes only at `memAlloc`/`memFree`.
Registers: the file's physical demand is a frame of `regPeak₀` word slots, by
interval-coloring the statically inferred live ranges. On the model side the buffer
identification is backed by the `State.WellFormed`/`State.liveMem` theorems: over
every state reachable from an honest start, `d` is the exact change and `p` a true
high-water mark of the absolute footprint, so "sum of reserved capacities" is a
well-defined quantity the profile really tracks.

Supporting facts, all discharged by the machine's design rather than by proof:

- The syntax of any program mentions finitely many registers and buffer names,
  both known statically. Registers become stack slots (L1-resident) or machine
  registers; each buffer becomes its own `Vec<u64>`. No dynamic name ever needs
  resolving, and the certified peak live count (`Stmt.regPeak₀`), not the number of
  fresh names, is the physical register demand.
- Words are exactly `u64`; no bignum arithmetic can hide inside an instruction
  (this is why the DSL exists instead of measuring Lean's GMP-backed `Nat`).
- No instruction does hidden work the model fails to charge: `memAlloc` reserves
  without initialising precisely so that no hidden `memset` exists, freeing a
  `u64` buffer has no per-element work, and allocation's per-word charge
  over-states the allocator's O(1) reservation.

One honest qualification remains: `c` is uniform over the memory hierarchy, so a
`memLoad` costs the same whether it hits L1 or DRAM. The *count* of memory accesses
is exact; sensitivity to their unit price is a `CostModel` calibration question,
not a soundness one.

## What is NOT proved

The theorems stop at the abstract machine. Stated plainly:

- No verified backend exists. There is no verified lowering from `Stmt` to a
  physical ISA, allocator, or runtime. The compilation contract above is an
  engineering argument, made per-instruction and kept inspectable; it is not a
  theorem.
- Only the Caliper `Stmt` under `Exec` is priced. Programs a higher-level
  language compiles to this machine typically also have other execution engines (a
  reference semantics, an interpreter). The cost theorems price the compiled
  Caliper artifact only, and the ratio between engines is not a constant: a step
  count certified here says nothing numerical about any other engine beyond
  whatever output-equality the compiler's own simulation theorem provides.
- `CostModel` is a parameter, not a fact about hardware. Every theorem is
  generic in `C`. The shipped `.unit` and `.cycles` tables are calibration choices,
  and the `cycles` entries are estimates (`memLoad := 4` assumes an L1 hit,
  `allocPerWord := 1` a cache-line-amortised first touch); no theorem relates them
  to any real chip.
- Abstract states are mathematical functions. `State` maps registers and buffer
  names through functions. That a backend realizes these as stack slots, machine
  registers and per-buffer vectors is part of the same informal contract, made
  credible by the finitely many statically-known names, not proved. Each buffer
  name also carries O(1) descriptor state (pointer, length, capacity) outside the
  word-count metric.
- Total semantics at the edges. `udiv`/`umod` by zero and `memPop` on an empty
  buffer follow the total `BitVec`/`Array` semantics: division by zero yields 0,
  pop on empty is a no-op. A native backend must insert the corresponding checks or
  establish the corresponding preconditions, which is bounded O(1) work per site,
  but that obligation lives in the contract, not in the proofs.
- Allocator realities are outside the metric. Allocator metadata, alignment,
  fragmentation, and code size are not measured. The peak `p` counts reserved
  words, made absolute by the `WellFormed`/`liveMem` theorems, but words-to-bytes,
  headers and padding are the allocator's business.
- Generation-time staging is unpriced. Builder programs, and compilers
  targeting this machine, unroll at *generation* time, so generated code size is
  proportional to their static parameters. The cost theorems price the runtime of
  the generated code; the size itself is visible as the instruction count under the
  unit model, but the generation work is Lean evaluation and carries no bound.
- Time data-independence is not a side-channel proof. `straight_time_eq` proves
  that the abstract time counter is the same on every input. It does not cover
  memory-access addresses (`memLoad b i` costs one unit whatever the data-dependent
  index `i` is), memory profiles, or faults. Allocation sizes do show up in the
  counter, since allocation is charged per word: the dynamic `memAlloc` is
  data-dependent and hence excluded from the straight-line fragment, while
  `memAllocI`'s size is syntactic.

### Trusted base

Checking the theorems requires trusting the Lean kernel plus the three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`). Everything in this repository
is proved without `native_decide`; the pinned example numbers are `rfl`/`#guard_msgs`
evaluations. Downstream projects may additionally rely on `Lean.ofReduceBool` for
their own concrete numerals. `#print axioms <theorem>` is the audit tool.

## Caveats / next steps
- Natural next steps: a performant runner beyond the reference interpreter, and
  refining the cost model toward a concrete backend.
- A `Proc` record bundling `code`/`Pre`/`Post`/`time`/`space`/`spec` would package
  subroutines more tightly; the examples inline this pattern with plain `have`s for
  now.
- Registers in the examples use fixed conventions (callee-clobbered scratch); a
  register-window or parameterized-register discipline is mechanical to add
  (distinctness side conditions close by `decide`).
