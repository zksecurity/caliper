# The Compilation Contract

[Documentation](00-overview.md)

The intended contract is concrete: every `Stmt` instruction is implementable in a constant number of machine instructions on a 64-bit CPU.
The goal is that an `Exec` derivation of cost `t` in the unit model corresponds to a real execution of at most `c · t` cycles,
with `c` the maximum overhead across the instruction set.
This is an implementation argument; there is no verified backend establishing it.

That claim is relative to the built word width `w`: one `w`-word operation is a constant number of machine operations *for the `w` the code was built at*.
The core is generic in `w`, and nothing stops instantiating it at a million-bit word, but that is a different machine, whose "unit" add is a million-bit add and whose `c` is correspondingly enormous.
The claims in this chapter are therefore about the fixed 64-bit surface `Caliper64`: words are exactly `u64`, downstream users pin `w = 64`, and the table below is a table about 64-bit hardware.

We inspect each instruction separately, including the per-word charge for allocation:

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

The peak-memory bound transfers one summand at a time.
Buffers: physical footprint = sum of reserved capacities = exactly what the dynamic profile charges, up to allocator metadata and fragmentation (a small constant for the few, long-lived, word-aligned buffers this machine uses); no shrinking policy or amortization argument is needed, since capacity changes only at `memAlloc`/`memFree`.
Registers: the file's physical demand is a frame of `regPeak₀` word slots, by interval-coloring the statically inferred live ranges.
On the model side the buffer identification is backed by the `State.WellFormed`/`State.liveMem` theorems: over every state reachable from an honest start, `d` is the exact change and `p` a true high-water mark of the absolute footprint, so "sum of reserved capacities" is a well-defined quantity the profile really tracks.

Supporting facts, all discharged by the machine's design rather than by proof:

- The syntax of any program mentions finitely many registers and buffer names, both known statically.
  Registers become stack slots (L1-resident) or machine registers; each buffer becomes its own `Vec<u64>`.
  No dynamic name ever needs resolving, and the certified peak live count (`Stmt.regPeak₀`), not the number of fresh names, is the physical register demand.
- Words are exactly `u64`; no bignum arithmetic can hide inside an instruction (this is why the DSL exists instead of measuring Lean's GMP-backed `Nat`).
- No instruction does hidden work the model fails to charge: `memAlloc` reserves without initialising precisely so that no hidden `memset` exists, freeing a `u64` buffer has no per-element work, and allocation's per-word charge over-states the allocator's O(1) reservation.

One honest qualification remains: `c` is uniform over the memory hierarchy, so a `memLoad` costs the same whether it hits L1 or DRAM.
The *count* of memory accesses is exact; sensitivity to their unit price is a `CostModel` calibration question, not a soundness one.

The formal definitions are in [Machine Model](01-machine-model.md#execution-judgments) and [Memory](02-memory.md).
The distinction between the machine-checked bounds and this implementation argument is stated in [Limitations](05-limitations.md).
