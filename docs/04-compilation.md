# The Compilation Contract

[Documentation](00-overview.md)

The intended contract is concrete: every `Stmt` instruction is implementable in a constant number of machine instructions on a 64-bit CPU.
The goal is that an `Exec` derivation of cost `t` in the unit model corresponds to a real execution of at most `c · t` cycles,
with `c` the maximum overhead across the instruction set.
This is an implementation argument; there is no verified backend establishing it.

That claim is relative to the built word width `w`: one `w`-word operation is a constant number of machine operations *for the `w` the code was built at*.
The core is generic in `w`, and nothing stops instantiating it at a million-bit word, but that is a different machine, whose "unit" add is a million-bit add and whose `c` is correspondingly enormous.
The claims in this chapter are therefore about the fixed 64-bit surface `Caliper64`: words are exactly `u64`, downstream users pin `w = 64`, and the table below is a table about 64-bit hardware.

We inspect each instruction separately, including the per-word charge for resizing:

| Instruction | Real implementation | Cost |
|---|---|---|
| `imm`, `mov` | load-immediate / register move | 1 instr |
| `un`, `bin` | one ALU op (`udiv`/`umod` ≈ 20–40 cycles, a *constant*, tabulated in `CostModel.cycles`) | 1 instr |
| `bin .mulhi` | high word of the widening multiply: `MULHU` (RISC-V M, required by the RVA application profiles), `UMULH` (AArch64), the `RDX` half of `MUL` (x86-64). With `.mul`, the full `2w`-bit product in 2 instructions | 1 instr |
| `shl`, `shr` | shift + compare/mask for the `≥ w ⇒ 0` convention (x86/ARM mask the amount) | 2–3 instr |
| `memLoad`, `memStore` | one load/store at `base + 8·i`; the in-range proof carried by the `Exec` rule means bounds checks can be elided | 1–2 instr |
| `memLen`, `memPop` | load / decrement of the length field | 1 instr |
| `memResize`, `memResizeI` to `n > 0` | `realloc` to `8n` bytes without initialising the new words: truncate the length to `min(len, n)`, then reserve (in place when the arena region has room, otherwise allocate, copy the at most `n` surviving words, release the old region). Charged `memResize + n·allocPerWord` with base 0, i.e. at least a tick per word of the new capacity: this covers the copy, over-provisions an in-place pointer bump, pays the object's whole lifetime, absorbs lazy page-mapping costs, and is the price of the `p ≤ t` theorem | O(n) worst case real, O(n) charged |
| `memResizeI b 0` (free) | release to the arena: set the length to 0, no per-element work for a `u64` buffer, and its O(1) cost was priced into the per-word charges of the resizes that acquired the capacity. A free of a never-acquired buffer is statically detectable and elidable, like `free(NULL)` | O(1) real, base (0) charged |
| `memPush` | store at `base + 8·len` plus length increment, capacity proved sufficient: worst-case O(1), no doubling | 1–2 instr |
| `ifNZ`, `whileNZ` guard | test + branch | 2 instr |

The peak-memory bound transfers one summand at a time.
Buffers: physical footprint = sum of reserved capacities = exactly what the dynamic profile charges, up to allocator metadata and fragmentation (a small constant for the few, long-lived, word-aligned buffers this machine uses); this identification counts live reserved words, so under a non-reclaiming bump arena a copying realloc leaves its old region unused and the physical footprint can reach about twice the certified peak (a reclaiming allocator, or in-place growth, avoids this); no shrinking policy or amortization argument is needed inside the backend, since capacity changes only at explicit `memResize`/`memResizeI` instructions (amortized growth, as in the corpus `GrowVec`, is a library-level argument over those explicit resizes).
Registers: the file's physical demand is a frame of `regPeak₀` word slots, by interval-coloring the statically inferred live ranges.
On the model side the buffer identification is backed by the `State.WellFormed`/`State.liveMem` theorems: over every state reachable from an honest start, `d` is the exact change and `p` a true high-water mark of the absolute footprint, so "sum of reserved capacities" is a well-defined quantity the profile really tracks.

Supporting facts, all discharged by the machine's design rather than by proof:

- The syntax of any program mentions finitely many registers and buffer names, both known statically.
  Registers become stack slots (L1-resident) or machine registers; each buffer becomes its own `Vec<u64>`.
  No dynamic name ever needs resolving, and the certified peak live count (`Stmt.regPeak₀`), not the number of fresh names, is the physical register demand.
- Words are exactly `u64`; no bignum arithmetic can hide inside an instruction (this is why the DSL exists instead of measuring Lean's GMP-backed `Nat`).
- No instruction does hidden work the model fails to charge: a resize reserves without initialising precisely so that no hidden `memset` exists, freeing a `u64` buffer has no per-element work, and the per-word charge on the new capacity covers a realloc's copy of the surviving prefix.

One honest qualification remains: `c` is uniform over the memory hierarchy, so a `memLoad` costs the same whether it hits L1 or DRAM.
The *count* of memory accesses is exact; sensitivity to their unit price is a `CostModel` calibration question, not a soundness one.

## The Realloc Contract

A backend realizes `memResize b n`/`memResizeI b n` as a `realloc` of buffer `b` to `n` words with the exact semantics of `State.resizeBuf`: the first `min(len, n)` words survive unchanged, the length becomes `min(len, n)`, the capacity becomes `n`, words beyond the length are unobservable, and no other buffer is affected.
Equivalently, truncate the length to `n`, then reserve capacity `n` (`Vec::truncate` followed by `Vec::reserve_exact`/`shrink_to` in Rust, or `realloc` in C with the length kept in the buffer descriptor).
The work may be proportional to `n` (a copy of the surviving words), which the `n · allocPerWord` charge pays for; `n = 0` releases the buffer.
The transient space of a copying realloc, old and new region live together, is inside the certified profile: a resize's peak is the whole new capacity `n` above the footprint before it, so a backend may always copy.
The RV64 test lowering (`CaliperTest/RV64.lean`) realizes it in place over preassigned per-buffer regions: `len ← min(len, n)` with one compare-and-branch, checked against the reference interpreter by the differential vectors, including a doubling vector (`grow_vec`) and a truncating one (`resize_shrink`).

The formal definitions are in [Machine Model](01-machine-model.md#execution-judgments) and [Memory](02-memory.md).
The distinction between the machine-checked bounds and this implementation argument is stated in [Limitations](05-limitations.md).
