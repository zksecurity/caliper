import Caliper.Corpus.Util
import Caliper.Corpus.Memory
import Caliper.Corpus.Arith
import Caliper.Corpus.Sort

/-!
# The test corpus

A set of small, complete programs exercising every instruction class of the
machine, each pinned against the reference interpreter (`#guard_msgs` on
concrete inputs) and the static register-liveness analysis (`Stmt.regPeak₀`),
with proved resource bounds for a representative few. The corpus doubles as
the source of the differential RV64 test vectors (`CaliperTest/`, not part of
this library).

| Program | File | Highlights | Proved bound |
| --- | --- | --- | --- |
| `Memcpy` | `Corpus/Memory.lean` | dynamic `memAlloc`, `memPush` | `Triple`: linear time, memory = payload |
| `Memset` | `Corpus/Memory.lean` | in-place `memStore` loop | pins |
| `Reverse` | `Corpus/Memory.lean` | two-pointer swap, compound guard | pins |
| `StackSum` | `Corpus/Memory.lean` | `memPop`/`memFree`, negative net | pins |
| `DotProduct` | `Corpus/Arith.lean` | two-buffer fold | `Triple`: linear time, zero memory |
| `Gcd` | `Corpus/Arith.lean` | value-measure loop, builder comparator | `Triple`: `Nat.gcd` spec, linear-in-`b` time |
| `BinExp` | `Corpus/Arith.lean` | square-and-multiply, `ifNZ`/`skip` | pins |
| `Popcount` | `Corpus/Arith.lean` | shift/mask loop | pins |
| `DivMod` | `Corpus/Arith.lean` | `udiv`/`umod`/`mulhi`, div-by-zero | `staticTime?` pins |
| `BitTricks` | `Corpus/Arith.lean` | `ule`/`neg`/`not`/`shl`/`or`/… | `staticTime?` pins |
| `InsertionSort` | `Corpus/Sort.lean` | nested data-dependent loops | pins (3 inputs, 3 times) |
| `MatMul3` | `Corpus/Sort.lean` | builder surface, triple nesting | pins |

Instruction-class coverage: `imm` (throughout), `mov` (`Gcd`,
`InsertionSort`), all four `un` ops (`not`/`neg` in `BitTricks`,
`isZero` in `BitTricks`, `isNonZero` in the loop guards), all fourteen `bin`
ops (`add`/`sub`/`mul` throughout, `mulhi`/`udiv`/`umod`/`eq` in `DivMod`,
`umod` in `Gcd`, `and`/`shr` in `Popcount`/`BinExp`, `or`/`xor`/`shl`/`ne`/
`ule` in `BitTricks`, `ult` in every counting guard), `memAlloc` (`Memcpy`),
`memAllocI` (`MatMul3`), `memFree` (`StackSum`), `memLoad`/`memStore`
(`Reverse`, `InsertionSort`, …), `memPush` (`Memcpy`, `MatMul3`), `memPop`
(`StackSum`), `memLen` (`Memcpy`, `Memset`, `StackSum`, `InsertionSort`),
`ifNZ` (`BinExp`, `InsertionSort`), `whileNZ` (all loops), `skip` (the else
branches of `BinExp` and `InsertionSort`).
-/
