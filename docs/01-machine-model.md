# Machine Model

[Documentation](00-overview.md)

Words have a fixed width $w$; register and buffer names are natural numbers.
The names occur in the program syntax, so we know which registers and buffers a program can use before running it.
The basic definitions in [Core.lean](../Caliper/Core.lean) are:

```lean
abbrev Reg := ℕ

abbrev BufId := ℕ

abbrev Word (w : ℕ) := BitVec w
```

The Lean blocks in this chapter are source excerpts from namespace `Caliper`; comments are omitted.
They use the surrounding word-width parameter `w` where it is implicit.

## Buffers Instead of a RAM

The machine has an unbounded supply of named, independent buffers rather than one flat address space.
Aliasing is impossible by construction: buffer names are part of the *syntax*, never runtime values, so "these two data structures don't overlap" is `b₁ ≠ b₂` on `ℕ`, which is decidable.
The separation theory is the one-line lemma `bufs_setBuf_ne`, and the frame rules (`Triple.frame_reg` / `Triple.frame_buf`) have syntactic, decidable side conditions (`Stmt.Writes` / `Stmt.Touches`, closed by `simp`).
Example 5 (`SumTwo`) composes two subroutine calls this way; no state-separation proofs appear anywhere.

Buffer *lengths* are fully dynamic; only the set of buffer names is static, and the builder allocates names automatically.

## State and Instructions

A state records register values, buffer contents, reserved capacities, and the next position on the random tape:

```lean
structure State (w : ℕ) where
  tapePos : ℕ := 0
  regs : Reg → Word w
  bufs : BufId → Array (Word w)
  caps : BufId → ℕ

def State.init (w : ℕ) : State w where
  regs _ := 0
  bufs _ := #[]
  caps _ := 0
```

`bufs b` contains the filled prefix; `caps b` is the reserved capacity.
Reserving capacity does not initialize its words.
We can only read words which have subsequently been filled.
The tape cursor advances when we execute `rand`; ordinary instructions cannot read or change it.

The complete statement type is small enough to read directly:

```lean
inductive Stmt (w : ℕ) where
  | skip
  | seq (c₁ c₂ : Stmt w)
  | imm (d : Reg) (v : Word w)
  | rand (d : Reg)
  | mov (d a : Reg)
  | un (op : UnOp) (d a : Reg)
  | bin (op : BinOp) (d a b : Reg)
  | memResize (b : BufId) (n : Reg)
  | memResizeI (b : BufId) (n : ℕ)
  | memLen (d : Reg) (b : BufId)
  | memLoad (d : Reg) (b : BufId) (i : Reg)
  | memStore (b : BufId) (i src : Reg)
  | memPush (b : BufId) (src : Reg)
  | memPop (b : BufId)
  | ifNZ (c : Reg) (thn els : Stmt w)
  | whileNZ (guard : Stmt w) (c : Reg) (body : Stmt w)
deriving Repr, Inhabited, BEq
```

`memResize` reads a capacity from a register; `memResizeI` carries it in the syntax.
Both are the one capacity instruction of the machine, a realloc:

```lean
def State.resizeBuf (s : State w) (b : BufId) (n : ℕ) : State w :=
  { s with bufs := fun b' => if b' = b then (s.bufs b).take n else s.bufs b',
           caps := fun b' => if b' = b then n else s.caps b' }
```

Growing keeps the contents, shrinking keeps the prefix that fits, and a resize to 0 frees the buffer; every other buffer, register and the tape cursor are unchanged, and the fill stays within the capacity by construction.
Acquiring a fresh buffer is a resize of an empty one; the builder's `Mem.alloc`/`Mem.allocI`/`Buf.free` are derived helpers emitting these instructions.
The loop guard is itself a statement, so evaluating it costs instructions.
`c₁ ;; c₂` is notation for `Stmt.seq c₁ c₂`.

## What "Unit Time" Means

Costs come from a `CostModel`: a table indexed by the *instruction*, never by the state.
`Exec C tape c s s' t d p` charges each instruction its table entry, so:

- `Exec.straight_time_eq`: a branch-free program's running time is a syntactic constant.
  The proved statement is data-independence of the *abstract time counter*: every input yields the same `t`.
  It does not cover memory-access addresses, allocation sizes, memory profiles, or faults; see [Limitations](05-limitations.md).
- One deliberate exception: resizing is charged per word of the *new* capacity.
  `memResize`(`I`) to capacity `n` costs `C.memResize + n * C.allocPerWord`, i.e. a base (0 in both shipped tables, since static names and explicit capacities admit an arena/bump allocator) plus at least one tick per word of the new capacity, which also covers a realloc copying up to `n` surviving words; so no instruction can acquire `n` words in `o(n)` time.
  The free `memResizeI b 0` costs only the base and credits the whole capacity.
  The memory profile of a resize is net `newCap - oldCap` and peak `newCap`, since a copying realloc holds old and new at once; `newCap · allocPerWord ≥ newCap` keeps the peak within the time.
  For `memResizeI` the capacity is an immediate, so static pricing still applies; the dynamic `memResize` reads its capacity from a register, so its time is data-dependent and it is excluded from `Stmt.Straight`, like a loop.
  The consequence is `Exec.peak_le_time`: in any model with `1 ≤ C.allocPerWord` every execution satisfies `p ≤ t`, so one time certificate bounds both resources.
  The register file has its own static analogue (`Stmt.Straight.regPeak₀_le`, and the combined `Exec.straight_total_footprint_le`).
- `Stmt.staticTime?` is the safe way to quote a static time: `some n` iff the code is straight-line with static time `n` (`staticTime?_eq_some`), in which case every execution takes exactly `n` (`Exec.staticTime?_time_eq`); `none` for anything containing `ifNZ`/`whileNZ` or a dynamic `memResize`.
  The raw `staticTime` returns 0 on loops and under-reports the dynamic `memResize`, so it is meaningful only under a `Stmt.Straight` proof, or, for branching but loop-free code, as the upper bound `Exec.time_le_staticTime_of_loopFree`.
- Bounds proved for a generic `C` instantiate to any concrete table: `CostModel.unit` (all 1) or `CostModel.cycles` (a rough modern-CPU latency table).
  The *shape* of the machine guarantees state-independence, the *table* calibrates it.
- Genericity cuts both ways: a degenerate table with a zero entry makes cost claims vacuous, since a model that prices real work at zero certifies any program under any budget.
  `CostModel.Admissible` requires every entry pricing an instruction to be ≥ 1, including the per-op `un`/`bin` entries and `allocPerWord`; both shipped tables are proved admissible.
  One entry is exempt, free-is-free: the resize *base* `memResize`, which needs no bound because `allocPerWord` already keeps the full resize charge ≥ 1 per word of new capacity; the only zero-time resize is the zero-capacity one, the free, whose release work was priced into the acquisitions that created the buffer.
  Under an admissible model `Exec.peak_le_time` applies through `Exec.peak_le_time_admissible`.

The cost table and its unit-cost instance are defined as follows:

```lean
structure CostModel where
  imm : ℕ := 1
  rand : ℕ := 1
  mov : ℕ := 1
  un : UnOp → ℕ := fun _ => 1
  bin : BinOp → ℕ := fun _ => 1
  memResize : ℕ := 0
  allocPerWord : ℕ := 1
  memLen : ℕ := 1
  memLoad : ℕ := 1
  memStore : ℕ := 1
  memPush : ℕ := 1
  memPop : ℕ := 1
  branch : ℕ := 1

def CostModel.unit : CostModel := {}
```

Observe that `memResize` is the resize *base*; `allocPerWord` supplies the size-dependent charge.
Hence the default table charges one step per word of new capacity, with no base charge, and zero for releasing a buffer (`memResizeI b 0`).

Consequences for the instruction set:

- Memory is *reserved*, not initialised: `memResize`/`memResizeI` set the capacity to `n` words, a realloc without `memset`.
  Reads are only allowed below the filled length, so uninitialised capacity is unobservable and initialisation is paid for by the pushes and stores that perform it.
- `memPush` requires free capacity, a proof obligation like the in-range obligation of `memLoad`, and is therefore worst-case unit time: no doubling, no amortisation anywhere in the machine.
  A growable vector is a *library* on top (`GrowVec` in the corpus), its doubling `memResize` costing what it visibly costs, with the amortized linear bound proved by a potential argument.
- `whileNZ` guards are *statements*, not expressions: evaluating a loop condition costs emitted instructions, never free side-computation.
- Words are `BitVec w` (fixed at 64 by the `Caliper64` surface); all arithmetic wraps, mirroring the u64 sort of typical source IRs.

## Execution Judgments

`Exec C tape c s s' t d p` means that program `c`, starting in state `s` on `tape`, terminates in `s'` with time $t$, net buffer-memory change $d$, and peak buffer-memory growth $p$.
Time is a natural number; the memory indices are integers, since freeing capacity can make the net change negative.

Here are the declaration and its first three rules; the remaining constructors are omitted:

```lean
inductive Exec (C : CostModel) (tape : RandomTape w) : Stmt w → State w → State w → ℕ → ℤ → ℤ → Prop where
  | skip {s} : Exec C tape .skip s s 0 0 0
  | seq {c₁ c₂ s s₁ s₂ t₁ d₁ p₁ t₂ d₂ p₂} :
      Exec C tape c₁ s s₁ t₁ d₁ p₁ → Exec C tape c₂ s₁ s₂ t₂ d₂ p₂ →
      Exec C tape (c₁ ;; c₂) s s₂ (t₁ + t₂) (d₁ + d₂) (max p₁ (d₁ + p₂))
  | imm {d v s} : Exec C tape (.imm d v) s (s.setReg d v) C.imm 0 0
  -- Remaining instruction rules omitted.
```

The `seq` rule explains how costs compose: times and net changes add, while the second program's peak is measured relative to the first program's net change. [Memory](02-memory.md) develops the resulting specifications.
