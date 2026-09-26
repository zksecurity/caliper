import Mathlib.Tactic

/-!
# A unit-cost machine model

A small imperative language whose every instruction runs in constant time, intended
as a compilation target for languages that want certified resource bounds. Programs
carry machine-checked upper bounds on running time and memory. Design rationale, the
lowering contract and the trust boundary are in `docs/00-overview.md`; this module is the
machine.

Buffers, not a RAM: the machine has an unbounded supply of independent, named
buffers, so the only separation fact a proof ever needs is `b₁ ≠ b₂` on buffer
names, decidable over `ℕ` (`bufs_setBuf_ne`). Names are part of the syntax, never
runtime values, so a program cannot alias two buffers; buffer *lengths* are fully
dynamic.

Every constructor other than `seq`/`ifNZ`/`whileNZ` is one instruction priced by a
`CostModel`, a table indexed by the *instruction*, never by the state. That is the
content of "unit time": `straight_time_eq` says a branch-free program's running
time is a syntactic constant. Two consequences for the instruction set:

* A buffer is a zero-initialised array whose length is its only size: there is
  no separate capacity and no reserved-but-unreadable state. `memResize`/
  `memResizeI` set the length realloc-style (growing keeps the contents and appends
  zeros, shrinking keeps a prefix, resizing to 0 frees), and `memLoad`/`memStore`
  require `i < length`. A resize to length `n` is charged
  `C.memResize + n * C.allocPerWord`, at least a tick per word of the new length
  (a realloc copies up to `n` words and zeroes the new ones), so nothing acquires
  `n` words in `o(n)` time and peak memory is bounded by running time
  (`Exec.peak_le_time`). The resize's peak is the whole new length `n`, since old
  and new coexist during a copying realloc; its net is `n - oldLength`.
* No instruction grows a buffer implicitly, so every instruction but a resize is
  worst-case unit time: no doubling, no amortisation anywhere in the machine. A
  growable vector is a library on top (`GrowVec` in `Corpus/GrowVec.lean`), a fill
  register plus a doubling `memResize` costing what it visibly costs.

`Exec C tape c s s' t d p`: from `s`, `c` terminates in `s'` spending `t` time units,
with net live-memory change `d` (signed words) and peak growth `p` above the
starting level. Live memory is the sum of buffer lengths, so stores are
memory-neutral. Registers are outside the dynamic profile: their lifetimes
are static, so the register footprint is the inferred peak `Stmt.regPeak₀`
(`Liveness.lean`). Profiles compose as high-water marks:

    seq:  net = d₁ + d₂        peak = max p₁ (d₁ + p₂)

so a scratch buffer reused across `n` iterations is charged once, not `n` times
(`ScratchLoop` in `Examples.lean`). Always `0 ≤ p` and `d ≤ p` (`peak_nonneg`,
`net_le_peak`); allocation-free code has `d ≤ 0 ∧ p ≤ 0` (`allocFree_space`). Time
is `ℕ`, the memory indices `ℤ`, so `omega` closes the arithmetic. Out-of-range
accesses have no `Exec` derivation, so exhibiting one proves memory safety along
the way.
-/

namespace Caliper

/-- Registers are unbounded in number; the builder allocates them, so a program uses
finitely many and a real compiler would give each one a stack slot. -/
abbrev Reg := ℕ

/-- Buffer names. Static: part of the syntax, never a runtime value. -/
abbrev BufId := ℕ

/-- Machine words. Fixed at `w = 64` by the `Caliper64` surface. -/
abbrev Word (w : ℕ) := BitVec w

/-- An immutable, infinite input tape of words. -/
abbrev RandomTape (w : ℕ) := ℕ → Word w

/-- A fixed tape for deterministic examples. -/
def RandomTape.zero {w : ℕ} : RandomTape w := fun _ => 0

variable {w : ℕ} {tape : RandomTape w}

/-! ## Operations -/

inductive UnOp where
  | not | neg | isZero | isNonZero
deriving DecidableEq, Repr, Inhabited

inductive BinOp where
  | add | sub | mul
  /-- High word of the widening unsigned multiply (`MULHU` on RISC-V M, `UMULH` on
  AArch64, the `RDX` half of `MUL` on x86-64). With `mul` it gives the full `2w`-bit
  product, the primitive field reduction (Goldilocks, Montgomery) needs. -/
  | mulhi
  | udiv | umod
  | and | or | xor | shl | shr
  | eq | ne | ult | ule
deriving DecidableEq, Repr, Inhabited

@[simp] def UnOp.eval : UnOp → Word w → Word w
  | .not, x => ~~~x
  | .neg, x => -x
  | .isZero, x => if x = 0 then 1 else 0
  | .isNonZero, x => if x = 0 then 0 else 1

/-- Shifts by an amount `≥ w` produce `0` (`BitVec` semantics). A backend targeting
x86/ARM, where the shift amount is masked, must emit an explicit mask. -/
@[simp] def BinOp.eval : BinOp → Word w → Word w → Word w
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | .mulhi, x, y => BitVec.ofNat w (x.toNat * y.toNat / 2 ^ w)
  | .udiv, x, y => x / y
  | .umod, x, y => x % y
  | .and, x, y => x &&& y
  | .or, x, y => x ||| y
  | .xor, x, y => x ^^^ y
  | .shl, x, y => x <<< y.toNat
  | .shr, x, y => x >>> y.toNat
  | .eq, x, y => if x = y then 1 else 0
  | .ne, x, y => if x = y then 0 else 1
  | .ult, x, y => if x.toNat < y.toNat then 1 else 0
  | .ule, x, y => if x.toNat ≤ y.toNat then 1 else 0

/-! ## Syntax -/

/-- Statements. The whole language, and the whole surface the cost model has to be
trusted about. Structures, typed values, arrays-of-structs and subroutines are built
on top at *generation* time (`Builder.lean`) and compile to these instructions. -/
inductive Stmt (w : ℕ) where
  /-- No-op. -/
  | skip
  /-- Sequencing, written `c₁ ;; c₂`. -/
  | seq (c₁ c₂ : Stmt w)
  /-- `d ← v` -/
  | imm (d : Reg) (v : Word w)
  /-- Read the next word of the supplied tape into `d`, advancing the tape cursor. -/
  | rand (d : Reg)
  /-- `d ← a` -/
  | mov (d a : Reg)
  /-- `d ← op a` -/
  | un (op : UnOp) (d a : Reg)
  /-- `d ← a op b` -/
  | bin (op : BinOp) (d a b : Reg)
  /-- `b ← realloc(b, regs n)`: set `b`'s length to the register value
  (`State.resizeBuf`): growing keeps the contents and appends zeros, shrinking
  truncates, and a resize to 0 frees. Time is `C.memResize + len * C.allocPerWord`
  with `len` the *runtime* register value (a realloc copies up to `len` words and
  zeroes the new ones), so the time is data-dependent: excluded from
  `Stmt.Straight`, and `staticTime?` returns `none`. Use `memResizeI` for a
  generation-time length. -/
  | memResize (b : BufId) (n : Reg)
  /-- `b ← realloc(b, n)` with the length `n` an immediate in the syntax: same
  semantics as `memResize` at that length, but the charge `C.memResize + n *
  C.allocPerWord` is a pure function of the instruction, so static pricing
  (`Stmt.Straight`, `staticTime`) applies. `memResizeI b 0` is the free: it costs
  only the base `C.memResize` (0 in both shipped tables) and credits the whole
  length.

  Hazard: the immediate is a bare `ℕ`, so unlike `memResize`, whose length comes
  from a `w`-bit register and is `< 2 ^ w`, a `memResizeI` with `n ≥ 2 ^ w` is
  expressible. Every cost and semantics theorem still holds, but a buffer that long
  makes `memLen` read back a wrapped length. Keep immediate lengths `< 2 ^ w`; the
  builder's `Mem.allocI` enforces that bound. -/
  | memResizeI (b : BufId) (n : ℕ)
  /-- `d ← |b|`, the length. It is loaded as `BitVec.ofNat w size`, so it is exact
  only while the size is `< 2 ^ w`; past that it reads back wrapped, reachable only
  through a `memResizeI` immediate length `≥ 2 ^ w`, since register-driven lengths
  are `< 2 ^ w`. -/
  | memLen (d : Reg) (b : BufId)
  /-- `d ← b[i]`; requires `i < |b|`. -/
  | memLoad (d : Reg) (b : BufId) (i : Reg)
  /-- `b[i] ← src`; requires `i < |b|`. -/
  | memStore (b : BufId) (i src : Reg)
  | ifNZ (c : Reg) (thn els : Stmt w)
  /-- `guard; while (c ≠ 0) { body; guard }`. The guard is a *statement* because
  computing a loop condition costs real instructions; as an expression it would
  smuggle in unaccounted work. `c` is the register the guard leaves its verdict in. -/
  | whileNZ (guard : Stmt w) (c : Reg) (body : Stmt w)
deriving Repr, Inhabited, BEq

@[inherit_doc] infixr:60 " ;; " => Stmt.seq

/-! ## Cost model

Per-instruction costs. Every field is a function of the *instruction* only; nothing
here can look at the machine state, which is why running time is data-independent.
The default is the uniform model (everything 1); `cycles` below is a rough
Skylake-ish latency table, and any bound proved generically over `C` instantiates to
both. -/
structure CostModel where
  imm : ℕ := 1
  /-- Abstract cost of consuming one input-tape word. -/
  rand : ℕ := 1
  mov : ℕ := 1
  un : UnOp → ℕ := fun _ => 1
  bin : BinOp → ℕ := fun _ => 1
  /-- Base cost of a resize: a resize to length `n` costs
  `memResize + n * allocPerWord`. 0 in both shipped tables, since static buffer
  names admit an arena/bump allocator. The free, `memResizeI b 0`, costs only this
  base: the released words' teardown was priced by the per-word charges that
  acquired them. `CostModel.Admissible` exempts this base. (The certified peak
  counts live buffer words, not allocator fragmentation: a non-reclaiming arena
  under copying reallocs can use up to about twice the peak.) -/
  memResize : ℕ := 0
  /-- Per-word cost of a resize, charged on the full *new* length (a realloc may
  copy every surviving word and zero every new one). `1 ≤ allocPerWord` makes peak
  memory bounded by running time (`Exec.peak_le_time`). -/
  allocPerWord : ℕ := 1
  memLen : ℕ := 1
  memLoad : ℕ := 1
  memStore : ℕ := 1
  /-- Cost of testing a condition register and taking the branch. -/
  branch : ℕ := 1

/-- Uniform model: every priced entry is 1, so a resize costs one tick per word of
the new length with no base, and a resize to 0 (the free) costs nothing (see
`memResize`). -/
def CostModel.unit : CostModel := {}

/-- A coarse "cycles on a modern out-of-order core" model, here to show that bounds
proved generically over `C` are not tied to the uniform model. -/
def CostModel.cycles : CostModel where
  bin := fun op => match op with
    | .mul | .mulhi => 3
    | .udiv | .umod => 30
    | _ => 1
  memResize := 0  -- no malloc: static buffer names admit an arena/bump allocator
  -- one cycle per word of new length: a cache-line-amortised zeroing store or
  -- copy. Kept ≥ 1 so `Exec.peak_le_time` applies to this table.
  allocPerWord := 1
  memLoad := 4     -- L1 hit
  memStore := 4
  branch := 2     -- mispredict-amortised

/-- Every table entry pricing an instruction is at least one time unit: no
instruction runs for free, and no word of live memory is acquired for free.

The predicate exists because every cost theorem is generic in `C`, and a degenerate
table with a zero entry makes cost claims vacuous: a model pricing real work at zero
certifies any program under any budget, and peak memory can exceed running time.
Under an admissible model every executed instruction other than a zero-length
resize contributes a tick to `t` (`skip` is no instruction and costs nothing), and
the `allocPerWord` field is literally the `1 ≤ C.allocPerWord` hypothesis of `Exec.peak_le_time`. Both shipped tables are
proved admissible (`CostModel.unit.admissible`, `CostModel.cycles.admissible`).

One exemption, free-is-free: the resize *base* `memResize`, since `allocPerWord`
already keeps the full resize charge ≥ 1 per word of new length. The only
zero-time resize is the zero-length one, the free, which acquires nothing and
whose release work was priced into the acquisitions that created the buffer. -/
structure CostModel.Admissible (C : CostModel) : Prop where
  imm : 1 ≤ C.imm
  rand : 1 ≤ C.rand
  mov : 1 ≤ C.mov
  un : ∀ op, 1 ≤ C.un op
  bin : ∀ op, 1 ≤ C.bin op
  allocPerWord : 1 ≤ C.allocPerWord
  memLen : 1 ≤ C.memLen
  memLoad : 1 ≤ C.memLoad
  memStore : 1 ≤ C.memStore
  branch : 1 ≤ C.branch

/-- The uniform table is admissible: every priced entry is literally 1. -/
theorem CostModel.unit.admissible : CostModel.unit.Admissible := by
  constructor <;> first
    | decide
    | exact fun op => by cases op <;> decide

/-- The calibrated cycles table is admissible: every priced entry is ≥ 1. -/
theorem CostModel.cycles.admissible : CostModel.cycles.Admissible := by
  constructor <;> first
    | decide
    | exact fun op => by cases op <;> decide

/-! ## Machine state -/

/-- Registers hold words; buffers hold zero-initialised arrays of words, whose
length is the buffer's size. All indexed by `ℕ` and represented as functions, which makes the
separation lemmas below one-liners. Buffers are real `Array`s so that the interpreter
does not walk a closure chain per element. -/
structure State (w : ℕ) where
  /-- Input-tape cursor; bookkeeping outside the program memory metric. -/
  tapePos : ℕ := 0
  regs : Reg → Word w
  /-- Buffer contents; live memory is the sum of lengths. -/
  bufs : BufId → Array (Word w)

/-- The initial state: all registers zero, all buffers empty and unallocated. -/
def State.init (w : ℕ) : State w where
  regs _ := 0
  bufs _ := #[]

def State.setReg (s : State w) (d : Reg) (v : Word w) : State w :=
  { s with regs := fun r => if r = d then v else s.regs r }

/-- Consume exactly one word without changing buffers. -/
def State.readRandom (s : State w) (tape : RandomTape w) (d : Reg) : State w :=
  { s.setReg d (tape s.tapePos) with tapePos := s.tapePos + 1 }

@[simp] theorem tapePos_readRandom (s : State w) (tape : RandomTape w) (d : Reg) :
    (s.readRandom tape d).tapePos = s.tapePos + 1 := rfl

@[simp] theorem regs_readRandom (s : State w) (tape : RandomTape w) (d : Reg) :
    (s.readRandom tape d).regs = (s.setReg d (tape s.tapePos)).regs := rfl

@[simp] theorem bufs_readRandom (s : State w) (tape : RandomTape w) (d : Reg) :
    (s.readRandom tape d).bufs = s.bufs := rfl

/-- Update the contents of `b`. -/
def State.setBuf (s : State w) (b : BufId) (a : Array (Word w)) : State w :=
  { s with bufs := fun b' => if b' = b then a else s.bufs b' }

/-- `a` resized to length `n`: its first `n` words, then zeros up to length `n`. -/
def zeroResize {α : Type} [Zero α] (a : Array α) (n : ℕ) : Array α :=
  a.take n ++ Array.replicate (n - a.size) 0

@[simp] theorem size_zeroResize {α : Type} [Zero α] (a : Array α) (n : ℕ) :
    (zeroResize a n).size = n := by
  simp [zeroResize]; omega

/-- Surviving words keep their value; new words read 0. -/
theorem getElem_zeroResize {α : Type} [Zero α] (a : Array α) (n j : ℕ)
    (h : j < (zeroResize a n).size) :
    (zeroResize a n)[j] = if hj : j < a.size then a[j] else 0 := by
  simp only [zeroResize, Array.take_eq_extract, Array.getElem_append, Array.size_extract,
    Array.getElem_extract, Array.getElem_replicate]
  rw [size_zeroResize] at h
  have hm : min n a.size - 0 = min n a.size := Nat.sub_zero _
  split_ifs with h1 h2 h2
  · simp only [Nat.zero_add]
  · omega
  · exact absurd (hm ▸ h1) (by rw [Nat.lt_min]; omega)
  · rfl

/-- `getElem?` form of `getElem_zeroResize` for a surviving word. -/
theorem getElem?_zeroResize_of_lt {α : Type} [Zero α] (a : Array α) {n j : ℕ}
    (hn : j < n) (ha : j < a.size) : (zeroResize a n)[j]? = a[j]? := by
  rw [Array.getElem?_eq_getElem (by simpa using hn), Array.getElem?_eq_getElem ha,
    getElem_zeroResize, dif_pos ha]

@[simp] theorem zeroResize_zero {α : Type} [Zero α] (a : Array α) :
    zeroResize a 0 = #[] := by
  simp [zeroResize]

/-- Resize `b` to length `n`, realloc-style: the first `n` words survive, new words
are zero, every other buffer and register is untouched. `resizeBuf b 0` frees `b`. -/
def State.resizeBuf (s : State w) (b : BufId) (n : ℕ) : State w :=
  { s with bufs := fun b' => if b' = b then zeroResize (s.bufs b) n else s.bufs b' }

@[simp] theorem regs_setReg_self (s : State w) (d : Reg) (v : Word w) :
    (s.setReg d v).regs d = v := by simp [State.setReg]

@[simp] theorem regs_setReg_ne (s : State w) {d r : Reg} (v : Word w) (h : r ≠ d) :
    (s.setReg d v).regs r = s.regs r := by simp [State.setReg, h]

@[simp] theorem bufs_setReg (s : State w) (d : Reg) (v : Word w) :
    (s.setReg d v).bufs = s.bufs := rfl

@[simp] theorem bufs_setBuf_self (s : State w) (b : BufId) (a : Array (Word w)) :
    (s.setBuf b a).bufs b = a := by simp [State.setBuf]

/-- The separation theory, in full: writing buffer `b` leaves buffer `b'` alone, with
a side condition decidable over two `ℕ`s. -/
@[simp] theorem bufs_setBuf_ne (s : State w) {b b' : BufId} (a : Array (Word w))
    (h : b' ≠ b) : (s.setBuf b a).bufs b' = s.bufs b' := by simp [State.setBuf, h]

@[simp] theorem regs_setBuf (s : State w) (b : BufId) (a : Array (Word w)) :
    (s.setBuf b a).regs = s.regs := rfl

@[simp] theorem regs_resizeBuf (s : State w) (b : BufId) (n : ℕ) :
    (s.resizeBuf b n).regs = s.regs := rfl

@[simp] theorem tapePos_resizeBuf (s : State w) (b : BufId) (n : ℕ) :
    (s.resizeBuf b n).tapePos = s.tapePos := rfl

@[simp] theorem bufs_resizeBuf_self (s : State w) (b : BufId) (n : ℕ) :
    (s.resizeBuf b n).bufs b = zeroResize (s.bufs b) n := by simp [State.resizeBuf]

/-- The resized buffer has exactly the requested length. -/
theorem size_bufs_resizeBuf_self (s : State w) (b : BufId) (n : ℕ) :
    ((s.resizeBuf b n).bufs b).size = n := by simp

@[simp] theorem bufs_resizeBuf_ne (s : State w) {b b' : BufId} (n : ℕ)
    (h : b' ≠ b) : (s.resizeBuf b n).bufs b' = s.bufs b' := by simp [State.resizeBuf, h]

/-! ## Semantics

`Exec C tape c s s' t d p`: statement `c` takes state `s` to `s'`, spending `t` time units,
changing live memory by `d` words (net, signed) with peak growth `p`.

Out-of-range `memLoad`/`memStore` have no rule, so a derivation witnesses memory
safety. -/
inductive Exec (C : CostModel) (tape : RandomTape w) : Stmt w → State w → State w → ℕ → ℤ → ℤ → Prop where
  | skip {s} : Exec C tape .skip s s 0 0 0
  | seq {c₁ c₂ s s₁ s₂ t₁ d₁ p₁ t₂ d₂ p₂} :
      Exec C tape c₁ s s₁ t₁ d₁ p₁ → Exec C tape c₂ s₁ s₂ t₂ d₂ p₂ →
      Exec C tape (c₁ ;; c₂) s s₂ (t₁ + t₂) (d₁ + d₂) (max p₁ (d₁ + p₂))
  | imm {d v s} : Exec C tape (.imm d v) s (s.setReg d v) C.imm 0 0
  | rand {d s} : Exec C tape (.rand d) s (s.readRandom tape d) C.rand 0 0
  | mov {d a s} : Exec C tape (.mov d a) s (s.setReg d (s.regs a)) C.mov 0 0
  | un {op d a s} :
      Exec C tape (.un op d a) s (s.setReg d (op.eval (s.regs a))) (C.un op) 0 0
  | bin {op d a b s} :
      Exec C tape (.bin op d a b) s (s.setReg d (op.eval (s.regs a) (s.regs b)))
        (C.bin op) 0 0
  /-- Resize (dynamic, from a register): net charges the new length and credits the
  old; the peak is the whole new length, since during a copying realloc the old and
  the new region coexist. Time is `C.memResize + cap * C.allocPerWord`,
  state-dependent, since the length is read from a register at runtime. -/
  | memResize {b n s} :
      Exec C tape (.memResize b n) s (s.resizeBuf b (s.regs n).toNat)
        (C.memResize + (s.regs n).toNat * C.allocPerWord)
        (((s.regs n).toNat : ℤ) - ((s.bufs b).size : ℤ))
        ((s.regs n).toNat : ℤ)
  /-- Resize (immediate): identical semantics at length `n`, with the per-word time
  charge a pure function of the instruction. At `n = 0` this is the free: time
  `C.memResize` (0 in both shipped tables), net `-|b|`, peak 0. -/
  | memResizeI {b n s} :
      Exec C tape (.memResizeI b n) s (s.resizeBuf b n)
        (C.memResize + n * C.allocPerWord)
        ((n : ℤ) - ((s.bufs b).size : ℤ))
        (n : ℤ)
  | memLen {d b s} :
      Exec C tape (.memLen d b) s (s.setReg d (BitVec.ofNat w (s.bufs b).size)) C.memLen 0 0
  | memLoad {d b i s} (h : (s.regs i).toNat < (s.bufs b).size) :
      Exec C tape (.memLoad d b i) s (s.setReg d (s.bufs b)[(s.regs i).toNat]) C.memLoad 0 0
  | memStore {b i src s} (h : (s.regs i).toNat < (s.bufs b).size) :
      Exec C tape (.memStore b i src) s
        (s.setBuf b ((s.bufs b).set (s.regs i).toNat (s.regs src) h)) C.memStore 0 0
  | ifNZ_true {c thn els s s' t d p} (h : s.regs c ≠ 0) :
      Exec C tape thn s s' t d p → Exec C tape (.ifNZ c thn els) s s' (C.branch + t) d p
  | ifNZ_false {c thn els s s' t d p} (h : s.regs c = 0) :
      Exec C tape els s s' t d p → Exec C tape (.ifNZ c thn els) s s' (C.branch + t) d p
  | while_done {g c b s s₁ tg dg pg} :
      Exec C tape g s s₁ tg dg pg → s₁.regs c = 0 →
      Exec C tape (.whileNZ g c b) s s₁ (tg + C.branch) dg pg
  | while_step {g c b s s₁ s₂ s₃ tg dg pg tb db pb tl dl pl} :
      Exec C tape g s s₁ tg dg pg → s₁.regs c ≠ 0 → Exec C tape b s₁ s₂ tb db pb →
      Exec C tape (.whileNZ g c b) s₂ s₃ tl dl pl →
      Exec C tape (.whileNZ g c b) s s₃ (tg + C.branch + tb + tl) (dg + db + dl)
        (max pg (dg + max pb (db + pl)))

/-! ## Basic metatheory -/

/-- For a fixed tape the machine is deterministic: a statement has at most one outcome, hence at most
one cost, so "the" running time is well defined and a bound proved for one execution
bounds all of them. -/
theorem Exec.deterministic {C : CostModel} {c : Stmt w} {s s₁ s₂ : State w}
    {t₁ t₂ : ℕ} {d₁ p₁ d₂ p₂ : ℤ}
    (h₁ : Exec C tape c s s₁ t₁ d₁ p₁) (h₂ : Exec C tape c s s₂ t₂ d₂ p₂) :
    s₁ = s₂ ∧ t₁ = t₂ ∧ d₁ = d₂ ∧ p₁ = p₂ := by
  induction h₁ generalizing s₂ t₂ d₂ p₂ with
  | seq _ _ ih₁ ih₂ =>
    cases h₂ with
    | seq h₁' h₂' =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ih₁ h₁'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ih₂ h₂'
      exact ⟨rfl, rfl, rfl, rfl⟩
  | ifNZ_true h _ ih =>
    cases h₂ with
    | ifNZ_true _ h' => obtain ⟨rfl, rfl, rfl, rfl⟩ := ih h'; exact ⟨rfl, rfl, rfl, rfl⟩
    | ifNZ_false h' _ => exact absurd h' h
  | ifNZ_false h _ ih =>
    cases h₂ with
    | ifNZ_true h' _ => exact absurd h h'
    | ifNZ_false _ h' => obtain ⟨rfl, rfl, rfl, rfl⟩ := ih h'; exact ⟨rfl, rfl, rfl, rfl⟩
  | while_done _ hz ihg =>
    cases h₂ with
    | while_done hg' hz' =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ihg hg'; exact ⟨rfl, rfl, rfl, rfl⟩
    | while_step hg' hnz' _ _ =>
      obtain ⟨rfl, _, _⟩ := ihg hg'; exact absurd hz hnz'
  | while_step _ hnz _ _ ihg ihb ihl =>
    cases h₂ with
    | while_done hg' hz' =>
      obtain ⟨rfl, _, _⟩ := ihg hg'; exact absurd hz' hnz
    | while_step hg' _ hb' hl' =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ihg hg'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ihb hb'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ihl hl'
      exact ⟨rfl, rfl, rfl, rfl⟩
  | _ => cases h₂; exact ⟨rfl, rfl, rfl, rfl⟩

/-- The peak never dips below the start level. -/
theorem Exec.peak_nonneg {C : CostModel} {c : Stmt w} {s s' : State w} {t : ℕ}
    {d p : ℤ} (h : Exec C tape c s s' t d p) : 0 ≤ p := by
  induction h <;> omega

/-- The net change is bounded by the peak. -/
theorem Exec.net_le_peak {C : CostModel} {c : Stmt w} {s s' : State w} {t : ℕ}
    {d p : ℤ} (h : Exec C tape c s s' t d p) : d ≤ p := by
  induction h <;> omega

/-- The induction core of `Exec.peak_le_time`: both memory indices bounded by the
running time in one induction, since the `seq`/`whileNZ` peak algebra needs the net
bound of the prefix to bound the peak of the whole. -/
theorem Exec.net_and_peak_le_time {C : CostModel} {c : Stmt w} {s s' : State w}
    {t : ℕ} {d p : ℤ} (h : Exec C tape c s s' t d p) (hC : 1 ≤ C.allocPerWord) :
    d ≤ (t : ℤ) ∧ p ≤ (t : ℤ) := by
  induction h with
  | @memResize b n s =>
    have := Nat.le_mul_of_pos_right (s.regs n).toNat (show 0 < C.allocPerWord by omega)
    constructor <;> push_cast <;> omega
  | @memResizeI b n s =>
    have := Nat.le_mul_of_pos_right n (show 0 < C.allocPerWord by omega)
    constructor <;> push_cast <;> omega
  | seq _ _ ih₁ ih₂ => obtain ⟨h₁, h₂⟩ := ih₁; obtain ⟨h₃, h₄⟩ := ih₂
                       constructor <;> push_cast <;> omega
  | ifNZ_true _ _ ih | ifNZ_false _ _ ih =>
    obtain ⟨h₁, h₂⟩ := ih; constructor <;> push_cast <;> omega
  | while_done _ _ ihg =>
    obtain ⟨h₁, h₂⟩ := ihg; constructor <;> push_cast <;> omega
  | while_step _ _ _ _ ihg ihb ihl =>
    obtain ⟨h₁, h₂⟩ := ihg; obtain ⟨h₃, h₄⟩ := ihb; obtain ⟨h₅, h₆⟩ := ihl
    constructor <;> push_cast <;> omega
  | _ => constructor <;> omega

/-- Peak memory is bounded by running time. In any model charging at least one time
unit per acquired word (`1 ≤ C.allocPerWord`, true of both shipped tables), no
execution's live-memory peak exceeds its running time, so one certificate covers
both resources. The register-side counterpart is `Stmt.Straight.regPeak₀_le`
(`Liveness.lean`). -/
theorem Exec.peak_le_time {C : CostModel} {c : Stmt w} {s s' : State w} {t : ℕ}
    {d p : ℤ} (h : Exec C tape c s s' t d p) (hC : 1 ≤ C.allocPerWord) : p ≤ (t : ℤ) :=
  (h.net_and_peak_le_time hC).2

/-- Corollary of `Exec.peak_le_time`: the net live-memory change is bounded by the
running time as well. -/
theorem Exec.net_le_time {C : CostModel} {c : Stmt w} {s s' : State w} {t : ℕ}
    {d p : ℤ} (h : Exec C tape c s s' t d p) (hC : 1 ≤ C.allocPerWord) : d ≤ (t : ℤ) :=
  (h.net_and_peak_le_time hC).1

/-- `Exec.peak_le_time` under the packaged `CostModel.Admissible` hypothesis
(satisfied by both shipped tables: `CostModel.unit.admissible`,
`CostModel.cycles.admissible`). -/
theorem Exec.peak_le_time_admissible {C : CostModel} {c : Stmt w} {s s' : State w}
    {t : ℕ} {d p : ℤ} (h : Exec C tape c s s' t d p) (hC : C.Admissible) : p ≤ (t : ℤ) :=
  h.peak_le_time hC.allocPerWord

/-- `Exec.net_le_time` under the packaged `CostModel.Admissible` hypothesis. -/
theorem Exec.net_le_time_admissible {C : CostModel} {c : Stmt w} {s s' : State w}
    {t : ℕ} {d p : ℤ} (h : Exec C tape c s s' t d p) (hC : C.Admissible) : d ≤ (t : ℤ) :=
  h.net_le_time hC.allocPerWord

/-! ### Framing: which registers and buffers a statement can touch

The replacement for separation logic. Both are computed syntactically, hence
decidable, hence dischargeable by `simp`/`decide` on concrete code. -/

/-- `c.Writes r`: `c` may assign register `r`'s *value*. -/
def Stmt.Writes : Stmt w → Reg → Prop
  | .skip, _ => False
  | .seq c₁ c₂, r => c₁.Writes r ∨ c₂.Writes r
  | .rand d, r => r = d
  | .imm d _, r => r = d
  | .mov d _, r => r = d
  | .un _ d _, r => r = d
  | .bin _ d _ _, r => r = d
  | .memResize .., _ => False
  | .memResizeI .., _ => False
  | .memLen d _, r => r = d
  | .memLoad d _ _, r => r = d
  | .memStore .., _ => False
  | .ifNZ _ t e, r => t.Writes r ∨ e.Writes r
  | .whileNZ g _ b, r => g.Writes r ∨ b.Writes r

/-- `c.Touches b`: `c` may modify buffer `b`. -/
def Stmt.Touches : Stmt w → BufId → Prop
  | .skip, _ => False
  | .seq c₁ c₂, b => c₁.Touches b ∨ c₂.Touches b
  | .memResize b' _, b => b = b'
  | .memResizeI b' _, b => b = b'
  | .memStore b' _ _, b => b = b'
  | .ifNZ _ t e, b => t.Touches b ∨ e.Touches b
  | .whileNZ g _ bd, b => g.Touches b ∨ bd.Touches b
  | _, _ => False

instance instDecidableWrites : ∀ (c : Stmt w) (r : Reg), Decidable (c.Writes r)
  | .skip, _ => inferInstanceAs (Decidable False)
  | .seq c₁ c₂, r =>
    have := instDecidableWrites c₁ r
    have := instDecidableWrites c₂ r
    inferInstanceAs (Decidable (_ ∨ _))
  | .rand d, r => inferInstanceAs (Decidable (r = d))
  | .imm d _, r => inferInstanceAs (Decidable (r = d))
  | .mov d _, r => inferInstanceAs (Decidable (r = d))
  | .un _ d _, r => inferInstanceAs (Decidable (r = d))
  | .bin _ d _ _, r => inferInstanceAs (Decidable (r = d))
  | .memResize .., _ => inferInstanceAs (Decidable False)
  | .memResizeI .., _ => inferInstanceAs (Decidable False)
  | .memLen d _, r => inferInstanceAs (Decidable (r = d))
  | .memLoad d _ _, r => inferInstanceAs (Decidable (r = d))
  | .memStore .., _ => inferInstanceAs (Decidable False)
  | .ifNZ _ t e, r =>
    have := instDecidableWrites t r
    have := instDecidableWrites e r
    inferInstanceAs (Decidable (_ ∨ _))
  | .whileNZ g _ b, r =>
    have := instDecidableWrites g r
    have := instDecidableWrites b r
    inferInstanceAs (Decidable (_ ∨ _))

instance instDecidableTouches : ∀ (c : Stmt w) (b : BufId), Decidable (c.Touches b)
  | .skip, _ => inferInstanceAs (Decidable False)
  | .seq c₁ c₂, b =>
    have := instDecidableTouches c₁ b
    have := instDecidableTouches c₂ b
    inferInstanceAs (Decidable (_ ∨ _))
  | .rand .., _ => inferInstanceAs (Decidable False)
  | .imm .., _ => inferInstanceAs (Decidable False)
  | .mov .., _ => inferInstanceAs (Decidable False)
  | .un .., _ => inferInstanceAs (Decidable False)
  | .bin .., _ => inferInstanceAs (Decidable False)
  | .memResize b' _, b => inferInstanceAs (Decidable (b = b'))
  | .memResizeI b' _, b => inferInstanceAs (Decidable (b = b'))
  | .memLen .., _ => inferInstanceAs (Decidable False)
  | .memLoad .., _ => inferInstanceAs (Decidable False)
  | .memStore b' _ _, b => inferInstanceAs (Decidable (b = b'))
  | .ifNZ _ t e, b =>
    have := instDecidableTouches t b
    have := instDecidableTouches e b
    inferInstanceAs (Decidable (_ ∨ _))
  | .whileNZ g _ bd, b =>
    have := instDecidableTouches g b
    have := instDecidableTouches bd b
    inferInstanceAs (Decidable (_ ∨ _))

/-! Build performance: pre-realize the `Stmt.Writes`/`Stmt.Touches` unfolding
lemmas here at the definition site (realizations made inside a retained theorem
ship in the `.olean`), so importing modules that `simp only [Stmt.Touches]` do
not each re-prove them. -/
set_option linter.unusedSimpArgs false in
private theorem Writes_Touches_eq_lemmas_realized : True := by
  simp -failIfUnchanged only [Stmt.Writes, Stmt.Touches]

@[simp] theorem Writes_skip (r : Reg) : (Stmt.skip (w := w)).Writes r ↔ False := Iff.rfl
@[simp] theorem Writes_seq (c₁ c₂ : Stmt w) (r : Reg) :
    (c₁ ;; c₂).Writes r ↔ c₁.Writes r ∨ c₂.Writes r := Iff.rfl
@[simp] theorem Touches_skip (b : BufId) : (Stmt.skip (w := w)).Touches b ↔ False := Iff.rfl
@[simp] theorem Touches_seq (c₁ c₂ : Stmt w) (b : BufId) :
    (c₁ ;; c₂).Touches b ↔ c₁.Touches b ∨ c₂.Touches b := Iff.rfl

/-- Register frame rule. -/
theorem Exec.frame_reg {C : CostModel} {c : Stmt w} {s s' : State w} {t : ℕ}
    {d p : ℤ} {r : Reg}
    (h : Exec C tape c s s' t d p) (hr : ¬ c.Writes r) : s'.regs r = s.regs r := by
  induction h with
  | skip => rfl
  | seq _ _ ih₁ ih₂ =>
    simp only [Writes_seq, not_or] at hr
    rw [ih₂ hr.2, ih₁ hr.1]
  | rand | imm | mov | un | bin | memLen | memLoad =>
    exact regs_setReg_ne _ _ hr
  | memResize | memResizeI | memStore => rfl
  | ifNZ_true _ _ ih => exact ih fun hh => hr (Or.inl hh)
  | ifNZ_false _ _ ih => exact ih fun hh => hr (Or.inr hh)
  | while_done _ _ ihg => exact ihg fun hh => hr (Or.inl hh)
  | while_step _ _ _ _ ihg ihb ihl =>
    rw [ihl hr, ihb fun hh => hr (Or.inr hh), ihg fun hh => hr (Or.inl hh)]

/-- Buffer frame rule: a separation-logic frame with a decidable side condition
instead of an entailment. -/
theorem Exec.frame_buf {C : CostModel} {c : Stmt w} {s s' : State w} {t : ℕ}
    {d p : ℤ} {b : BufId}
    (h : Exec C tape c s s' t d p) (hb : ¬ c.Touches b) : s'.bufs b = s.bufs b := by
  induction h with
  | skip => rfl
  | seq _ _ ih₁ ih₂ =>
    simp only [Touches_seq, not_or] at hb
    rw [ih₂ hb.2, ih₁ hb.1]
  | rand | imm | mov | un | bin | memLen | memLoad => rfl
  | memStore => exact bufs_setBuf_ne _ _ hb
  | memResize | memResizeI => exact bufs_resizeBuf_ne _ _ hb
  | ifNZ_true _ _ ih => exact ih fun hh => hb (Or.inl hh)
  | ifNZ_false _ _ ih => exact ih fun hh => hb (Or.inr hh)
  | while_done _ _ ihg => exact ihg fun hh => hb (Or.inl hh)
  | while_step _ _ _ _ ihg ihb ihl =>
    rw [ihl hb, ihb fun hh => hb (Or.inr hh), ihg fun hh => hb (Or.inl hh)]

/-! ### Unit time, precisely

A statement with no branches costs a syntactically-determined number of time units,
for *every* input state: nothing in the machine makes an instruction cheaper or more
expensive depending on data. -/

/-- No `ifNZ`, no `whileNZ`, no *dynamic* `memResize`: the three constructs whose
time depends on the state. `memResizeI` is straight, its per-word charge being a
function of the syntax. -/
def Stmt.Straight : Stmt w → Prop
  | .seq c₁ c₂ => c₁.Straight ∧ c₂.Straight
  | .memResize .. => False
  | .ifNZ .. => False
  | .whileNZ .. => False
  | _ => True

/-- No `whileNZ` and no dynamic `memResize` anywhere; `ifNZ` is allowed, with both
branches loop-free. For such code `staticTime` is an upper bound on every execution
(`Exec.time_le_staticTime_of_loopFree`). The dynamic `memResize` is excluded for the
same reason as loops: its charge depends on the runtime length. -/
def Stmt.LoopFree : Stmt w → Prop
  | .seq c₁ c₂ => c₁.LoopFree ∧ c₂.LoopFree
  | .memResize .. => False
  | .ifNZ _ thn els => thn.LoopFree ∧ els.LoopFree
  | .whileNZ .. => False
  | _ => True

/-- Straight code is in particular loop-free. -/
theorem Stmt.Straight.loopFree {c : Stmt w} (h : c.Straight) : c.LoopFree := by
  induction c with
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | memResize | ifNZ | whileNZ => exact h.elim
  | _ => trivial

/-- The syntactic running time of a branch-free statement, exact for `Straight` code
(`straight_time_eq`). For `ifNZ` it is the upper-bound shape `branch + max`, proved
safe for loop-free code by `Exec.time_le_staticTime_of_loopFree`.

Two ways to misuse it: on `whileNZ` it returns 0, so a number quoted for looping
code bounds nothing; on the *dynamic* `memResize` it returns the base `C.memResize`
and under-reports, since the real charge adds `len * C.allocPerWord` for a runtime
length no function of the syntax can know. At the API surface use `staticTime?`,
which returns `none` unless the number is exact, or pair this with a
`Stmt.Straight` (exact) or `Stmt.LoopFree` (upper bound) proof. Bounds for looping
or dynamically-resizing code come from the `Triple` logic. -/
def Stmt.staticTime (C : CostModel) : Stmt w → ℕ
  | .skip => 0
  | .seq c₁ c₂ => c₁.staticTime C + c₂.staticTime C
  | .rand .. => C.rand
  | .imm .. => C.imm
  | .mov .. => C.mov
  | .un op .. => C.un op
  | .bin op .. => C.bin op
  | .memResize .. => C.memResize
  | .memResizeI _ n => C.memResize + n * C.allocPerWord
  | .memLen .. => C.memLen
  | .memLoad .. => C.memLoad
  | .memStore .. => C.memStore
  | .ifNZ _ t e => C.branch + max (t.staticTime C) (e.staticTime C)
  | .whileNZ .. => 0

/-- `c` acquires no live memory anywhere, branches and loops included: no
`memResize`, and `memResizeI` only at length 0. The free `memResizeI b 0` is
allowed, as it only ever decreases live memory, which is what
`Exec.allocFree_space`'s `d ≤ 0 ∧ p ≤ 0` certifies. -/
def Stmt.AllocFree : Stmt w → Prop
  | .seq c₁ c₂ => c₁.AllocFree ∧ c₂.AllocFree
  | .ifNZ _ t e => t.AllocFree ∧ e.AllocFree
  | .whileNZ g _ b => g.AllocFree ∧ b.AllocFree
  | .memResize .. => False
  | .memResizeI _ n => n = 0
  | _ => True

/-- Branch-free code runs in constant time: the running time is a function of the
syntax alone, never of the state. -/
theorem Exec.straight_time_eq {C : CostModel} {c : Stmt w} {s s' : State w} {t : ℕ}
    {d p : ℤ} (h : Exec C tape c s s' t d p) (hs : c.Straight) : t = c.staticTime C := by
  induction h with
  | seq _ _ ih₁ ih₂ => exact congrArg₂ (· + ·) (ih₁ hs.1) (ih₂ hs.2)
  | memResize | ifNZ_true | ifNZ_false | while_done | while_step => exact hs.elim
  | _ => rfl

/-- Loop-free code is bounded by its static time. With `ifNZ` in play the time is no
longer exact, since the branches may cost different amounts, but `staticTime`'s
`branch + max` shape bounds every execution. -/
theorem Exec.time_le_staticTime_of_loopFree {C : CostModel} {c : Stmt w}
    {s s' : State w} {t : ℕ} {d p : ℤ} (h : Exec C tape c s s' t d p)
    (hl : c.LoopFree) : t ≤ c.staticTime C := by
  induction h with
  | seq _ _ ih₁ ih₂ => exact Nat.add_le_add (ih₁ hl.1) (ih₂ hl.2)
  | ifNZ_true _ _ ih =>
    exact Nat.add_le_add_left ((ih hl.1).trans (le_max_left _ _)) _
  | ifNZ_false _ _ ih =>
    exact Nat.add_le_add_left ((ih hl.2).trans (le_max_right _ _)) _
  | memResize | while_done | while_step => exact hl.elim
  | _ => exact le_rfl

/-- Memory only ever enters through a resize to positive length, so alloc-free
code, straight-line or not, has non-positive net and zero peak growth. The free
`memResizeI b 0` may make the net strictly negative. -/
theorem Exec.allocFree_space {C : CostModel} {c : Stmt w} {s s' : State w} {t : ℕ}
    {d p : ℤ} (h : Exec C tape c s s' t d p) (ha : c.AllocFree) :
    d ≤ 0 ∧ p ≤ 0 := by
  induction h with
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨h1, h2⟩ := ih₁ ha.1
    obtain ⟨h3, h4⟩ := ih₂ ha.2
    omega
  | memResize => exact ha.elim
  | memResizeI => subst ha; omega
  | ifNZ_true _ _ ih => obtain ⟨h1, h2⟩ := ih ha.1; omega
  | ifNZ_false _ _ ih => obtain ⟨h1, h2⟩ := ih ha.2; omega
  | while_done _ _ ihg => obtain ⟨h1, h2⟩ := ihg ha.1; omega
  | while_step _ _ _ _ ihg ihb ihl =>
    obtain ⟨h1, h2⟩ := ihg ha.1
    obtain ⟨h3, h4⟩ := ihb ha.2
    obtain ⟨h5, h6⟩ := ihl ha
    omega
  | _ => omega

/-- Corollary: two runs of the same branch-free program take the same time, whatever
their inputs. This is data-independence of the abstract time counter, an ingredient
of a constant-time argument, not by itself a side-channel guarantee. -/
theorem Exec.straight_data_independent {C : CostModel} {c : Stmt w}
    {s₁ s₁' s₂ s₂' : State w} {t₁ t₂ : ℕ} {d₁ p₁ d₂ p₂ : ℤ}
    (h₁ : Exec C tape c s₁ s₁' t₁ d₁ p₁) (h₂ : Exec C tape c s₂ s₂' t₂ d₂ p₂)
    (hs : c.Straight) : t₁ = t₂ :=
  (h₁.straight_time_eq hs).trans (h₂.straight_time_eq hs).symm

/-- The static running time as a *partial* function, and the safe way to quote a
static time. `some n` exactly when the statement is straight-line with static time
`n`, in which case every execution takes exactly `n` time units
(`Exec.staticTime?_time_eq`); `none` as soon as an `ifNZ`, a `whileNZ` or a dynamic
`memResize` appears. Unlike the raw `staticTime` it cannot silently return a
meaningless number, since it mirrors the fragment on which `straight_time_eq` holds
(`staticTime?_eq_some`). -/
def Stmt.staticTime? (C : CostModel) : Stmt w → Option ℕ
  | .seq c₁ c₂ => (c₁.staticTime? C).bind fun t₁ => (c₂.staticTime? C).map (t₁ + ·)
  | .memResize .. => none
  | .ifNZ .. => none
  | .whileNZ .. => none
  | c => some (c.staticTime C)

/-- `staticTime?` characterised: it returns `some n` precisely when the statement is
straight-line with static time `n`. -/
theorem Stmt.staticTime?_eq_some {C : CostModel} {c : Stmt w} {n : ℕ} :
    c.staticTime? C = some n ↔ c.Straight ∧ c.staticTime C = n := by
  induction c generalizing n with
  | seq c₁ c₂ ih₁ ih₂ =>
    constructor
    · intro h
      simp only [Stmt.staticTime?] at h
      cases h₁ : c₁.staticTime? C with
      | none => simp [h₁] at h
      | some t₁ =>
        cases h₂ : c₂.staticTime? C with
        | none => simp [h₁, h₂] at h
        | some t₂ =>
          simp only [h₁, h₂, Option.bind_some, Option.map_some, Option.some.injEq] at h
          obtain ⟨hs₁, ht₁⟩ := ih₁.mp h₁
          obtain ⟨hs₂, ht₂⟩ := ih₂.mp h₂
          exact ⟨⟨hs₁, hs₂⟩, by simp only [Stmt.staticTime]; omega⟩
    · rintro ⟨hs, rfl⟩
      simp only [Stmt.staticTime?, ih₁.mpr ⟨hs.1, rfl⟩, ih₂.mpr ⟨hs.2, rfl⟩,
        Option.bind_some, Option.map_some, Stmt.staticTime]
  | memResize =>
    simp only [Stmt.staticTime?]
    exact ⟨fun h => by simp at h, fun h => h.1.elim⟩
  | ifNZ =>
    simp only [Stmt.staticTime?]
    exact ⟨fun h => by simp at h, fun h => h.1.elim⟩
  | whileNZ =>
    simp only [Stmt.staticTime?]
    exact ⟨fun h => by simp at h, fun h => h.1.elim⟩
  | _ => simp [Stmt.staticTime?, Stmt.Straight]

/-- On straight-line code, `staticTime?` succeeds and agrees with `staticTime`. -/
theorem Stmt.Straight.staticTime?_eq {c : Stmt w} (hs : c.Straight) (C : CostModel) :
    c.staticTime? C = some (c.staticTime C) :=
  Stmt.staticTime?_eq_some.mpr ⟨hs, rfl⟩

/-- Whenever `staticTime?` returns a number, that number is the exact running time of
every execution, on every input. The `Option`-valued API needs no side condition:
`some` already certifies straightness. -/
theorem Exec.staticTime?_time_eq {C : CostModel} {c : Stmt w} {s s' : State w}
    {t n : ℕ} {d p : ℤ} (h : Exec C tape c s s' t d p) (hn : c.staticTime? C = some n) :
    t = n := by
  obtain ⟨hs, rfl⟩ := Stmt.staticTime?_eq_some.mp hn
  exact h.straight_time_eq hs

/-! ### Absolute live memory

`Exec` defines the indices `d` and `p` for arbitrary start states. They are pinned
to the *absolute* footprint `State.liveMem B`, the words held by buffers below any
bound `B` covering the buffers `c` names:

* the net change is exact: `liveMem s' = liveMem s + d` (`Exec.liveMem_eq`);
* the final state is within the peak (`Exec.liveMem_le_peak`), and so is every
  intermediate state (`Exec.reaches_liveMem_le_peak`, with `Reaches` enumerating
  the states an execution passes through).

Since a buffer's length is its only size, every stored word is a live word, so `p`
is a high-water mark on physical buffer memory above the start level. -/

/-- Absolute live memory below `B`: the words held by buffers `0, …, B - 1`.
Defined by recursion on `B` (rather than a `Finset` sum) so that the update lemmas
prove by `induction`/`omega`. -/
def State.liveMem (s : State w) : ℕ → ℕ
  | 0 => 0
  | B + 1 => s.liveMem B + (s.bufs B).size

@[simp] theorem liveMem_readRandom (s : State w) (tape : RandomTape w) (r : Reg)
    (B : ℕ) : (s.readRandom tape r).liveMem B = s.liveMem B := by
  induction B with
  | zero => rfl
  | succ B ih => simp only [State.liveMem, bufs_readRandom, ih]

@[simp] theorem liveMem_setReg (s : State w) (r : Reg) (v : Word w) (B : ℕ) :
    (s.setReg r v).liveMem B = s.liveMem B := by
  induction B with
  | zero => rfl
  | succ B ih => simp only [State.liveMem, ih, bufs_setReg]

/-- Overwriting a buffer with an array of the same length keeps the footprint. -/
theorem liveMem_setBuf (s : State w) {b : BufId} {a : Array (Word w)}
    (ha : a.size = (s.bufs b).size) (B : ℕ) : (s.setBuf b a).liveMem B = s.liveMem B := by
  induction B with
  | zero => rfl
  | succ B ih =>
    simp only [State.liveMem, ih]
    by_cases hB : B = b
    · subst hB; rw [bufs_setBuf_self, ha]
    · rw [bufs_setBuf_ne _ _ hB]

theorem liveMem_resizeBuf_of_le (s : State w) {b : BufId} (n : ℕ) {B : ℕ}
    (hB : B ≤ b) : (s.resizeBuf b n).liveMem B = s.liveMem B := by
  induction B with
  | zero => rfl
  | succ B ih =>
    simp only [State.liveMem, ih (Nat.le_of_succ_le hB),
      bufs_resizeBuf_ne _ _ (Nat.ne_of_lt (Nat.lt_of_succ_le hB))]

/-- Resizing buffer `b` to length `n` moves the footprint by exactly the amount
`Exec.memResize` charges. -/
theorem liveMem_resizeBuf (s : State w) {b : BufId} (n : ℕ) {B : ℕ} (hb : b < B) :
    ((s.resizeBuf b n).liveMem B : ℤ) = s.liveMem B + n - (s.bufs b).size := by
  induction B with
  | zero => exact absurd hb (Nat.not_lt_zero b)
  | succ B ih =>
    rcases Nat.lt_or_ge b B with hbB | hbB
    · have := ih hbB
      simp only [State.liveMem, bufs_resizeBuf_ne _ _ (Nat.ne_of_gt hbB)]
      push_cast
      omega
    · have heq : b = B := Nat.le_antisymm (Nat.lt_succ_iff.mp hb) hbB
      subst heq
      simp only [State.liveMem, size_bufs_resizeBuf_self,
        liveMem_resizeBuf_of_le _ _ (Nat.le_refl b)]
      push_cast
      omega

/-- The net index is exact: over any bound `B` covering the buffers `c` names, the
absolute footprint moves by exactly `d`, not merely by at most `d`. A `Triple` still
only certifies `d ≤ D`; the exactness is between `d` and the state. -/
theorem Exec.liveMem_eq {C : CostModel} {c : Stmt w} {s s' : State w} {t : ℕ}
    {d p : ℤ} {B : ℕ} (h : Exec C tape c s s' t d p)
    (hc : ∀ b, c.Touches b → b < B) :
    (s'.liveMem B : ℤ) = s.liveMem B + d := by
  induction h with
  | skip => omega
  | seq _ _ ih₁ ih₂ =>
    rw [ih₂ (fun b hb => hc b (Or.inr hb)), ih₁ (fun b hb => hc b (Or.inl hb))]
    ring
  | rand | imm | mov | un | bin | memLen | memLoad => simp
  | memResize | memResizeI => rw [liveMem_resizeBuf _ _ (hc _ rfl)]; omega
  | memStore => rw [liveMem_setBuf _ (Array.size_set ..)]; omega
  | ifNZ_true _ _ ih => exact ih fun b hb => hc b (Or.inl hb)
  | ifNZ_false _ _ ih => exact ih fun b hb => hc b (Or.inr hb)
  | while_done _ _ ihg => exact ihg fun b hb => hc b (Or.inl hb)
  | while_step _ _ _ _ ihg ihb ihl =>
    rw [ihl hc, ihb (fun b hb => hc b (Or.inr hb)),
      ihg (fun b hb => hc b (Or.inl hb))]
    ring

/-- The final footprint stays within the peak: `liveMem s' ≤ liveMem s + p`. -/
theorem Exec.liveMem_le_peak {C : CostModel} {c : Stmt w} {s s' : State w} {t : ℕ}
    {d p : ℤ} {B : ℕ} (h : Exec C tape c s s' t d p)
    (hc : ∀ b, c.Touches b → b < B) :
    (s'.liveMem B : ℤ) ≤ s.liveMem B + p := by
  have h₁ := h.liveMem_eq hc
  have h₂ := h.net_le_peak
  omega

/-- `Reaches C tape c s m`: an execution of `c` from `s` passes through state `m`, either
the start state or a state at an instruction boundary strictly inside the execution;
the branch conditions keep every constructor on the path actually taken. The final
state is covered separately by `Exec.liveMem_le_peak`, so together the two enumerate
every state an execution visits. -/
inductive Reaches (C : CostModel) (tape : RandomTape w) : Stmt w → State w → State w → Prop where
  | start {c : Stmt w} {s : State w} : Reaches C tape c s s
  | seq_left {c₁ c₂ : Stmt w} {s m : State w} :
      Reaches C tape c₁ s m → Reaches C tape (c₁ ;; c₂) s m
  | seq_right {c₁ c₂ : Stmt w} {s s₁ m : State w} {t₁ : ℕ} {d₁ p₁ : ℤ} :
      Exec C tape c₁ s s₁ t₁ d₁ p₁ → Reaches C tape c₂ s₁ m → Reaches C tape (c₁ ;; c₂) s m
  | ifNZ_true {r : Reg} {thn els : Stmt w} {s m : State w} :
      s.regs r ≠ 0 → Reaches C tape thn s m → Reaches C tape (.ifNZ r thn els) s m
  | ifNZ_false {r : Reg} {thn els : Stmt w} {s m : State w} :
      s.regs r = 0 → Reaches C tape els s m → Reaches C tape (.ifNZ r thn els) s m
  | while_guard {g body : Stmt w} {r : Reg} {s m : State w} :
      Reaches C tape g s m → Reaches C tape (.whileNZ g r body) s m
  | while_body {g body : Stmt w} {r : Reg} {s s₁ m : State w} {tg : ℕ} {dg pg : ℤ} :
      Exec C tape g s s₁ tg dg pg → s₁.regs r ≠ 0 → Reaches C tape body s₁ m →
      Reaches C tape (.whileNZ g r body) s m
  | while_loop {g body : Stmt w} {r : Reg} {s s₁ s₂ m : State w} {tg tb : ℕ}
      {dg pg db pb : ℤ} :
      Exec C tape g s s₁ tg dg pg → s₁.regs r ≠ 0 → Exec C tape body s₁ s₂ tb db pb →
      Reaches C tape (.whileNZ g r body) s₂ m → Reaches C tape (.whileNZ g r body) s m

/-- The peak bounds every intermediate state: any state an execution passes through
(`Reaches`) has absolute footprint at most `p` above the start, so `p` is the
high-water mark of the whole execution, not a statement about its endpoints. -/
theorem Exec.reaches_liveMem_le_peak {C : CostModel} {c : Stmt w} {s s' m : State w}
    {t : ℕ} {d p : ℤ} {B : ℕ} (h : Exec C tape c s s' t d p) (hm : Reaches C tape c s m)
    (hc : ∀ b, c.Touches b → b < B) :
    (m.liveMem B : ℤ) ≤ s.liveMem B + p := by
  induction hm generalizing s' t d p with
  | start => have := h.peak_nonneg; omega
  | seq_left _ ih =>
    cases h with
    | seq h₁ _ =>
      have h1 := ih h₁ fun b hb => hc b (Or.inl hb)
      omega
  | seq_right hex _ ih =>
    cases h with
    | seq h₁ h₂ =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Exec.deterministic h₁ hex
      have h1 := ih h₂ fun b hb => hc b (Or.inr hb)
      have h2 := Exec.liveMem_eq h₁ fun b hb => hc b (Or.inl hb)
      omega
  | ifNZ_true hnz _ ih =>
    cases h with
    | ifNZ_true _ hthn => exact ih hthn fun b hb => hc b (Or.inl hb)
    | ifNZ_false hz _ => exact absurd hz hnz
  | ifNZ_false hz _ ih =>
    cases h with
    | ifNZ_true hnz _ => exact absurd hz hnz
    | ifNZ_false _ hels => exact ih hels fun b hb => hc b (Or.inr hb)
  | while_guard _ ih =>
    cases h with
    | while_done hg _ => exact ih hg fun b hb => hc b (Or.inl hb)
    | while_step hg _ _ _ =>
      have h1 := ih hg fun b hb => hc b (Or.inl hb)
      omega
  | while_body hexg hnz _ ih =>
    cases h with
    | while_done hg hz =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Exec.deterministic hg hexg
      exact absurd hz hnz
    | while_step hg _ hb _ =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Exec.deterministic hg hexg
      have h1 := ih hb fun b hb' => hc b (Or.inr hb')
      have h2 := Exec.liveMem_eq hg fun b hb' => hc b (Or.inl hb')
      omega
  | while_loop hexg hnz hexb _ ih =>
    cases h with
    | while_done hg hz =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Exec.deterministic hg hexg
      exact absurd hz hnz
    | while_step hg _ hb hl =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Exec.deterministic hg hexg
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Exec.deterministic hb hexb
      have h1 := ih hl hc
      have h2 := Exec.liveMem_eq hg fun b hb' => hc b (Or.inl hb')
      have h3 := Exec.liveMem_eq hb fun b hb' => hc b (Or.inr hb')
      omega

/-! ## Reference interpreter

Executable semantics, agreeing with `Exec`. `fuel` bounds the recursion depth (every
recursive call consumes one unit, so any `fuel ≥` statement depth × loop trip counts
suffices); `none` means "ran out of fuel, or hit an out-of-range buffer access". Fuel
is an interpreter artifact; no cost is derived from it. -/

def run (C : CostModel) (tape : RandomTape w) : ℕ → Stmt w → State w → Option (State w × ℕ × ℤ × ℤ)
  | 0, _, _ => none
  | f + 1, c, s =>
    match c with
    | .skip => some (s, 0, 0, 0)
    | .seq c₁ c₂ => do
        let (s₁, t₁, d₁, p₁) ← run C tape f c₁ s
        let (s₂, t₂, d₂, p₂) ← run C tape f c₂ s₁
        some (s₂, t₁ + t₂, d₁ + d₂, max p₁ (d₁ + p₂))
    | .rand d => some (s.readRandom tape d, C.rand, 0, 0)
    | .imm d v => some (s.setReg d v, C.imm, 0, 0)
    | .mov d a => some (s.setReg d (s.regs a), C.mov, 0, 0)
    | .un op d a => some (s.setReg d (op.eval (s.regs a)), C.un op, 0, 0)
    | .bin op d a b =>
        some (s.setReg d (op.eval (s.regs a) (s.regs b)), C.bin op, 0, 0)
    | .memResize b n =>
        some (s.resizeBuf b (s.regs n).toNat,
          C.memResize + (s.regs n).toNat * C.allocPerWord,
          ((s.regs n).toNat : ℤ) - ((s.bufs b).size : ℤ),
          ((s.regs n).toNat : ℤ))
    | .memResizeI b n =>
        some (s.resizeBuf b n, C.memResize + n * C.allocPerWord,
          (n : ℤ) - ((s.bufs b).size : ℤ),
          (n : ℤ))
    | .memLen d b =>
        some (s.setReg d (BitVec.ofNat w (s.bufs b).size), C.memLen, 0, 0)
    | .memLoad d b i =>
        if h : (s.regs i).toNat < (s.bufs b).size then
          some (s.setReg d (s.bufs b)[(s.regs i).toNat], C.memLoad, 0, 0)
        else none
    | .memStore b i src =>
        if h : (s.regs i).toNat < (s.bufs b).size then
          some (s.setBuf b ((s.bufs b).set (s.regs i).toNat (s.regs src) h),
            C.memStore, 0, 0)
        else none
    | .ifNZ c thn els =>
        if s.regs c = 0 then do
          let (s', t, d, p) ← run C tape f els s
          some (s', C.branch + t, d, p)
        else do
          let (s', t, d, p) ← run C tape f thn s
          some (s', C.branch + t, d, p)
    | .whileNZ g cc b => do
        let (s₁, tg, dg, pg) ← run C tape f g s
        if s₁.regs cc = 0 then
          some (s₁, tg + C.branch, dg, pg)
        else do
          let (s₂, tb, db, pb) ← run C tape f b s₁
          let (s₃, tl, dl, pl) ← run C tape f (.whileNZ g cc b) s₂
          some (s₃, tg + C.branch + tb + tl, dg + db + dl,
            max pg (dg + max pb (db + pl)))

/-- The interpreter is sound: anything it computes is a real execution, with exactly
the costs it reports. So `#eval`-ing a program gives numbers that the `Exec`-level
theorems are about. -/
theorem run_sound {C : CostModel} : ∀ (f : ℕ) (c : Stmt w) {s s' : State w} {t : ℕ} {d p : ℤ},
    run C tape f c s = some (s', t, d, p) → Exec C tape c s s' t d p := by
  intro f
  induction f with
  | zero => intro c s s' t d p h; cases h
  | succ f ih =>
    intro c s s' t d p h
    match c with
    | .skip =>
      simp only [run, Option.some.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact .skip
    | .seq c₁ c₂ =>
      simp only [run] at h
      cases h₁ : run C tape f c₁ s with
      | none =>
        simp only [h₁, Option.bind_eq_bind, Option.bind_none] at h
        cases h
      | some r₁ =>
        obtain ⟨s₁, t₁, d₁, p₁⟩ := r₁
        simp only [h₁, Option.bind_eq_bind, Option.bind_some] at h
        cases h₂ : run C tape f c₂ s₁ with
        | none =>
          simp only [h₂, Option.bind_none] at h
          cases h
        | some r₂ =>
          obtain ⟨s₂, t₂, d₂, p₂⟩ := r₂
          simp only [h₂, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact .seq (ih _ h₁) (ih _ h₂)
    | .rand d =>
      simp only [run, Option.some.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact .rand
    | .imm d v =>
      simp only [run, Option.some.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact .imm
    | .mov d a =>
      simp only [run, Option.some.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact .mov
    | .un op d a =>
      simp only [run, Option.some.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact .un
    | .bin op d a b =>
      simp only [run, Option.some.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact .bin
    | .memResize b n =>
      simp only [run, Option.some.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact .memResize
    | .memResizeI b n =>
      simp only [run, Option.some.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact .memResizeI
    | .memLen d b =>
      simp only [run, Option.some.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact .memLen
    | .memLoad d b i =>
      simp only [run] at h
      split at h
      · simp only [Option.some.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact .memLoad ‹_›
      · cases h
    | .memStore b i src =>
      simp only [run] at h
      split at h
      · simp only [Option.some.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact .memStore ‹_›
      · cases h
    | .ifNZ c thn els =>
      simp only [run] at h
      by_cases hc : s.regs c = 0
      · rw [if_pos hc] at h
        cases h₁ : run C tape f els s with
        | none =>
          simp only [h₁, Option.bind_eq_bind, Option.bind_none] at h
          cases h
        | some r₁ =>
          obtain ⟨s₁, t₁, d₁, p₁⟩ := r₁
          simp only [h₁, Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact .ifNZ_false hc (ih _ h₁)
      · rw [if_neg hc] at h
        cases h₁ : run C tape f thn s with
        | none =>
          simp only [h₁, Option.bind_eq_bind, Option.bind_none] at h
          cases h
        | some r₁ =>
          obtain ⟨s₁, t₁, d₁, p₁⟩ := r₁
          simp only [h₁, Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact .ifNZ_true hc (ih _ h₁)
    | .whileNZ g cc b =>
      simp only [run] at h
      cases hg : run C tape f g s with
      | none =>
        simp only [hg, Option.bind_eq_bind, Option.bind_none] at h
        cases h
      | some rg =>
        obtain ⟨s₁, tg, dg, pg⟩ := rg
        simp only [hg, Option.bind_eq_bind, Option.bind_some] at h
        by_cases hz : s₁.regs cc = 0
        · rw [if_pos hz] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact .while_done (ih _ hg) hz
        · rw [if_neg hz] at h
          cases hb : run C tape f b s₁ with
          | none =>
            simp only [hb, Option.bind_none] at h
            cases h
          | some rb =>
            obtain ⟨s₂, tb, db, pb⟩ := rb
            simp only [hb, Option.bind_some] at h
            cases hl : run C tape f (.whileNZ g cc b) s₂ with
            | none =>
              simp only [hl, Option.bind_none] at h
              cases h
            | some rl =>
              obtain ⟨s₃, tl, dl, pl⟩ := rl
              simp only [hl, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl, rfl⟩ := h
              exact .while_step (ih _ hg) hz (ih _ hb) (ih _ hl)

end Caliper
