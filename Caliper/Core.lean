import Mathlib.Tactic

/-!
# A unit-cost machine model

This is the core of a small imperative language whose **every instruction runs in
constant time**, intended as a compilation target for Clean's witness-generation IR
(`Clean/Circuit/WitnessIR.lean`). Programs in this language carry machine-checked
*upper bounds* on running time and memory.

## Why not a RAM machine?

A flat address space forces every proof about two data structures to first establish
that their address ranges are disjoint — separation logic, in other words. Instead the
machine has an unbounded supply of **independent, named buffers**. Two buffers are
either the same buffer or completely disjoint, so the only "separation" fact a proof
ever needs is `b₁ ≠ b₂` on buffer *names*, which is a decidable statement about `ℕ`.
See `bufs_set_ne` — that lemma is the entire separation theory.

Buffer names are part of the *syntax*, not values held in registers, so a program can
never alias two buffers at runtime. Buffer *lengths* are fully dynamic; only the number
of distinct buffers is fixed statically (and `Builder.lean` allocates those names
automatically, so this is invisible when writing programs).

## What "unit time" means here

Every constructor of `Stmt` other than `seq`/`ifNZ`/`whileNZ` maps to one instruction
whose cost is drawn from a `CostModel` — a table indexed by the *instruction*, never by
the *state*. That is the formal content of "unit time": see `straight_time_eq`, which
says a branch-free program's running time is a syntactic constant, independent of its
input. (That also makes branch-free code constant-time in the side-channel sense.)

Two consequences for the instruction set:

* Memory is *reserved*, not initialised: `bufAlloc b n` reserves capacity for `n`
  words in O(1) — a `malloc` without `memset`. Reads are only allowed below the
  *filled* length (`bufGet` requires `i < size`), so uninitialised capacity is never
  observable, and initialisation is paid for by the `bufPush`/`bufSet` instructions
  that perform it. There is no instruction that both allocates and initialises `n`
  words — that would hide `O(n)` work in one tick.
* `bufPush` requires free capacity (`size < cap` — a proof obligation, like the
  in-range obligation of `bufGet`) and is therefore **worst-case** unit time: no
  doubling, no amortisation anywhere in the machine. A growable vector is a *library*
  on top — its realloc-copy loop costs what it visibly costs, and its amortised spec
  is proved in the program logic rather than trusted in the machine.

## Cost is a time and a memory *profile*

`Exec C c s s' t d p` says: from `s`, statement `c` terminates in `s'`, having spent
`t` time units, with **net** live-memory change `d` (in words, signed) and **peak**
live-memory growth `p` above the starting level. Live memory is the sum of reserved
capacities: `bufAlloc` charges `n - oldCap`, `bufFree` credits the capacity back, and
`bufPush`/`bufPop` move the fill level inside already-charged capacity, so they are
memory-neutral. Profiles compose like resource high-water marks:

    seq:  net = d₁ + d₂        peak = max p₁ (d₁ + p₂)

so memory *reuse* is visible: code that frees (or works inside fixed capacity) does
not accumulate a phantom footprint, and a working buffer reused across `n` loop
iterations is charged once, not `n` times (see `ScratchLoop` in `Examples.lean`).
`0 ≤ p` and `d ≤ p` always (`peak_nonneg`, `net_le_peak`); code containing no
`bufAlloc` has `d ≤ 0 ∧ p ≤ 0` (`allocFree_space`). Time stays a plain `ℕ`; the
memory indices are `ℤ` so that `omega` closes the arithmetic.

Out-of-range buffer accesses have *no* `Exec` derivation, so exhibiting a derivation
(which is what a `Triple` does) proves memory safety along the way.
-/

namespace LowLevel

/-- Registers are unbounded in number; the builder allocates them, so a program uses
finitely many and a real compiler would give each one a stack slot. -/
abbrev Reg := ℕ

/-- Buffer names. Static: part of the syntax, never a runtime value. -/
abbrev BufId := ℕ

/-- Machine words. Fixed at `w = 64` for Clean's witgen backend. -/
abbrev Word (w : ℕ) := BitVec w

variable {w : ℕ}

/-! ## Operations -/

inductive UnOp where
  | not | neg | isZero | isNonZero
deriving DecidableEq, Repr, Inhabited

inductive BinOp where
  | add | sub | mul
  /-- High word of the widening unsigned multiply (`MULHU` on RISC-V M, `UMULH` on
  AArch64, the `RDX` half of `MUL` on x86-64). `mulhi` + `mul` give the full
  `2w`-bit product — the primitive that field reduction (Goldilocks, Montgomery)
  needs. -/
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
x86/ARM, where the shift amount is masked, must emit an explicit mask; see
`doc/lowlevel-dsl.md`. -/
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

/-- Statements. The whole language: this is what the cost model has to be trusted
about, and it is deliberately tiny. Structures, typed values, arrays-of-structs and
subroutines are all built on top at *generation* time (`Builder.lean`) and compile away
to exactly these instructions. -/
inductive Stmt (w : ℕ) where
  /-- No-op. -/
  | skip
  /-- Sequencing, written `c₁ ;; c₂`. -/
  | seq (c₁ c₂ : Stmt w)
  /-- `d ← v` -/
  | imm (d : Reg) (v : Word w)
  /-- `d ← a` -/
  | mov (d a : Reg)
  /-- `d ← op a` -/
  | un (op : UnOp) (d a : Reg)
  /-- `d ← a op b` -/
  | bin (op : BinOp) (d a b : Reg)
  /-- `b ← alloc(regs n)`: reserve capacity for that many words, empty fill. Frees
  whatever `b` previously held. Reserved words are charged but uninitialised —
  unreadable until pushed. -/
  | bufAlloc (b : BufId) (n : Reg)
  /-- `free b`: release `b`'s capacity entirely. -/
  | bufFree (b : BufId)
  /-- `d ← |b|` (the filled length, not the capacity). -/
  | bufLen (d : Reg) (b : BufId)
  /-- `d ← b[i]`; requires `i < |b|`. -/
  | bufGet (d : Reg) (b : BufId) (i : Reg)
  /-- `b[i] ← src`; requires `i < |b|`. -/
  | bufSet (b : BufId) (i src : Reg)
  /-- `b.push src`; requires free capacity (`|b| < cap b`), hence worst-case unit
  time. Memory-neutral: the word was charged at `bufAlloc`. -/
  | bufPush (b : BufId) (src : Reg)
  /-- `b.pop`; a no-op on an empty buffer. Keeps the capacity, so memory-neutral. -/
  | bufPop (b : BufId)
  | ifNZ (c : Reg) (thn els : Stmt w)
  /-- `guard; while (c ≠ 0) { body; guard }`. The guard is a *statement* because
  computing a loop condition costs real instructions; making it an expression would
  smuggle in unaccounted work. `c` is the register the guard leaves its verdict in. -/
  | whileNZ (guard : Stmt w) (c : Reg) (body : Stmt w)
deriving Repr, Inhabited, BEq

@[inherit_doc] infixr:60 " ;; " => Stmt.seq

/-! ## Cost model

The costs of the individual instructions. Every field is a function of the
*instruction* only — nothing here can look at the machine state, which is exactly why
running time is data-independent. The default is the uniform model (everything 1); the
`cycles` model below is a rough Skylake-ish latency table, and any bound proved
generically over `C` instantiates to both. -/
structure CostModel where
  imm : ℕ := 1
  mov : ℕ := 1
  un : UnOp → ℕ := fun _ => 1
  bin : BinOp → ℕ := fun _ => 1
  /-- Capacity reservation without initialisation — `malloc`, constant time. -/
  bufAlloc : ℕ := 1
  bufFree : ℕ := 1
  bufLen : ℕ := 1
  bufGet : ℕ := 1
  bufSet : ℕ := 1
  bufPush : ℕ := 1
  bufPop : ℕ := 1
  /-- Cost of testing a condition register and taking the branch. -/
  branch : ℕ := 1

/-- Uniform model: every instruction costs 1. -/
def CostModel.unit : CostModel := {}

/-- A coarse "cycles on a modern out-of-order core" model. Included to show that
bounds proved generically over `C` are not tied to the uniform model. -/
def CostModel.cycles : CostModel where
  bin := fun op => match op with
    | .mul | .mulhi => 3
    | .udiv | .umod => 30
    | _ => 1
  bufAlloc := 50  -- malloc fast path
  bufFree := 30
  bufGet := 4     -- L1 hit
  bufSet := 4
  bufPush := 5
  branch := 2     -- mispredict-amortised

/-! ## Machine state -/

/-- Registers hold words; buffers hold arrays of words (the filled prefix) plus a
reserved capacity. All indexed by `ℕ` and represented as functions, which makes the
separation lemmas below one-liners. Buffers are real `Array`s so that the interpreter
does not walk a closure chain per element. -/
structure State (w : ℕ) where
  regs : Reg → Word w
  bufs : BufId → Array (Word w)
  /-- Reserved capacity in words; live memory is the sum of capacities. -/
  caps : BufId → ℕ

/-- The initial state: all registers zero, all buffers empty and unallocated. -/
def State.init (w : ℕ) : State w where
  regs _ := 0
  bufs _ := #[]
  caps _ := 0

def State.setReg (s : State w) (d : Reg) (v : Word w) : State w :=
  { s with regs := fun r => if r = d then v else s.regs r }

/-- Update the filled contents of `b` (capacity unchanged). -/
def State.setBuf (s : State w) (b : BufId) (a : Array (Word w)) : State w :=
  { s with bufs := fun b' => if b' = b then a else s.bufs b' }

/-- Reserve capacity `n` for `b`, dropping its old contents and capacity.
`allocBuf b 0` is `bufFree`'s effect. -/
def State.allocBuf (s : State w) (b : BufId) (n : ℕ) : State w :=
  { s with bufs := fun b' => if b' = b then #[] else s.bufs b',
           caps := fun b' => if b' = b then n else s.caps b' }

@[simp] theorem regs_setReg_self (s : State w) (d : Reg) (v : Word w) :
    (s.setReg d v).regs d = v := by simp [State.setReg]

@[simp] theorem regs_setReg_ne (s : State w) {d r : Reg} (v : Word w) (h : r ≠ d) :
    (s.setReg d v).regs r = s.regs r := by simp [State.setReg, h]

@[simp] theorem bufs_setReg (s : State w) (d : Reg) (v : Word w) :
    (s.setReg d v).bufs = s.bufs := rfl

@[simp] theorem bufs_setBuf_self (s : State w) (b : BufId) (a : Array (Word w)) :
    (s.setBuf b a).bufs b = a := by simp [State.setBuf]

/-- **The entire separation theory.** Writing buffer `b` leaves buffer `b'` alone, and
the side condition is a decidable statement about two `ℕ`s. -/
@[simp] theorem bufs_setBuf_ne (s : State w) {b b' : BufId} (a : Array (Word w))
    (h : b' ≠ b) : (s.setBuf b a).bufs b' = s.bufs b' := by simp [State.setBuf, h]

@[simp] theorem regs_setBuf (s : State w) (b : BufId) (a : Array (Word w)) :
    (s.setBuf b a).regs = s.regs := rfl

@[simp] theorem caps_setBuf (s : State w) (b : BufId) (a : Array (Word w)) :
    (s.setBuf b a).caps = s.caps := rfl

@[simp] theorem caps_setReg (s : State w) (d : Reg) (v : Word w) :
    (s.setReg d v).caps = s.caps := rfl

@[simp] theorem regs_allocBuf (s : State w) (b : BufId) (n : ℕ) :
    (s.allocBuf b n).regs = s.regs := rfl

@[simp] theorem bufs_allocBuf_self (s : State w) (b : BufId) (n : ℕ) :
    (s.allocBuf b n).bufs b = #[] := by simp [State.allocBuf]

@[simp] theorem bufs_allocBuf_ne (s : State w) {b b' : BufId} (n : ℕ)
    (h : b' ≠ b) : (s.allocBuf b n).bufs b' = s.bufs b' := by simp [State.allocBuf, h]

@[simp] theorem caps_allocBuf_self (s : State w) (b : BufId) (n : ℕ) :
    (s.allocBuf b n).caps b = n := by simp [State.allocBuf]

@[simp] theorem caps_allocBuf_ne (s : State w) {b b' : BufId} (n : ℕ)
    (h : b' ≠ b) : (s.allocBuf b n).caps b' = s.caps b' := by simp [State.allocBuf, h]

/-! ## Semantics

`Exec C c s s' t d p`: statement `c` takes state `s` to `s'`, spending `t` time units,
changing live memory by `d` words (net, signed) with peak growth `p`.

Out-of-range `bufGet`/`bufSet` simply have no rule, so a derivation witnesses memory
safety. -/
inductive Exec (C : CostModel) : Stmt w → State w → State w → ℕ → ℤ → ℤ → Prop where
  | skip {s} : Exec C .skip s s 0 0 0
  | seq {c₁ c₂ s s₁ s₂ t₁ d₁ p₁ t₂ d₂ p₂} :
      Exec C c₁ s s₁ t₁ d₁ p₁ → Exec C c₂ s₁ s₂ t₂ d₂ p₂ →
      Exec C (c₁ ;; c₂) s s₂ (t₁ + t₂) (d₁ + d₂) (max p₁ (d₁ + p₂))
  | imm {d v s} : Exec C (.imm d v) s (s.setReg d v) C.imm 0 0
  | mov {d a s} : Exec C (.mov d a) s (s.setReg d (s.regs a)) C.mov 0 0
  | un {op d a s} :
      Exec C (.un op d a) s (s.setReg d (op.eval (s.regs a))) (C.un op) 0 0
  | bin {op d a b s} :
      Exec C (.bin op d a b) s (s.setReg d (op.eval (s.regs a) (s.regs b)))
        (C.bin op) 0 0
  /-- Reserve capacity: charges the new capacity, credits the old. -/
  | bufAlloc {b n s} :
      Exec C (.bufAlloc b n) s (s.allocBuf b (s.regs n).toNat) C.bufAlloc
        (((s.regs n).toNat : ℤ) - (s.caps b : ℤ))
        (max (((s.regs n).toNat : ℤ) - (s.caps b : ℤ)) 0)
  /-- Free: credits the whole capacity. -/
  | bufFree {b s} :
      Exec C (.bufFree b) s (s.allocBuf b 0) C.bufFree (-(s.caps b : ℤ)) 0
  | bufLen {d b s} :
      Exec C (.bufLen d b) s (s.setReg d (BitVec.ofNat w (s.bufs b).size)) C.bufLen 0 0
  | bufGet {d b i s} (h : (s.regs i).toNat < (s.bufs b).size) :
      Exec C (.bufGet d b i) s (s.setReg d (s.bufs b)[(s.regs i).toNat]) C.bufGet 0 0
  | bufSet {b i src s} (h : (s.regs i).toNat < (s.bufs b).size) :
      Exec C (.bufSet b i src) s
        (s.setBuf b ((s.bufs b).set (s.regs i).toNat (s.regs src) h)) C.bufSet 0 0
  /-- Push requires free capacity — no rule otherwise, so a derivation proves the
  program stays within what it reserved. Memory-neutral. -/
  | bufPush {b src s} (h : (s.bufs b).size < s.caps b) :
      Exec C (.bufPush b src) s (s.setBuf b ((s.bufs b).push (s.regs src)))
        C.bufPush 0 0
  /-- Pop keeps the capacity: memory-neutral. -/
  | bufPop {b s} :
      Exec C (.bufPop b) s (s.setBuf b (s.bufs b).pop) C.bufPop 0 0
  | ifNZ_true {c thn els s s' t d p} (h : s.regs c ≠ 0) :
      Exec C thn s s' t d p → Exec C (.ifNZ c thn els) s s' (C.branch + t) d p
  | ifNZ_false {c thn els s s' t d p} (h : s.regs c = 0) :
      Exec C els s s' t d p → Exec C (.ifNZ c thn els) s s' (C.branch + t) d p
  | while_done {g c b s s₁ tg dg pg} :
      Exec C g s s₁ tg dg pg → s₁.regs c = 0 →
      Exec C (.whileNZ g c b) s s₁ (tg + C.branch) dg pg
  | while_step {g c b s s₁ s₂ s₃ tg dg pg tb db pb tl dl pl} :
      Exec C g s s₁ tg dg pg → s₁.regs c ≠ 0 → Exec C b s₁ s₂ tb db pb →
      Exec C (.whileNZ g c b) s₂ s₃ tl dl pl →
      Exec C (.whileNZ g c b) s s₃ (tg + C.branch + tb + tl) (dg + db + dl)
        (max pg (dg + max pb (db + pl)))

/-! ## Basic metatheory -/

/-- The machine is deterministic: a statement has at most one outcome, and in
particular at most one cost. So "the" running time is well defined and an upper bound
proved for one execution is a bound on all of them. -/
theorem Exec.deterministic {C : CostModel} {c : Stmt w} {s s₁ s₂ : State w}
    {t₁ t₂ : ℕ} {d₁ p₁ d₂ p₂ : ℤ}
    (h₁ : Exec C c s s₁ t₁ d₁ p₁) (h₂ : Exec C c s s₂ t₂ d₂ p₂) :
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
    {d p : ℤ} (h : Exec C c s s' t d p) : 0 ≤ p := by
  induction h <;> omega

/-- The net change is bounded by the peak. -/
theorem Exec.net_le_peak {C : CostModel} {c : Stmt w} {s s' : State w} {t : ℕ}
    {d p : ℤ} (h : Exec C c s s' t d p) : d ≤ p := by
  induction h <;> omega

/-! ### Framing: which registers and buffers a statement can touch

These are the ergonomic replacement for separation logic. Both are computed
syntactically, hence decidable, hence dischargeable by `simp`/`decide` on the concrete
code the builder produces. -/

/-- `c.Writes r`: `c` may assign register `r`. -/
def Stmt.Writes : Stmt w → Reg → Prop
  | .skip, _ => False
  | .seq c₁ c₂, r => c₁.Writes r ∨ c₂.Writes r
  | .imm d _, r => r = d
  | .mov d _, r => r = d
  | .un _ d _, r => r = d
  | .bin _ d _ _, r => r = d
  | .bufAlloc .., _ => False
  | .bufFree _, _ => False
  | .bufLen d _, r => r = d
  | .bufGet d _ _, r => r = d
  | .bufSet .., _ => False
  | .bufPush .., _ => False
  | .bufPop _, _ => False
  | .ifNZ _ t e, r => t.Writes r ∨ e.Writes r
  | .whileNZ g _ b, r => g.Writes r ∨ b.Writes r

/-- `c.Touches b`: `c` may modify buffer `b`. -/
def Stmt.Touches : Stmt w → BufId → Prop
  | .skip, _ => False
  | .seq c₁ c₂, b => c₁.Touches b ∨ c₂.Touches b
  | .bufAlloc b' _, b => b = b'
  | .bufFree b', b => b = b'
  | .bufSet b' _ _, b => b = b'
  | .bufPush b' _, b => b = b'
  | .bufPop b', b => b = b'
  | .ifNZ _ t e, b => t.Touches b ∨ e.Touches b
  | .whileNZ g _ bd, b => g.Touches b ∨ bd.Touches b
  | _, _ => False

instance instDecidableWrites : ∀ (c : Stmt w) (r : Reg), Decidable (c.Writes r)
  | .skip, _ => inferInstanceAs (Decidable False)
  | .seq c₁ c₂, r =>
    have := instDecidableWrites c₁ r
    have := instDecidableWrites c₂ r
    inferInstanceAs (Decidable (_ ∨ _))
  | .imm d _, r => inferInstanceAs (Decidable (r = d))
  | .mov d _, r => inferInstanceAs (Decidable (r = d))
  | .un _ d _, r => inferInstanceAs (Decidable (r = d))
  | .bin _ d _ _, r => inferInstanceAs (Decidable (r = d))
  | .bufAlloc .., _ => inferInstanceAs (Decidable False)
  | .bufFree _, _ => inferInstanceAs (Decidable False)
  | .bufLen d _, r => inferInstanceAs (Decidable (r = d))
  | .bufGet d _ _, r => inferInstanceAs (Decidable (r = d))
  | .bufSet .., _ => inferInstanceAs (Decidable False)
  | .bufPush .., _ => inferInstanceAs (Decidable False)
  | .bufPop _, _ => inferInstanceAs (Decidable False)
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
  | .imm .., _ => inferInstanceAs (Decidable False)
  | .mov .., _ => inferInstanceAs (Decidable False)
  | .un .., _ => inferInstanceAs (Decidable False)
  | .bin .., _ => inferInstanceAs (Decidable False)
  | .bufAlloc b' _, b => inferInstanceAs (Decidable (b = b'))
  | .bufFree b', b => inferInstanceAs (Decidable (b = b'))
  | .bufLen .., _ => inferInstanceAs (Decidable False)
  | .bufGet .., _ => inferInstanceAs (Decidable False)
  | .bufSet b' _ _, b => inferInstanceAs (Decidable (b = b'))
  | .bufPush b' _, b => inferInstanceAs (Decidable (b = b'))
  | .bufPop b', b => inferInstanceAs (Decidable (b = b'))
  | .ifNZ _ t e, b =>
    have := instDecidableTouches t b
    have := instDecidableTouches e b
    inferInstanceAs (Decidable (_ ∨ _))
  | .whileNZ g _ bd, b =>
    have := instDecidableTouches g b
    have := instDecidableTouches bd b
    inferInstanceAs (Decidable (_ ∨ _))

@[simp] theorem Writes_skip (r : Reg) : (Stmt.skip (w := w)).Writes r ↔ False := Iff.rfl
@[simp] theorem Writes_seq (c₁ c₂ : Stmt w) (r : Reg) :
    (c₁ ;; c₂).Writes r ↔ c₁.Writes r ∨ c₂.Writes r := Iff.rfl
@[simp] theorem Touches_skip (b : BufId) : (Stmt.skip (w := w)).Touches b ↔ False := Iff.rfl
@[simp] theorem Touches_seq (c₁ c₂ : Stmt w) (b : BufId) :
    (c₁ ;; c₂).Touches b ↔ c₁.Touches b ∨ c₂.Touches b := Iff.rfl

/-- Register frame rule. -/
theorem Exec.frame_reg {C : CostModel} {c : Stmt w} {s s' : State w} {t : ℕ}
    {d p : ℤ} {r : Reg}
    (h : Exec C c s s' t d p) (hr : ¬ c.Writes r) : s'.regs r = s.regs r := by
  induction h with
  | skip => rfl
  | seq _ _ ih₁ ih₂ =>
    simp only [Writes_seq, not_or] at hr
    rw [ih₂ hr.2, ih₁ hr.1]
  | imm | mov | un | bin | bufLen | bufGet =>
    exact regs_setReg_ne _ _ hr
  | bufAlloc | bufFree | bufSet | bufPush | bufPop => rfl
  | ifNZ_true _ _ ih => exact ih fun hh => hr (Or.inl hh)
  | ifNZ_false _ _ ih => exact ih fun hh => hr (Or.inr hh)
  | while_done _ _ ihg => exact ihg fun hh => hr (Or.inl hh)
  | while_step _ _ _ _ ihg ihb ihl =>
    rw [ihl hr, ihb fun hh => hr (Or.inr hh), ihg fun hh => hr (Or.inl hh)]

/-- Buffer frame rule — the analogue of a separation-logic frame, but with a decidable
side condition instead of an entailment. -/
theorem Exec.frame_buf {C : CostModel} {c : Stmt w} {s s' : State w} {t : ℕ}
    {d p : ℤ} {b : BufId}
    (h : Exec C c s s' t d p) (hb : ¬ c.Touches b) : s'.bufs b = s.bufs b := by
  induction h with
  | skip => rfl
  | seq _ _ ih₁ ih₂ =>
    simp only [Touches_seq, not_or] at hb
    rw [ih₂ hb.2, ih₁ hb.1]
  | imm | mov | un | bin | bufLen | bufGet => rfl
  | bufSet | bufPush | bufPop => exact bufs_setBuf_ne _ _ hb
  | bufAlloc | bufFree => exact bufs_allocBuf_ne _ _ hb
  | ifNZ_true _ _ ih => exact ih fun hh => hb (Or.inl hh)
  | ifNZ_false _ _ ih => exact ih fun hh => hb (Or.inr hh)
  | while_done _ _ ihg => exact ihg fun hh => hb (Or.inl hh)
  | while_step _ _ _ _ ihg ihb ihl =>
    rw [ihl hb, ihb fun hh => hb (Or.inr hh), ihg fun hh => hb (Or.inl hh)]

/-- Capacity frame rule: an untouched buffer keeps its reserved capacity too. -/
theorem Exec.frame_cap {C : CostModel} {c : Stmt w} {s s' : State w} {t : ℕ}
    {d p : ℤ} {b : BufId}
    (h : Exec C c s s' t d p) (hb : ¬ c.Touches b) : s'.caps b = s.caps b := by
  induction h with
  | skip => rfl
  | seq _ _ ih₁ ih₂ =>
    simp only [Touches_seq, not_or] at hb
    rw [ih₂ hb.2, ih₁ hb.1]
  | imm | mov | un | bin | bufLen | bufGet => rfl
  | bufSet | bufPush | bufPop => rfl
  | bufAlloc | bufFree => exact caps_allocBuf_ne _ _ hb
  | ifNZ_true _ _ ih => exact ih fun hh => hb (Or.inl hh)
  | ifNZ_false _ _ ih => exact ih fun hh => hb (Or.inr hh)
  | while_done _ _ ihg => exact ihg fun hh => hb (Or.inl hh)
  | while_step _ _ _ _ ihg ihb ihl =>
    rw [ihl hb, ihb fun hh => hb (Or.inr hh), ihg fun hh => hb (Or.inl hh)]

/-! ### Unit time, precisely

A statement with no branches costs a syntactically-determined number of time units, for
*every* input state. This is the theorem that makes the cost model meaningful: nothing
in the machine can make an instruction cheaper or more expensive depending on data. -/

/-- No `ifNZ`, no `whileNZ`. -/
def Stmt.Straight : Stmt w → Prop
  | .seq c₁ c₂ => c₁.Straight ∧ c₂.Straight
  | .ifNZ .. => False
  | .whileNZ .. => False
  | _ => True

/-- The syntactic running time of a branch-free statement. -/
def Stmt.staticTime (C : CostModel) : Stmt w → ℕ
  | .skip => 0
  | .seq c₁ c₂ => c₁.staticTime C + c₂.staticTime C
  | .imm .. => C.imm
  | .mov .. => C.mov
  | .un op .. => C.un op
  | .bin op .. => C.bin op
  | .bufAlloc .. => C.bufAlloc
  | .bufFree _ => C.bufFree
  | .bufLen .. => C.bufLen
  | .bufGet .. => C.bufGet
  | .bufSet .. => C.bufSet
  | .bufPush .. => C.bufPush
  | .bufPop _ => C.bufPop
  | .ifNZ _ t e => t.staticTime C + e.staticTime C
  | .whileNZ .. => 0

/-- `c` contains no `bufAlloc` — anywhere, including under branches and loops. -/
def Stmt.AllocFree : Stmt w → Prop
  | .seq c₁ c₂ => c₁.AllocFree ∧ c₂.AllocFree
  | .ifNZ _ t e => t.AllocFree ∧ e.AllocFree
  | .whileNZ g _ b => g.AllocFree ∧ b.AllocFree
  | .bufAlloc .. => False
  | _ => True

/-- **Branch-free code runs in constant time.** The running time is a function of the
syntax alone — it does not mention the state. -/
theorem Exec.straight_time_eq {C : CostModel} {c : Stmt w} {s s' : State w} {t : ℕ}
    {d p : ℤ} (h : Exec C c s s' t d p) (hs : c.Straight) : t = c.staticTime C := by
  induction h with
  | seq _ _ ih₁ ih₂ => exact congrArg₂ (· + ·) (ih₁ hs.1) (ih₂ hs.2)
  | ifNZ_true | ifNZ_false | while_done | while_step => exact hs.elim
  | _ => rfl

/-- Memory only ever enters through `bufAlloc`: alloc-free code — straight-line or
not — has non-positive net and zero peak growth. -/
theorem Exec.allocFree_space {C : CostModel} {c : Stmt w} {s s' : State w} {t : ℕ}
    {d p : ℤ} (h : Exec C c s s' t d p) (ha : c.AllocFree) :
    d ≤ 0 ∧ p ≤ 0 := by
  induction h with
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨h1, h2⟩ := ih₁ ha.1
    obtain ⟨h3, h4⟩ := ih₂ ha.2
    omega
  | bufAlloc => exact ha.elim
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
their inputs. (This is also a constant-time / side-channel statement.) -/
theorem Exec.straight_data_independent {C : CostModel} {c : Stmt w}
    {s₁ s₁' s₂ s₂' : State w} {t₁ t₂ : ℕ} {d₁ p₁ d₂ p₂ : ℤ}
    (h₁ : Exec C c s₁ s₁' t₁ d₁ p₁) (h₂ : Exec C c s₂ s₂' t₂ d₂ p₂)
    (hs : c.Straight) : t₁ = t₂ :=
  (h₁.straight_time_eq hs).trans (h₂.straight_time_eq hs).symm

/-! ## Reference interpreter

Executable semantics, agreeing with `Exec`. `fuel` bounds the recursion depth (every
recursive call consumes one unit, so any `fuel ≥` statement depth × loop trip counts
suffices); `none` means "ran out of fuel, or hit an out-of-range buffer access".
Fuel is an interpreter artifact only — no cost is derived from it. -/

def run (C : CostModel) : ℕ → Stmt w → State w → Option (State w × ℕ × ℤ × ℤ)
  | 0, _, _ => none
  | f + 1, c, s =>
    match c with
    | .skip => some (s, 0, 0, 0)
    | .seq c₁ c₂ => do
        let (s₁, t₁, d₁, p₁) ← run C f c₁ s
        let (s₂, t₂, d₂, p₂) ← run C f c₂ s₁
        some (s₂, t₁ + t₂, d₁ + d₂, max p₁ (d₁ + p₂))
    | .imm d v => some (s.setReg d v, C.imm, 0, 0)
    | .mov d a => some (s.setReg d (s.regs a), C.mov, 0, 0)
    | .un op d a => some (s.setReg d (op.eval (s.regs a)), C.un op, 0, 0)
    | .bin op d a b =>
        some (s.setReg d (op.eval (s.regs a) (s.regs b)), C.bin op, 0, 0)
    | .bufAlloc b n =>
        some (s.allocBuf b (s.regs n).toNat, C.bufAlloc,
          ((s.regs n).toNat : ℤ) - (s.caps b : ℤ),
          max (((s.regs n).toNat : ℤ) - (s.caps b : ℤ)) 0)
    | .bufFree b => some (s.allocBuf b 0, C.bufFree, -(s.caps b : ℤ), 0)
    | .bufLen d b =>
        some (s.setReg d (BitVec.ofNat w (s.bufs b).size), C.bufLen, 0, 0)
    | .bufGet d b i =>
        if h : (s.regs i).toNat < (s.bufs b).size then
          some (s.setReg d (s.bufs b)[(s.regs i).toNat], C.bufGet, 0, 0)
        else none
    | .bufSet b i src =>
        if h : (s.regs i).toNat < (s.bufs b).size then
          some (s.setBuf b ((s.bufs b).set (s.regs i).toNat (s.regs src) h),
            C.bufSet, 0, 0)
        else none
    | .bufPush b src =>
        if h : (s.bufs b).size < s.caps b then
          some (s.setBuf b ((s.bufs b).push (s.regs src)), C.bufPush, 0, 0)
        else none
    | .bufPop b => some (s.setBuf b (s.bufs b).pop, C.bufPop, 0, 0)
    | .ifNZ c thn els =>
        if s.regs c = 0 then do
          let (s', t, d, p) ← run C f els s
          some (s', C.branch + t, d, p)
        else do
          let (s', t, d, p) ← run C f thn s
          some (s', C.branch + t, d, p)
    | .whileNZ g cc b => do
        let (s₁, tg, dg, pg) ← run C f g s
        if s₁.regs cc = 0 then
          some (s₁, tg + C.branch, dg, pg)
        else do
          let (s₂, tb, db, pb) ← run C f b s₁
          let (s₃, tl, dl, pl) ← run C f (.whileNZ g cc b) s₂
          some (s₃, tg + C.branch + tb + tl, dg + db + dl,
            max pg (dg + max pb (db + pl)))

/-- The interpreter is sound: anything it computes is a real execution, with exactly
the costs it reports. So `#eval`-ing a program gives numbers that the `Exec`-level
theorems are about. -/
theorem run_sound {C : CostModel} : ∀ (f : ℕ) (c : Stmt w) {s s' : State w} {t : ℕ} {d p : ℤ},
    run C f c s = some (s', t, d, p) → Exec C c s s' t d p := by
  intro f
  induction f with
  | zero => intro c s s' t d p h; simp [run] at h
  | succ f ih =>
    intro c s s' t d p h
    match c with
    | .skip =>
      simp only [run, Option.some.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact .skip
    | .seq c₁ c₂ =>
      simp only [run] at h
      cases h₁ : run C f c₁ s with
      | none => simp [h₁] at h
      | some r₁ =>
        obtain ⟨s₁, t₁, d₁, p₁⟩ := r₁
        simp only [h₁, Option.bind_eq_bind, Option.bind_some] at h
        cases h₂ : run C f c₂ s₁ with
        | none => simp [h₂] at h
        | some r₂ =>
          obtain ⟨s₂, t₂, d₂, p₂⟩ := r₂
          simp only [h₂, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact .seq (ih _ h₁) (ih _ h₂)
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
    | .bufAlloc b n =>
      simp only [run, Option.some.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact .bufAlloc
    | .bufFree b =>
      simp only [run, Option.some.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact .bufFree
    | .bufLen d b =>
      simp only [run, Option.some.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact .bufLen
    | .bufGet d b i =>
      simp only [run] at h
      split at h
      · simp only [Option.some.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact .bufGet ‹_›
      · exact absurd h (by simp)
    | .bufSet b i src =>
      simp only [run] at h
      split at h
      · simp only [Option.some.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact .bufSet ‹_›
      · exact absurd h (by simp)
    | .bufPush b src =>
      simp only [run] at h
      split at h
      · simp only [Option.some.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact .bufPush ‹_›
      · exact absurd h (by simp)
    | .bufPop b =>
      simp only [run, Option.some.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact .bufPop
    | .ifNZ c thn els =>
      simp only [run] at h
      by_cases hc : s.regs c = 0
      · rw [if_pos hc] at h
        cases h₁ : run C f els s with
        | none => simp [h₁] at h
        | some r₁ =>
          obtain ⟨s₁, t₁, d₁, p₁⟩ := r₁
          simp only [h₁, Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact .ifNZ_false hc (ih _ h₁)
      · rw [if_neg hc] at h
        cases h₁ : run C f thn s with
        | none => simp [h₁] at h
        | some r₁ =>
          obtain ⟨s₁, t₁, d₁, p₁⟩ := r₁
          simp only [h₁, Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact .ifNZ_true hc (ih _ h₁)
    | .whileNZ g cc b =>
      simp only [run] at h
      cases hg : run C f g s with
      | none => simp [hg] at h
      | some rg =>
        obtain ⟨s₁, tg, dg, pg⟩ := rg
        simp only [hg, Option.bind_eq_bind, Option.bind_some] at h
        by_cases hz : s₁.regs cc = 0
        · rw [if_pos hz] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact .while_done (ih _ hg) hz
        · rw [if_neg hz] at h
          cases hb : run C f b s₁ with
          | none => simp [hb] at h
          | some rb =>
            obtain ⟨s₂, tb, db, pb⟩ := rb
            simp only [hb, Option.bind_some] at h
            cases hl : run C f (.whileNZ g cc b) s₂ with
            | none => simp [hl] at h
            | some rl =>
              obtain ⟨s₃, tl, dl, pl⟩ := rl
              simp only [hl, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl, rfl⟩ := h
              exact .while_step (ih _ hg) hz (ih _ hb) (ih _ hl)

end LowLevel
