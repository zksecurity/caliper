import Clean.Caliper.Core

/-!
# Surface syntax: the program builder

`Stmt` is deliberately austere — three-address code over registers and named buffers.
This file is the ergonomic layer for *writing* programs: a builder monad with

* automatic allocation of registers and buffer names (`freshReg`, `freshBuf`),
* an expression language `Exp` that compiles compound arithmetic to three-address
  code through fresh temporaries,
* structured control flow (`if_`, `while_`) whose guards are builder actions, so
  guard *cost* is real emitted code, never a free side condition,
* subroutines as plain Lean functions `... → Build w α` — calling one splices its
  code in with fresh temporaries, so caller and callee cannot clash on registers.

Everything here is *generation-time only*: `build` runs the monad and returns a plain
`Stmt`, and that `Stmt` is what specs and cost theorems are about. The builder adds
nothing to the trusted surface — `Clean/Caliper/Examples.lean` checks by `rfl` that
builder output coincides with hand-written core syntax.

Data structures follow the same pattern: a "struct" is a Lean-level record of
registers/buffer names, an array-of-structs is a buffer with a stride convention, and
the accessor functions are ordinary Lean functions emitting indexing code. Because
buffer names are static, two different structures can never alias.
-/

namespace Caliper

variable {w : ℕ}

/-- Builder state: fresh-name counters and the code emitted so far (in order). -/
structure BuildState (w : ℕ) where
  nextReg : ℕ := 0
  nextBuf : ℕ := 0
  /-- Emitted code, in **reverse** order (prepending keeps generation linear;
  `capture`/`build` reverse once at the end). -/
  code : List (Stmt w) := []

/-- The program-builder monad. -/
def Build (w : ℕ) (α : Type) := BuildState w → α × BuildState w

namespace Build

instance : Monad (Build w) where
  pure a := fun s => (a, s)
  bind m f := fun s => let (a, s') := m s; f a s'

def freshReg : Build w Reg :=
  fun s => (s.nextReg, { s with nextReg := s.nextReg + 1 })

def freshBuf : Build w BufId :=
  fun s => (s.nextBuf, { s with nextBuf := s.nextBuf + 1 })

def emit (c : Stmt w) : Build w Unit :=
  fun s => ((), { s with code := c :: s.code })

/-- Right-nested sequencing of a code list (no trailing `skip`). -/
def seqAll : List (Stmt w) → Stmt w
  | [] => .skip
  | [c] => c
  | c :: cs => c ;; seqAll cs

/-- Run a sub-builder, capturing its code instead of emitting it. Fresh-name counters
keep advancing, so captured blocks never clash with the surrounding code. -/
def capture {α : Type} (m : Build w α) : Build w (α × Stmt w) := fun s =>
  let (a, s') := m { s with code := [] }
  ((a, seqAll s'.code.reverse), { s' with code := s.code })

/-- Run a builder to completion, returning its result and the generated program. -/
def build {α : Type} (m : Build w α) : α × Stmt w :=
  let (a, s) := m {}
  (a, seqAll s.code.reverse)

/-! ## Control flow -/

/-- `if_ c thn els`: branch on register `c`. -/
def if_ (c : Reg) (thn : Build w Unit) (els : Build w Unit := pure ()) :
    Build w Unit := do
  let (_, tc) ← capture thn
  let (_, ec) ← capture els
  emit (.ifNZ c tc ec)

/-- `while_ guard body`: the guard is a builder action returning the register its
verdict lands in; its code runs before every iteration check, and is billed there. -/
def while_ (guard : Build w Reg) (body : Build w Unit) : Build w Unit := do
  let (r, gc) ← capture guard
  let (_, bc) ← capture body
  emit (.whileNZ gc r bc)

end Build

/-! ## Expressions

Compound arithmetic, compiled to three-address code through fresh temporaries.
`ℕ`-typed variables coerce as *registers*; numeric literals are word *constants*. -/

inductive Exp (w : ℕ) where
  | reg (r : Reg)
  | lit (v : Word w)
  | un (op : UnOp) (e : Exp w)
  | bin (op : BinOp) (a b : Exp w)

instance : Coe Reg (Exp w) := ⟨.reg⟩
instance {n : ℕ} : OfNat (Exp w) n := ⟨.lit (BitVec.ofNat w n)⟩
instance : Add (Exp w) := ⟨.bin .add⟩
instance : Sub (Exp w) := ⟨.bin .sub⟩
instance : Mul (Exp w) := ⟨.bin .mul⟩
instance : Div (Exp w) := ⟨.bin .udiv⟩
instance : Mod (Exp w) := ⟨.bin .umod⟩
instance : AndOp (Exp w) := ⟨.bin .and⟩
instance : OrOp (Exp w) := ⟨.bin .or⟩
instance : XorOp (Exp w) := ⟨.bin .xor⟩

/-- High word of the widening multiply (see `BinOp.mulhi`). -/
def Exp.mulhi (a b : Exp w) : Exp w := .bin .mulhi a b

/-- Unsigned less-than, valued in {0, 1}. -/
notation:50 a:51 " .< " b:51 => Exp.bin BinOp.ult a b
/-- Equality test, valued in {0, 1}. -/
notation:50 a:51 " .== " b:51 => Exp.bin BinOp.eq a b
/-- Disequality test, valued in {0, 1}. -/
notation:50 a:51 " .!= " b:51 => Exp.bin BinOp.ne a b

namespace Build

/-- Compile an expression; the result register holds its value. A bare register
compiles to itself (no code). -/
def compileExp : Exp w → Build w Reg
  | .reg r => pure r
  | .lit v => do
    let d ← freshReg
    emit (.imm d v)
    return d
  | .un op e => do
    let a ← compileExp e
    let d ← freshReg
    emit (.un op d a)
    return d
  | .bin op x y => do
    let a ← compileExp x
    let b ← compileExp y
    let d ← freshReg
    emit (.bin op d a b)
    return d

/-- `assign d e` — `d ← e`, compiling operands as needed. -/
def assign (d : Reg) (e : Exp w) : Build w Unit := do
  match e with
  | .reg a => emit (.mov d a)
  | .lit v => emit (.imm d v)
  | .un op a => do
    let ra ← compileExp a
    emit (.un op d ra)
  | .bin op a b => do
    let ra ← compileExp a
    let rb ← compileExp b
    emit (.bin op d ra rb)

@[inherit_doc] infix:20 " <~ " => assign

/-- Declare a fresh register initialized to `e` — `let x ← var e`. -/
def var (e : Exp w) : Build w Reg := do
  let d ← freshReg
  assign d e
  return d

end Build

/-! ## Buffers

At the surface, buffers are handled through the newtype `Buf w`, not raw `BufId`s.
`Reg` and `BufId` are both `ℕ` in the core (which keeps proof goals numeral-friendly),
so without the wrapper a buffer name could be passed where a register — or an
arbitrary index — was expected. The newtype prevents *accidental* mixing of the
three; it is not an enforced capability: the constructor stays public (tests write
`⟨0⟩` directly), so the intended source `Build.alloc` is a convention, not a
guarantee. -/

/-- Typed handle to a buffer of `w`-bit words. Obtain one from `Build.alloc` or
`Build.allocI`. -/
structure Buf (w : ℕ) where
  id : BufId
deriving Repr

namespace Build

/-- Allocate a fresh buffer with capacity `n` (an expression, evaluated at runtime).
The capacity is charged now; pushes into it are memory-free. Emits a *dynamic*
`bufAlloc`, whose time charge `C.bufAlloc + cap * C.allocPerWord` depends on the
runtime capacity — the emitted code is therefore not `Stmt.Straight`. When the
capacity is known at generation time, prefer `allocI`, which is statically
priced. -/
def alloc (n : Exp w) : Build w (Buf w) := do
  let rn ← compileExp n
  let b ← freshBuf
  emit (.bufAlloc b rn)
  return ⟨b⟩

/-- Allocate a fresh buffer with the *immediate* capacity `n`, emitting `bufAllocI`:
one instruction, no capacity register, and the time charge
`C.bufAlloc + n * C.allocPerWord` is a syntactic constant, so the emitted code
stays `Stmt.Straight` (statically priced). Semantics are identical to `alloc` at
that capacity.

The immediate capacity of `Stmt.bufAllocI` is a bare `ℕ` — unlike `alloc`, whose
capacity comes from a `w`-bit register and is therefore `< 2 ^ w`. An oversized
immediate (`n ≥ 2 ^ w`) would let the fill level grow past `2 ^ w`, at which point
`bufLen` reads back a *wrapped* length while every theorem still holds. The
autoparam closes that hole at the builder surface: `allocI` requires
`n < 2 ^ w`, discharged by `norm_num` at concrete capacities (and suppliable
explicitly otherwise). The proof is not threaded anywhere — it exists purely so
that builder-produced programs keep `bufLen` exact. -/
def allocI (n : ℕ) (_h : n < 2 ^ w := by norm_num) : Build w (Buf w) := do
  let b ← freshBuf
  emit (.bufAllocI b n)
  return ⟨b⟩

/-- Release a buffer's capacity. -/
def free (b : Buf w) : Build w Unit :=
  emit (.bufFree b.id)

/-- Read `b[i]` into a fresh register. -/
def get (b : Buf w) (i : Exp w) : Build w Reg := do
  let ri ← compileExp i
  let d ← freshReg
  emit (.bufGet d b.id ri)
  return d

/-- Write `b[i] ← e`. -/
def set (b : Buf w) (i e : Exp w) : Build w Unit := do
  let ri ← compileExp i
  let re ← compileExp e
  emit (.bufSet b.id ri re)

/-- Append `e` to `b`. -/
def push (b : Buf w) (e : Exp w) : Build w Unit := do
  let re ← compileExp e
  emit (.bufPush b.id re)

/-- Length of `b`, in a fresh register. -/
def len (b : Buf w) : Build w Reg := do
  let d ← freshReg
  emit (.bufLen d b.id)
  return d

end Build

/-! ## Product types

A struct is *generation-time* data: scalar fields live in a Lean record of registers,
and an array-of-structs is one buffer with a stride convention. Field access compiles
to index arithmetic on the underlying buffer, so its cost (a multiply, an add, a read)
is fully visible to the cost model — the abstraction adds nothing trusted. `PairBuf`
below is the two-field case; an n-field record is the same construction with stride n
(and generating the accessors from a field list is ordinary Lean metaprogramming).

Because each `PairBuf` owns its own buffer name, two arrays-of-structs can never
alias, and framing across them is the usual decidable `Touches` check. -/

/-- A pair of words held in registers (a "local struct"). -/
structure PairR (w : ℕ) where
  fst : Reg
  snd : Reg

/-- Allocate a fresh local pair. -/
def Build.mkPairR : Build w (PairR w) := do
  let a ← Build.freshReg
  let b ← Build.freshReg
  return ⟨a, b⟩

/-- An array of pairs: one buffer, stride 2, fields interleaved. -/
structure PairBuf (w : ℕ) where
  buf : Buf w

/-- Allocate an array of pairs with room for `nPairs` entries (2·nPairs words,
charged now — pushes are then memory-free). -/
def Build.mkPairBuf (nPairs : Exp w) : Build w (PairBuf w) := do
  let b ← Build.alloc (2 * nPairs)
  return ⟨b⟩

namespace PairBuf

/-- Append a pair: two pushes, requiring two words of free capacity. -/
def push (pb : PairBuf w) (x y : Exp w) : Build w Unit := do
  Build.push pb.buf x
  Build.push pb.buf y

/-- Number of pairs, in a fresh register. -/
def size (pb : PairBuf w) : Build w Reg := do
  let n ← Build.len pb.buf
  Build.var ((n : Exp w) / 2)

/-- First component of pair `i`. -/
def fst (pb : PairBuf w) (i : Exp w) : Build w Reg :=
  Build.get pb.buf (2 * i)

/-- Second component of pair `i`. -/
def snd (pb : PairBuf w) (i : Exp w) : Build w Reg :=
  Build.get pb.buf (2 * i + 1)

end PairBuf

end Caliper
