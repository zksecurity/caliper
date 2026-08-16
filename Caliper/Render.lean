import Caliper.Core

/-!
# Pretty-printer

`Stmt.render` prints a statement in Caliper's assembly dialect: one instruction per
line, memory operations under the `mem.` qualifier, destination first, buffers as
`b<i>`, registers as `r<i>`, two-space indentation for block bodies.

Control flow renders structurally: `ifnz r<c> { … } else { … }`, and `whileNZ` as
`loop { <guard> bifz r<c> <body> }`, where `bifz` is break-if-zero on the guard's
verdict register, mirroring the `Exec` rules (guard, test, body, repeat). `skip`
renders as `skip`, since compiled code can contain genuine no-ops.

The printer is for *reading* programs, builder output or compiled code. It is
not part of any trusted surface and nothing is proved about it.
-/

namespace Caliper

variable {w : ℕ}

/-- Assembly mnemonic of a unary operation. The zero tests render as `seqz`/`snez`,
the RISC-V pseudo-mnemonics for exactly these operations. -/
def UnOp.mnemonic : UnOp → String
  | .not => "not"
  | .neg => "neg"
  | .isZero => "seqz"
  | .isNonZero => "snez"

/-- Assembly mnemonic of a binary operation. -/
def BinOp.mnemonic : BinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .mulhi => "mulhi"
  | .udiv => "udiv" | .umod => "umod"
  | .and => "and" | .or => "or" | .xor => "xor" | .shl => "shl" | .shr => "shr"
  | .eq => "eq" | .ne => "ne" | .ult => "ult" | .ule => "ule"

/-- Pad a mnemonic to column `n` with at least one trailing space. -/
private def pad (m : String) (n : ℕ) : String :=
  m ++ "".pushn ' ' (max 1 (n - m.length))

/-- Render a statement as lines of canonical assembly (see the module docstring
for the dialect). Blocks indent their bodies by two spaces per nesting level. -/
def Stmt.render : Stmt w → List String
  | .skip => ["skip"]
  | .seq c₁ c₂ => c₁.render ++ c₂.render
  | .imm d v => [s!"{pad "imm" 6}r{d}, {v.toNat}"]
  | .mov d a => [s!"{pad "mov" 6}r{d}, r{a}"]
  | .un op d a => [s!"{pad op.mnemonic 5}r{d}, r{a}"]
  | .bin op d a b => [s!"{pad op.mnemonic 5}r{d}, r{a}, r{b}"]
  | .memAlloc b n => [s!"{pad "mem.alloc" 10}b{b}, r{n}"]
  | .memAllocI b n => [s!"{pad "mem.alloci" 10}b{b}, {n}"]
  | .memFree b => [s!"{pad "mem.free" 10}b{b}"]
  | .memLen d b => [s!"{pad "mem.len" 10}r{d}, b{b}"]
  | .memLoad d b i => [s!"{pad "mem.load" 10}r{d}, b{b}[r{i}]"]
  | .memStore b i src => [s!"{pad "mem.store" 10}b{b}[r{i}], r{src}"]
  | .memPush b src => [s!"{pad "mem.push" 10}b{b}, r{src}"]
  | .memPop b => [s!"{pad "mem.pop" 10}b{b}"]
  | .ifNZ c thn els =>
      s!"ifnz r{c} \{" :: thn.render.map ("  " ++ ·) ++
      "} else {" :: els.render.map ("  " ++ ·) ++ ["}"]
  | .whileNZ g c body =>
      "loop {" :: g.render.map ("  " ++ ·) ++
      s!"  bifz r{c}" :: body.render.map ("  " ++ ·) ++ ["}"]

/-- The rendered statement as one newline-joined string (for `IO.println`). -/
def Stmt.renderString (c : Stmt w) : String :=
  String.intercalate "\n" c.render

instance : ToString (Stmt w) := ⟨Stmt.renderString⟩

/-! ### Pinned example

One statement exercising every class of the dialect: immediates, ALU ops,
every `mem.` instruction, a conditional and a loop. -/

private def renderDemo : Stmt 64 :=
  .imm 2 5 ;;
  .memAllocI 0 3 ;;
  .whileNZ (.bin .ult 1 0 2) 1
    (.memPush 0 0 ;;
     .imm 3 1 ;;
     .bin .add 0 0 3) ;;
  .ifNZ 1
    (.memLoad 4 0 1 ;; .memStore 0 1 4 ;; .memPop 0)
    (.un .isZero 4 1 ;; .memLen 5 0 ;; .memAlloc 1 5 ;; .mov 6 4 ;; .skip) ;;
  .memFree 0

/--
info: imm   r2, 5
mem.alloci b0, 3
loop {
  ult  r1, r0, r2
  bifz r1
  mem.push  b0, r0
  imm   r3, 1
  add  r0, r0, r3
}
ifnz r1 {
  mem.load  r4, b0[r1]
  mem.store b0[r1], r4
  mem.pop   b0
} else {
  seqz r4, r1
  mem.len   r5, b0
  mem.alloc b1, r5
  mov   r6, r4
  skip
}
mem.free  b0
-/
#guard_msgs in
#eval IO.println renderDemo.renderString

end Caliper
