import Caliper.Core

/-!
# RV64IM encoder and Caliper → RV64 lowering (test-only, UNVERIFIED)

This module is **not part of the Caliper library** and nothing here is proved:
it exists to produce differential test vectors (`CaliperTest/Export.lean`)
that are executed by a real RISC-V emulator (`tests/run_unicorn.py`).
Correctness of the encoder and lowering comes from those differential tests
alone — that is deliberate: this is the *untrusted* side of the experiment
that measures the constant `c` in "one Caliper tick ≤ c RV64 instructions".

## Encoder

Raw 32-bit instruction words for the RV64IM subset the lowering needs.
Field layout per format (bit ranges inclusive, `f3`/`f7` = funct3/funct7):

| fmt | 31–25            | 24–20 | 19–15 | 14–12 | 11–7        | 6–0 |
| --- | ---------------- | ----- | ----- | ----- | ----------- | --- |
| R   | f7               | rs2   | rs1   | f3    | rd          | op  |
| I   | imm[11:5]        | imm[4:0] (with rs2 col) | rs1 | f3 | rd | op  |
| S   | imm[11:5]        | rs2   | rs1   | f3    | imm[4:0]    | op  |
| B   | imm[12], imm[10:5] | rs2 | rs1   | f3    | imm[4:1], imm[11] | op |
| U   | imm[31:12]                       |       | rd          | op  |
| J   | imm[20], imm[10:1], imm[11], imm[19:12] |   | rd          | op  |

Mnemonic → (format, opcode, f3, f7):

| mnemonic | fmt | opcode  | f3  | f7      |
| -------- | --- | ------- | --- | ------- |
| LUI      | U   | 0110111 |     |         |
| ADDI     | I   | 0010011 | 000 |         |
| SLTIU    | I   | 0010011 | 011 |         |
| XORI     | I   | 0010011 | 100 |         |
| SLLI     | I   | 0010011 | 001 | 000000· (6-bit shamt) |
| SRLI     | I   | 0010011 | 101 | 000000· |
| ADD      | R   | 0110011 | 000 | 0000000 |
| SUB      | R   | 0110011 | 000 | 0100000 |
| SLL      | R   | 0110011 | 001 | 0000000 |
| SLTU     | R   | 0110011 | 011 | 0000000 |
| XOR      | R   | 0110011 | 100 | 0000000 |
| SRL      | R   | 0110011 | 101 | 0000000 |
| OR       | R   | 0110011 | 110 | 0000000 |
| AND      | R   | 0110011 | 111 | 0000000 |
| MUL      | R   | 0110011 | 000 | 0000001 |
| MULHU    | R   | 0110011 | 011 | 0000001 |
| DIVU     | R   | 0110011 | 101 | 0000001 |
| REMU     | R   | 0110011 | 111 | 0000001 |
| LD       | I   | 0000011 | 011 |         |
| SD       | S   | 0100011 | 011 |         |
| BEQ      | B   | 1100011 | 000 |         |
| BNE      | B   | 1100011 | 001 |         |
| BLTU     | B   | 1100011 | 110 |         |
| JAL      | J   | 1101111 |     |         |
| EBREAK   | I   | 1110011 | 000 | (imm = 1) |

## Lowering conventions

* **Registers**: Caliper `rN` maps to RISC-V `x(5+N)` (`x5`–`x30`); the
  lowering *fails* (returns `.error`) for `N ≥ 26`. `x1`–`x3` are scratch
  registers for the fixup sequences and address arithmetic; `x0` is the
  hard-wired zero; `x4` and `x31` are unused.
* **Buffer arena**: each `BufId` gets a fixed region decided at lowering
  time from a per-test declared maximum capacity (a lowering parameter —
  dynamic `memAlloc` capacities are not statically known). The region is
  `1 + cap` 64-bit words starting at its base address: word 0 is the
  buffer's **fill length**, the data follows. Regions are laid out
  back-to-back from `arenaBase = 0x100000`.
* **Semantics fixups** (Caliper semantics differ from raw RV64):
  - `udiv` by zero is 0 in Caliper, all-ones on RV64 → mask the `DIVU`
    result with `-(b ≠ 0)` (4 instructions total).
  - `umod` by zero is the dividend in Caliper — `REMU` already agrees; no
    fixup.
  - shift amounts ≥ 64 give 0 in Caliper, RV64 masks to 6 bits → mask the
    `SLL`/`SRL` result with `-(shamt <ᵤ 64)` (4 instructions total).
  - `memAlloc`/`memAllocI`/`memFree` all reduce to *zeroing the length
    slot*: regions are preassigned (so no runtime bump pointer is needed)
    and `memFree` does not reclaim arena space — fine for the test arena,
    where each buffer's region is dedicated.
  - `memPop` on an empty buffer is a no-op → branch over the decrement.
* Programs end with `EBREAK`; the harness runs until it is reached.
-/

namespace CaliperTest.RV64

open Caliper

/-! ## Encoder -/

/-- Truncate a (possibly negative) immediate to `bits` bits, two's complement. -/
def signedBits (v : Int) (bits : Nat) : Nat :=
  (v.emod (2 ^ bits)).toNat

def rtype (f7 rs2 rs1 f3 rd op : Nat) : UInt32 :=
  UInt32.ofNat <|
    (f7 <<< 25) ||| (rs2 <<< 20) ||| (rs1 <<< 15) ||| (f3 <<< 12) ||| (rd <<< 7) ||| op

def itype (imm : Int) (rs1 f3 rd op : Nat) : UInt32 :=
  UInt32.ofNat <|
    (signedBits imm 12 <<< 20) ||| (rs1 <<< 15) ||| (f3 <<< 12) ||| (rd <<< 7) ||| op

def stype (imm : Int) (rs2 rs1 f3 op : Nat) : UInt32 :=
  let v := signedBits imm 12
  UInt32.ofNat <|
    ((v >>> 5) <<< 25) ||| (rs2 <<< 20) ||| (rs1 <<< 15) ||| (f3 <<< 12)
      ||| ((v &&& 0x1f) <<< 7) ||| op

def btype (imm : Int) (rs2 rs1 f3 : Nat) : UInt32 :=
  let v := signedBits imm 13
  UInt32.ofNat <|
    (((v >>> 12) &&& 1) <<< 31) ||| (((v >>> 5) &&& 0x3f) <<< 25)
      ||| (rs2 <<< 20) ||| (rs1 <<< 15) ||| (f3 <<< 12)
      ||| (((v >>> 1) &&& 0xf) <<< 8) ||| (((v >>> 11) &&& 1) <<< 7) ||| 0x63

def utype (imm20 rd op : Nat) : UInt32 :=
  UInt32.ofNat <| ((imm20 &&& 0xfffff) <<< 12) ||| (rd <<< 7) ||| op

def jtype (imm : Int) (rd : Nat) : UInt32 :=
  let v := signedBits imm 21
  UInt32.ofNat <|
    (((v >>> 20) &&& 1) <<< 31) ||| (((v >>> 1) &&& 0x3ff) <<< 21)
      ||| (((v >>> 11) &&& 1) <<< 20) ||| (((v >>> 12) &&& 0xff) <<< 12)
      ||| (rd <<< 7) ||| 0x6f

def lui (rd imm20 : Nat) : UInt32 := utype imm20 rd 0x37
def addi (rd rs1 : Nat) (imm : Int) : UInt32 := itype imm rs1 0x0 rd 0x13
def sltiu (rd rs1 : Nat) (imm : Int) : UInt32 := itype imm rs1 0x3 rd 0x13
def xori (rd rs1 : Nat) (imm : Int) : UInt32 := itype imm rs1 0x4 rd 0x13
def slli (rd rs1 shamt : Nat) : UInt32 := itype (Int.ofNat shamt) rs1 0x1 rd 0x13
def srli (rd rs1 shamt : Nat) : UInt32 := itype (Int.ofNat shamt) rs1 0x5 rd 0x13
def add (rd rs1 rs2 : Nat) : UInt32 := rtype 0x00 rs2 rs1 0x0 rd 0x33
def sub (rd rs1 rs2 : Nat) : UInt32 := rtype 0x20 rs2 rs1 0x0 rd 0x33
def sll (rd rs1 rs2 : Nat) : UInt32 := rtype 0x00 rs2 rs1 0x1 rd 0x33
def sltu (rd rs1 rs2 : Nat) : UInt32 := rtype 0x00 rs2 rs1 0x3 rd 0x33
def xor (rd rs1 rs2 : Nat) : UInt32 := rtype 0x00 rs2 rs1 0x4 rd 0x33
def srl (rd rs1 rs2 : Nat) : UInt32 := rtype 0x00 rs2 rs1 0x5 rd 0x33
def or (rd rs1 rs2 : Nat) : UInt32 := rtype 0x00 rs2 rs1 0x6 rd 0x33
def and (rd rs1 rs2 : Nat) : UInt32 := rtype 0x00 rs2 rs1 0x7 rd 0x33
def mul (rd rs1 rs2 : Nat) : UInt32 := rtype 0x01 rs2 rs1 0x0 rd 0x33
def mulhu (rd rs1 rs2 : Nat) : UInt32 := rtype 0x01 rs2 rs1 0x3 rd 0x33
def divu (rd rs1 rs2 : Nat) : UInt32 := rtype 0x01 rs2 rs1 0x5 rd 0x33
def remu (rd rs1 rs2 : Nat) : UInt32 := rtype 0x01 rs2 rs1 0x7 rd 0x33
def ld (rd : Nat) (off : Int) (rs1 : Nat) : UInt32 := itype off rs1 0x3 rd 0x03
def sd (rs2 : Nat) (off : Int) (rs1 : Nat) : UInt32 := stype off rs2 rs1 0x3 0x23
def beq (rs1 rs2 : Nat) (off : Int) : UInt32 := btype off rs2 rs1 0x0
def jal (rd : Nat) (off : Int) : UInt32 := jtype off rd
def ebreak : UInt32 := itype 1 0 0x0 0 0x73

/-- Materialize the 64-bit constant `v` into `rd`.

* `v < 2048`: one `ADDI`.
* `v` (plus rounding) within 31 bits: `LUI` + `ADDI` (the classic split, with
  the low part sign-adjusted).
* otherwise: 11-bit chunks, most significant first — `ADDI` then repeated
  `SLLI 11; ADDI`. Always correct, never optimal; the corpus's large
  constants are rare. -/
def li (rd : Nat) (v : Nat) : Array UInt32 :=
  if v < 2048 then
    #[addi rd 0 (Int.ofNat v)]
  else if v + 0x800 < 2 ^ 31 then
    let hi := (v + 0x800) >>> 12
    let lo : Int := Int.ofNat v - Int.ofNat (hi <<< 12)
    #[lui rd hi, addi rd rd lo]
  else
    -- 6 chunks of 11 bits cover 66 ≥ 64 bits; drop leading zero chunks
    let chunks := (List.range 6).map fun idx => (v >>> ((5 - idx) * 11)) &&& 0x7ff
    let chunks := match chunks.dropWhile (· == 0) with
      | [] => [0]
      | cs => cs
    match chunks with
    | [] => #[]  -- unreachable
    | c :: cs =>
      cs.foldl (fun acc c => (acc.push (slli rd rd 11)).push (addi rd rd (Int.ofNat c)))
        #[addi rd 0 (Int.ofNat c)]

/-! ## Lowering -/

/-- Fixed arena region of one buffer: `base` is the address of the length
slot; the data words start at `base + 8`; `cap` words of data follow. -/
structure BufLayout where
  base : Nat
  cap : Nat
deriving Repr

/-- The lowering context: where each buffer lives. Decided before lowering
from per-test declared maximum capacities. -/
structure Ctx where
  bufs : List (BufId × BufLayout)
deriving Repr

def arenaBase : Nat := 0x100000

/-- Lay out buffers back-to-back from `arenaBase`, one length slot plus
`cap` data words each. -/
def layout (caps : List (BufId × Nat)) : Ctx :=
  let (bufs, _) := caps.foldl
    (fun (acc, base) (b, cap) => ((b, ⟨base, cap⟩) :: acc, base + 8 * (1 + cap)))
    ([], arenaBase)
  ⟨bufs.reverse⟩

/-- One past the end of the arena (for sizing the emulator mapping). -/
def Ctx.arenaEnd (ctx : Ctx) : Nat :=
  ctx.bufs.foldl (fun acc (_, l) => max acc (l.base + 8 * (1 + l.cap))) arenaBase

-- scratch registers (never holding Caliper state)
private def s1 : Nat := 1
private def s2 : Nat := 2
private def s3 : Nat := 3

/-- Caliper register → RISC-V register. Direct map `rN ↦ x(5+N)`, failing
beyond the 26 registers `x5`–`x30` — plenty for the corpus. -/
def regMap (r : Reg) : Except String Nat :=
  if r < 26 then .ok (5 + r)
  else .error s!"register r{r} out of range: the RV64 test lowering maps r0–r25 only"

def Ctx.find (ctx : Ctx) (b : BufId) : Except String BufLayout :=
  match ctx.bufs.find? (·.1 == b) with
  | some (_, l) => .ok l
  | none => .error s!"buffer b{b} has no declared layout"

/-- `rd ← rd & -(cond)`, with the {0,1}-valued `cond` in `sc`: the
select-with-mask tail shared by the `udiv` and shift fixups. -/
private def maskBy (rd sc : Nat) : Array UInt32 :=
  #[sub sc 0 sc, and rd rd sc]

/-- Conditional-branch offsets are 13-bit signed; fail loudly if a block is
too large instead of emitting garbage. -/
def checkBranch (off : Int) : Except String Unit :=
  if off < 4096 ∧ -4096 ≤ off then .ok ()
  else .error s!"branch offset {off} out of B-type range (block too large)"

/-- Lower one statement to position-independent code (all internal branches
are relative). -/
partial def lowerStmt (ctx : Ctx) : Stmt 64 → Except String (Array UInt32)
  | .skip => .ok #[]
  | .seq c₁ c₂ => do
    let a ← lowerStmt ctx c₁
    let b ← lowerStmt ctx c₂
    .ok (a ++ b)
  | .imm d v => do
    let rd ← regMap d
    .ok (li rd v.toNat)
  | .mov d a => do
    let rd ← regMap d
    let ra ← regMap a
    .ok #[addi rd ra 0]
  | .un op d a => do
    let rd ← regMap d
    let ra ← regMap a
    match op with
    | .not => .ok #[xori rd ra (-1)]
    | .neg => .ok #[sub rd 0 ra]
    | .isZero => .ok #[sltiu rd ra 1]
    | .isNonZero => .ok #[sltu rd 0 ra]
  | .bin op d a b => do
    let rd ← regMap d
    let ra ← regMap a
    let rb ← regMap b
    match op with
    | .add => .ok #[add rd ra rb]
    | .sub => .ok #[sub rd ra rb]
    | .mul => .ok #[mul rd ra rb]
    | .mulhi => .ok #[mulhu rd ra rb]
    | .udiv =>
      -- Caliper: x/0 = 0; DIVU gives all-ones → mask with -(b ≠ 0)
      .ok (#[divu s1 ra rb, sltu s2 0 rb, addi rd s1 0] ++ maskBy rd s2)
    | .umod => .ok #[remu rd ra rb]  -- REMU x%0 = x matches Caliper
    | .and => .ok #[and rd ra rb]
    | .or => .ok #[or rd ra rb]
    | .xor => .ok #[xor rd ra rb]
    | .shl =>
      -- Caliper: shamt ≥ 64 gives 0; SLL masks to 6 bits → mask with -(shamt < 64)
      .ok (#[sll s1 ra rb, sltiu s2 rb 64, addi rd s1 0] ++ maskBy rd s2)
    | .shr =>
      .ok (#[srl s1 ra rb, sltiu s2 rb 64, addi rd s1 0] ++ maskBy rd s2)
    | .eq => .ok #[xor s1 ra rb, sltiu rd s1 1]
    | .ne => .ok #[xor s1 ra rb, sltu rd 0 s1]
    | .ult => .ok #[sltu rd ra rb]
    | .ule => .ok #[sltu s1 rb ra, xori rd s1 1]
  -- all three allocation-shaped instructions reduce to zeroing the length
  -- slot: regions are preassigned, memFree does not reclaim (test arena)
  | .memAlloc b _ => do
    let l ← ctx.find b
    .ok (li s1 l.base ++ #[sd 0 0 s1])
  | .memAllocI b _ => do
    let l ← ctx.find b
    .ok (li s1 l.base ++ #[sd 0 0 s1])
  | .memFree b => do
    let l ← ctx.find b
    .ok (li s1 l.base ++ #[sd 0 0 s1])
  | .memLen d b => do
    let rd ← regMap d
    let l ← ctx.find b
    .ok (li s1 l.base ++ #[ld rd 0 s1])
  | .memLoad d b i => do
    let rd ← regMap d
    let ri ← regMap i
    let l ← ctx.find b
    .ok (li s1 (l.base + 8) ++ #[slli s2 ri 3, add s1 s1 s2, ld rd 0 s1])
  | .memStore b i src => do
    let ri ← regMap i
    let rs ← regMap src
    let l ← ctx.find b
    .ok (li s1 (l.base + 8) ++ #[slli s2 ri 3, add s1 s1 s2, sd rs 0 s1])
  | .memPush b src => do
    let rs ← regMap src
    let l ← ctx.find b
    .ok (li s1 l.base ++
      #[ld s2 0 s1,        -- len
        slli s3 s2 3,
        add s3 s3 s1,
        sd rs 8 s3,        -- data[len] (skipping the length slot)
        addi s2 s2 1,
        sd s2 0 s1])
  | .memPop b => do
    let l ← ctx.find b
    .ok (li s1 l.base ++
      #[ld s2 0 s1,
        beq s2 0 12,       -- empty: skip the decrement (no-op pop)
        addi s2 s2 (-1),
        sd s2 0 s1])
  | .ifNZ c thn els => do
    let rc ← regMap c
    let thnW ← lowerStmt ctx thn
    let elsW ← lowerStmt ctx els
    let skipThn : Int := 4 * (Int.ofNat thnW.size + 2)
    let skipEls : Int := 4 * (Int.ofNat elsW.size + 1)
    checkBranch skipThn
    .ok (#[beq rc 0 skipThn] ++ thnW ++ #[jal 0 skipEls] ++ elsW)
  | .whileNZ g c body => do
    let rc ← regMap c
    let gW ← lowerStmt ctx g
    let bodyW ← lowerStmt ctx body
    let exitOff : Int := 4 * (Int.ofNat bodyW.size + 2)
    let backOff : Int := -4 * (Int.ofNat gW.size + 1 + Int.ofNat bodyW.size)
    checkBranch exitOff
    .ok (gW ++ #[beq rc 0 exitOff] ++ bodyW ++ #[jal 0 backOff])

/-- Lower a whole program: the statement, then `EBREAK` as the stop marker
the harness runs to. -/
def lowerProgram (ctx : Ctx) (c : Stmt 64) : Except String (Array UInt32) := do
  let w ← lowerStmt ctx c
  .ok (w.push ebreak)

end CaliperTest.RV64
