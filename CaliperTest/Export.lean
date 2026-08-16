import CaliperTest.RV64
import Caliper.Corpus
import Caliper.Liveness

/-!
# Differential test-vector exporter (test-only)

For each corpus program, plus a few of the examples, this emits a JSON vector to
`tests/vectors/<name>.json` containing the lowered RV64 code and the expected
outcome computed by the reference interpreter `Caliper.run`, the executable
semantics proved sound against `Exec` by `run_sound`. The Unicorn harness
(`tests/run_unicorn.py`) executes the RV64 words on a real emulator and checks that
registers and buffer contents agree, counting executed instructions to measure the
lowering constant `c`.

Vector format (JSON, fixed key order, values decimal except `code_hex`):

```json
{
  "name": "gcd",
  "code_base": 4096,
  "code_hex": ["0x0007b023", …],
  "arena_base": 1048576,
  "arena_end": 1048608,
  "initial_regs": [[5, 252], [6, 105]],        // [rv64 reg, value]
  "initial_mem": [[1048576, [3, 7, 11, 13]]],  // [addr, words] (length slot first)
  "expected_regs": [[5, 21], …],               // every reg the program touches
  "expected_bufs": [[1048576, 3, [7, 11, 13]]],// [len slot addr, len, data]
  "caliper_steps": 17,                          // unit-model time (staticTime? if straight)
  "result_reg": 5
}
```

Run with `lake env lean --run CaliperTest/Export.lean` from the repo root, in
interpreter mode, so no native compilation of the mathlib closure is needed.
-/

namespace CaliperTest.Export

open Caliper CaliperTest.RV64

/-- One differential test case. Buffers are given as
`(id, initial contents, layout capacity)`; the initial Caliper capacity is
the contents' length (programs that push first reserve via `memAlloc*`,
exactly as on the RV64 side, where the layout capacity sizes the arena
region). -/
structure TestCase where
  name : String
  stmt : Stmt 64
  initRegs : List (Reg × Nat) := []
  bufs : List (BufId × List Nat × Nat) := []
  resultReg : Reg
  fuel : Nat := 1000000

def TestCase.state (tc : TestCase) : State 64 where
  regs := fun r => match tc.initRegs.find? (·.1 == r) with
    | some (_, v) => BitVec.ofNat 64 v
    | none => 0
  bufs := fun b => match tc.bufs.find? (·.1 == b) with
    | some (_, ws, _) => (ws.map (BitVec.ofNat 64)).toArray
    | none => #[]
  caps := fun b => match tc.bufs.find? (·.1 == b) with
    | some (_, ws, _) => ws.length
    | none => 0

def TestCase.ctx (tc : TestCase) : Ctx :=
  layout (tc.bufs.map fun (b, _, cap) => (b, cap))

/-! ## JSON helpers (hand-rolled: fixed key order, deterministic output) -/

private def natToHex : Nat → String := fun n => String.ofList (Nat.toDigits 16 n)

def hex8 (w : UInt32) : String :=
  let s := natToHex w.toNat
  "0x" ++ "".pushn '0' (8 - s.length) ++ s

private def jList (xs : List String) : String :=
  "[" ++ String.intercalate ", " xs ++ "]"

private def jPair (a b : String) : String := "[" ++ a ++ ", " ++ b ++ "]"

/-! ## Export -/

def codeBase : Nat := 0x1000

def exportCase (tc : TestCase) : IO Unit := do
  let s₀ := tc.state
  let some (s', t, _, _) := run .unit tc.fuel tc.stmt s₀
    | throw <| IO.userError s!"{tc.name}: interpreter failed (out of fuel or unsafe access)"
  let ctx := tc.ctx
  let words ← match lowerProgram ctx tc.stmt with
    | .ok ws => pure ws
    | .error e => throw <| IO.userError s!"{tc.name}: lowering failed: {e}"
  let steps := (tc.stmt.staticTime? .unit).getD t
  let rv64Reg (r : Reg) : IO Nat := match regMap r with
    | .ok x => pure x
    | .error e => throw <| IO.userError s!"{tc.name}: {e}"
  -- every register the program reads or writes, in ascending order
  let regsOfInterest := (tc.stmt.readsSet ∪ tc.stmt.writesSet).sort (· ≤ ·)
  let initialRegs ← tc.initRegs.mapM fun (r, v) => do
    pure (jPair (toString (← rv64Reg r)) (toString v))
  let expectedRegs ← regsOfInterest.mapM fun r => do
    pure (jPair (toString (← rv64Reg r)) (toString (s'.regs r).toNat))
  let initialMem ← tc.bufs.mapM fun (b, ws, _) => do
    let l ← match ctx.find b with
      | .ok l => pure l
      | .error e => throw <| IO.userError s!"{tc.name}: {e}"
    pure (jPair (toString l.base) (jList ((ws.length :: ws).map toString)))
  let expectedBufs ← ctx.bufs.mapM fun (b, l) => do
    let arr := s'.bufs b
    pure ("[" ++ toString l.base ++ ", " ++ toString arr.size ++ ", "
      ++ jList (arr.toList.map fun v => toString v.toNat) ++ "]")
  let resultReg ← rv64Reg tc.resultReg
  let json := String.intercalate "\n"
    [ "{"
    , s!"  \"name\": \"{tc.name}\","
    , s!"  \"code_base\": {codeBase},"
    , s!"  \"code_hex\": {jList (words.toList.map fun w => s!"\"{hex8 w}\"")},"
    , s!"  \"arena_base\": {arenaBase},"
    , s!"  \"arena_end\": {ctx.arenaEnd},"
    , s!"  \"initial_regs\": {jList initialRegs},"
    , s!"  \"initial_mem\": {jList initialMem},"
    , s!"  \"expected_regs\": {jList expectedRegs},"
    , s!"  \"expected_bufs\": {jList expectedBufs},"
    , s!"  \"caliper_steps\": {steps},"
    , s!"  \"result_reg\": {resultReg}"
    , "}"
    , "" ]
  IO.FS.writeFile s!"tests/vectors/{tc.name}.json" json
  IO.println s!"  {tc.name}: {words.size} rv64 words, {steps} caliper steps"

/-! ## The cases: the corpus plus four worked examples -/

open Caliper.Corpus in
def cases : List TestCase :=
  [ { name := "memcpy", stmt := Memcpy.code 0 1
    , bufs := [(0, [7, 11, 13], 3), (1, [], 3)], resultReg := 0 }
  , { name := "memset", stmt := Memset.code 0
    , initRegs := [(5, 9)], bufs := [(0, [1, 2, 3, 4], 4)], resultReg := 0 }
  , { name := "reverse", stmt := Reverse.code 0
    , bufs := [(0, [1, 2, 3, 4, 5], 5)], resultReg := 0 }
  , { name := "stack_sum", stmt := StackSum.code 0
    , bufs := [(0, [3, 5, 9], 3)], resultReg := 0 }
  , { name := "dot_product", stmt := DotProduct.code 0 1
    , bufs := [(0, [1, 2, 3], 3), (1, [4, 5, 6], 3)], resultReg := 0 }
  , { name := "gcd", stmt := Gcd.code
    , initRegs := [(0, 252), (1, 105)], resultReg := 0 }
  , { name := "binexp", stmt := BinExp.code
    , initRegs := [(0, 3), (1, 13)], resultReg := 2 }
  , { name := "popcount", stmt := Popcount.code
    , initRegs := [(0, 0xDEADBEEF)], resultReg := 1 }
  , { name := "divmod", stmt := DivMod.code
    , initRegs := [(0, 0xFFFFFFFFFFFFFFFF), (1, 10)], resultReg := 5 }
  , { name := "divmod_zero", stmt := DivMod.code
    , initRegs := [(0, 5), (1, 0)], resultReg := 5 }
  , { name := "bittricks_min", stmt := BitTricks.minCode
    , initRegs := [(0, 1000), (1, 37)], resultReg := 5 }
  , { name := "bittricks_min_rev", stmt := BitTricks.minCode
    , initRegs := [(0, 37), (1, 1000)], resultReg := 5 }
  , { name := "bittricks_ispow2", stmt := BitTricks.isPow2Code
    , initRegs := [(0, 64)], resultReg := 5 }
  , { name := "bittricks_pack", stmt := BitTricks.packCode
    , initRegs := [(0, 0xDEAD), (1, 0xBEEF)], resultReg := 4 }
  , { name := "insertion_sort", stmt := InsertionSort.code 0
    , bufs := [(0, [5, 2, 4, 6, 1, 3], 6)], resultReg := 0 }
  , { name := "insertion_sort_rev", stmt := InsertionSort.code 0
    , bufs := [(0, [6, 5, 4, 3, 2, 1], 6)], resultReg := 0 }
  , { name := "matmul3", stmt := MatMul3.prog
    , bufs := [(0, [1, 2, 3, 4, 5, 6, 7, 8, 9], 9)
             , (1, [9, 8, 7, 6, 5, 4, 3, 2, 1], 9)
             , (2, [], 9)], resultReg := 0 }
  -- worked examples from Caliper/Examples.lean
  , { name := "sum_buf", stmt := Caliper.Examples.SumBuf.code 0
    , bufs := [(0, [3, 5, 9], 3)], resultReg := 0 }
  , { name := "scoped_sumsq", stmt := Caliper.Examples.ScopedSumSq.code
    , resultReg := 4 }
  , { name := "iota", stmt := Caliper.Examples.Iota.code 0
    , initRegs := [(2, 5)], bufs := [(0, [], 5)], resultReg := 0 }
  , { name := "scratch_loop", stmt := Caliper.Examples.ScratchLoop.code 0
    , initRegs := [(2, 100)], bufs := [(0, [], 1)], resultReg := 0 }
  ]

def main : IO Unit := do
  IO.FS.createDirAll "tests/vectors"
  IO.println s!"exporting {cases.length} vectors to tests/vectors/"
  for tc in cases do
    exportCase tc
  IO.println "done"

end CaliperTest.Export

/-- Entry point for `lake env lean --run CaliperTest/Export.lean`. -/
def main : IO Unit := CaliperTest.Export.main
