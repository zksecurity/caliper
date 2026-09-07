import Caliper.Tape
import Caliper.Builder
import Caliper.Render
import Caliper.Liveness

/-!
# Replaying computations against fixed word tapes

These examples are compiled by `lake build Examples`, including in CI. The tape
is supplied by the caller; the same tape and initial state always give the same run.
-/

namespace CaliperExamples.Replay

open Caliper

def tape : RandomTape 64 := fun i => BitVec.ofNat 64 (i + 7)

def pair : Stmt 64 := .rand 0 ;; .rand 1

example : (run .unit tape 10 pair (State.init 64)).map
    (fun (s, t, d, p) => (s.regs 0, s.regs 1, s.tapePos, t, d, p)) =
    some (7, 8, 2, 2, 0, 0) := rfl

/-- A resumed execution continues from the returned cursor. -/
example : (do
    let (s, _, _, _) ← run .unit tape 10 pair (State.init 64)
    let (s', t, d, p) ← run .unit tape 10 (.rand 2) s
    pure (s'.regs 2, s'.tapePos, t, d, p)) = some (9, 3, 1, 0, 0) := rfl

example : (run .unit tape 10 (.rand 0) { State.init 64 with tapePos := 5 }).map
    (fun (s, _, _, _) => (s.regs 0, s.tapePos)) = some (12, 6) := rfl

example : (run .unit RandomTape.zero 10 pair (State.init 64)).map
    (fun (s, t, _, _) => (s.regs 0, s.regs 1, s.tapePos, t)) = some (0, 0, 2, 2) := rfl

/-- Only the branch actually taken consumes words. -/
def branch : Stmt 4 :=
  .rand 0 ;; .ifNZ 0 (.rand 1 ;; .rand 2) .skip ;; .rand 3

example : (run .unit (fun i => BitVec.ofNat 4 i) 20 branch (State.init 4)).map
    (fun (s, t, _, _) => (s.regs 3, s.tapePos, t)) = some (1, 2, 3) := rfl

example : (run .unit (fun i => BitVec.ofNat 4 (i + 1)) 20 branch (State.init 4)).map
    (fun (s, t, _, _) => (s.regs 3, s.tapePos, t)) = some (4, 4, 5) := rfl

/-- Even the zero-bit word consumes one tape position. -/
example : (run .unit RandomTape.zero 2 (.rand 0) (State.init 0)).map
    (fun (s, t, _, _) => (s.regs 0, s.tapePos, t)) = some (0, 1, 1) := rfl

example : Build.build (Build.rand (w := 64)) = (0, .rand 0) := rfl
example : (Stmt.rand (w := 64) 0).renderString = "rand  r0" := rfl
example : pair.staticTime? .unit = some 2 := rfl
example : pair.readsSet = ∅ := by decide
example : pair.writesSet = {0, 1} := by decide
example : (Stmt.rand (w := 64) 0).RandomFree = False := rfl

end CaliperExamples.Replay
