import CaliperTest.RV64
import CaliperTest.Export

/-!
# CaliperTest — differential-testing harness support (test-only, UNVERIFIED)

A separate library target that the `Caliper` library does **not** import:
`lake build Caliper` never builds it, and nothing in it is proved.

* `CaliperTest/RV64.lean` — RV64IM encoder and a Caliper → RV64 lowering.
* `CaliperTest/Export.lean` — emits JSON differential test vectors for the
  corpus (expected values computed by the reference interpreter); run it
  with `lake env lean --run CaliperTest/Export.lean`.

The vectors are executed by `tests/run_unicorn.py` (uv-managed) on the
Unicorn emulator, which checks results and reports the per-program lowering
constant `c` = RV64 instructions / Caliper steps.
-/
