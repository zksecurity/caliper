import Lake
open Lake DSL

package caliper where
  -- Mathlib is a module-system library; Caliper's files are not, which is deliberate.
  allowNonModules := true
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib Caliper where

/-- Executable examples and their proofs; built in CI. -/
@[default_target]
lean_lib Examples where

/-- Test-only: RV64 lowering + differential-vector exporter. Not imported by
`Caliper`; users running `lake build Caliper` never build it. -/
lean_lib CaliperTest where

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"fc4f59e577feb1a4956671bc04ac18aaaf8cd842"
