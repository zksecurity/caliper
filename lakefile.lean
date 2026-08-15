import Lake
open Lake DSL

package caliper where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib Caliper where

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"905b95818eb32af7874a58b427f50c1711a5e96c"
