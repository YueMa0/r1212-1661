import Lake

open Lake DSL

require "leanprover-community" / "mathlib" @ git "v4.32.1"

package RamseyIncrement where
  version := v!"0.1.0"
  keywords := #["mathematics", "ramsey-theory", "graph-theory"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩
  ]

@[default_target]
lean_lib RamseyIncrement
