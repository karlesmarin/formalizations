import Lake
open Lake DSL

-- Lean 4 formalizations for the atiyah-l2 research (free fields, inversion height, 3XX).
-- Author: Carles Marín (with Claude as AI assistant). Lean v4.35.0, Mathlib pinned below.
-- Build: `lake exe cache get && lake build`.
package «atiyah_l2_lean» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "f0b4c8150aa0dbc758aff1291410c5ae335aff3a"

@[default_target]
lean_lib «AtiyahL2» where
  srcDir := "."
  roots := #[`DGHStrat, `DGHLex, `DGHAbsorb, `DGHFinite, `DGHHessenberg, `DGHEps0,
    `Continuantes, `FqLower, `FreeLocusLinAlg, `LociLibresCert,
    `T151Residuos, `T152Identidades, `T155Identidades, `T158Identidades]
