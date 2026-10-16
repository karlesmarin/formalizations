import Lake
open Lake DSL

/-!
# Formalizations

Lean 4 / Mathlib formalizations by Carles Marín, organized like Mathlib (by mathematical area).
Build: `lake exe cache get && lake build`. Axiom audit: `scripts/check_axioms.sh`.
-/

package «formalizations» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "f0b4c8150aa0dbc758aff1291410c5ae335aff3a"

@[default_target]
lean_lib «Formalizations» where
  globs := #[.andSubmodules `Formalizations]

lean_lib «FormalizationsTest» where
  globs := #[.submodules `FormalizationsTest]
