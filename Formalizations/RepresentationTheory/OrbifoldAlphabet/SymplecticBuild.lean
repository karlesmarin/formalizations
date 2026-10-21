/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.Data.Matrix.Block
public import Mathlib.Analysis.Complex.Basic

/-!
# Building a symplectic form for each orbifold label

Proposition 2 of the orbifold-alphabet paper realises every label of its symplectic table by a pair of
matrices `R` and a nondegenerate antisymmetric form `J` with `Rᵀ J R = J`. Three constructions:

* real type: `R = ρ ⊗ I₂` and `J = B ⊗ ε`, with `ρᵀ B ρ = B`, `B` symmetric and `ε` antisymmetric;
* complex type: `R = ρ ⊕ ρ̄` and `J = [[0, I], [−I, 0]]`, with `ρ` unitary;
* quaternionic type: `R = ρ`, `J = B` (nothing to prove).

## Main results

* `kronecker_one_preserves`: `(ρ ⊗ I)ᵀ (B ⊗ ε) (ρ ⊗ I) = (ρᵀ B ρ) ⊗ ε = B ⊗ ε`.
* `kronecker_transpose_eq_neg`: a symmetric `B` against an antisymmetric `ε` gives `(B ⊗ ε)ᵀ = −(B ⊗ ε)`.
* `fromBlocks_conj_preserves_J`: for unitary `ρ`, `ρ ⊕ ρ̄` preserves `J`; the off-diagonal blocks are
  `ρᵀ ρ̄ = (ρᴴ ρ)ᵀ = I` and `ρ̄ᵀ ρ = ρᴴ ρ = I`.

## References

* C. Marín, *The orbifold alphabet*, Proposition 2 (`prop:spbuild`).
-/

@[expose] public section

namespace OrbifoldAlphabet.SymplecticBuild

open Matrix
open scoped Kronecker

/-- Real type: if `ρ` preserves the bilinear form `B` (`ρᵀ B ρ = B`), then `ρ ⊗ I₂` preserves `B ⊗ ε` for every
`2 × 2` matrix `ε`. -/
theorem kronecker_one_preserves {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (ρ B : Matrix n n R) (ε : Matrix (Fin 2) (Fin 2) R) (h : ρᵀ * B * ρ = B) :
    (ρ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) R))ᵀ * (B ⊗ₖ ε) * (ρ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) R)) = B ⊗ₖ ε := by
  rw [← kroneckerMap_transpose, transpose_one, ← mul_kronecker_mul, ← mul_kronecker_mul, h, one_mul, mul_one]

/-- Real type: a symmetric `B` against an antisymmetric `ε` gives an antisymmetric form `B ⊗ ε`. -/
theorem kronecker_transpose_eq_neg {R n : Type*} [CommRing R]
    (B : Matrix n n R) (ε : Matrix (Fin 2) (Fin 2) R) (hB : Bᵀ = B) (hε : εᵀ = -ε) :
    (B ⊗ₖ ε)ᵀ = -(B ⊗ₖ ε) := by
  rw [← kroneckerMap_transpose, hB, hε]
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [kroneckerMap_apply]

/-- Complex type: if `ρ` is unitary, `ρ ⊕ ρ̄` preserves the standard symplectic form `J = [[0, I], [−I, 0]]`, i.e.
`Rᵀ J R = J`. -/
theorem fromBlocks_conj_preserves_J {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : Matrix n n ℂ) (h : ρᴴ * ρ = 1) :
    (fromBlocks ρ 0 0 (ρ.map (starRingEnd ℂ)))ᵀ * fromBlocks 0 1 (-1) 0 *
        fromBlocks ρ 0 0 (ρ.map (starRingEnd ℂ)) = fromBlocks 0 1 (-1) 0 := by
  have h1 : (ρ.map (starRingEnd ℂ))ᵀ * ρ = 1 := h
  have h2 : ρᵀ * ρ.map (starRingEnd ℂ) = 1 := by
    have := congrArg transpose h
    rwa [transpose_mul, transpose_one] at this
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp [h1, h2]

end OrbifoldAlphabet.SymplecticBuild
