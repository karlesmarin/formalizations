/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Analysis.RCLike.Basic

/-!
# Rank of a block matrix through its Schur complement

Over a field, a block matrix with invertible top-left block A has rank |A| plus the rank of its
Schur complement. In particular a real symmetric block matrix with positive definite A and zero
Schur complement is positive semidefinite of rank |A|: the exact certificate behind "this Gram
matrix has rank r".

## Main results

* `Matrix.rank_fromBlocks_diagonal`: rank (fromBlocks A 0 0 D) = rank A + rank D
* `Matrix.rank_fromBlocks_of_isUnit₁₁`: A invertible: rank (fromBlocks A B C D) = card m + rank (D - C * A⁻¹ * B)
* `Matrix.posSemidef_rank_of_schur_eq_zero`: A ≻ 0 and D - Bᴴ A⁻¹ B = 0: fromBlocks A B Bᴴ D is PSD of rank card m

## References

* Mathlib: Matrix.fromBlocks_eq_of_invertible₁₁ (LDU), Matrix.rank_mul_eq_left_of_isUnit_det, Matrix.rank_mul_eq_right_of_isUnit_det, Matrix.PosDef.fromBlocks₁₁ (PSD ⇔ Schur PSD; sin rango).
* Mathlib NO tiene el rango de un bloque diagonal ni el rango por complemento de Schur (grep 20-nov). Clones (TauCeti, atlas-lean, RealRooted): tampoco.
-/

@[expose] public section

namespace Matrix

variable {l m n p K : Type*} [Field K]

/-- The rank of a block diagonal matrix is the sum of the ranks of its blocks. -/
theorem rank_fromBlocks_diagonal [Fintype l] [Fintype m] [Fintype n] [Fintype p]
    (A : Matrix l m K) (D : Matrix p n K) :
    (fromBlocks A 0 0 D).rank = A.rank + D.rank := by
  let e := LinearEquiv.sumArrowLequivProdArrow l p K K
  let e' := LinearEquiv.sumArrowLequivProdArrow m n K K
  have h : (fromBlocks A 0 0 D).mulVecLin =
      e.symm.toLinearMap ∘ₗ (A.mulVecLin.prodMap D.mulVecLin) ∘ₗ e'.toLinearMap := by
    refine LinearMap.ext fun v => funext fun i => ?_
    rcases i with i | i <;> simp [e, e', fromBlocks_mulVec] <;> rfl
  rw [rank, h, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ e'.range,
    LinearEquiv.finrank_map_eq, LinearMap.range_prodMap, (Submodule.prodEquiv _ _).finrank_eq,
    Module.finrank_prod]
  rfl

variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Rank of a block matrix with invertible top-left block, through the Schur complement. -/
theorem rank_fromBlocks_of_isUnit₁₁ (A : Matrix m m K) (B : Matrix m n K) (C : Matrix n m K)
    (D : Matrix n n K) (hA : IsUnit A) :
    (fromBlocks A B C D).rank = Fintype.card m + (D - C * A⁻¹ * B).rank := by
  have := hA.invertible
  rw [fromBlocks_eq_of_invertible₁₁ A B C D, invOf_eq_nonsing_inv,
    rank_mul_eq_left_of_isUnit_det _ _ (by simp),
    rank_mul_eq_right_of_isUnit_det _ _ (by simp), rank_fromBlocks_diagonal,
    rank_of_isUnit A hA]

section PosDef

variable {𝕜 : Type*} [RCLike 𝕜] [PartialOrder 𝕜] [StarOrderedRing 𝕜]

/-- If `A` is positive definite and the Schur complement `D - Bᴴ * A⁻¹ * B` vanishes, then
`fromBlocks A B Bᴴ D` is positive semidefinite of rank `card m`. -/
theorem posSemidef_rank_of_schur_eq_zero {A : Matrix m m 𝕜} (B : Matrix m n 𝕜) (D : Matrix n n 𝕜)
    (hA : A.PosDef) (hS : D - Bᴴ * A⁻¹ * B = 0) :
    (fromBlocks A B Bᴴ D).PosSemidef ∧ (fromBlocks A B Bᴴ D).rank = Fintype.card m := by
  have hU : IsUnit A := hA.isUnit
  have := hU.invertible
  refine ⟨(PosDef.fromBlocks₁₁ B D hA).2 (hS ▸ PosSemidef.zero), ?_⟩
  rw [rank_fromBlocks_of_isUnit₁₁ A B Bᴴ D hU, hS, rank_zero, add_zero]

end PosDef

end Matrix
