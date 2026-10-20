/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.TensorProduct.Matrix
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Rank of Kronecker products

## Main results

* `LinearMap.finrank_range_tensorProductMap`: over a field, `dim range (f ⊗ g) = dim range f · dim range g`.
* `Matrix.rank_kronecker`: `(A ⊗ₖ B).rank = A.rank * B.rank` over a field.
* `Matrix.rank_kronecker_one`: `(A ⊗ₖ (1 : Matrix p p K)).rank = Fintype.card p * A.rank`.

The general statement goes through linear maps: with standard bases `A ⊗ₖ B` is the matrix of
`TensorProduct.map (toLin A) (toLin B)` (`Matrix.toLin_kronecker`), and `map f g` factors as the surjection
`map f.rangeRestrict g.rangeRestrict` followed by the inclusion `range f ⊗ range g → P ⊗ Q`, which is injective
because vector spaces are flat.
-/

@[expose] public section

open Module
open scoped Kronecker

namespace LinearMap

variable {K : Type*} [Field K]

/-- Over a field, the image of `f ⊗ g` has dimension `dim range f · dim range g`. -/
theorem finrank_range_tensorProductMap {M N P Q : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [AddCommGroup Q] [Module K M] [Module K N] [Module K P] [Module K Q]
    [FiniteDimensional K M] [FiniteDimensional K N] (f : M →ₗ[K] P) (g : N →ₗ[K] Q) :
    finrank K (range (TensorProduct.map f g)) = finrank K (range f) * finrank K (range g) := by
  have hcomp : TensorProduct.map f g =
      (TensorProduct.map (range f).subtype (range g).subtype).comp
        (TensorProduct.map f.rangeRestrict g.rangeRestrict) := by
    rw [← TensorProduct.map_comp]
    rfl
  have hsurj : Function.Surjective (TensorProduct.map f.rangeRestrict g.rangeRestrict) :=
    TensorProduct.map_surjective f.surjective_rangeRestrict g.surjective_rangeRestrict
  have hinj : Function.Injective (TensorProduct.map (range f).subtype (range g).subtype) :=
    TensorProduct.map_injective_of_flat_flat _ _ Subtype.val_injective Subtype.val_injective
  rw [hcomp, range_comp_of_range_eq_top _ (range_eq_top.2 hsurj), finrank_range_of_inj hinj,
    Module.finrank_tensorProduct]

end LinearMap

namespace Matrix

/-- **The rank of a Kronecker product is the product of the ranks** (over a field). -/
theorem rank_kronecker {m n p q K : Type*} [Field K] [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q] (A : Matrix m n K)
    (B : Matrix p q K) : (A ⊗ₖ B).rank = A.rank * B.rank := by
  rw [rank_eq_finrank_range_toLin (A ⊗ₖ B) ((Pi.basisFun K m).tensorProduct (Pi.basisFun K p))
      ((Pi.basisFun K n).tensorProduct (Pi.basisFun K q)),
    show A ⊗ₖ B = kroneckerMap (· * ·) A B from rfl, toLin_kronecker,
    LinearMap.finrank_range_tensorProductMap,
    ← rank_eq_finrank_range_toLin A (Pi.basisFun K m) (Pi.basisFun K n),
    ← rank_eq_finrank_range_toLin B (Pi.basisFun K p) (Pi.basisFun K q)]

variable {m n p K : Type*} [Field K]

section Kronecker

variable [Fintype n] [Fintype p] [DecidableEq p]

private theorem kronecker_one_mulVec_apply (A : Matrix m n K) (v : n × p → K) (i : m) (k : p) :
    ((A ⊗ₖ (1 : Matrix p p K)) *ᵥ v) (i, k) = (A *ᵥ fun j => v (j, k)) i := by
  simp [mulVec, dotProduct, kroneckerMap_apply, one_apply, Fintype.sum_prod_type]

/-- `ker (A ⊗ₖ 1) ≃ (p → ker A)`. -/
private noncomputable def kerKroneckerOneEquiv (A : Matrix m n K) :
    LinearMap.ker (A ⊗ₖ (1 : Matrix p p K)).mulVecLin ≃ₗ[K] (p → LinearMap.ker A.mulVecLin) where
  toFun v k := ⟨fun j => (v : n × p → K) (j, k), by
    rw [LinearMap.mem_ker, mulVecLin_apply]
    funext i
    have hv : (A ⊗ₖ (1 : Matrix p p K)) *ᵥ (v : n × p → K) = 0 := v.2
    rw [← kronecker_one_mulVec_apply, hv]
    rfl⟩
  invFun w := ⟨fun q => (w q.2 : n → K) q.1, by
    rw [LinearMap.mem_ker, mulVecLin_apply]
    funext ⟨i, k⟩
    rw [kronecker_one_mulVec_apply]
    exact congrFun (w k).2 i⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The rank of `A ⊗ₖ 1` is `Fintype.card p` times the rank of `A`. -/
theorem rank_kronecker_one (A : Matrix m n K) :
    (A ⊗ₖ (1 : Matrix p p K)).rank = Fintype.card p * A.rank := by
  have hk := (kerKroneckerOneEquiv (p := p) A).finrank_eq
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hk
  have h1 : (A ⊗ₖ (1 : Matrix p p K)).rank +
      finrank K (LinearMap.ker (A ⊗ₖ (1 : Matrix p p K)).mulVecLin) = Fintype.card (n × p) := by
    rw [rank, LinearMap.finrank_range_add_finrank_ker, Module.finrank_fintype_fun_eq_card]
  have h2 : A.rank + finrank K (LinearMap.ker A.mulVecLin) = Fintype.card n := by
    rw [rank, LinearMap.finrank_range_add_finrank_ker, Module.finrank_fintype_fun_eq_card]
  rw [Fintype.card_prod, hk] at h1
  have h3 : Fintype.card p * (A.rank + finrank K (LinearMap.ker A.mulVecLin)) =
      Fintype.card p * Fintype.card n := by
    rw [h2]
  rw [Nat.mul_add] at h3
  rw [Nat.mul_comm (Fintype.card n)] at h1
  omega

end Kronecker

end Matrix
