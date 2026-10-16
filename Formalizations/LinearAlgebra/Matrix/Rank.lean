/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank inequalities for sums and block triangular matrices

Throughout, `K` is a field. The nullity of a matrix `A` is expressed as
`Module.finrank K (LinearMap.ker A.mulVecLin)`; by `Matrix.rank_add_finrank_ker_mulVecLin` it equals
`Fintype.card n - A.rank` when `A` has columns indexed by `n`.

## Main results

* `Matrix.rank_add_le`: `(A + B).rank ≤ A.rank + B.rank`.
* `Matrix.rank_add_finrank_ker_mulVecLin`: rank–nullity for matrices.
* `Matrix.finrank_ker_mulVecLin_add_le`: if `U` is invertible, the nullity of `U + E` is at most
  `E.rank`; `Matrix.finrank_ker_mulVecLin_sub_mul_le`: the nullity of `U - P * Q` is at most the
  number of columns of `P`.
* `Matrix.finrank_ker_mulVecLin_fromBlocks_zero₂₁_le`: the nullity of `fromBlocks A B 0 D` is at
  most the sum of the nullities of `A` and `D`.
* `Matrix.rank_add_rank_le_rank_fromBlocks_zero₂₁`: `A.rank + D.rank ≤ (fromBlocks A B 0 D).rank`.
* `Matrix.rank_fromBlocks_zero₂₁_le_left`, `Matrix.rank_fromBlocks_zero₂₁_le_right`: upper bounds
  for the rank of `fromBlocks A B 0 D` in terms of the rank of one diagonal block.
-/

@[expose] public section

open Module

namespace Matrix

variable {l m n o p K : Type*} [Field K]

section Sum

variable [Fintype n]

/-- Subadditivity of the rank of matrices. -/
theorem rank_add_le (A B : Matrix m n K) : (A + B).rank ≤ A.rank + B.rank := by
  rw [rank, mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- Negating a matrix does not change its rank. -/
@[simp]
theorem rank_neg (A : Matrix m n K) : (-A).rank = A.rank := by
  have h : (-A).mulVecLin = -A.mulVecLin := LinearMap.ext fun v => neg_mulVec v A
  rw [rank, rank, h, LinearMap.range_neg]

/-- The rank of a difference is at most the sum of the ranks. -/
theorem rank_sub_le (A B : Matrix m n K) : (A - B).rank ≤ A.rank + B.rank := by
  simpa [sub_eq_add_neg] using rank_add_le A (-B)

/-- Rank–nullity for matrices: the rank plus the dimension of the kernel of `A.mulVecLin` is the
number of columns. -/
theorem rank_add_finrank_ker_mulVecLin (A : Matrix m n K) :
    A.rank + finrank K (LinearMap.ker A.mulVecLin) = Fintype.card n := by
  rw [rank, LinearMap.finrank_range_add_finrank_ker, Module.finrank_fintype_fun_eq_card]

/-- If `U` is invertible, the nullity of `U + E` is at most the rank of `E`. -/
theorem finrank_ker_mulVecLin_add_le [DecidableEq n] {U : Matrix n n K} (hU : IsUnit U)
    (E : Matrix n n K) : finrank K (LinearMap.ker (U + E).mulVecLin) ≤ E.rank := by
  have h1 := rank_add_finrank_ker_mulVecLin (U + E)
  have h2 : U.rank ≤ (U + E).rank + (-E).rank := by
    simpa using rank_add_le (U + E) (-E)
  rw [rank_of_isUnit U hU, rank_neg] at h2
  omega

/-- If `U` is invertible, the nullity of `U - E` is at most the rank of `E`. -/
theorem finrank_ker_mulVecLin_sub_le [DecidableEq n] {U : Matrix n n K} (hU : IsUnit U)
    (E : Matrix n n K) : finrank K (LinearMap.ker (U - E).mulVecLin) ≤ E.rank := by
  rw [sub_eq_add_neg, ← rank_neg E]
  exact finrank_ker_mulVecLin_add_le hU (-E)

/-- If `U` is invertible and `P` has columns indexed by `o`, the nullity of `U - P * Q` is at most
`Fintype.card o`. -/
theorem finrank_ker_mulVecLin_sub_mul_le [DecidableEq n] [Fintype o] {U : Matrix n n K}
    (hU : IsUnit U) (P : Matrix n o K) (Q : Matrix o n K) :
    finrank K (LinearMap.ker (U - P * Q).mulVecLin) ≤ Fintype.card o :=
  (finrank_ker_mulVecLin_sub_le hU _).trans <|
    (rank_mul_le_left P Q).trans (rank_le_card_width P)

end Sum

section Blocks

variable [Fintype n] [Fintype o]

/-- The nullity of a block upper triangular matrix is at most the sum of the nullities of its
diagonal blocks. -/
theorem finrank_ker_mulVecLin_fromBlocks_zero₂₁_le (A : Matrix l n K) (B : Matrix l o K)
    (D : Matrix p o K) :
    finrank K (LinearMap.ker (fromBlocks A B 0 D).mulVecLin) ≤
      finrank K (LinearMap.ker A.mulVecLin) + finrank K (LinearMap.ker D.mulVecLin) := by
  set KM := LinearMap.ker (fromBlocks A B 0 D).mulVecLin
  have hmem : ∀ v : KM, A *ᵥ ((v : n ⊕ o → K) ∘ Sum.inl) + B *ᵥ ((v : n ⊕ o → K) ∘ Sum.inr) = 0
      ∧ D *ᵥ ((v : n ⊕ o → K) ∘ Sum.inr) = 0 := by
    intro v
    have hv : fromBlocks A B 0 D *ᵥ (v : n ⊕ o → K) = 0 := v.2
    rw [fromBlocks_mulVec] at hv
    refine ⟨funext fun i => ?_, funext fun i => ?_⟩
    · simpa using congrFun hv (Sum.inl i)
    · simpa using congrFun hv (Sum.inr i)
  let f : KM →ₗ[K] (o → K) := (LinearMap.funLeft K K Sum.inr).comp KM.subtype
  have hf : ∀ v : KM, f v = (v : n ⊕ o → K) ∘ Sum.inr := fun v => rfl
  have hfr : LinearMap.range f ≤ LinearMap.ker D.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker, mulVecLin_apply, hf]
    exact (hmem v).2
  let g : LinearMap.ker f →ₗ[K] (n → K) :=
    (LinearMap.funLeft K K Sum.inl).comp (KM.subtype.comp (LinearMap.ker f).subtype)
  have hg : ∀ u : LinearMap.ker f, g u = ((u : KM) : n ⊕ o → K) ∘ Sum.inl := fun u => rfl
  have hinr : ∀ u : LinearMap.ker f, ((u : KM) : n ⊕ o → K) ∘ Sum.inr = 0 := by
    intro u
    rw [← hf]
    exact u.2
  have hginj : Function.Injective g := by
    intro u u' hu
    rw [hg, hg] at hu
    apply Subtype.ext
    apply Subtype.ext
    funext s
    rcases s with i | i
    · exact congrFun hu i
    · exact (congrFun (hinr u) i).trans (congrFun (hinr u') i).symm
  have hgr : LinearMap.range g ≤ LinearMap.ker A.mulVecLin := by
    rintro _ ⟨u, rfl⟩
    rw [LinearMap.mem_ker, mulVecLin_apply, hg]
    have h := (hmem (u : KM)).1
    rwa [hinr u, mulVec_zero, add_zero] at h
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : finrank K (LinearMap.range f) ≤ finrank K (LinearMap.ker D.mulVecLin) :=
    Submodule.finrank_mono hfr
  have h3 : finrank K (LinearMap.ker f) ≤ finrank K (LinearMap.ker A.mulVecLin) := by
    rw [← LinearMap.finrank_range_of_inj hginj]
    exact Submodule.finrank_mono hgr
  omega

/-- The rank of a block upper triangular matrix is at least the sum of the ranks of its diagonal
blocks. -/
theorem rank_add_rank_le_rank_fromBlocks_zero₂₁ (A : Matrix l n K) (B : Matrix l o K)
    (D : Matrix p o K) : A.rank + D.rank ≤ (fromBlocks A B 0 D).rank := by
  have h := finrank_ker_mulVecLin_fromBlocks_zero₂₁_le A B D
  have hA := rank_add_finrank_ker_mulVecLin A
  have hD := rank_add_finrank_ker_mulVecLin D
  have hM := rank_add_finrank_ker_mulVecLin (fromBlocks A B 0 D)
  rw [Fintype.card_sum] at hM
  omega

/-- The rank of `fromBlocks A B 0 D` is at most the rank of `A` plus the number of columns
of `D`. -/
theorem rank_fromBlocks_zero₂₁_le_left [Finite l] (A : Matrix l n K) (B : Matrix l o K)
    (D : Matrix p o K) : (fromBlocks A B 0 D).rank ≤ A.rank + Fintype.card o := by
  classical
  have := Fintype.ofFinite l
  have hsplit : fromBlocks A B 0 D = fromBlocks A 0 0 0 + fromBlocks 0 B 0 D := by
    rw [fromBlocks_add]
    simp
  let P : Matrix (l ⊕ p) l K := of fun i j => if i = Sum.inl j then 1 else 0
  let Q : Matrix n (n ⊕ o) K := of fun j k => if k = Sum.inl j then 1 else 0
  have hL : fromBlocks A 0 0 0 = P * A * Q := by
    ext (i | i) (k | k) <;> simp [P, Q, mul_apply, fromBlocks]
  let X : Matrix (l ⊕ p) o K := of fun i j => fromBlocks (0 : Matrix l n K) B 0 D i (Sum.inr j)
  let Y : Matrix o (n ⊕ o) K := of fun j k => if k = Sum.inr j then 1 else 0
  have hR : fromBlocks 0 B 0 D = X * Y := by
    ext (i | i) (k | k) <;> simp [X, Y, mul_apply]
  have h1 : (fromBlocks A (0 : Matrix l o K) 0 (0 : Matrix p o K)).rank ≤ A.rank := by
    rw [hL]
    exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  have h2 : (fromBlocks (0 : Matrix l n K) B 0 D).rank ≤ Fintype.card o := by
    rw [hR]
    exact (rank_mul_le_left _ _).trans (rank_le_card_width _)
  rw [hsplit]
  exact (rank_add_le _ _).trans (Nat.add_le_add h1 h2)

/-- The rank of `fromBlocks A B 0 D` is at most the number of rows of `A` plus the rank
of `D`. -/
theorem rank_fromBlocks_zero₂₁_le_right [Fintype l] [Finite p] (A : Matrix l n K)
    (B : Matrix l o K) (D : Matrix p o K) :
    (fromBlocks A B 0 D).rank ≤ Fintype.card l + D.rank := by
  classical
  have := Fintype.ofFinite p
  have hsplit : fromBlocks A B 0 D = fromBlocks A B 0 0 + fromBlocks 0 0 0 D := by
    rw [fromBlocks_add]
    simp
  let X : Matrix (l ⊕ p) l K := of fun i j => if i = Sum.inl j then 1 else 0
  let Y : Matrix l (n ⊕ o) K :=
    of fun j k => fromBlocks A B (0 : Matrix p n K) (0 : Matrix p o K) (Sum.inl j) k
  have hL : fromBlocks A B 0 0 = X * Y := by
    ext (i | i) (k | k) <;> simp [X, Y, mul_apply]
  let P : Matrix (l ⊕ p) p K := of fun i j => if i = Sum.inr j then 1 else 0
  let Q : Matrix o (n ⊕ o) K := of fun j k => if k = Sum.inr j then 1 else 0
  have hR : fromBlocks 0 0 0 D = P * D * Q := by
    ext (i | i) (k | k) <;> simp [P, Q, mul_apply, fromBlocks]
  have h1 : (fromBlocks A B 0 (0 : Matrix p o K)).rank ≤ Fintype.card l := by
    rw [hL]
    exact (rank_mul_le_left _ _).trans (rank_le_card_width _)
  have h2 : (fromBlocks (0 : Matrix l n K) (0 : Matrix l o K) 0 D).rank ≤ D.rank := by
    rw [hR]
    exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  rw [hsplit]
  exact (rank_add_le _ _).trans (Nat.add_le_add h1 h2)

end Blocks

end Matrix
