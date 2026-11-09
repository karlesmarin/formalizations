/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
-- encaje: general core of the block rank bounds; `Formalizations.LinearAlgebra.Matrix.Rank` (archive) and
-- `Formalizations.Reusable.LinearAlgebra` (stable facade) both import it, so the proof lives in one place.
module

public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Upper bounds for the rank of block upper triangular matrices

Throughout, `K` is a field. This file needs only `Mathlib.LinearAlgebra.Matrix.Rank`. It is the
smallest home of the rank bound re-exposed by `Formalizations.Reusable.LinearAlgebra`, so a user of
that bound does not compile the rest of `Formalizations.LinearAlgebra.Matrix.Rank`.

## Main results

* `Matrix.rank_add_le`: `(A + B).rank ≤ A.rank + B.rank`.
* `Matrix.rank_fromBlocks_zero₂₁_le_left`, `Matrix.rank_fromBlocks_zero₂₁_le_right`: upper bounds
  for the rank of `fromBlocks A B 0 D` in terms of the rank of one diagonal block.

## Related

Mathlib has `LinearMap.rank_add_le` (cardinal rank of linear maps) but no `Matrix.rank_add_le`.
The lower bound `Matrix.rank_add_rank_le_rank_fromBlocks_zero₂₁` and the nullity bounds are in
`Formalizations.LinearAlgebra.Matrix.Rank`, which imports this file.
-/

@[expose] public section

namespace Matrix

variable {l m n o p K : Type*} [Field K]

/-- Subadditivity of the rank of matrices. -/
theorem rank_add_le [Fintype n] (A B : Matrix m n K) : (A + B).rank ≤ A.rank + B.rank := by
  rw [rank, mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

section Blocks

variable [Fintype n] [Fintype o]

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
