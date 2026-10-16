/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Diagonal entries of the adjugate as principal minors

For a square matrix `A` indexed by an arbitrary finite type `n`, the diagonal entry
`adjugate A i i` is the determinant of the principal submatrix of `A` obtained by deleting row
and column `i`. The analogous statement for `Fin n.succ`, including the off-diagonal entries, is
`Matrix.adjugate_fin_succ_eq_det_submatrix`; the version here needs no reindexing to `Fin`.

## Main results

* `Matrix.adjugate_apply_self_eq_det_submatrix`: `adjugate A i i` is the determinant of
  `A.submatrix (↑) (↑)`, where `(↑) : {j // j ≠ i} → n`.
-/

@[expose] public section

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The diagonal entry `adjugate A i i` is the principal minor of `A` obtained by deleting row
and column `i`. See `Matrix.adjugate_fin_succ_eq_det_submatrix` for all entries when the index
type is `Fin n.succ`. -/
theorem adjugate_apply_self_eq_det_submatrix (A : Matrix n n R) (i : n) :
    adjugate A i i =
      det (A.submatrix ((↑) : {j // j ≠ i} → n) ((↑) : {j // j ≠ i} → n)) := by
  have : Unique {a : n // a = i} := ⟨⟨⟨i, rfl⟩⟩, fun y => Subtype.ext y.2⟩
  rw [adjugate_apply,
    ← det_submatrix_equiv_self (Equiv.sumCompl (· = i)) (A.updateRow i (Pi.single i (1 : R))),
    ← fromBlocks_toBlocks
        ((A.updateRow i (Pi.single i (1 : R))).submatrix
          (Equiv.sumCompl (· = i)) (Equiv.sumCompl (· = i)))]
  have h12 : ((A.updateRow i (Pi.single i (1 : R))).submatrix
      (Equiv.sumCompl (· = i)) (Equiv.sumCompl (· = i))).toBlocks₁₂ = 0 := by
    ext s t
    simp only [toBlocks₁₂, of_apply, submatrix_apply, Equiv.sumCompl_apply_inl,
      Equiv.sumCompl_apply_inr, zero_apply]
    rw [show ((s : {a // a = i}) : n) = i from s.2, updateRow_self, Pi.single_eq_of_ne t.2]
  have h11 : ((A.updateRow i (Pi.single i (1 : R))).submatrix
      (Equiv.sumCompl (· = i)) (Equiv.sumCompl (· = i))).toBlocks₁₁.det = 1 := by
    rw [det_unique]
    simp only [toBlocks₁₁, of_apply, submatrix_apply, Equiv.sumCompl_apply_inl]
    rw [show ((default : {a // a = i}) : n) = i from (default : {a // a = i}).2, updateRow_self,
      Pi.single_eq_same]
  have h22 : ((A.updateRow i (Pi.single i (1 : R))).submatrix
      (Equiv.sumCompl (· = i)) (Equiv.sumCompl (· = i))).toBlocks₂₂ =
      A.submatrix ((↑) : {j // j ≠ i} → n) ((↑) : {j // j ≠ i} → n) := by
    ext s t
    simp only [toBlocks₂₂, of_apply, submatrix_apply, Equiv.sumCompl_apply_inr]
    rw [updateRow_ne s.2]
  rw [h12, det_fromBlocks_zero₁₂, h11, h22, one_mul]

end Matrix
