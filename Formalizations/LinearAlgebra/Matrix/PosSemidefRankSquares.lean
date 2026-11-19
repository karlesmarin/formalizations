/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef

/-!
# A positive semidefinite matrix of rank k is a sum of k squares

A real positive semidefinite matrix of rank k is a sum of k rank-one matrices v v^T. Equivalently
its quadratic form is a sum of k squares of linear forms.

## Main results

* `PosSemidefRankSquares.exists_sum_vecMulVec_self`: PSD A with rank k: A = sum of k vecMulVec (v i) (v i)
* `PosSemidefRankSquares.quadForm_eq_sum_sq`: u ⬝ᵥ (A *ᵥ u) = sum of k squares (v i ⬝ᵥ u)^2

## References

* Mathlib: Matrix.IsHermitian.spectral_theorem, Matrix.PosSemidef.eigenvalues_nonneg, Matrix.IsHermitian.rank_eq_card_non_zero_eigs, Finset.equivFinOfCardEq.
* Mathlib no tiene la factorizacion con k filas (solo posSemidef_iff_eq_conjTranspose_mul_self, B cuadrada).
-/

@[expose] public section

namespace PosSemidefRankSquares

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **PSD of rank `k` is a sum of `k` rank-one squares.** -/
theorem exists_sum_vecMulVec_self {A : Matrix n n ℝ} (hA : A.PosSemidef) {k : ℕ}
    (hk : A.rank = k) :
    ∃ v : Fin k → (n → ℝ), A = ∑ i, vecMulVec (v i) (v i) := by
  have hH := hA.isHermitian
  set w : n → (n → ℝ) := fun j a =>
    Real.sqrt (hH.eigenvalues j) * hH.eigenvectorBasis j a with hw
  have hsum : A = ∑ j, vecMulVec (w j) (w j) := by
    ext a b
    rw [hH.spectral_theorem]
    simp only [Matrix.sum_apply, vecMulVec_apply, hw]
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply,
      Unitary.conjStarAlgAut_apply, Matrix.IsHermitian.eigenvectorUnitary_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h0 := hA.eigenvalues_nonneg j
    have h1 : Real.sqrt (hH.eigenvalues j) * Real.sqrt (hH.eigenvalues j) = hH.eigenvalues j :=
      Real.mul_self_sqrt h0
    linear_combination (-(hH.eigenvectorBasis j a)) * (hH.eigenvectorBasis j b) * h1
  classical
  have hcard : (univ.filter fun j => hH.eigenvalues j ≠ 0).card = k := by
    rw [← hk, hH.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  let e : Fin k ≃ {j // j ∈ univ.filter fun j => hH.eigenvalues j ≠ 0} :=
    ((univ.filter fun j => hH.eigenvalues j ≠ 0).equivFinOfCardEq hcard).symm
  refine ⟨fun i => w (e i).1, ?_⟩
  rw [Equiv.sum_comp e (fun s => vecMulVec (w s.1) (w s.1)),
    Finset.sum_coe_sort (univ.filter fun j => hH.eigenvalues j ≠ 0)
      (fun j => vecMulVec (w j) (w j))]
  conv_lhs => rw [hsum]
  symm
  refine Finset.sum_subset (Finset.filter_subset _ _) fun j _ hj => ?_
  have hj0 : hH.eigenvalues j = 0 := by simpa using hj
  have : w j = 0 := by
    ext a; simp [hw, hj0]
  simp [this]

/-- **Corollary.** The quadratic form of a PSD matrix of rank `k` is a sum of `k` squares of
linear forms: `u ⬝ᵥ (A *ᵥ u) = ∑ i, (v i ⬝ᵥ u)^2`. -/
theorem quadForm_eq_sum_sq {A : Matrix n n ℝ} (hA : A.PosSemidef) {k : ℕ}
    (hk : A.rank = k) :
    ∃ v : Fin k → (n → ℝ), ∀ u : n → ℝ, u ⬝ᵥ (A *ᵥ u) = ∑ i, (v i ⬝ᵥ u) ^ 2 := by
  obtain ⟨v, hv⟩ := exists_sum_vecMulVec_self hA hk
  refine ⟨v, fun u => ?_⟩
  rw [hv, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.vecMulVec_mulVec, dotProduct_smul]
  simp [dotProduct_comm u (v i), sq]

end PosSemidefRankSquares
