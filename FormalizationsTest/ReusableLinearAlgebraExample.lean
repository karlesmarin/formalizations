/-
Usage example of the reusable layer, area LinearAlgebra, with the minimal import of that area: the
same code a user pastes into a file of their own project (README, section "Reusable layer").
-/
import Formalizations.Reusable.LinearAlgebra

open Formalizations.Reusable Matrix

/-- Rank of a block triangular matrix with a `1 × 1` identity corner. -/
example (B : Matrix (Fin 1) (Fin 2) ℚ) (D : Matrix (Fin 2) (Fin 2) ℚ) :
    (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) B 0 D).rank ≤ 1 + D.rank := by
  simpa only [Fintype.card_fin] using
    rank_fromBlocks_zero₂₁_le_card_add_rank (1 : Matrix (Fin 1) (Fin 1) ℚ) B D

/-- Subadditivity of the rank: `rank (A + A) ≤ 2 · rank A`. -/
example (A : Matrix (Fin 2) (Fin 3) ℚ) : (A + A).rank ≤ 2 * A.rank := by
  have := matrix_rank_add_le A A
  omega

/-- Cauchy–Binet with more rows than inner columns: the sum is empty, so `det (A * B) = 0`. -/
example (A : Matrix (Fin 3) (Fin 2) ℚ) (B : Matrix (Fin 2) (Fin 3) ℚ) : (A * B).det = 0 := by
  rw [det_mul_eq_sum_det_submatrix_mul_det_submatrix]
  refine Finset.sum_eq_zero fun S _ => absurd S.2 ?_
  have := S.1.card_le_univ
  simp only [Fintype.card_fin] at this ⊢
  omega

/-- Jacobi's formula on the characteristic matrix: `charpoly′ = trace (adjugate (X − M))`. -/
example (M : Matrix (Fin 3) (Fin 3) ℚ) :
    Polynomial.derivative M.charpoly = M.charmatrix.adjugate.trace := by
  have h1 : M.charmatrix.map Polynomial.derivative = 1 := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [charmatrix_apply_eq]
    · simp [charmatrix_apply_ne _ _ _ h, one_apply_ne h]
  rw [charpoly, derivative_det_eq_trace_adjugate_mul, h1, Matrix.mul_one]
