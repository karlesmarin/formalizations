/-
Usage example of the reusable layer, area LinearAlgebra, with the minimal import of that area: the
same code a user pastes into a file of their own project (README, section "Reusable layer").
-/
import Formalizations.Reusable.LinearAlgebra

open Formalizations.Reusable Matrix
open scoped Kronecker

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

/-- A block upper-triangular matrix with identity diagonal blocks is invertible, whatever its
corner `B`: its rank is at least `2 + 2`. -/
example (B : Matrix (Fin 2) (Fin 2) ℚ) :
    4 ≤ (fromBlocks (1 : Matrix (Fin 2) (Fin 2) ℚ) B 0 (1 : Matrix (Fin 2) (Fin 2) ℚ)).rank := by
  have h := matrix_rank_add_rank_le_rank_fromBlocks (1 : Matrix (Fin 2) (Fin 2) ℚ) B
    (1 : Matrix (Fin 2) (Fin 2) ℚ)
  simpa only [rank_one, Fintype.card_fin] using h

/-- The Kronecker square of a matrix has the square of its rank. -/
example (A : Matrix (Fin 2) (Fin 3) ℚ) : (A ⊗ₖ A).rank = A.rank ^ 2 := by
  rw [matrix_rank_kronecker, sq]

/-- The trace of the adjugate is the sum of the principal `(n − 1) × (n − 1)` minors (up to sign,
the coefficient of `X` in the characteristic polynomial). -/
example {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℚ) :
    A.adjugate.trace = ∑ i : n, (A.submatrix ((↑) : {j // j ≠ i} → n) ((↑) : {j // j ≠ i} → n)).det := by
  rw [Matrix.trace]
  exact Finset.sum_congr rfl fun i _ => adjugate_apply_self_eq_det_principal_submatrix A i

/-- A symmetric matrix with alternating characteristic polynomial is PSD (passes the hypothesis on). -/
example (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.IsSymm)
    (h : ∀ k ≤ A.charpoly.natDegree, 0 ≤ (-1 : ℝ) ^ (A.charpoly.natDegree - k) * A.charpoly.coeff k) :
    A.PosSemidef :=
  posSemidef_of_charpoly_alternating hA h

/-- A PSD matrix is a sum of `rank A` squares of linear forms. -/
example (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.PosSemidef) :
    ∃ v : Fin A.rank → (Fin 3 → ℝ), ∀ u, u ⬝ᵥ (A *ᵥ u) = ∑ i, (v i ⬝ᵥ u) ^ 2 :=
  psd_quadForm_eq_sum_rank_sq hA rfl

/-- Rank through the Schur complement: an invertible corner adds its size to the rank. -/
example (A : Matrix (Fin 1) (Fin 1) ℚ) (hA : IsUnit A) (B : Matrix (Fin 1) (Fin 2) ℚ)
    (C : Matrix (Fin 2) (Fin 1) ℚ) (D : Matrix (Fin 2) (Fin 2) ℚ) :
    (fromBlocks A B C D).rank = 1 + (D - C * A⁻¹ * B).rank := by
  simpa using Formalizations.Reusable.rank_fromBlocks_of_isUnit₁₁ A B C D hA

/-- Sums of squares of bilinear forms transport under an orthogonal change `H ↦ Dᵀ H D`. -/
example (H D : Matrix (Fin 3) (Fin 3) ℚ) (hD : Dᵀ * D = 1) (B : Fin 4 → Matrix (Fin 2) (Fin 3) ℚ)
    (h : ∀ x y, BiquadraticSOS.P H x y = ∑ i, (x ⬝ᵥ (B i *ᵥ y)) ^ 2) (x : Fin 2 → ℚ) (y : Fin 3 → ℚ) :
    BiquadraticSOS.P (Dᵀ * H * D) x y = ∑ i, (x ⬝ᵥ ((B i * D) *ᵥ y)) ^ 2 :=
  biquadratic_sos_transport hD B h x y

/-- Integer orthonormal columns are signed unit vectors in distinct rows. -/
example (A : Matrix (Fin 3) (Fin 2) ℤ) (hA : Aᵀ * A = 1) :
    ∃ f : Fin 2 → Fin 3, Function.Injective f ∧
      ∀ j, (fun i => A i j) = Pi.single (f j) 1 ∨ (fun i => A i j) = Pi.single (f j) (-1) :=
  int_columns_of_transpose_mul_self hA

/-- Schur: a commutative subspace of `M₂(ℚ)` has dimension at most `2`. -/
example (S : Submodule ℚ (Matrix (Fin 2) (Fin 2) ℚ)) (hS : ∀ A ∈ S, ∀ B ∈ S, A * B = B * A) :
    Module.finrank ℚ S ≤ 2 := by
  simpa using schur_commuting_finrank_le S hS


/-- Hua's identity over `ℚ` with `a = 2`, `b = 1`: `2 − (1/2 + (1 − 2)⁻¹)⁻¹ = 4`. -/
example : (2 : ℚ) - ((2 : ℚ)⁻¹ + ((1 : ℚ)⁻¹ - 2)⁻¹)⁻¹ = 4 := by
  have h := hua_identity (a := (2 : ℚ)) (b := 1) (by norm_num) (by norm_num) (by norm_num)
  rw [h]; norm_num

open PowerSeries in
/-- Newton's identity for traces for a `2 × 2` integer matrix. -/
example (M : Matrix (Fin 2) (Fin 2) ℤ) :
    d⁄dX (M.charpolyRev : ℤ⟦X⟧) =
      -(M.charpolyRev : ℤ⟦X⟧) * PowerSeries.mk fun k => (M ^ (k + 1)).trace :=
  Formalizations.Reusable.derivative_coe_charpolyRev M
