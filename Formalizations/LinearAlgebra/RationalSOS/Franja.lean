/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The Lebedev 3×2 strip: four real squares suffice, four rational squares do not

The biquadratic form of the 3×2 strip of Lebedev (arXiv:2610.05442, eq. (19)) is a sum of four
squares of real bilinear forms, with coefficients in Q(√3), but not a sum of four squares of
rational bilinear forms, not even with nonnegative rational weights. The proof forces the Gram
matrix to a three-parameter family by comparing coefficients and uses five 5×5 minors.

## Main results

* `Franja.real_four_squares`: the strip form is a sum of 4 squares of real bilinear forms (Theorem A)
* `Franja.not_rational_four_squares`: it is not a weighted sum of 4 squares of rational bilinear forms with nonnegative weights (Theorem B)

## References

* N. Lebedev, Asymptotic equivalence and exact values for second-order Zarankiewicz numbers, arXiv:2610.05442 (2026), eq. (19) (the strip).
* C. Marín, Rational sums-of-squares lengths of biquadratic forms and orthogonal dilations (in preparation).
-/

@[expose] public section

namespace Franja

/-- The biquadratic form of the 3×2 strip. -/
def P {R : Type*} [CommRing R] (x0 x1 x2 y0 y1 : R) : R :=
  (x0 * y0 + x1 * y1) ^ 2 + (x0 * y1) ^ 2 + (x1 * y0) ^ 2 + (x2 * y0) ^ 2 + (x2 * y1) ^ 2

/-- The six cells `u_c = x_a y_b`. -/
def cells {R : Type*} [CommRing R] (x0 x1 x2 y0 y1 : R) : Fin 6 → R :=
  ![x0 * y0, x0 * y1, x1 * y0, x1 * y1, x2 * y0, x2 * y1]

/-- **Theorem A.** Four real squares of bilinear forms suffice. -/
theorem real_four_squares :
    ∃ ℓ : Fin 4 → Fin 6 → ℝ, ∀ x0 x1 x2 y0 y1 : ℝ,
      P x0 x1 x2 y0 y1 = ∑ k, (∑ c, ℓ k c * cells x0 x1 x2 y0 y1 c) ^ 2 := by
  set s : ℝ := √3 / 2 with hs_def
  refine ⟨![![1, 0, 0, 1 / 2, 0, -s], ![0, 0, 0, s, 0, 1 / 2], ![0, 1, 1 / 2, 0, s, 0],
    ![0, 0, s, 0, -(1 / 2), 0]], ?_⟩
  intro x0 x1 x2 y0 y1
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [P, cells, Fin.sum_univ_four, Fin.sum_univ_six, Matrix.cons_val, hs_def]
  linear_combination
    (-(1 / 4) * ((x1 * y0) ^ 2 + (x1 * y1) ^ 2 + (x2 * y0) ^ 2 + (x2 * y1) ^ 2)) * h3

/-- The forced Gram matrix (rows/columns `u0..u5`). -/
def Gt (t a b : ℚ) : Matrix (Fin 6) (Fin 6) ℚ :=
  !![1, 0, 0, 1 - t, 0, -a;
     0, 1, t, 0, a, 0;
     0, t, 1, 0, 0, -b;
     1 - t, 0, 0, 1, b, 0;
     0, a, 0, b, 1, 0;
     -a, 0, -b, 0, 0, 1]

/-- A 5×5 matrix that factors through `Fin 4` is singular. -/
lemma det_eq_zero_of_factor (M : Matrix (Fin 5) (Fin 5) ℚ) (A : Matrix (Fin 5) (Fin 4) ℚ)
    (B : Matrix (Fin 4) (Fin 5) ℚ) (h : M = A * B) : M.det = 0 := by
  by_contra hne
  have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.2 hne)
  have h1 := Matrix.rank_of_isUnit M hu
  have h2 : M.rank ≤ 4 := h ▸ (Matrix.rank_mul_le_left A B).trans (Matrix.rank_le_width A)
  simp only [Fintype.card_fin] at h1
  omega

/-- `q^2 = 3` has no rational solution. -/
lemma no_rat_sqrt_three (q : ℚ) : q ^ 2 ≠ 3 := by
  intro h
  have hsq : IsSquare ((3 : ℕ) : ℚ) := ⟨q, by push_cast; rw [← h]; ring⟩
  exact Nat.prime_three.not_isSquare (Rat.isSquare_natCast_iff.1 hsq)

lemma minor_01245 (t a b : ℚ) : ((Gt t a b).submatrix ![0, 1, 2, 4, 5] ![0, 1, 2, 4, 5]).det
    = (a ^ 2 - 1) * (a ^ 2 + b ^ 2 + t ^ 2 - 1) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  rw [Matrix.det_succ_row_zero, Matrix.det_succ_row_zero, Matrix.det_succ_row_zero,
    Matrix.det_succ_row_zero, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Gt, Fin.succAbove, Matrix.submatrix]
  ring

lemma minor_01345 (t a b : ℚ) : ((Gt t a b).submatrix ![0, 1, 3, 4, 5] ![0, 1, 3, 4, 5]).det
    = (a ^ 2 - 1) * (a ^ 2 + b ^ 2 + t ^ 2 - 2 * t) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  rw [Matrix.det_succ_row_zero, Matrix.det_succ_row_zero, Matrix.det_succ_row_zero,
    Matrix.det_succ_row_zero, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Gt, Fin.succAbove, Matrix.submatrix]
  ring

lemma minor_02345 (t a b : ℚ) : ((Gt t a b).submatrix ![0, 2, 3, 4, 5] ![0, 2, 3, 4, 5]).det
    = (b ^ 2 - 1) * (a ^ 2 + b ^ 2 + t ^ 2 - 2 * t) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  rw [Matrix.det_succ_row_zero, Matrix.det_succ_row_zero, Matrix.det_succ_row_zero,
    Matrix.det_succ_row_zero, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Gt, Fin.succAbove, Matrix.submatrix]
  ring

lemma minor_12345 (t a b : ℚ) : ((Gt t a b).submatrix ![1, 2, 3, 4, 5] ![1, 2, 3, 4, 5]).det
    = (b ^ 2 - 1) * (a ^ 2 + b ^ 2 + t ^ 2 - 1) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  rw [Matrix.det_succ_row_zero, Matrix.det_succ_row_zero, Matrix.det_succ_row_zero,
    Matrix.det_succ_row_zero, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Gt, Fin.succAbove, Matrix.submatrix]
  ring

/-- A non-principal minor: rows `{0,1,2,3,4}`, columns `{0,1,2,3,5}`. -/
lemma minor_01234_01235 (t a b : ℚ) :
    ((Gt t a b).submatrix ![0, 1, 2, 3, 4] ![0, 1, 2, 3, 5]).det
      = -(a * b * (t ^ 2 - t + 1)) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  rw [Matrix.det_succ_row_zero, Matrix.det_succ_row_zero, Matrix.det_succ_row_zero,
    Matrix.det_succ_row_zero, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Gt, Fin.succAbove, Matrix.submatrix]
  ring

/-- **Theorem B.** No four rational squares with nonnegative rational weights. -/
theorem not_rational_four_squares :
    ¬ ∃ (d : Fin 4 → ℚ) (ℓ : Fin 4 → Fin 6 → ℚ), (∀ k, 0 ≤ d k) ∧
      ∀ x0 x1 x2 y0 y1 : ℚ,
        P x0 x1 x2 y0 y1 = ∑ k, d k * (∑ c, ℓ k c * cells x0 x1 x2 y0 y1 c) ^ 2 := by
  rintro ⟨d, ℓ, -, hP⟩
  obtain ⟨g, hg⟩ : ∃ g : Fin 6 → Fin 6 → ℚ, ∀ i j, g i j = ∑ k, d k * ℓ k i * ℓ k j :=
    ⟨_, fun _ _ => rfl⟩
  have hQ : ∀ u : Fin 6 → ℚ,
      ∑ k, d k * (∑ c, ℓ k c * u c) ^ 2 = ∑ i, ∑ j, g i j * u i * u j := by
    intro u
    simp only [hg, Fin.sum_univ_four, Fin.sum_univ_six]
    ring
  have hs : ∀ i j, g i j = g j i := fun i j => by
    rw [hg, hg]; exact Finset.sum_congr rfl fun k _ => by ring
  have E : ∀ x0 x1 x2 y0 y1 : ℚ, P x0 x1 x2 y0 y1 =
      ∑ i, ∑ j, g i j * cells x0 x1 x2 y0 y1 i * cells x0 x1 x2 y0 y1 j :=
    fun x0 x1 x2 y0 y1 => (hP x0 x1 x2 y0 y1).trans (hQ _)
  -- coefficient extraction: x ∈ {e0,e1,e2,e0+e1,e0+e2,e1+e2}, y ∈ {e0, e1, e0+e1}
  have a1 := E 1 0 0 1 0
  have a2 := E 1 0 0 0 1
  have a3 := E 1 0 0 1 1
  have a4 := E 0 1 0 1 0
  have a5 := E 0 1 0 0 1
  have a6 := E 0 1 0 1 1
  have a7 := E 0 0 1 1 0
  have a8 := E 0 0 1 0 1
  have a9 := E 0 0 1 1 1
  have b1 := E 1 1 0 1 0
  have b2 := E 1 1 0 0 1
  have b3 := E 1 1 0 1 1
  have b4 := E 1 0 1 1 0
  have b5 := E 1 0 1 0 1
  have b6 := E 1 0 1 1 1
  have b7 := E 0 1 1 1 0
  have b8 := E 0 1 1 0 1
  have b9 := E 0 1 1 1 1
  simp only [P, cells, Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, mul_one, mul_zero, add_zero, zero_add] at a1 a2 a3 a4 a5 a6 a7 a8 a9
  simp only [P, cells, Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, mul_one, mul_zero, add_zero, zero_add] at b1 b2 b3 b4 b5 b6 b7 b8 b9
  norm_num at a1 a2 a3 a4 a5 a6 a7 a8 a9 b1 b2 b3 b4 b5 b6 b7 b8 b9
  have s10 := hs 1 0; have s20 := hs 2 0; have s30 := hs 3 0; have s40 := hs 4 0
  have s50 := hs 5 0; have s21 := hs 2 1; have s31 := hs 3 1; have s41 := hs 4 1
  have s51 := hs 5 1; have s32 := hs 3 2; have s42 := hs 4 2; have s52 := hs 5 2
  have s43 := hs 4 3; have s53 := hs 5 3; have s54 := hs 5 4
  have hG : ∀ i j, g i j = Gt (g 1 2) (g 1 4) (g 3 4) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Gt] <;> linarith
  -- rank ≤ 4 ⇒ every 5×5 minor of `Gt` vanishes
  have hmin0 : ∀ σ τ : Fin 5 → Fin 6, (Matrix.of fun i j => g (σ i) (τ j)).det = 0 := by
    intro σ τ
    apply det_eq_zero_of_factor _ (Matrix.of fun i k => ℓ k (σ i))
      (Matrix.of fun k j => d k * ℓ k (τ j))
    ext i j
    rw [Matrix.of_apply, hg, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => by simp only [Matrix.of_apply]; ring
  have hmin : ∀ σ τ : Fin 5 → Fin 6,
      ((Gt (g 1 2) (g 1 4) (g 3 4)).submatrix σ τ).det = 0 := by
    intro σ τ
    have hGm : (Matrix.of fun i j => g (σ i) (τ j)) =
        (Gt (g 1 2) (g 1 4) (g 3 4)).submatrix σ τ := by
      ext i j
      exact hG _ _
    rw [← hGm]
    exact hmin0 σ τ
  clear hmin0 hG a1 a2 a3 a4 a5 a6 a7 a8 a9 b1 b2 b3 b4 b5 b6 b7 b8 b9 s10 s20 s30 s40 s50 s21
    s31 s41 s51 s32 s42 s52 s43 s53 s54 E hQ hs
  generalize g 1 2 = t at hmin
  generalize g 1 4 = a at hmin
  generalize g 3 4 = b at hmin
  have m3 := hmin ![0, 1, 2, 4, 5] ![0, 1, 2, 4, 5]
  rw [minor_01245] at m3
  have m4 := hmin ![0, 1, 3, 4, 5] ![0, 1, 3, 4, 5]
  rw [minor_01345] at m4
  have m5 := hmin ![0, 2, 3, 4, 5] ![0, 2, 3, 4, 5]
  rw [minor_02345] at m5
  have m6 := hmin ![1, 2, 3, 4, 5] ![1, 2, 3, 4, 5]
  rw [minor_12345] at m6
  have m7 := hmin ![0, 1, 2, 3, 4] ![0, 1, 2, 3, 5]
  rw [minor_01234_01235] at m7
  -- `a b = 0`, since `t^2 - t + 1 > 0`
  have hpos : 0 < t ^ 2 - t + 1 := by
    rw [show t ^ 2 - t + 1 = (t - 1 / 2) ^ 2 + 3 / 4 by ring]
    positivity
  have hab : a * b = 0 := by
    have h : (a * b) * (t ^ 2 - t + 1) = 0 := by linear_combination -m7
    rcases mul_eq_zero.1 h with h | h
    · exact h
    · linarith
  -- `t = 1/2`
  have ht : 2 * t - 1 = 0 := by
    by_contra hne
    have ha : a ^ 2 - 1 = 0 :=
      (mul_eq_zero.1 (show (a ^ 2 - 1) * (2 * t - 1) = 0 by linear_combination m3 - m4)).resolve_right
        hne
    have hb : b ^ 2 - 1 = 0 :=
      (mul_eq_zero.1 (show (b ^ 2 - 1) * (2 * t - 1) = 0 by linear_combination m6 - m5)).resolve_right
        hne
    have h1 : (a * b) ^ 2 = 1 := by linear_combination b ^ 2 * ha + hb
    rw [hab] at h1
    norm_num at h1
  have ht' : t = 1 / 2 := by linarith
  subst ht'
  -- `a^2 + b^2 = 3/4` with `a b = 0`: a rational square root of 3
  rcases mul_eq_zero.1 hab with h | h
  · subst h
    exact no_rat_sqrt_three (2 * b) (by linear_combination -4 * m3)
  · subst h
    exact no_rat_sqrt_three (2 * a) (by linear_combination -4 * m6)

end Franja
