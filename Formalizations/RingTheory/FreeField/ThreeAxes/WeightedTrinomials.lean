/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NoncommRing

/-!
# Weighted trinomials for the three-axes problem

Finite identities behind the weighted-trinomial construction: a hidden commutator in `GL₂`, a
curve of nilpotent `2×2` matrices realising the weighted trinomials, and the Schur complement of
the rank-two block matrix.

## Main results

* `sq_eq_trace_smul_sub_det_smul`: Cayley–Hamilton for `2×2` matrices, `X * X = tr X • X − det X • 1`.
* `hidden_commutator`: if `tr X = tr Y = −1`, `T = 1 + X + Y` satisfies `T * T = 0` and `X`, `Y`
  are invertible with `a = det X`, `b = det Y`, then
  `(X Y) (Y X) (X Y)⁻¹ (Y X)⁻¹ = 1 + (a⁻¹ − b⁻¹) • T`; the commutator is unipotent.
* `weighted_trinomial`: for any three matrices `n 0, n 1, n 2`, with
  `T i = (n i − z n (i+1) + z² n (i+2)) / (1 + z³)` and `X i = −1/(1+z) • 1 + T i`, one has
  `1 + X i + z X (i+1) = n i`. `weighted_curve`: the instance `N i = !![i t², −t; i² t³, −i t²]`;
  `N_sq`: `N i * N i = 0`.
* `schur_r2`: over any ring, with `Q = A + 2B` and `S = A + B − C Q⁻¹ C` units, the block matrix
  `!![A + B, C; C, A + 2B]` has right inverse
  `!![S⁻¹, −S⁻¹ C Q⁻¹; −Q⁻¹ C S⁻¹, Q⁻¹ + Q⁻¹ C S⁻¹ C Q⁻¹]`; in particular its `(1,1)` entry is
  `S⁻¹`.
-/

@[expose] public section

namespace ThreeAxes.WeightedTrinomials

open Matrix

/-! ### The hidden commutator -/

theorem sq_eq_trace_smul_sub_det_smul {R : Type*} [CommRing R] (X : Matrix (Fin 2) (Fin 2) R) :
    X * X = X.trace • X - X.det • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

section Hidden

variable {K : Type*} [Field K]

theorem hidden_commutator (X Y : Matrix (Fin 2) (Fin 2) K) (hX : X.trace = -1) (hY : Y.trace = -1)
    (hT : (1 + X + Y) * (1 + X + Y) = 0) (ha : X.det ≠ 0) (hb : Y.det ≠ 0) :
    (X * Y) * (Y * X) * (X * Y)⁻¹ * (Y * X)⁻¹ =
      1 + (X.det⁻¹ - Y.det⁻¹) • (1 + X + Y) := by
  set a := X.det with ha'
  set b := Y.det with hb'
  set T := 1 + X + Y with hTdef
  have hXX : X * X = -X - a • 1 := by
    rw [sq_eq_trace_smul_sub_det_smul, hX]; module
  have hYY : Y * Y = -Y - b • 1 := by
    rw [sq_eq_trace_smul_sub_det_smul, hY]; module
  have hYT : Y = T - 1 - X := by rw [hTdef]; abel
  -- `T X + X T = (b − a) • 1 − T`
  have hS : T * X + X * T = (b - a) • 1 - T := by
    have h := hYY
    rw [hYT] at h
    simp only [sub_mul, mul_sub, mul_one, one_mul, hT, hXX] at h
    linear_combination (norm := module) -h
  -- `T X T = (b − a) • T`
  have hTXT : T * X * T = (b - a) • T := by
    have h := congrArg (T * ·) hS
    simp only [mul_add, mul_sub, mul_smul_comm, mul_one, ← mul_assoc, hT, zero_mul] at h
    linear_combination (norm := module) h
  have hA : X * Y = a • 1 + X * T := by
    rw [hYT]; simp only [mul_sub, mul_one, hXX]; module
  have hB : Y * X = a • 1 + T * X := by
    rw [hYT]; simp only [sub_mul, one_mul, hXX]; module
  have hTA : T * (X * Y) = b • T := by
    rw [hA, mul_add, mul_smul_comm, mul_one, ← mul_assoc, hTXT]; module
  have hTB : T * (Y * X) = a • T := by
    rw [hB, mul_add, mul_smul_comm, mul_one, ← mul_assoc, hT, zero_mul, add_zero]
  have hcomm : (X * Y) * (Y * X) = (Y * X) * (X * Y) + (b - a) • T := by
    rw [hA, hB]
    have e1 : X * T * (T * X) = 0 := by rw [mul_assoc, ← mul_assoc T, hT, zero_mul, mul_zero]
    have e2 : T * X * (X * T) = -((b - a) • T) - a • (T * T) := by
      rw [mul_assoc, ← mul_assoc X, hXX]
      simp only [sub_mul, mul_sub, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, one_mul,
        ← mul_assoc, hTXT]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, e1, hT] at e2 ⊢
    rw [e2]
    module
  have hdetA : IsUnit (X * Y).det := by
    rw [det_mul]; exact (ha.isUnit.mul hb.isUnit)
  have hdetB : IsUnit (Y * X).det := by
    rw [det_mul]; exact (hb.isUnit.mul ha.isUnit)
  have hTAinv : T * (X * Y)⁻¹ = b⁻¹ • T := by
    have h : T * (X * Y) * (X * Y)⁻¹ = (b • T) * (X * Y)⁻¹ := by rw [hTA]
    rw [mul_assoc, mul_nonsing_inv _ hdetA, mul_one, smul_mul_assoc] at h
    calc T * (X * Y)⁻¹ = b⁻¹ • (b • (T * (X * Y)⁻¹)) := by
          rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
      _ = b⁻¹ • T := by rw [← h]
  have hTBinv : T * (Y * X)⁻¹ = a⁻¹ • T := by
    have h : T * (Y * X) * (Y * X)⁻¹ = (a • T) * (Y * X)⁻¹ := by rw [hTB]
    rw [mul_assoc, mul_nonsing_inv _ hdetB, mul_one, smul_mul_assoc] at h
    calc T * (Y * X)⁻¹ = a⁻¹ • (a • (T * (Y * X)⁻¹)) := by
          rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
      _ = a⁻¹ • T := by rw [← h]
  rw [hcomm, add_mul, add_mul, mul_assoc (Y * X), mul_nonsing_inv _ hdetA, mul_one,
    mul_nonsing_inv _ hdetB, smul_mul_assoc, smul_mul_assoc, hTAinv, smul_mul_assoc, hTBinv,
    smul_smul, smul_smul]
  congr 2
  field_simp

end Hidden

/-! ### The weighted curve -/

section Curve

variable {K : Type*} [Field K]

/-- The weighted trinomial built from three matrices `n 0, n 1, n 2`. -/
noncomputable def trinomial (z : K) (n : Fin 3 → Matrix (Fin 2) (Fin 2) K) (i : Fin 3) :
    Matrix (Fin 2) (Fin 2) K :=
  (1 + z ^ 3)⁻¹ • (n i - z • n (i + 1) + z ^ 2 • n (i + 2))

/-- `X i = λ • 1 + T i` with `λ = −1/(1+z)`. -/
noncomputable def curvePoint (z : K) (n : Fin 3 → Matrix (Fin 2) (Fin 2) K) (i : Fin 3) :
    Matrix (Fin 2) (Fin 2) K :=
  (-(1 + z)⁻¹) • 1 + trinomial z n i

theorem weighted_trinomial (z : K) (hz : 1 + z ≠ 0) (hz3 : 1 + z ^ 3 ≠ 0)
    (n : Fin 3 → Matrix (Fin 2) (Fin 2) K) (i : Fin 3) :
    1 + curvePoint z n i + z • curvePoint z n (i + 1) = n i := by
  have h1 : i + 1 + 1 = i + 2 := by fin_cases i <;> rfl
  have h2 : i + 1 + 2 = i := by fin_cases i <;> rfl
  simp only [curvePoint, trinomial, h1, h2]
  match_scalars <;> field_simp <;> ring

/-- The nilpotent curve `N i = !![i t², −t; i² t³, −i t²]`. -/
def N (t : K) (i : Fin 3) : Matrix (Fin 2) (Fin 2) K :=
  !![(i : K) * t ^ 2, -t; (i : K) ^ 2 * t ^ 3, -((i : K) * t ^ 2)]

theorem N_sq (t : K) (i : Fin 3) : N t i * N t i = 0 := by
  ext j k
  fin_cases j <;> fin_cases k <;> simp [N, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem weighted_curve (t z : K) (hz : 1 + z ≠ 0) (hz3 : 1 + z ^ 3 ≠ 0) (i : Fin 3) :
    1 + curvePoint z (N t) i + z • curvePoint z (N t) (i + 1) = N t i :=
  weighted_trinomial z hz hz3 (N t) i

end Curve

/-! ### The Schur complement for `r = 2` -/

theorem schur_r2 {R : Type*} [Ring R] (A B C : R) (Q S : Rˣ) (hQ : (Q : R) = A + 2 * B)
    (hS : (S : R) = A + B - C * ↑Q⁻¹ * C) :
    !![A + B, C; C, A + 2 * B] *
        !![(↑S⁻¹ : R), -(↑S⁻¹ * C * ↑Q⁻¹);
          -(↑Q⁻¹ * C * ↑S⁻¹), ↑Q⁻¹ + ↑Q⁻¹ * C * ↑S⁻¹ * C * ↑Q⁻¹] = 1 := by
  have hAB : A + B = S + C * ↑Q⁻¹ * C := by rw [hS]; abel
  rw [← hQ, hAB]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, add_mul, mul_add, mul_assoc]

/-- The `(1,1)` entry of the inverse of the block matrix is the inverse Schur complement. -/
theorem schur_r2_col {R : Type*} [Ring R] (A B C : R) (Q S : Rˣ) (hQ : (Q : R) = A + 2 * B)
    (hS : (S : R) = A + B - C * ↑Q⁻¹ * C) :
    (A + B) * ↑S⁻¹ + C * (-(↑Q⁻¹ * C * ↑S⁻¹)) = 1 ∧
      C * ↑S⁻¹ + (A + 2 * B) * (-(↑Q⁻¹ * C * ↑S⁻¹)) = 0 := by
  have h := congrFun (congrFun (schur_r2 A B C Q S hQ hS) 0)
  refine ⟨by simpa [Matrix.mul_apply, Fin.sum_univ_two] using h 0, ?_⟩
  have h' := congrFun (congrFun (schur_r2 A B C Q S hQ hS) 1) 0
  simpa [Matrix.mul_apply, Fin.sum_univ_two] using h'

end ThreeAxes.WeightedTrinomials
