/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Tactic.Ring

/-!
# Orthogonal change of variables in the biquadratic form P_H

For a square matrix H over a commutative ring, the biquadratic form P_H(x, y) = (x₀² + x₁²)(y·y) +
2x₀x₁(y·Hy) satisfies P_H(x, Dy) = P_{DᵀHD}(x, y) whenever DᵀD = 1. Hence any representation of P_H
as a sum of squares of bilinear forms transports to P_{DᵀHD} with the same number of squares, which
covers signed-graph switching D = diag(±1).

## Main results

* `BiquadraticSOS.dotProduct_mulVec_congr`: (D y) ⬝ᵥ (M (D y)) = y ⬝ᵥ ((Dᵀ * M * D) y)
* `BiquadraticSOS.P_mulVec_orthogonal`: Dᵀ * D = 1: P H x (D y) = P (Dᵀ * H * D) x y
* `BiquadraticSOS.sos_transport`: Dᵀ * D = 1 and P H = ∑ (x ⬝ᵥ B i y)²: P (Dᵀ * H * D) = ∑ (x ⬝ᵥ (B i * D) y)²
* `BiquadraticSOS.P_switching`: s i * s i = 1: P H x (diagonal s y) = P (diagonal s * H * diagonal s) x y

## References

* Mathlib: Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.one_mulVec, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_one.
* Nuestro repo (grep 20-nov de «orthogonal», «mulVec», «dotProduct_mulVec», «Dᵀ»): nada equivalente. Lo más cercano es el lema privado sim_dot de Formalizations/Combinatorics/Configuration/BruckRyserChowla.lean ((M x)·(M y) = n (x·y) si Mᵀ M = n • 1, solo sobre ℚ, sin la forma P_H ni el transporte SOS). RationalSOS/Franja.lean trata P_H concretas (rango, det), no el cambio de variables.
-/

@[expose] public section

namespace BiquadraticSOS

open Matrix

variable {R n : Type*} [CommRing R] [Fintype n]

/-- The biquadratic form `P_H(x, y) = (x₀² + x₁²) (y ⬝ᵥ y) + 2 x₀ x₁ (y ⬝ᵥ H y)`. -/
def P (H : Matrix n n R) (x : Fin 2 → R) (y : n → R) : R :=
  (x 0 ^ 2 + x 1 ^ 2) * (y ⬝ᵥ y) + 2 * x 0 * x 1 * (y ⬝ᵥ (H *ᵥ y))

/-- Congruence of a quadratic form under the substitution `y ↦ D y`. -/
theorem dotProduct_mulVec_congr (D M : Matrix n n R) (y : n → R) :
    (D *ᵥ y) ⬝ᵥ (M *ᵥ (D *ᵥ y)) = y ⬝ᵥ ((Dᵀ * M * D) *ᵥ y) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec y, vecMul_transpose]

/-- Orthogonal substitution in `P_H`: if `Dᵀ D = 1`, then `P_H(x, D y) = P_{Dᵀ H D}(x, y)`. -/
theorem P_mulVec_orthogonal [DecidableEq n] {H D : Matrix n n R} (hD : Dᵀ * D = 1)
    (x : Fin 2 → R) (y : n → R) :
    P H x (D *ᵥ y) = P (Dᵀ * H * D) x y := by
  have h1 : (D *ᵥ y) ⬝ᵥ (D *ᵥ y) = y ⬝ᵥ y := by
    have := dotProduct_mulVec_congr D 1 y
    rwa [one_mulVec, Matrix.mul_one, hD, one_mulVec] at this
  simp only [P, h1, dotProduct_mulVec_congr]

/-- Transport of sums of squares of bilinear forms under orthogonal congruence `H ↦ Dᵀ H D`;
the number of squares is unchanged. -/
theorem sos_transport [DecidableEq n] {ι : Type*} [Fintype ι] {H D : Matrix n n R}
    (hD : Dᵀ * D = 1) (B : ι → Matrix (Fin 2) n R)
    (h : ∀ x y, P H x y = ∑ i, (x ⬝ᵥ (B i *ᵥ y)) ^ 2) (x : Fin 2 → R) (y : n → R) :
    P (Dᵀ * H * D) x y = ∑ i, (x ⬝ᵥ ((B i * D) *ᵥ y)) ^ 2 := by
  rw [← P_mulVec_orthogonal hD, h]
  simp only [mulVec_mulVec]

/-- Signed-graph switching: `D = diagonal s` with `s i * s i = 1` is orthogonal. -/
theorem P_switching [DecidableEq n] (H : Matrix n n R) {s : n → R} (hs : ∀ i, s i * s i = 1)
    (x : Fin 2 → R) (y : n → R) :
    P H x (diagonal s *ᵥ y) = P (diagonal s * H * diagonal s) x y := by
  have hD : (diagonal s)ᵀ * diagonal s = 1 := by
    rw [diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext hs)
  simpa [diagonal_transpose] using P_mulVec_orthogonal hD x y

end BiquadraticSOS

end
