/-
Author: Carles Marín (with Claude as AI assistant).

Continuantes: Euler's continuant in a (noncommutative) ring and the absorption
identities behind the DGH strata (notas: a⁻¹ + r + b⁻¹ = a⁻¹ K(a,r,b) b⁻¹).
(1) `K` with K [] = 1, K [x] = x, K (xs ++ [y, z]) = K (xs ++ [y]) * z + K xs;
    K [a, r, b] = a*r*b + a + b.
(2) absorption for units a, b; (3) two-sided reduction for units w₁, w₂;
(4) harmonic denominator in a field; (5) the continuant is the (0,0) entry of
E a * E r * E b in M₂(R), E x = !![x, 1; 1, 0] (Möbius / GL₂ picture).
-/
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Continuantes

section Ring
variable {R : Type*} [Ring R]

/-- Continuant on the REVERSED list: `Kr (xₙ :: xₙ₋₁ :: t) = Kr (xₙ₋₁ :: t) * xₙ + Kr t`. -/
def Kr : List R → R
  | [] => 1
  | [x] => x
  | x :: y :: t => Kr (y :: t) * x + Kr t

/-- Euler's continuant `K(x₁, …, xₙ)`. -/
def K (l : List R) : R := Kr l.reverse

@[simp] theorem K_nil : K ([] : List R) = 1 := rfl
@[simp] theorem K_singleton (x : R) : K [x] = x := rfl

/-- Recursion `K(x₁..xₙ y z) = K(x₁..xₙ y) * z + K(x₁..xₙ)`. -/
theorem K_append_two (xs : List R) (y z : R) :
    K (xs ++ [y, z]) = K (xs ++ [y]) * z + K xs := by
  simp [K, Kr, List.reverse_append]

/-- (1) `K [a, r, b] = a*r*b + a + b`. -/
theorem K_three (a r b : R) : K [a, r, b] = a * r * b + a + b := by
  simp [K, Kr]; noncomm_ring

/-- (2) Absorption: `a⁻¹ + r + b⁻¹ = a⁻¹ (a r b + a + b) b⁻¹` for units `a, b`. -/
theorem absorb (a b : Rˣ) (r : R) :
    (↑a⁻¹ : R) + r + ↑b⁻¹ = ↑a⁻¹ * (↑a * r * ↑b + ↑a + ↑b) * ↑b⁻¹ := by
  simp only [mul_add, add_mul, ← mul_assoc, Units.inv_mul, one_mul]
  simp only [mul_assoc, Units.mul_inv, mul_one]
  abel

/-- (2') Absorption written with the continuant. -/
theorem absorb_K (a b : Rˣ) (r : R) :
    (↑a⁻¹ : R) + r + ↑b⁻¹ = ↑a⁻¹ * K [(↑a : R), r, ↑b] * ↑b⁻¹ := by
  rw [K_three]; exact absorb a b r

/-- (3) Two-sided reduction: `p + w₁⁻¹ + w₂⁻¹ + s = w₁⁻¹ (w₁ + w₂ + w₁ (p + s) w₂) w₂⁻¹`. -/
theorem reduce_bilateral (w₁ w₂ : Rˣ) (p s : R) :
    p + ↑w₁⁻¹ + ↑w₂⁻¹ + s = ↑w₁⁻¹ * (↑w₁ + ↑w₂ + ↑w₁ * (p + s) * ↑w₂) * ↑w₂⁻¹ := by
  simp only [mul_add, add_mul, ← mul_assoc, Units.inv_mul, one_mul]
  simp only [mul_assoc, Units.mul_inv, mul_one]
  abel

/-- The GL₂ generator `E x = !![x, 1; 1, 0]`. -/
def E (x : R) : Matrix (Fin 2) (Fin 2) R := !![x, 1; 1, 0]

/-- (5) `E a * E r * E b = !![a r b + a + b, a r + 1; r b + 1, r]`. -/
theorem E_mul_three (a r b : R) :
    E a * E r * E b = !![a * r * b + a + b, a * r + 1; r * b + 1, r] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals noncomm_ring

theorem E_mul_three_00 (a r b : R) : (E a * E r * E b) 0 0 = K [a, r, b] := by
  rw [E_mul_three, K_three]; rfl
theorem E_mul_three_01 (a r b : R) : (E a * E r * E b) 0 1 = a * r + 1 := by
  rw [E_mul_three]; rfl
theorem E_mul_three_10 (a r b : R) : (E a * E r * E b) 1 0 = r * b + 1 := by
  rw [E_mul_three]; rfl
theorem E_mul_three_11 (a r b : R) : (E a * E r * E b) 1 1 = r := by
  rw [E_mul_three]; rfl

end Ring

/-- (4) Harmonic denominator (commutative): `(1/a + 1/b + 1/c)⁻¹ = abc/(ab+bc+ca)`. -/
theorem harmonic_three {F : Type*} [Field F] (a b c : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (_h : a * b + b * c + c * a ≠ 0) :
    (1 / a + 1 / b + 1 / c)⁻¹ = a * b * c / (a * b + b * c + c * a) := by
  have e : 1 / a + 1 / b + 1 / c = (a * b + b * c + c * a) / (a * b * c) := by
    field_simp; ring
  rw [e, inv_div]

end Continuantes

#print axioms Continuantes.K_append_two
#print axioms Continuantes.K_three
#print axioms Continuantes.absorb
#print axioms Continuantes.absorb_K
#print axioms Continuantes.reduce_bilateral
#print axioms Continuantes.E_mul_three
#print axioms Continuantes.E_mul_three_00
#print axioms Continuantes.E_mul_three_01
#print axioms Continuantes.E_mul_three_10
#print axioms Continuantes.E_mul_three_11
#print axioms Continuantes.harmonic_three
