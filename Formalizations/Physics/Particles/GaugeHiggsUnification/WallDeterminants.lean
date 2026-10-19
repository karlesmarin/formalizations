/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Tactic.Ring

/-!
# Determinant and energy identities for Higgs walls

Polynomial identities, over any commutative ring, behind the analysis of Higgs walls in
six-dimensional gauge-Higgs unification: the rank-one wall determinant, the neutral `3 × 3`
Gram determinant and its sum-of-squares decomposition, and the rationalized gap formula. They do
not formalize traces in `H¹`, the Robin boundary problem, the positivity of its spectrum or the
physical derivation of the input matrices.

## Main results

* `amplitude_circle`: `(p² − q²)² + (2pq)² = (p² + q²)²` (the parametrization of Pythagorean
  triples; Mathlib's `PythagoreanTriple` is stated over `ℤ`).
* `rank_one_wall_det`: `det [[a x², a x y], [a x y, a y² + b]] = a b x²`.
* `gap_discriminant`, `gap_rationalization`: `(r + t − z)(r + t + z) = 4rt(1 − c)` when
  `z² = (r − t)² + 4rtc`.
* `neutral_three_det`: the neutral `3 × 3` Gram determinant is `a b x² (k + a(1 − d²))`.
* `neutral_energy_decomposition`: the corresponding quadratic form is
  `a (x u + y v − d w)² + b v² + (k + a(1 − d²)) w²`.
-/

@[expose] public section

namespace GaugeHiggsUnification.WallDeterminants

variable {R : Type*} [CommRing R]

/-- The `2 × 2` determinant. -/
def det2 (a b c d : R) : R := a*d-b*c

/-- The `3 × 3` determinant, expanded along the first row. -/
def det3 (a b c d e f g h i : R) : R :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

/-- The amplitude circle. -/
theorem amplitude_circle (p q : R) :
    (p^2-q^2)^2+(2*p*q)^2=(p^2+q^2)^2 := by
  grind

/-- The rank-one wall determinant. -/
theorem rank_one_wall_det (a b x y : R) :
    det2 (a*x^2) (a*x*y) (a*x*y) (a*y^2+b)=a*b*x^2 := by
  unfold det2
  grind

/-- The discriminant of the gap. -/
theorem gap_discriminant (r t c : R) :
    (r+t)^2-((r-t)^2+4*r*t*c)=4*r*t*(1-c) := by
  grind

/-- The cross-multiplied, stable form of the gap formula; no division is involved. -/
theorem gap_rationalization (r t c z : R)
    (hz : z^2=(r-t)^2+4*r*t*c) :
    (r+t-z)*(r+t+z)=4*r*t*(1-c) := by
  grind

/-- The neutral Gram determinant `[[a x², a x y, −a d x], [a x y, a y² + b, −a d y],
[−a d x, −a d y, a + k]]`; `b` is the coefficient of the bulk field and `k` the total additional
hidden coefficient. -/
theorem neutral_three_det (a b k d x y : R) :
    det3 (a*x^2) (a*x*y) (-a*d*x)
         (a*x*y) (a*y^2+b) (-a*d*y)
         (-a*d*x) (-a*d*y) (a+k)
      = a*b*x^2*(k+a*(1-d^2)) := by
  unfold det3
  grind

/-- The neutral quadratic form as a sum of three weighted squares. -/
theorem neutral_energy_decomposition (a b k d x y u v w : R) :
    a*x^2*u^2 + (a*y^2+b)*v^2 + (a+k)*w^2
      + 2*a*x*y*u*v - 2*a*d*x*u*w - 2*a*d*y*v*w
      = a*(x*u+y*v-d*w)^2 + b*v^2 + (k+a*(1-d^2))*w^2 := by
  grind

/-- The determinant factor at the endpoint `d = 1`. -/
theorem endpoint_det_factor (a b k x : R) :
    a*b*x^2*(k+a*(1-(1:R)^2))=a*b*x^2*k := by
  grind

/-- The determinant factor at the balanced point `d = 0`. -/
theorem balanced_det_factor (a b k x : R) :
    a*b*x^2*(k+a*(1-(0:R)^2))=a*b*x^2*(k+a) := by
  grind

/-- The scalar skeleton of the energy addition. -/
theorem weighted_energy_addition (a b x y : R) :
    a*x*x+b*y*y=a*x^2+b*y^2 := by
  grind

end GaugeHiggsUnification.WallDeterminants
