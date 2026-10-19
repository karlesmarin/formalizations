/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.Ring

/-!
# Exact algebra of the expansion of the effective potential

Identities over `ℚ` used in the expansion of the Wilson-line effective potential in `h / f_H`.
`r` stands for `1 / f_H` in the coefficient convention, and `a, b, c, d` for the normalized
derivatives `D'/D, …, D''''/D`. Real differentiation, Taylor remainders, Bessel integrals and the
physics are outside these statements.

## Main results

* `canonical_quartic`: the coefficients of `h²`, `h³`, `h⁴` after the rescaling `h ↦ h r`.
* `log_third_recurrence`, `log_fourth_recurrence`: the third and fourth logarithmic derivatives
  `c − 3ab + 2a³` and `d − 4ac − 3b² + 12a²b − 6a⁴`.
* `normalization_null_column`: a null column of the two-bin normalization Jacobian.
* `covariance_pullback_two`: the pullback of a `2 × 2` covariance form.
* `gram_minor_two`: `(a² + b²)(c² + d²) − (ac + bd)² = (ad − bc)²` (Lagrange's identity for two
  terms, a rearrangement of Mathlib's `sq_add_sq_mul_sq_add_sq`).
* `covariance_unit_minor`: the `2 × 2` minor after rescaling by `sᵢ, sⱼ`.
-/

@[expose] public section

namespace GaugeHiggsUnification.EffectivePotentialAlgebra

/-- The quartic Taylor polynomial in `h r`, written in powers of `h`. -/
theorem canonical_quartic (v2 v3 v4 h r : ℚ) :
    v2*(h*r)^2/2 + v3*(h*r)^3/6 + v4*(h*r)^4/24 =
    (v2*r^2)/2*h^2 + (v3*r^3/6)*h^3 + (v4*r^4/24)*h^4 := by
  grind

/-- The mass coefficient. -/
theorem mass_coefficient (v2 r : ℚ) :
    2*(v2*r^2/2) = v2*r^2 := by grind

/-- The numerator of the second logarithmic derivative, with `D r = 1`. -/
theorem log_second_numerator (D u v r : ℚ) (hr : D*r=1) :
    (v*D-u^2)*r^2 = v*r-(u*r)^2 := by grind

/-- The recurrence for the third logarithmic derivative. -/
theorem log_third_recurrence (a b c : ℚ) :
    (c-a*b)-2*a*(b-a^2) = c-3*a*b+2*a^3 := by grind

/-- The recurrence for the fourth logarithmic derivative. -/
theorem log_fourth_recurrence (a b c d : ℚ) :
    (d-a*c)-3*((b-a^2)*b+a*(c-a*b))+6*a^2*(b-a^2) =
    d-4*a*c-3*b^2+12*a^2*b-6*a^4 := by grind

/-- A constant offset of the vacuum cancels. -/
theorem vacuum_offset_cancels (v v0 c : ℚ) :
    (v+c)-(v0+c)=v-v0 := by grind

/-- The numerator `T² J` for two bins, `T = w₀ x₀ + w₁ x₁`, has a null column. -/
theorem normalization_null_column (w0 w1 x0 x1 : ℚ) :
    w0*((w0*x0+w1*x1)-x0*w0)+w1*(-x1*w0)=0 := by grind

/-- The pullback of a `2 × 2` covariance form. -/
theorem covariance_pullback_two (a b c u v p q : ℚ) :
    a*(u*p+v*q)^2 + 2*b*(u*p+v*q)*(p-q) + c*(p-q)^2 =
    (a*u^2+2*b*u+c)*p^2 +
    2*(a*u*v+b*(v-u)-c)*p*q + (a*v^2-2*b*v+c)*q^2 := by grind

/-- The `2 × 2` Gram minor. -/
theorem gram_minor_two (a b c d : ℚ) :
    (a^2+b^2)*(c^2+d^2)-(a*c+b*d)^2=(a*d-b*c)^2 := by grind

/-- The `2 × 2` covariance minor after rescaling. -/
theorem covariance_unit_minor (a b c si sj : ℚ) :
    (si^2*a)*(sj^2*c)-(si*sj*b)^2 = (si*sj)^2*(a*c-b^2) := by grind

end GaugeHiggsUnification.EffectivePotentialAlgebra
