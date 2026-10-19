/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Tactic.Ring

/-!
# Polynomial identities of the alignment audit of a restricted potential

Polynomial identities, over any commutative ring, used in the audit of the alignment of a
restricted Wilson-line potential in six-dimensional gauge-Higgs unification. They are the
polynomial core of that audit only: no partial differential equation, positivity statement or
physical derivation of the coefficients is formalized.

## Main results

* `quartic_family`: `9p⁴ + 2p²q² + 9q⁴ = 5(p² + q²)² + 4(p² − q²)²`.
* `charged_descent_numerator`, `same_hidden_descent_numerator`: the descent numerators
  `4e²(e² − 8)` and `−16e²`.
* `charged_angle_polynomial`: `5(1 − t)² + 9t² − 6t(1 − t) = 5 − 16t + 20t²`.
* `opposed_angular_curvatures`, `corner_uniform_weight`: two linear cancellations.
-/

@[expose] public section

namespace GaugeHiggsUnification.AlignmentPolynomials

variable {R : Type*} [CommRing R]

/-- The quartic family as a positive combination of `(p² + q²)²` and `(p² − q²)²`. -/
theorem quartic_family (p q : R) :
    9*p^4+2*p^2*q^2+9*q^4
      =5*(p^2+q^2)^2+4*(p^2-q^2)^2 := by grind

/-- The charged descent numerator. -/
theorem charged_descent_numerator (e : R) :
    (20-12*e^2+9*e^4)-5*(e^2+2)^2=4*e^2*(e^2-8) := by grind

/-- The descent numerator with the same hidden charge. -/
theorem same_hidden_descent_numerator (e : R) :
    (5-6*e^2+5*e^4)-5*(1+e^2)^2 = -16*e^2 := by grind

/-- The charged angle polynomial. -/
theorem charged_angle_polynomial (t : R) :
    5*(1-t)^2+9*t^2-6*t*(1-t)=5-16*t+20*t^2 := by grind

/-- Opposed angular curvatures cancel. -/
theorem opposed_angular_curvatures (k rho : R) :
    8*k*rho^2+(-8*k*rho^2)=0 := by grind

/-- The corner term with a uniform weight. -/
theorem corner_uniform_weight (k eta L A iv ih : R) :
    k*L*A*(iv+ih)-eta*A*iv=A*((k*L-eta)*iv+k*L*ih) := by grind

end GaugeHiggsUnification.AlignmentPolynomials
