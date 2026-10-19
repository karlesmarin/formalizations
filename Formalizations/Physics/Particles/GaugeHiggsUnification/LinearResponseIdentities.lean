/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.Ring

/-!
# Algebraic invariants of the linear response

Exact identities over `ℚ`. The physical derivation of the encoded formulas, the positivity of
kinetic terms, anomaly cancellation and the experimental interpretation are not formalized.

## Main results

* `linear_lambda_independent`: the two-pole linear response does not depend on the quartic
  coupling.
* `correlated_kinetic_cancellation`: twice the first-order mass numerator is `−2dδ` once both
  induced entries are kept.
* `constant_contact_cancellation`: a constant contact term drops out of a first difference.
* `two_support_moment_identity`: `(a + b)(a u² + b v²) − (a u + b v)² = a b (u − v)²`.
-/

@[expose] public section

namespace GaugeHiggsUnification.LinearResponseIdentities

/-- The two-pole linear response `r + c₁²/(A − x) + c₂²/(B − x)`; the quartic coupling is an
unused argument. -/
def linearResponse (A B c1 c2 r _lambda x : ℚ) : ℚ :=
  r + c1*c1/(A-x) + c2*c2/(B-x)

/-- The linear response is independent of the quartic coupling. -/
theorem linear_lambda_independent (A B c1 c2 r l1 l2 x : ℚ) :
    linearResponse A B c1 c2 r l1 x = linearResponse A B c1 c2 r l2 x := by
  rfl

/-- Twice the first-order mass numerator, with both induced entries. -/
theorem correlated_kinetic_cancellation (M d delta c : ℚ) :
    M*(-delta*d*c) - d*(2*delta-delta*M*c) = -2*d*delta := by
  grind

/-- A constant contact term disappears from a first difference. -/
theorem constant_contact_cancellation (f1 f2 r : ℚ) :
    (f2+r)-(f1+r) = f2-f1 := by
  grind

/-- The two-support moment identity; positivity needs in addition nonnegative weights. -/
theorem two_support_moment_identity (a b u v : ℚ) :
    (a+b)*(a*u^2+b*v^2)-(a*u+b*v)^2 = a*b*(u-v)^2 := by
  grind

end GaugeHiggsUnification.LinearResponseIdentities
