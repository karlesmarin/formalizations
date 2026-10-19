/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# The square of an Airy solution

For a solution `u` of the shifted Airy equation `u'' = (x − E) u` (the bouncer eigenstate is
`u(x) = Ai(x − E)`), the square `w = u²` satisfies the third-order linear equation
`w''' = 4 (x − E) w' + 2 w`. This identity underlies Crandall's sum rules for the Airy zeros.

## Main results

* `Airy.airySq_ode`: the three `HasDerivAt` links `w → w' → w'' → w'''`, with
  `w' = 2 u u'`, `w'' = 2 u'² + 2 (x − E) u²` and `w''' = 4 (x − E) w' + 2 w`.

## References

* R. E. Crandall, *On the quantum zeta function*, J. Phys. A: Math. Gen. 29 (1996) 6795–6816.
* O. Vallée, M. Soares, *Airy Functions and Applications to Physics*, Imperial College Press (2010).
-/

@[expose] public section

namespace Airy

/-- **The third-order ODE for the square of an Airy solution.**
If `u' ` is the derivative of `u` and `u'' = (x-E)·u` (the shifted Airy equation), then with
`w = u²`, `w' = 2 u u'`, `w'' = 2 u'² + 2(x-E)u²`, one has `w''' = 4(x-E)w' + 2w`. Returned as the
three `HasDerivAt` links `w → w' → w'' → w'''`. -/
theorem airySq_ode {u u' : ℝ → ℝ} {E : ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu2 : ∀ x, HasDerivAt u' ((x - E) * u x) x) (x : ℝ) :
    HasDerivAt (fun y => u y * u y) (u' x * u x + u x * u' x) x ∧
    HasDerivAt (fun y => 2 * u y * u' y)
      (2 * (u' x * u' x) + 2 * ((x - E) * (u x * u x))) x ∧
    HasDerivAt (fun y => 2 * (u' y * u' y) + 2 * ((y - E) * (u y * u y)))
      (4 * (x - E) * (2 * u x * u' x) + 2 * (u x * u x)) x := by
  have hid : HasDerivAt (fun y => y - E) (1 : ℝ) x := (hasDerivAt_id x).sub_const E
  refine ⟨(hu x).mul (hu x), ?_, ?_⟩
  · -- w'' = 2 u'² + 2(x-E)u²
    convert ((hu x).const_mul (2 : ℝ)).mul (hu2 x) using 1; ring
  · -- w''' = 4(x-E)w' + 2w
    have h1 := ((hu2 x).mul (hu2 x)).const_mul (2 : ℝ)
    have h2 := (hid.mul ((hu x).mul (hu x))).const_mul (2 : ℝ)
    convert h1.add h2 using 1
    simp only [Pi.mul_apply]; ring

end Airy
