/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Tactic.Ring

/-!
# Periodic counts under two equal torus twists in the hidden `(1, 5, 4)` basis

Integer arithmetic in the basis `(1, 5, 4)` of hidden-sector multiplicities `(a, b, c)`:
dimension `a + 5b + 4c`, central action `a + 5b − 4c`, periodic count `a + 5b`. The central
signs, the two equal torus twists and the Fourier interpretation are inputs; nothing is stated
about the full orbifold or the Standard Model.

## Main results

* `projected_character`: `2 · periodic = dim + center`.
* `two_equal_twists`: `4 · periodic = 2 dim + 2 center`.
* `candidate_periodic_counts`: the periodic counts `5` and `13` of the two candidate contents.
* `periodic_resolves_integer_kernel`: dimension, second moment and periodic count together
  determine the multiplicities (augmented determinant `−16`).
-/

@[expose] public section

namespace GaugeHiggsUnification.TorusTwistBasis

/-- The dimension of the content `(a, b, c)`. -/
def dim (a b c : Int) : Int := a + 5*b + 4*c

/-- The central action of the content `(a, b, c)`. -/
def center (a b c : Int) : Int := a + 5*b - 4*c

/-- The periodic count of the content `(a, b, c)`. -/
def periodic (a b : Int) : Int := a + 5*b

/-- The projected character: twice the periodic count is dimension plus central action. -/
theorem projected_character (a b c : Int) :
    2 * periodic a b = dim a b c + center a b c := by
  unfold periodic dim center
  omega

/-- The same with two equal twists. -/
theorem two_equal_twists (a b c : Int) :
    4 * periodic a b = 2 * dim a b c + 2 * center a b c := by
  unfold periodic dim center
  omega

/-- The periodic counts of the two candidate contents. -/
theorem candidate_periodic_counts : periodic 0 1 = 5 ∧ periodic 3 2 = 13 := by decide

/-- The determinant of the system (dimension, second moment, periodic count). -/
theorem augmented_determinant :
    (1 : Int)*(4*0-2*5)-5*(0*0-2*1)+4*(0*5-4*1) = -16 := by decide

/-- Dimension, second moment and periodic count have trivial common integer kernel. -/
theorem periodic_resolves_integer_kernel (a b c : Int)
    (hd : a+5*b+4*c=0) (h2 : 4*b+2*c=0) (hp : a+5*b=0) :
    a=0 ∧ b=0 ∧ c=0 := by omega

end GaugeHiggsUnification.TorusTwistBasis
