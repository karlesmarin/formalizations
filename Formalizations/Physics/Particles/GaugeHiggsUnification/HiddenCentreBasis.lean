/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Tactic.Ring

/-!
# Central action in the hidden `(1, 5, 4)` basis

Finite integer arithmetic in the basis `(1, 5, 4)` of hidden-sector multiplicities `(a, b, c)`:
dimension `a + 5b + 4c`, central action `a + 5b − 4c`. The central actions assigned to the Lie
representations are input data; no Wilson loop, topology or anomaly cancellation is formalized.

## Main results

* `center_original`, `center_alternative`, `center_jump`: the central actions `−3` and `13` of
  the two candidate contents, which differ by `16`.
* `center_resolves_integer_kernel`: dimension, second moment and central action together
  determine the multiplicities (augmented determinant `−32`).
* `simultaneous_central_descent`: both central signs are trivial iff both markers are trivial.
-/

@[expose] public section

namespace GaugeHiggsUnification.HiddenCentreBasis

/-- The central action of the content `(a, b, c)`. -/
def center (a b c : Int) : Int := a + 5*b - 4*c

/-- The central action of the original content. -/
theorem center_original : center 0 1 2 = -3 := by decide

/-- The central action of the alternative content. -/
theorem center_alternative : center 3 2 0 = 13 := by decide

/-- The two central actions differ by `16`. -/
theorem center_jump : center 3 2 0 - center 0 1 2 = 16 := by decide

/-- The determinant of the system (dimension, second moment, central action). -/
theorem center_augmented_determinant :
    (1 : Int)*(4*(-4)-2*5)-5*(0*(-4)-2*1)+4*(0*5-4*1) = -32 := by decide

/-- Dimension, second moment and central action have trivial common integer kernel. -/
theorem center_resolves_integer_kernel (a b c : Int)
    (hd : a+5*b+4*c=0) (h2 : 4*b+2*c=0) (hz : a+5*b-4*c=0) :
    a=0 ∧ b=0 ∧ c=0 := by omega

/-- With `a`, `b` marking nontrivial central elements of `Spin(11)` and `USp(4)`, the sign on
`(32, 5)` is `a` and on `(32, 4)` it is `a xor b`; both vanish iff `a` and `b` do. -/
theorem simultaneous_central_descent :
    ∀ a b : Bool, (a = false ∧ Bool.xor a b = false) ↔ (a = false ∧ b = false) := by decide

end GaugeHiggsUnification.HiddenCentreBasis
