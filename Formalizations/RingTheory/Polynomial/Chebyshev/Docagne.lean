/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# d'Ocagne's identity for the Vieta–Fibonacci polynomials

Mathlib's `Polynomial.Chebyshev.S` are the rescaled Chebyshev polynomials of the second kind
(Vieta–Fibonacci polynomials), indexed by `ℤ`, with the Cassini-type identity `S_sq_add_S_sq`. This
file proves the two-index identity of which that is the case `q = p + 1`:

`S p * S (q - 1) - S q * S (p - 1) = - S (p - q - 1)`.

## Main results

* `Orbit.S_docagne`: d'Ocagne's identity.
* `Orbit.S_sq_add_S_sq_of_docagne`: Mathlib's `S_sq_add_S_sq` recovered from it.
-/

@[expose] public section

namespace Orbit

open Polynomial Polynomial.Chebyshev

variable (R : Type*) [CommRing R]

/-- **d'Ocagne's identity** for the Vieta–Fibonacci polynomials `S`. Classical. -/
public theorem S_docagne (p q : ℤ) :
    S R p * S R (q - 1) - S R q * S R (p - 1) = - S R (p - q - 1) := by
  induction q using Polynomial.Chebyshev.induct with
  | zero =>
      simp [S_neg_one]
  | one =>
      linear_combination (norm := ring_nf)
        S R p * S_zero R - S R (p - 1) * S_one R + S_sub_two R p
  | add_two q ih1 ih2 =>
      linear_combination (norm := ring_nf) X * ih1 - ih2 - S R (p - 1) * S_add_two R q
        + S R p * S_add_one R q + S_sub_two R (p - q - 1)
  | neg_add_one q ih1 ih2 =>
      linear_combination (norm := ring_nf) X * ih1 - ih2 + S R p * S_sub_one R (-(q : ℤ) - 1)
        - S R (p - 1) * S_sub_one R (-(q : ℤ)) + S_add_one R (p + q - 1)

/-- Mathlib's `S_sq_add_S_sq` is the case `q = p + 1`, recovered as a consistency check. -/
public theorem S_sq_add_S_sq_of_docagne (n : ℤ) :
    S R n ^ 2 + S R (n + 1) ^ 2 - X * S R n * S R (n + 1) = 1 := by
  have h := S_docagne R n (n + 1)
  linear_combination (norm := ring_nf) h + S R (n + 1) * S_add_one R n - S_neg_two R

end Orbit
