/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Tactic.Ring

/-!
# A quaternion curve with scalar squares

In the quaternions `ℍ[R]` over a commutative ring, the three pure quaternions `ξ = t i`,
`η = t j`, `ζ = t k` square to the scalar `−t²` and anticommute pairwise.

## Main results

* `xi_mul_self`, `eta_mul_self`, `zeta_mul_self`: `ξ² = η² = ζ² = −t²`.
* `xi_mul_eta_add`, `eta_mul_zeta_add`, `zeta_mul_xi_add`: `ξ η + η ξ = 0` and the other two pairs.
-/

@[expose] public section

namespace ThreeAxes.QuaternionCurve

open Quaternion

variable {R : Type*} [CommRing R]

/-- `ξ = t i`. -/
def xi (t : R) : ℍ[R] := ⟨0, t, 0, 0⟩

/-- `η = t j`. -/
def eta (t : R) : ℍ[R] := ⟨0, 0, t, 0⟩

/-- `ζ = t k`. -/
def zeta (t : R) : ℍ[R] := ⟨0, 0, 0, t⟩

theorem xi_mul_self (t : R) : xi t * xi t = ((-t ^ 2 : R) : ℍ[R]) := by
  ext <;> simp [xi, -Quaternion.coe_pow, -Quaternion.coe_neg]
  ring

theorem eta_mul_self (t : R) : eta t * eta t = ((-t ^ 2 : R) : ℍ[R]) := by
  ext <;> simp [eta, -Quaternion.coe_pow, -Quaternion.coe_neg]
  ring

theorem zeta_mul_self (t : R) : zeta t * zeta t = ((-t ^ 2 : R) : ℍ[R]) := by
  ext <;> simp [zeta, -Quaternion.coe_pow, -Quaternion.coe_neg]
  ring

theorem xi_mul_eta_add (t : R) : xi t * eta t + eta t * xi t = 0 := by
  ext <;> simp [xi, eta]

theorem eta_mul_zeta_add (t : R) : eta t * zeta t + zeta t * eta t = 0 := by
  ext <;> simp [eta, zeta]

theorem zeta_mul_xi_add (t : R) : zeta t * xi t + xi t * zeta t = 0 := by
  ext <;> simp [zeta, xi]

end ThreeAxes.QuaternionCurve
