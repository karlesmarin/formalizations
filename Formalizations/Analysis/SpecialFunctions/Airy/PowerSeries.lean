/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

/-!
# The Airy equation for formal power series

The power-series solutions `y = Σ cₖ xᵏ` of the Airy equation `y'' = x y` satisfy
`(k + 2)(k + 1) c_{k+2} = c_{k-1}` and `c₂ = 0`, i.e. `c_{k+3} = cₖ / ((k + 2)(k + 3))` with
`c₀`, `c₁` free. This file defines these coefficients over `ℚ` and proves that the resulting power
series satisfies `d²/dX² y = X · y` in `ℚ⟦X⟧`.

## Main results

* `Airy.coeff`: the coefficients with `y(0) = c0`, `y'(0) = c1`; `Airy.f`, `Airy.g` the two
  standard solutions (`c0, c1 = 1, 0` and `0, 1`).
* `Airy.coeff_airy_ode`: `d⁄dX (d⁄dX (mk (coeff c0 c1))) = X * mk (coeff c0 c1)`.
* `Airy.Fps_airy`, `Airy.Gps_airy`: the same for the two standard solutions.

The real-analytic function, its entireness and its zeros are in
`Formalizations.Analysis.SpecialFunctions.Airy.Basic`.

## References

* NIST Digital Library of Mathematical Functions, Chapter 9 (Airy and Related Functions),
  https://dlmf.nist.gov/9.
* O. Vallée, M. Soares, *Airy Functions and Applications to Physics*, Imperial College Press (2010).
* C. Marín, *How a Falling Particle Counts Its Floors: the Airy function as a verified entire
  solution of y''=xy, its oscillation, and the quantum-bouncer spectrum, machine-checked in Lean 4*
  (2026), doi:10.5281/zenodo.20787671. Ported from `Airy.lean` of
  [karlesmarin/airy-bouncer-lean](https://github.com/karlesmarin/airy-bouncer-lean)
  (Lean v4.30.0-rc2).
-/

@[expose] public section

namespace Airy

/-- Power-series coefficients of a solution of y''=xy with y(0)=c0, y'(0)=c1. -/
def coeff (c0 c1 : ℚ) : Nat → ℚ
  | 0       => c0
  | 1       => c1
  | 2       => 0
  | (k + 3) => coeff c0 c1 k / (((k : ℚ) + 2) * ((k : ℚ) + 3))

/-- First entire solution f:  f(0)=1, f'(0)=0.  f = 1 + x³/6 + x⁶/180 + x⁹/12960 + ⋯ -/
def f (k : Nat) : ℚ := coeff 1 0 k
/-- Second entire solution g:  g(0)=0, g'(0)=1.  g = x + x⁴/12 + x⁷/504 + ⋯ -/
def g (k : Nat) : ℚ := coeff 0 1 k

open PowerSeries

/-- Definitional base case: `c₂ = 0`. -/
theorem coeff_two (c0 c1 : ℚ) : Airy.coeff c0 c1 2 = 0 := rfl

/-- Definitional recurrence: `c_{k+3} = c_k / ((k+2)(k+3))`. -/
theorem coeff_succ3 (c0 c1 : ℚ) (k : ℕ) :
    Airy.coeff c0 c1 (k + 3) = Airy.coeff c0 c1 k / (((k : ℚ) + 2) * ((k : ℚ) + 3)) := rfl

/-- The two entire solutions of `y''=xy`, as power series over ℚ. -/
noncomputable def Fps : ℚ⟦X⟧ := mk (Airy.coeff 1 0)
/-- The second standard solution of `y''=xy`, as a power series over ℚ. -/
noncomputable def Gps : ℚ⟦X⟧ := mk (Airy.coeff 0 1)

/-- **The Airy equation `y'' = x·y`, verified at the power-series level**, for the solution with
`y(0)=c0`, `y'(0)=c1`. -/
theorem coeff_airy_ode (c0 c1 : ℚ) :
    d⁄dX (d⁄dX (mk (Airy.coeff c0 c1))) = X * mk (Airy.coeff c0 c1) := by
  ext n
  rw [coeff_derivative, coeff_derivative, coeff_mk]
  rcases n with _ | m
  · simp [coeff_two, coeff_zero_X_mul]
  · have h2 : ((m : ℚ) + 2) ≠ 0 := by positivity
    have h3 : ((m : ℚ) + 3) ≠ 0 := by positivity
    rw [coeff_succ_X_mul, coeff_mk, show m + 1 + 1 + 1 = m + 3 from rfl, coeff_succ3]
    push_cast
    field_simp
    ring

theorem Fps_airy : d⁄dX (d⁄dX Fps) = X * Fps := coeff_airy_ode 1 0
theorem Gps_airy : d⁄dX (d⁄dX Gps) = X * Gps := coeff_airy_ode 0 1

/-! ### Examples: the classical series `f = 1 + x³/6 + x⁶/180 + x⁹/12960 + ⋯`,
`g = x + x⁴/12 + x⁷/504 + ⋯`. -/

example : [f 0, f 3, f 6, f 9] = [1, 1 / 6, 1 / 180, 1 / 12960] := by norm_num [f, coeff]
example : [g 1, g 4, g 7, g 10] = [1, 1 / 12, 1 / 504, 1 / 45360] := by norm_num [g, coeff]
example : f 1 = 0 ∧ f 2 = 0 ∧ g 0 = 0 ∧ g 2 = 0 := by norm_num [f, g, coeff]

end Airy
