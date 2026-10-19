/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The integral of `log x / x`

`(log x)² / 2` is an antiderivative of `log x / x` on `(0, ∞)`, so
`∫₁ᴺ log x / x dx = (log N)² / 2` for `N ≥ 1`.

This is the integral behind the corrected heat-capacity coefficient `(log N)² / 12` at the Hagedorn
point (see `Formalizations.Analysis.TransformerAttention.HeatCapacity`).

## Main results

* `Real.hasDerivAt_log_sq_div_two`: `d/dx [(log x)² / 2] = log x / x` for `x > 0`.
* `integral_log_div_self`: `∫ x in 1..N, log x / x = (log N)² / 2` for `1 ≤ N`.

## References

* C. Marín, *Predicting How Transformers Attend* (2026), §5.2 and its erratum, Zenodo 19826343.
  Ported from `Taf/CvHagedornCorrection.lean` of
  [karlesmarin/lean-taf](https://github.com/karlesmarin/lean-taf) (Lean v4.30.0-rc2).

## Related

Mathlib has `integral_log`, `integral_inv` and `integral_inv_div_log` in
`Mathlib.Analysis.SpecialFunctions.Integrals.Basic`, but not this integral, neither at the pinned
commit nor in current Mathlib (checked with Loogle, LeanSearch and GitHub code search, October 2026).
-/

@[expose] public section

open Set

/-- `d/dx [(log x)² / 2] = log x / x` for `x > 0`. -/
theorem Real.hasDerivAt_log_sq_div_two {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => (Real.log y) ^ 2 / 2) (Real.log x / x) x := by
  have h1 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log (ne_of_gt hx)
  have h2 : HasDerivAt (fun y => (Real.log y) ^ 2) (2 * Real.log x * x⁻¹) x := by
    convert h1.fun_mul h1 using 1
    · funext y; ring
    · ring
  have h3 := h2.div_const 2
  convert h3 using 1
  field_simp

/-- `∫₁ᴺ log x / x dx = (log N)² / 2` for `N ≥ 1`. -/
theorem integral_log_div_self (N : ℝ) (hN : 1 ≤ N) :
    ∫ x in (1 : ℝ)..N, Real.log x / x = (Real.log N) ^ 2 / 2 := by
  have hpos : ∀ x ∈ Set.uIcc (1 : ℝ) N, 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le hN] at hx
    linarith [hx.1]
  have hderiv : ∀ x ∈ Set.uIcc (1 : ℝ) N,
      HasDerivAt (fun y => (Real.log y) ^ 2 / 2) (Real.log x / x) x :=
    fun x hx => Real.hasDerivAt_log_sq_div_two (hpos x hx)
  have hcont : ContinuousOn (fun x => Real.log x / x) (Set.uIcc (1 : ℝ) N) := by
    refine ContinuousOn.div₀ (Real.continuousOn_log.mono fun x hx => ?_) continuousOn_id ?_
    · exact ne_of_gt (hpos x hx)
    · intro x hx; exact ne_of_gt (hpos x hx)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp [Real.log_one]
