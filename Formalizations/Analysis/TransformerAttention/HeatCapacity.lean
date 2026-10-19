/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The heat-capacity coefficient at the Hagedorn point (erratum)

Theorem 5.2 of the paper states `C_V(γ = 1, N) = (log N)²/4`; the erratum corrects it to
`(log N)²/12` (a factor `3`). This file checks the algebraic chain of both derivations of the
corrected coefficient, with `L = log N`. The asymptotic statement (`→` as `N → ∞`, which needs
Euler–Maclaurin bounds for the harmonic sums) is not formalized. The integral
`∫₁ᴺ log x / x dx = (log N)²/2` behind it is `integral_log_div_self`
(`Formalizations.Analysis.SpecialFunctions.Integrals.LogDivSelf`).

## Main results

* `var_log_d_identity`, `cv_from_cumulant_at_hagedorn` (cumulant route):
  `L²/3 − (L/2)² = L²/12`, and `C_V = γ² Var(log d) = L²/12` at `γ = 1`.
* `log_one_plus_x_coefficient_24`, `log_z_quadratic_coefficient`, `log_z_to_U_coefficient`
  (Taylor route): `1/6 − 1/8 = 1/24`, `2 · L²/24 = L²/12`.
* `deriv_U_corrected_at_one`, `cv_corrected_at_hagedorn`: for
  `U(γ) = L/2 + (1 − γ) L²/12`, `U'(1) = −L²/12` and `C_V = −γ² U'(1) = L²/12`.
* `original_is_three_times_corrected`, `original_ne_corrected`, `cv_factor_three_decomposition`:
  the published `L²/4` is three times the corrected value and differs from it for `L ≠ 0`.

## References

* C. Marín, *Predicting How Transformers Attend* (2026), §5.2, and its erratum (2026-05-02),
  Zenodo 19826343. Ported from `Taf/ErratumCV.lean` of
  [karlesmarin/lean-taf](https://github.com/karlesmarin/lean-taf) (Lean v4.30.0-rc2).
-/

@[expose] public section

namespace TransformerAttention.HeatCapacity

/-! ### Cumulant route -/

/-- `(log N)²/3 − ((log N)/2)² = (log N)²/12`. -/
theorem var_log_d_identity (L : ℝ) : L ^ 2 / 3 - (L / 2) ^ 2 = L ^ 2 / 12 := by ring

/-- `C_V(γ = 1) = γ² Var(log d) = (log N)²/12`. -/
theorem cv_from_cumulant_at_hagedorn (L : ℝ) :
    (1 : ℝ) ^ 2 * (L ^ 2 / 3 - (L / 2) ^ 2) = L ^ 2 / 12 := by ring

/-! ### Taylor route -/

/-- `1/6 − 1/8 = 1/24` (the `log (1 + x)` step). -/
theorem log_one_plus_x_coefficient_24 : (1 : ℝ) / 6 - 1 / 8 = 1 / 24 := by norm_num

/-- `L²/6 − L²/8 = L²/24`. -/
theorem log_z_quadratic_coefficient (L : ℝ) : L ^ 2 / 6 - L ^ 2 / 8 = L ^ 2 / 24 := by ring

/-- `2 · (L²/24) = L²/12` (derivative of the quadratic Taylor term). -/
theorem log_z_to_U_coefficient (L : ℝ) : (2 : ℝ) * (L ^ 2 / 24) = L ^ 2 / 12 := by ring

/-- The corrected internal energy `U(γ) = L/2 + (1 − γ) L²/12`. -/
noncomputable def U_corrected (L γ : ℝ) : ℝ := L / 2 + (1 - γ) * L ^ 2 / 12

/-- Erratum eq. (5): `dU/dγ` at `γ = 1` is `−(log N)²/12`. -/
theorem deriv_U_corrected_at_one (L : ℝ) :
    deriv (fun γ => U_corrected L γ) 1 = -L ^ 2 / 12 := by
  unfold U_corrected
  have h_const : HasDerivAt (fun _ : ℝ => L / 2) 0 1 := hasDerivAt_const 1 (L / 2)
  have h_id : HasDerivAt (fun γ : ℝ => γ) 1 1 := hasDerivAt_id 1
  have h_one_minus : HasDerivAt (fun γ : ℝ => 1 - γ) (-1) 1 := by
    simpa using (hasDerivAt_const (1 : ℝ) (1 : ℝ)).fun_sub h_id
  have h_factor : HasDerivAt (fun γ : ℝ => (1 - γ) * L ^ 2 / 12) (-L ^ 2 / 12) 1 := by
    have step1 : HasDerivAt (fun γ : ℝ => (1 - γ) * L ^ 2) (-1 * L ^ 2) 1 :=
      h_one_minus.mul_const _
    have step2 := step1.div_const 12
    have h_eq : (-1 * L ^ 2) / 12 = -L ^ 2 / 12 := by ring
    rw [h_eq] at step2
    exact step2
  have h_total := h_const.fun_add h_factor
  have h_eq : (0 + -L ^ 2 / 12) = -L ^ 2 / 12 := by ring
  rw [h_eq] at h_total
  exact h_total.deriv

/-- Erratum eq. (6): `C_V(γ = 1, N) = −γ² dU/dγ = (log N)²/12`. -/
theorem cv_corrected_at_hagedorn (L : ℝ) :
    -((1 : ℝ) ^ 2) * (deriv (fun γ => U_corrected L γ) 1) = L ^ 2 / 12 := by
  rw [deriv_U_corrected_at_one]
  ring

/-! ### Original versus corrected -/

/-- The published `(log N)²/4` is exactly three times `(log N)²/12`. -/
theorem original_is_three_times_corrected (L : ℝ) : L ^ 2 / 4 = 3 * (L ^ 2 / 12) := by ring

/-- The two coefficients differ unless `L = 0`. -/
theorem original_ne_corrected (L : ℝ) (hL : L ≠ 0) : L ^ 2 / 4 ≠ L ^ 2 / 12 := by
  intro h
  have hL2 : L ^ 2 = 0 := by linarith
  have hLz : L = 0 := sq_eq_zero_iff.mp hL2
  exact hL hLz

/-- The residual of the wrong derivation: `L²/8 = 3 · (L²/24)`. -/
theorem cv_factor_three_decomposition (L : ℝ) : L ^ 2 / 8 = 3 * (L ^ 2 / 24) := by ring

end TransformerAttention.HeatCapacity
