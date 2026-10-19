/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The renormalization-group flow of the decay exponent

The paper's β-function is `β(γ) = −(1 − γ²)/2`. Its formula tables also state the potential
`V(γ) = γ − γ³/3` with `β = −V'`; the two are inconsistent by a factor `2`.

## Main results

* `logistic_beta`: with `x = (1 − γ)/2`, `x (1 − x) = (1 − γ²)/4` (logistic ODE ↔ `β`).
* `deriv_V`, `neg_deriv_V_ne_beta`: for `V(γ) = γ − γ³/3`, `V' = 1 − γ²`, and `−V'(γ) ≠ β(γ)`
  for `γ ∉ {−1, 1}` (the factor-2 finding).
* `deriv_V_correct`, `neg_deriv_V_correct`: the corrected potential `γ/2 − γ³/6` has
  `−V' = −(1 − γ²)/2 = β`.
* `trajectory_sign_inversion`: negating a trajectory flips the sign of the velocity.
* `rg_flow_tanh`: `γ(t) = tanh (t/2 + c)` solves `γ' = (1 − γ²)/2`.

## Related

Mathlib has `Real.hasDerivAt_sinh`, `Real.hasDerivAt_cosh` and `Real.tanh_eq_sinh_div_cosh`; at
the pinned commit it has no derivative lemma for `Real.tanh`, so `rg_flow_tanh` uses the quotient
rule.

## References

* C. Marín, *Predicting How Transformers Attend* (2026), §19, §23 of the formula toolkit,
  Zenodo 19826343. Ported from `Taf/RGFlow.lean` and `Taf/ScalingLawIdentities.lean` of
  [karlesmarin/lean-taf](https://github.com/karlesmarin/lean-taf) (Lean v4.30.0-rc2).
-/

@[expose] public section

namespace TransformerAttention.RGFlow

/-- Logistic ↔ `β`: with `x = (1 − γ)/2`, `x (1 − x) = (1 − γ²)/4`. -/
theorem logistic_beta (γ : ℝ) : ((1 - γ) / 2) * (1 - (1 - γ) / 2) = (1 - γ ^ 2) / 4 := by
  ring

/-- `V(γ) = γ − γ³/3` has `V'(γ) = 1 − γ²`. -/
theorem deriv_V (γ : ℝ) : deriv (fun x : ℝ => x - x ^ 3 / 3) γ = 1 - γ ^ 2 := by
  have h_id : HasDerivAt (fun x : ℝ => x) 1 γ := hasDerivAt_id γ
  have h_pow : HasDerivAt (fun x : ℝ => x ^ 3) (3 * γ ^ 2) γ := by
    simpa using hasDerivAt_pow 3 γ
  have h_div : HasDerivAt (fun x : ℝ => x ^ 3 / 3) (γ ^ 2) γ := by
    have := h_pow.div_const 3
    simpa using this
  have h := h_id.fun_sub h_div
  simpa using h.deriv

/-- The factor-2 finding: `−V'(γ) ≠ β(γ) = −(1 − γ²)/2` unless `γ = ±1`. -/
theorem neg_deriv_V_ne_beta (γ : ℝ) (hne1 : γ ≠ 1) (hne2 : γ ≠ -1) :
    -(deriv (fun x : ℝ => x - x ^ 3 / 3) γ) ≠ -(1 - γ ^ 2) / 2 := by
  rw [deriv_V]
  intro h
  have : 1 - γ ^ 2 = 0 := by linarith
  have factored : (1 - γ) * (1 + γ) = 0 := by nlinarith
  rcases mul_eq_zero.mp factored with h1 | h2
  · exact hne1 (by linarith)
  · exact hne2 (by linarith)

/-- The corrected potential `V(γ) = γ/2 − γ³/6` has `V'(γ) = (1 − γ²)/2`. -/
theorem deriv_V_correct (γ : ℝ) : deriv (fun x : ℝ => x / 2 - x ^ 3 / 6) γ = (1 - γ ^ 2) / 2 := by
  have h_id : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) γ := by
    have := (hasDerivAt_id γ).div_const 2
    simpa using this
  have h_pow : HasDerivAt (fun x : ℝ => x ^ 3) (3 * γ ^ 2) γ := by
    simpa using hasDerivAt_pow 3 γ
  have h_div : HasDerivAt (fun x : ℝ => x ^ 3 / 6) (γ ^ 2 / 2) γ := by
    have := h_pow.div_const 6
    have h_eq : (3 * γ ^ 2) / 6 = γ ^ 2 / 2 := by ring
    rw [h_eq] at this
    exact this
  have h := h_id.fun_sub h_div
  have h_eq : (1 / 2 : ℝ) - γ ^ 2 / 2 = (1 - γ ^ 2) / 2 := by ring
  rw [← h_eq]
  exact h.deriv

/-- `−V'_correct(γ) = −(1 − γ²)/2 = β(γ)`. -/
theorem neg_deriv_V_correct (γ : ℝ) :
    -(deriv (fun x : ℝ => x / 2 - x ^ 3 / 6) γ) = -(1 - γ ^ 2) / 2 := by
  rw [deriv_V_correct]; ring

/-- Negating the trajectory inverts the sign of the velocity: `−((1 − γ²)/2) = −(1 − (−γ)²)/2`. -/
theorem trajectory_sign_inversion (γ : ℝ) : -((1 - γ ^ 2) / 2) = -(1 - (-γ) ^ 2) / 2 := by
  ring

/-- `γ(t) = tanh (t/2 + c)` solves the flow `γ'(t) = (1 − γ²)/2`. -/
theorem rg_flow_tanh (c t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.tanh (s / 2 + c)) ((1 - Real.tanh (t / 2 + c) ^ 2) / 2) t := by
  have base : ∀ u : ℝ, HasDerivAt Real.tanh (1 - Real.tanh u ^ 2) u := by
    intro u
    have hc : Real.cosh u ≠ 0 := (Real.cosh_pos u).ne'
    have h := (Real.hasDerivAt_sinh u).div (Real.hasDerivAt_cosh u) hc
    have hfun : Real.sinh / Real.cosh = Real.tanh := by
      funext x; rw [Pi.div_apply]; exact (Real.tanh_eq_sinh_div_cosh x).symm
    rw [hfun] at h
    convert h using 1
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
  have inner : HasDerivAt (fun s : ℝ => s / 2 + c) (1 / 2) t :=
    ((hasDerivAt_id t).div_const 2).add_const c
  have hcomp := (base (t / 2 + c)).comp t inner
  exact hcomp.congr_deriv (by ring)

end TransformerAttention.RGFlow
