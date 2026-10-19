/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The Padé attention-decay exponent as a Möbius transform

The Padé exponent `γ_Padé(θ, T) = (2θ − T s) / (2θ + T s)`, with `s = √2`, is the Möbius (Cayley)
transform `(1 − u) / (1 + u)` of the single reduced variable `u = T / (θ s)`. The collapse uses
`s² = 2`: for another constant the numerator and denominator do not factor. The constant `s` is
kept abstract (`0 < s`, `s ^ 2 = 2`) and instantiated at `√2` at the end.

## Main results

* `gammaPade_eq_mobius`: `γ_Padé = (1 − u) / (1 + u)` (uses `s² = 2`).
* `mobius_mobius`: `x ↦ (1 − x) / (1 + x)` is an involution, `(1 − γ) / (1 + γ) = u`.
* `dHorizon_eq`: `θ s (1 − γ) / (1 + γ) = T` at `γ = γ_Padé`, so the information horizon
  `d_horizon` evaluated at the Padé exponent is the training length `T`.
* `beta_mobius`: `−(1 − γ²) / 2 = −2u / (1 + u)²` for `γ = (1 − u) / (1 + u)`.
* `gammaPade_sqrt_two_eq_mobius`: the collapse at `s = √2`.

## Related

The same exponent appears, as `pade11 (T √2 / θ)`, in `TransformerAttention.Pade`
(`pade11_z_substitution`). No Möbius form of it is in Mathlib at the pinned commit (existence
check of 2026-10-19 against Mathlib, LeanSearch, the AFP and GitHub); the algebra is elementary.

## References

* C. Marín, *Predicting How Transformers Attend* (2026), Zenodo 19826343.
  Ported from `Taf/GammaMobius.lean` of
  [karlesmarin/lean-taf](https://github.com/karlesmarin/lean-taf) (Lean v4.30.0-rc2).
-/

@[expose] public section

namespace TransformerAttention.GammaMobius

/-- The Padé attention-decay exponent; `s` stands for `√2`. -/
noncomputable def gammaPade (s θ T : ℝ) : ℝ := (2 * θ - T * s) / (2 * θ + T * s)

/-- The reduced distance variable `u = T / (θ s)`. -/
noncomputable def reducedVar (s θ T : ℝ) : ℝ := T / (θ * s)

/-- **Möbius collapse.** With `u = T / (θ √2)`, the Padé exponent is `(1 − u) / (1 + u)`.
The hypothesis `s ^ 2 = 2` is essential. -/
theorem gammaPade_eq_mobius {s θ T : ℝ} (hs2 : s ^ 2 = 2) (hs : 0 < s)
    (hθ : 0 < θ) (hT : 0 < T) :
    gammaPade s θ T = (1 - reducedVar s θ T) / (1 + reducedVar s θ T) := by
  unfold gammaPade reducedVar
  have hsne : s ≠ 0 := ne_of_gt hs
  have hθne : θ ≠ 0 := ne_of_gt hθ
  have hpos1 : (0 : ℝ) < 2 * θ + T * s := by positivity
  have hpos3 : (0 : ℝ) < θ * s + T := by positivity
  -- cross-multiplied core identity (this is where `s ^ 2 = 2` is used)
  have key : (2 * θ - T * s) * (θ * s + T) = (θ * s - T) * (2 * θ + T * s) := by
    linear_combination (-2 * θ * T) * hs2
  have e1 : (2 * θ - T * s) / (2 * θ + T * s) = (θ * s - T) / (θ * s + T) := by
    rw [div_eq_div_iff (ne_of_gt hpos1) (ne_of_gt hpos3)]
    linear_combination key
  have e2 : (1 - T / (θ * s)) / (1 + T / (θ * s)) = (θ * s - T) / (θ * s + T) := by
    rw [div_eq_div_iff (by positivity) (ne_of_gt hpos3)]
    field_simp
  rw [e1, e2]

/-- **Inverse Möbius.** `x ↦ (1 − x) / (1 + x)` is an involution:
`(1 − γ) / (1 + γ) = u` when `γ = (1 − u) / (1 + u)`. -/
theorem mobius_mobius {u : ℝ} (hu : (1 : ℝ) + u ≠ 0) :
    (1 - (1 - u) / (1 + u)) / (1 + (1 - u) / (1 + u)) = u := by
  have hden : (1 : ℝ) + (1 - u) / (1 + u) ≠ 0 := by
    have h : (1 : ℝ) + (1 - u) / (1 + u) = 2 / (1 + u) := by field_simp; ring
    rw [h]; exact div_ne_zero (by norm_num) hu
  rw [div_eq_iff hden]
  field_simp
  ring

/-- The information horizon `d_horizon = θ √2 (1 − γ) / (1 + γ)` evaluated at `γ = γ_Padé` is
exactly the training length `T`. -/
theorem dHorizon_eq {s θ T : ℝ} (hs2 : s ^ 2 = 2) (hs : 0 < s)
    (hθ : 0 < θ) (hT : 0 < T) :
    θ * s * ((1 - gammaPade s θ T) / (1 + gammaPade s θ T)) = T := by
  rw [gammaPade_eq_mobius hs2 hs hθ hT]
  have hsne : s ≠ 0 := ne_of_gt hs
  have hθne : θ ≠ 0 := ne_of_gt hθ
  have hu : (1 : ℝ) + reducedVar s θ T ≠ 0 := by unfold reducedVar; positivity
  rw [mobius_mobius hu]
  unfold reducedVar
  field_simp

/-- **RG β-function in the reduced variable.** `−(1 − γ²) / 2 = −2u / (1 + u)²` for
`γ = (1 − u) / (1 + u)`. -/
theorem beta_mobius {u : ℝ} (hu : (1 : ℝ) + u ≠ 0) :
    -(1 - ((1 - u) / (1 + u)) ^ 2) / 2 = -2 * u / (1 + u) ^ 2 := by
  field_simp
  ring

/-- `√2` satisfies the two hypotheses on `s`. -/
theorem sq_sqrt_two_and_pos : (Real.sqrt 2) ^ 2 = 2 ∧ 0 < Real.sqrt 2 :=
  ⟨Real.sq_sqrt (by norm_num), Real.sqrt_pos.mpr (by norm_num)⟩

/-- The Möbius collapse at `s = √2`. -/
theorem gammaPade_sqrt_two_eq_mobius {θ T : ℝ} (hθ : 0 < θ) (hT : 0 < T) :
    gammaPade (Real.sqrt 2) θ T
      = (1 - reducedVar (Real.sqrt 2) θ T) / (1 + reducedVar (Real.sqrt 2) θ T) :=
  gammaPade_eq_mobius sq_sqrt_two_and_pos.1 sq_sqrt_two_and_pos.2 hθ hT

end TransformerAttention.GammaMobius
