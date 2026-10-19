/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Padé approximants of `e^{−z}` in the attention-decay model

`[1/1]` and `[2/2]` Padé approximants of `e^{−z}`:
`P₁₁(z) = (1 − z/2) / (1 + z/2)` and `P₂₂(z) = (1 − z/2 + z²/12) / (1 + z/2 + z²/12)`.
In the paper `γ_Padé = P₁₁(z)` with `z = T √2 / θ`.

## Main results

* `pade22_sub_pade11` (G-15): `P₂₂ − P₁₁ = 2 z³ / ((z + 2)(z² + 6z + 12))`, also in the cleared
  form `pade22_sub_pade11'`.
* `pade_difference_at_zero`, `pade_saturation_leading_coefficient`: the difference vanishes at
  `0` with leading coefficient `2 / 24 = 1/12` of `z³`.
* `one_sub_pade11`: `1 − (2 − z)/(2 + z) = 2z / (2 + z)`.
* `pade11_z_substitution`: `γ_Padé = (2θ − T√2) / (2θ + T√2)`.
* `theta_eff_pade`: `T √2 / (1 − γ_Padé) = θ + T / √2`.

## References

* C. Marín, *Predicting How Transformers Attend* (2026), Zenodo 19826343.
  Ported from `Taf/AmGmPade.lean`, `Taf/RGFlow.lean` and `Taf/ScalingLawIdentities.lean` of
  [karlesmarin/lean-taf](https://github.com/karlesmarin/lean-taf) (Lean v4.30.0-rc2).
-/

@[expose] public section

namespace TransformerAttention.Pade

/-- The `[1/1]` Padé approximant of `e^{−z}`. -/
noncomputable def pade11 (z : ℝ) : ℝ := (1 - z / 2) / (1 + z / 2)

/-- The `[2/2]` Padé approximant of `e^{−z}`. -/
noncomputable def pade22 (z : ℝ) : ℝ := (1 - z / 2 + z ^ 2 / 12) / (1 + z / 2 + z ^ 2 / 12)

/-- G-15, cleared form: `(12 − 6z + z²)/(12 + 6z + z²) − (2 − z)/(2 + z)
= 2 z³ / ((z + 2)(z² + 6z + 12))`. -/
theorem pade22_sub_pade11' (z : ℝ) (h1 : z + 2 ≠ 0) (h2 : z ^ 2 + 6 * z + 12 ≠ 0) :
    (12 - 6 * z + z ^ 2) / (12 + 6 * z + z ^ 2) - (2 - z) / (2 + z)
      = (2 * z ^ 3) / ((z + 2) * (z ^ 2 + 6 * z + 12)) := by
  have h2' : (12 + 6 * z + z ^ 2) ≠ 0 := by
    have : (12 + 6 * z + z ^ 2) = (z ^ 2 + 6 * z + 12) := by ring
    rw [this]; exact h2
  have h1' : (2 + z) ≠ 0 := by
    have : (2 + z) = (z + 2) := by ring
    rw [this]; exact h1
  rw [div_sub_div _ _ h2' h1', div_eq_div_iff (mul_ne_zero h2' h1') (mul_ne_zero h1 h2)]
  ring

/-- `P₂₂ − P₁₁ = 2 z³ / ((z + 2)(z² + 6z + 12))`. -/
theorem pade22_sub_pade11 (z : ℝ) (h11 : 1 + z / 2 ≠ 0) (h22 : 1 + z / 2 + z ^ 2 / 12 ≠ 0) :
    pade22 z - pade11 z = 2 * z ^ 3 / ((z + 2) * (z ^ 2 + 6 * z + 12)) := by
  unfold pade22 pade11
  have hz2 : z + 2 ≠ 0 := by
    intro hcontra
    apply h11
    linarith
  have hquad : z ^ 2 + 6 * z + 12 ≠ 0 := by
    intro hcontra
    have h_pos : z ^ 2 + 6 * z + 12 > 0 := by nlinarith [sq_nonneg (z + 3)]
    linarith
  have h2' : (12 + 6 * z + z ^ 2) ≠ 0 := by
    rw [show (12 + 6 * z + z ^ 2) = (z ^ 2 + 6 * z + 12) by ring]; exact hquad
  have h1' : (2 + z) ≠ 0 := by rw [add_comm]; exact hz2
  have e22 : (1 - z / 2 + z ^ 2 / 12) / (1 + z / 2 + z ^ 2 / 12)
      = (12 - 6 * z + z ^ 2) / (12 + 6 * z + z ^ 2) := by
    rw [div_eq_div_iff h22 h2']; ring
  have e11 : (1 - z / 2) / (1 + z / 2) = (2 - z) / (2 + z) := by
    rw [div_eq_div_iff h11 h1']; ring
  rw [e22, e11]
  exact pade22_sub_pade11' z hz2 hquad

/-- The difference `2 z³ / ((z + 2)(z² + 6z + 12))` vanishes at `z = 0`. -/
theorem pade_difference_at_zero :
    let f : ℝ → ℝ := fun z => 2 * z ^ 3 / ((z + 2) * (z ^ 2 + 6 * z + 12))
    f 0 = 0 := by
  show (2 * (0 : ℝ) ^ 3 / ((0 + 2) * ((0 : ℝ) ^ 2 + 6 * 0 + 12))) = 0
  norm_num

/-- Leading coefficient of `z³` in the difference: `2 / ((0 + 2)(0 + 0 + 12)) = 1/12`. -/
theorem pade_saturation_leading_coefficient :
    (2 : ℝ) / ((0 + 2) * (0 ^ 2 + 6 * 0 + 12)) = 1 / 12 := by
  norm_num

/-- `1 − (2 − z)/(2 + z) = 2z / (2 + z)`. -/
theorem one_sub_pade11 (z : ℝ) (h : 2 + z ≠ 0) : 1 - (2 - z) / (2 + z) = (2 * z) / (2 + z) := by
  field_simp
  ring

/-- With `z = T √2 / θ`: `(2 − z)/(2 + z) = (2θ − T√2) / (2θ + T√2)`. -/
theorem pade11_z_substitution (θ T : ℝ) (hθ : θ ≠ 0) (hsum_θ : 2 * θ + T * Real.sqrt 2 ≠ 0) :
    (2 - T * Real.sqrt 2 / θ) / (2 + T * Real.sqrt 2 / θ)
      = (2 * θ - T * Real.sqrt 2) / (2 * θ + T * Real.sqrt 2) := by
  field_simp

/-- `θ_eff`: with `z = T √2 / θ`, `T √2 / (1 − (2 − z)/(2 + z)) = θ + T / √2`. -/
theorem theta_eff_pade (θ T : ℝ) (hθ : θ ≠ 0) (hT : T ≠ 0) (hsum : 2 * θ + T * Real.sqrt 2 ≠ 0) :
    T * Real.sqrt 2 / (1 - (2 - T * Real.sqrt 2 / θ) / (2 + T * Real.sqrt 2 / θ))
      = θ + T / Real.sqrt 2 := by
  have hsqrt2_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt2 : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt2_pos
  have h2plus : 2 + T * Real.sqrt 2 / θ ≠ 0 := by
    intro hbad
    apply hsum
    have : θ * (2 + T * Real.sqrt 2 / θ) = θ * 0 := by rw [hbad]
    field_simp at this
    linarith
  field_simp
  ring_nf
  have h_cubed : (Real.sqrt 2) ^ 3 = Real.sqrt 2 * 2 := by
    rw [show (3 : ℕ) = 1 + 2 from by norm_num, pow_add, pow_one, hsqrt2_sq]
  rw [h_cubed]
  ring

end TransformerAttention.Pade
