/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Critical exponents of the attention decay (Phase A)

For the decay exponent `γ ≠ 1` (Phase A is `0 < γ < 1`) the paper sets
`ν = 1 / (1 − γ)`, `β = γ − 1`, `η = γ − 1` (corrected from `η = 2γ`), `α = 2 − 1 / (1 − γ)`,
`χ = 1 / (1 − γ)` and `γ_χ = 1 / (1 − γ) + 2 (1 − γ)` (Rushbrooke definition).

## Main results

* `two_mul_ηc_sq_add_ηc_mul_γχ_add_one` (D-SAGE-1): `2 η² + η γ_χ + 1 = 0`.
* `βc_mul_χ` (D-SAGE-2, anti-Ising): `β χ = −1`; `αC_add_χ` (D-SAGE-4): `α + χ = 2`;
  `αC_add_γχ` (D-SAGE-5); `βc_mul_γχ` (D-SAGE-6); `νc_mul_βc`: `ν β = −1`.
* `rushbrooke`, `josephson`: the scaling relations with `d = 1` hold identically.
* `fisher_residual`, `fisher_residual_eq_zero_iff`: `γ_χ − (2 − η) ν = γ (2γ − 3) / (1 − γ)`, which
  vanishes iff `γ ∈ {0, 3/2}`.
* `eta_two_gamma_residual`, `eta_two_gamma_residual_pos`: with the old `η = 2γ`, D-SAGE-1 has
  residual `(−4γ³ + 5γ + 1) / (1 − γ)`, positive on all of Phase A.
* `two_mul_sqrt_two_le_γχ` (AM-GM bound): `2 √2 ≤ γ_χ` for `γ < 1`.
* Other closed forms: `nu_imprint_mul_two_pi`, `central_charge_mul_two_pi`, `nu_mul_one_sub`,
  `levy_index`, `two_s_sub_deff`, `sqrt_three_div_six_eq_one_div_sqrt_twelve` (RoPE `β = 1/√12`).

## Related

The AM-GM step is Mathlib's `two_mul_le_add_of_sq_le_mul` (`two_mul_sqrt_mul_le_add` restates it
for `√(a b)` in one line). `nu_imprint_mul_two_pi`, `central_charge_mul_two_pi` and
`nu_mul_one_sub` are instances of `div_mul_cancel₀` and `one_div_mul_cancel`.

## References

* C. Marín, *Predicting How Transformers Attend* (2026), Zenodo 19826343.
  Ported from `Taf/Identities.lean`, `Taf/AmGmPade.lean`, `Taf/RGFlow.lean` and
  `Taf/ScalingLawIdentities.lean` of [karlesmarin/lean-taf](https://github.com/karlesmarin/lean-taf)
  (Lean v4.30.0-rc2).
-/

@[expose] public section

namespace TransformerAttention.CriticalExponents

/-- `ν = 1 / (1 − γ)` (correlation-length exponent, Phase A). -/
noncomputable def νc (γ : ℝ) : ℝ := 1 / (1 - γ)

/-- `β = γ − 1` (order-parameter exponent). -/
def βc (γ : ℝ) : ℝ := γ - 1

/-- `η = γ − 1` (anomalous dimension; corrected from `2γ`). -/
def ηc (γ : ℝ) : ℝ := γ - 1

/-- `α = 2 − 1 / (1 − γ)` (heat-capacity exponent, Phase A). -/
noncomputable def αC (γ : ℝ) : ℝ := 2 - 1 / (1 - γ)

/-- `γ_χ = 1 / (1 − γ) + 2 (1 − γ)` (susceptibility exponent, Rushbrooke definition). -/
noncomputable def γχ (γ : ℝ) : ℝ := 1 / (1 - γ) + 2 * (1 - γ)

/-- `χ = 1 / (1 − γ)` (susceptibility scaling, Phase A). -/
noncomputable def χ (γ : ℝ) : ℝ := 1 / (1 - γ)

/-! ### Identities -/

/-- D-SAGE-1: `2 η² + η γ_χ + 1 = 0`. -/
theorem two_mul_ηc_sq_add_ηc_mul_γχ_add_one (γ : ℝ) (h : γ ≠ 1) :
    2 * (ηc γ) ^ 2 + (ηc γ) * (γχ γ) + 1 = 0 := by
  unfold ηc γχ
  have h1 : 1 - γ ≠ 0 := sub_ne_zero.mpr (fun heq => h heq.symm)
  field_simp
  ring

/-- D-SAGE-2 (anti-Ising): `β χ = −1`. -/
theorem βc_mul_χ (γ : ℝ) (h : γ ≠ 1) : (βc γ) * (χ γ) = -1 := by
  unfold βc χ
  have h1 : 1 - γ ≠ 0 := sub_ne_zero.mpr (fun heq => h heq.symm)
  field_simp
  ring

/-- D-SAGE-4: `α + χ = 2`. -/
theorem αC_add_χ (γ : ℝ) (h : γ ≠ 1) : αC γ + χ γ = 2 := by
  unfold αC χ
  have h1 : 1 - γ ≠ 0 := sub_ne_zero.mpr (fun heq => h heq.symm)
  field_simp
  ring

/-- D-SAGE-5: `α + γ_χ = 2 (2 − γ)`. -/
theorem αC_add_γχ (γ : ℝ) (h : γ ≠ 1) : αC γ + γχ γ = 2 * (2 - γ) := by
  unfold αC γχ
  have h1 : 1 - γ ≠ 0 := sub_ne_zero.mpr (fun heq => h heq.symm)
  field_simp
  ring

/-- D-SAGE-6: `β γ_χ = −2γ² + 4γ − 3`. -/
theorem βc_mul_γχ (γ : ℝ) (h : γ ≠ 1) : (βc γ) * (γχ γ) = -2 * γ ^ 2 + 4 * γ - 3 := by
  unfold βc γχ
  have h1 : 1 - γ ≠ 0 := sub_ne_zero.mpr (fun heq => h heq.symm)
  field_simp
  ring

/-- Rushbrooke with `d = 1`: `2β + γ_χ − ν = 0`. -/
theorem rushbrooke (γ : ℝ) (h : γ ≠ 1) : 2 * (βc γ) + (γχ γ) - (νc γ) * 1 = 0 := by
  unfold βc γχ νc
  have h1 : 1 - γ ≠ 0 := sub_ne_zero.mpr (fun heq => h heq.symm)
  field_simp
  ring

/-- Josephson with `d = 1`: `2 − α − ν = 0`. -/
theorem josephson (γ : ℝ) (h : γ ≠ 1) : 2 - (αC γ) - (νc γ) * 1 = 0 := by
  unfold αC νc
  have h1 : 1 - γ ≠ 0 := sub_ne_zero.mpr (fun heq => h heq.symm)
  field_simp
  ring

/-- Fisher residual: `γ_χ − (2 − η) ν = γ (2γ − 3) / (1 − γ)`. -/
theorem fisher_residual (γ : ℝ) (h : γ ≠ 1) :
    (γχ γ) - (2 - ηc γ) * (νc γ) = γ * (2 * γ - 3) / (1 - γ) := by
  unfold γχ ηc νc
  have h1 : 1 - γ ≠ 0 := sub_ne_zero.mpr (fun heq => h heq.symm)
  field_simp
  ring

/-- The Fisher residual vanishes iff `γ = 0` or `γ = 3/2`. -/
theorem fisher_residual_eq_zero_iff (γ : ℝ) (h : γ ≠ 1) :
    (γχ γ) - (2 - ηc γ) * (νc γ) = 0 ↔ γ = 0 ∨ γ = 3 / 2 := by
  rw [fisher_residual γ h]
  have h1 : 1 - γ ≠ 0 := sub_ne_zero.mpr (fun heq => h heq.symm)
  rw [div_eq_zero_iff]
  constructor
  · intro hcase
    rcases hcase with h_num | h_den
    · rcases mul_eq_zero.mp h_num with h0 | h32
      · left; exact h0
      · right; linarith
    · exact absurd h_den h1
  · intro hcase
    left
    rcases hcase with h0 | h32
    · subst h0; ring
    · subst h32; ring

/-- With the old `η = 2γ`, D-SAGE-1 has residual `(−4γ³ + 5γ + 1) / (1 − γ)`. -/
theorem eta_two_gamma_residual (γ : ℝ) (h : γ ≠ 1) :
    2 * (2 * γ) ^ 2 + (2 * γ) * (γχ γ) + 1 = (-4 * γ ^ 3 + 5 * γ + 1) / (1 - γ) := by
  unfold γχ
  have h1 : 1 - γ ≠ 0 := sub_ne_zero.mpr (fun heq => h heq.symm)
  field_simp
  ring

/-- `η = 2γ` fails D-SAGE-1 everywhere in Phase A: the residual is positive on `(0, 1)`. -/
theorem eta_two_gamma_residual_pos (γ : ℝ) (hγ_lo : 0 < γ) (hγ_hi : γ < 1) :
    2 * (2 * γ) ^ 2 + (2 * γ) * (γχ γ) + 1 > 0 := by
  have h_neq : γ ≠ 1 := ne_of_lt hγ_hi
  rw [eta_two_gamma_residual γ h_neq]
  have hden : 1 - γ > 0 := by linarith
  have hnum : -4 * γ ^ 3 + 5 * γ + 1 > 0 := by
    have h_cube : γ ^ 3 < γ := by
      have : γ ^ 3 = γ * γ ^ 2 := by ring
      rw [this]
      have hγ2_lt_1 : γ ^ 2 < 1 := by
        rw [show (1 : ℝ) = 1 ^ 2 by ring]
        exact sq_lt_sq' (by linarith) hγ_hi
      nlinarith [hγ_lo, hγ2_lt_1]
    linarith
  positivity

/-- `β χ + 1 = 0`: D-SAGE-2 rearranged. -/
theorem βc_mul_χ_add_one (γ : ℝ) (h : γ ≠ 1) : (βc γ) * (χ γ) + 1 = 0 := by
  rw [βc_mul_χ γ h]; ring

/-- `ν β = −1`. -/
theorem νc_mul_βc (γ : ℝ) (h : γ ≠ 1) : (νc γ) * (βc γ) = -1 := by
  unfold νc βc
  have h1 : 1 - γ ≠ 0 := sub_ne_zero.mpr (fun heq => h heq.symm)
  field_simp
  ring

/-! ### AM-GM bound on `γ_χ` -/

/-- AM-GM for two variables, `2 √(a b) ≤ a + b`: Mathlib's `two_mul_le_add_of_sq_le_mul`. -/
theorem two_mul_sqrt_mul_le_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * Real.sqrt (a * b) ≤ a + b :=
  two_mul_le_add_of_sq_le_mul ha hb (Real.sq_sqrt (mul_nonneg ha hb)).le

/-- `γ_χ = 1 / (1 − γ) + 2 (1 − γ) ≥ 2 √2` for `γ < 1` (the product of the two terms is `2`). -/
theorem two_mul_sqrt_two_le_γχ (γ : ℝ) (hγ : γ < 1) :
    2 * Real.sqrt 2 ≤ 1 / (1 - γ) + 2 * (1 - γ) := by
  have h1mg : 0 < 1 - γ := by linarith
  have h_prod : (1 / (1 - γ)) * (2 * (1 - γ)) = 2 := by field_simp
  have := two_mul_sqrt_mul_le_add (one_div_pos.mpr h1mg).le (by linarith : (0 : ℝ) ≤ 2 * (1 - γ))
  rwa [h_prod] at this

/-! ### Other closed forms -/

/-- `ν_imprint · 2π = −1` with `ν_imprint = −1 / (2π)`: an instance of `div_mul_cancel₀`. -/
theorem nu_imprint_mul_two_pi (π_val : ℝ) (hπ : π_val > 0) :
    (-1 / (2 * π_val)) * (2 * π_val) = -1 :=
  div_mul_cancel₀ (-1) (by positivity)

/-- D-SAGE-7: `c · |ν_imprint| · 2π = 3` with `c = 3`. -/
theorem central_charge_mul_two_pi (π_val : ℝ) (hπ : π_val > 0) :
    (3 : ℝ) * (1 / (2 * π_val)) * (2 * π_val) = 3 := by
  rw [mul_assoc, one_div_mul_cancel (by positivity), mul_one]

/-- CFT₂: `ν (1 − γ) = 1` for `ν = 1 / (1 − γ)`: an instance of `one_div_mul_cancel`. -/
theorem nu_mul_one_sub (γ : ℝ) (h : 1 - γ ≠ 0) : (1 / (1 - γ)) * (1 - γ) = 1 :=
  one_div_mul_cancel h

/-- Lévy / fractional-Laplacian index: with `s = (γ − 1)/2`, `2s = γ − 1`. -/
theorem levy_index (γ : ℝ) : 2 * ((γ - 1) / 2) = γ - 1 := by ring

/-- `(γ² − γ − 1)/γ + γ = (2γ + 1)(γ − 1)/γ`, so `2s − d_eff` vanishes iff `γ ∈ {1, −1/2}`. -/
theorem two_s_sub_deff (γ : ℝ) (hγ : γ ≠ 0) :
    (γ ^ 2 - γ - 1) / γ + γ = (2 * γ + 1) * (γ - 1) / γ := by
  field_simp
  ring

/-- RoPE coefficient: `√3 / 6 = 1 / √12` (`σ` of the uniform law on `[−1, 0]`). -/
theorem sqrt_three_div_six_eq_one_div_sqrt_twelve : Real.sqrt 3 / 6 = 1 / Real.sqrt 12 := by
  have h12 : Real.sqrt 12 = 2 * Real.sqrt 3 := by
    rw [show (12 : ℝ) = 4 * 3 from by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show Real.sqrt 4 = 2 from by
          rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]]
  rw [h12]
  have h3_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h3_sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  field_simp
  nlinarith [h3_sq, h3_pos]

end TransformerAttention.CriticalExponents
