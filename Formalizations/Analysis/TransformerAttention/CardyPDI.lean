/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The Cardy entropy shift and the PDI

For a decay exponent `γ ∈ (−1, 1)`, a scale `θ > 0` and `z > 0`, the paper sets
`d_horizon = θ (1 − γ) √2 / (1 + γ)` (from the Padé saturation), `PDI = d_horizon / (z θ)`, and
two forms of the Cardy entropy shift:
`ΔH₇ = log (z / √2) + 2 artanh γ` (Phase 7) and `ΔH₈ = log (z / 2) + 2 artanh γ` (Phase 8).

## Main results

* `log_pdi_add_dHCardyPhase7` (D-DEEP-15): `log PDI + ΔH₇ = 0` exactly.
* `log_pdi_add_dHCardyPhase8`: with the Phase 8 form the residual is `−log 2 / 2`.
* `hasDerivAt_artanh`: `d/dx artanh x = 1 / (1 − x²)` on `(−1, 1)`.
* `deriv_dHCardyPhase8` (D-DEEP-22): `d ΔH₈ / dγ = 2 / (1 − γ²)` on `(−1, 1)`.

## Related

Mathlib defines `Real.artanh` (with `Real.artanh_eq_half_log`) but, at the pinned commit, has no
derivative lemma for it; `hasDerivAt_artanh` derives it from `artanh_eq_half_log` and
`HasDerivAt.log`. Current Mathlib has none either (checked with Loogle and LeanSearch, October 2026).
The same lemma, under the same name, is in
[TauCeti](https://github.com/TauCetiProject/TauCeti) (`TauCeti/Analysis/SpecialFunctions/Artanh.lean`).

## References

* C. Marín, *Predicting How Transformers Attend* (2026), Zenodo 19826343.
  Ported from `Taf/Identities.lean` of
  [karlesmarin/lean-taf](https://github.com/karlesmarin/lean-taf) (Lean v4.30.0-rc2). The
  original refers to `Real.arctanh`, `Real.arctanh_eq_log`, `Real.deriv_arctanh` and
  `Real.differentiableAt_arctanh`, which do not exist in Mathlib (neither at the commit pinned by
  lean-taf nor here): the three statements above were not machine-checked there.
-/

@[expose] public section

namespace TransformerAttention.CardyPDI

/-- Phase 7 Cardy entropy shift `log (z / √2) + 2 artanh γ`. -/
noncomputable def dHCardyPhase7 (z γ : ℝ) : ℝ :=
  Real.log (z / Real.sqrt 2) + 2 * Real.artanh γ

/-- Phase 8 Cardy entropy shift `log (z / 2) + 2 artanh γ`. -/
noncomputable def dHCardyPhase8 (z γ : ℝ) : ℝ :=
  Real.log (z / 2) + 2 * Real.artanh γ

/-- `d_horizon = θ (1 − γ) √2 / (1 + γ)`, the solution `T` of `γ_Padé(θ, T) = γ`. -/
noncomputable def dHorizon (θ γ : ℝ) : ℝ :=
  θ * (1 - γ) * Real.sqrt 2 / (1 + γ)

/-- `PDI = d_horizon / T_eval` with `T_eval = z θ`. -/
noncomputable def pdi (θ z γ : ℝ) : ℝ :=
  (dHorizon θ γ) / (z * θ)

/-- D-DEEP-15: `log PDI + ΔH₇ = 0`. -/
theorem log_pdi_add_dHCardyPhase7 (θ z γ : ℝ)
    (hθ : θ > 0) (hz : z > 0) (hγ_lo : 0 < 1 - γ) (hγ_hi : 0 < 1 + γ) :
    Real.log (pdi θ z γ) + dHCardyPhase7 z γ = 0 := by
  unfold pdi dHorizon dHCardyPhase7
  have hsqrt2 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num)
  have h_atanh : Real.artanh γ = (1 / 2) * Real.log ((1 + γ) / (1 - γ)) :=
    Real.artanh_eq_half_log ⟨by linarith, by linarith⟩
  have h1mg : (1 - γ : ℝ) > 0 := hγ_lo
  have h1pg : (1 + γ : ℝ) > 0 := hγ_hi
  have hθ_ne : θ ≠ 0 := ne_of_gt hθ
  have hz_ne : z ≠ 0 := ne_of_gt hz
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt2
  rw [h_atanh]
  have step1 : θ * (1 - γ) * Real.sqrt 2 / (1 + γ) / (z * θ) =
      (1 - γ) * Real.sqrt 2 / ((1 + γ) * z) := by
    field_simp
  rw [step1]
  rw [show 2 * ((1 / 2) * Real.log ((1 + γ) / (1 - γ))) =
        Real.log ((1 + γ) / (1 - γ)) by ring]
  have hlog1 : Real.log ((1 - γ) * Real.sqrt 2 / ((1 + γ) * z))
      + Real.log (z / Real.sqrt 2) = Real.log ((1 - γ) / (1 + γ)) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  rw [← add_assoc, hlog1]
  rw [← Real.log_mul (by positivity) (by positivity)]
  rw [show (1 - γ) / (1 + γ) * ((1 + γ) / (1 - γ)) = 1 by field_simp]
  exact Real.log_one

/-- `d/dx artanh x = 1 / (1 − x²)` for `x ∈ (−1, 1)`. -/
theorem hasDerivAt_artanh {x : ℝ} (hlo : -1 < x) (hhi : x < 1) :
    HasDerivAt Real.artanh (1 / (1 - x ^ 2)) x := by
  have h1m : (1 - x) ≠ 0 := by linarith
  have h1p : (1 + x) ≠ 0 := by linarith
  have hq : HasDerivAt (fun y => (1 + y) / (1 - y))
      ((1 * (1 - x) - (1 + x) * (-1)) / (1 - x) ^ 2) x :=
    ((hasDerivAt_id x).const_add 1).div ((hasDerivAt_id x).const_sub 1) h1m
  have hlog := (hq.log (div_ne_zero h1p h1m)).const_mul (1 / 2 : ℝ)
  have heq : (fun y => (1 / 2 : ℝ) * Real.log ((1 + y) / (1 - y))) =ᶠ[nhds x] Real.artanh := by
    filter_upwards [Ioo_mem_nhds hlo hhi] with y hy
    exact (Real.artanh_eq_half_log ⟨hy.1.le, hy.2.le⟩).symm
  have h2 : 1 - x ^ 2 ≠ 0 := by
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring]; exact mul_ne_zero h1m h1p
  convert hlog.congr_of_eventuallyEq heq.symm using 1
  field_simp
  ring

/-- D-DEEP-22: `d ΔH₈ / dγ = 2 / (1 − γ²)` for `γ ∈ (−1, 1)`. -/
theorem deriv_dHCardyPhase8 (z γ : ℝ) (hγ_lo : -1 < γ) (hγ_hi : γ < 1) :
    deriv (fun γ' => dHCardyPhase8 z γ') γ = 2 / (1 - γ ^ 2) := by
  unfold dHCardyPhase8
  have h := ((hasDerivAt_artanh hγ_lo hγ_hi).const_mul (2 : ℝ)).const_add (Real.log (z / 2))
  rw [h.deriv]
  ring

/-- With the Phase 8 form, `log PDI + ΔH₈ = −log 2 / 2`. -/
theorem log_pdi_add_dHCardyPhase8 (θ z γ : ℝ)
    (hθ : θ > 0) (hz : z > 0) (hγ_lo : 0 < 1 - γ) (hγ_hi : 0 < 1 + γ) :
    Real.log (pdi θ z γ) + dHCardyPhase8 z γ = -(Real.log 2) / 2 := by
  unfold dHCardyPhase8
  have h := log_pdi_add_dHCardyPhase7 θ z γ hθ hz hγ_lo hγ_hi
  unfold dHCardyPhase7 at h
  have h1 : Real.log (z / 2) = Real.log (z / Real.sqrt 2) - Real.log 2 / 2 := by
    have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    rw [show z / 2 = (z / Real.sqrt 2) / Real.sqrt 2 by rw [div_div, hs]]
    rw [Real.log_div (by positivity) (by positivity)]
    rw [Real.log_sqrt (by norm_num : (2 : ℝ) ≥ 0)]
  linarith

end TransformerAttention.CardyPDI
