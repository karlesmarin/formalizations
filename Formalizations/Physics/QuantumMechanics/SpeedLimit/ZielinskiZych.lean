/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Algebra.Order.Field

/-!
# The Zieliński–Zych speed limits and their limit α → 0

For a discrete spectral measure with populations p n ≥ 0, ∑ p n = 1, energies E n ≥ E₀ and
fractional moment M_α = ∑ p n (E n − E₀)^α, if the autocorrelation ∑ p n e^{−i E n τ} vanishes at τ
≥ 0, then π^α ≤ 2 M_α τ^α, that is τ ≥ π / (2 M_α)^{1/α} (ħ = 1; Zieliński–Zych, Phys. Rev. A 74,
034301 (2006), Eq. (10)). The inequality x^α − π^α/2 + (π^α/2) cos x + α π^{α−1} sin x ≥ 0 behind
it, stated without proof by Zieliński and Zych, is proved here for 0 < α ≤ 1 (the case α = 1 is
Margolus–Levitin); the case α > 1 is not formalized. E₀ only needs to bound from below the energies
that carry population. When the lowest populated level E 0 = E₀ carries p 0 and the others lie
strictly above it, M_α → 1 − p 0 as α → 0⁺, so the bound tends to +∞ when 1/2 < p 0 < 1 and to 0
when p 0 < 1/2: in that limit the family reduces to the dominant-population criterion.

## Main results

* `QSL.zz_inequality`: x^α − π^α/2 + (π^α/2) cos x + α π^{α−1} sin x ≥ 0 for 0 < α ≤ 1, x ≥ 0
* `QSL.zielinski_zych`: orthogonality at τ forces π^α ≤ 2 M_α τ^α (0 < α ≤ 1)
* `QSL.zielinski_zych_time`: the same as τ ≥ π / (2 M_α)^{1/α}
* `QSL.tendsto_fractionalMoment`: M_α → 1 − p 0 as α → 0⁺
* `QSL.zz_bound_tendsto_atTop`: the bound tends to +∞ as α → 0⁺ when 1/2 < p 0 < 1
* `QSL.zz_bound_tendsto_zero`: the bound tends to 0 as α → 0⁺ when p 0 < 1/2

## References

* C. Marín, *The Clock That Never Ticks: a machine-checked path from the dilogarithm to quantum
  speed limits in Lean 4*, Zenodo (2026), doi:10.5281/zenodo.20675271, `thm:clock`.
-/

@[expose] public section

noncomputable section
open scoped Real Topology
open Set Filter

namespace QSL

/-! ### Elementary trigonometric bounds -/

private lemma sin_ge_sub_cube {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ Real.sin x := by
  have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Real.sin y - y + y ^ 3 / 6)
      (Real.cos y - 1 + y ^ 2 / 2) y := by
    intro y
    have h1 := (Real.hasDerivAt_sin y).sub (hasDerivAt_id y)
    have h2 := (hasDerivAt_pow 3 y).div_const 6
    refine (h1.add h2).congr_deriv ?_
    norm_num
    ring
  have hmono : Monotone fun y : ℝ => Real.sin y - y + y ^ 3 / 6 := by
    apply monotone_of_deriv_nonneg
    · exact fun y => (hd y).differentiableAt
    · intro y
      rw [(hd y).deriv]
      linarith [Real.one_sub_sq_div_two_le_cos (x := y)]
  have h := hmono hx
  norm_num at h
  linarith

/-- Auxiliary inequality on `[0, π/2]`. -/
private lemma P_small {v : ℝ} (h0 : 0 ≤ v) (hv : v ≤ π / 2) :
    0 ≤ π ^ 2 * Real.sin (v / 2) ^ 2 - π * v + (π - v) * Real.sin v := by
  have hp1 := Real.pi_gt_d2
  have hp2 := Real.pi_lt_d2
  have hv' : v ≤ 1.575 := by linarith
  have ha : v / 2 - (v / 2) ^ 3 / 6 ≤ Real.sin (v / 2) := sin_ge_sub_cube (by linarith)
  have hb : v - v ^ 3 / 6 ≤ Real.sin v := sin_ge_sub_cube h0
  have hv2 : v ^ 2 ≤ 3 := by nlinarith
  have hl : 0 ≤ v / 2 - (v / 2) ^ 3 / 6 := by
    nlinarith [mul_nonneg h0 (sub_nonneg.2 hv2)]
  have ha2 : (v / 2 - (v / 2) ^ 3 / 6) ^ 2 ≤ Real.sin (v / 2) ^ 2 := pow_le_pow_left₀ hl ha 2
  have hpv : 0 ≤ π - v := by linarith [Real.pi_pos]
  have e1 : π * v ≤ 3.15 * 1.575 := by nlinarith
  have e2 : (π * v) ^ 2 ≤ (3.15 * 1.575) ^ 2 :=
    pow_le_pow_left₀ (by positivity [Real.pi_pos]) e1 2
  have hpp : (3.14 : ℝ) ^ 2 ≤ π ^ 2 := pow_le_pow_left₀ (by norm_num) hp1.le 2
  have hR : 0 ≤ π ^ 2 / 4 - 1 - π * v / 6 - π ^ 2 * v ^ 2 / 48 := by nlinarith
  have key : π ^ 2 * (v / 2 - (v / 2) ^ 3 / 6) ^ 2 - π * v + (π - v) * (v - v ^ 3 / 6)
      = v ^ 2 * (π ^ 2 / 4 - 1 - π * v / 6 - π ^ 2 * v ^ 2 / 48)
        + (v ^ 4 / 6 + π ^ 2 * v ^ 6 / 2304) := by ring
  have h3 : 0 ≤ v ^ 2 * (π ^ 2 / 4 - 1 - π * v / 6 - π ^ 2 * v ^ 2 / 48)
        + (v ^ 4 / 6 + π ^ 2 * v ^ 6 / 2304) :=
    add_nonneg (mul_nonneg (sq_nonneg v) hR) (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left ha2 (sq_nonneg π),
    mul_le_mul_of_nonneg_left hb hpv]

/-- Auxiliary inequality on `[π/2, π]`. -/
private lemma P_large {v : ℝ} (h0 : π / 2 ≤ v) (hv : v ≤ π) :
    0 ≤ π ^ 2 * Real.sin (v / 2) ^ 2 - π * v + (π - v) * Real.sin v := by
  obtain ⟨w, rfl⟩ : ∃ w, v = π - w := ⟨π - v, by ring⟩
  have hπ := Real.pi_pos
  have hp1 := Real.pi_gt_d2
  have hp2 := Real.pi_lt_d2
  have hw0 : 0 ≤ w := by linarith
  have hw1 : w ≤ π / 2 := by linarith
  have e1 : Real.sin ((π - w) / 2) = Real.cos (w / 2) := by
    rw [show (π - w) / 2 = π / 2 - w / 2 by ring, Real.sin_pi_div_two_sub]
  rw [e1, show π - (π - w) = w by ring, Real.sin_pi_sub]
  have hc : Real.cos (w / 2) ^ 2 = 1 - Real.sin (w / 2) ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq (w / 2)]
  have hs0 : 0 ≤ Real.sin (w / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hs1 : Real.sin (w / 2) ≤ w / 2 := Real.sin_le (by linarith)
  have hs2 : Real.sin (w / 2) ^ 2 ≤ (w / 2) ^ 2 := pow_le_pow_left₀ hs0 hs1 2
  have hsw0 : 2 / π * w ≤ Real.sin w := Real.mul_le_sin hw0 hw1
  have hsw : 2 * w ≤ π * Real.sin w := by
    have h := mul_le_mul_of_nonneg_left hsw0 hπ.le
    have e : π * (2 / π * w) = 2 * w := by field_simp
    linarith
  have h1 : π ^ 3 * Real.sin (w / 2) ^ 2 ≤ π ^ 3 * (w / 2) ^ 2 :=
    mul_le_mul_of_nonneg_left hs2 (by positivity)
  have h2 : w * (2 * w) ≤ w * (π * Real.sin w) := mul_le_mul_of_nonneg_left hsw hw0
  have hp3 : (3.14 : ℝ) ^ 3 ≤ π ^ 3 := pow_le_pow_left₀ (by norm_num) hp1.le 3
  have hp2' : (3.14 : ℝ) ^ 2 ≤ π ^ 2 := pow_le_pow_left₀ (by norm_num) hp1.le 2
  have hp4 : π ^ 4 ≤ (3.15 : ℝ) ^ 4 := pow_le_pow_left₀ hπ.le hp2.le 4
  have hK : 0 ≤ (π / 2 - w) * (π ^ 3 / 4 - 2) :=
    mul_nonneg (by linarith) (by nlinarith)
  have h3 : 0 ≤ π ^ 2 - π ^ 3 * w / 4 + 2 * w := by nlinarith
  have h4 : 0 ≤ w * (π ^ 2 - π ^ 3 * w / 4 + 2 * w) := mul_nonneg hw0 h3
  by_contra hneg
  push Not at hneg
  have hm := mul_neg_of_pos_of_neg hπ hneg
  nlinarith [h1, h2, h4, hm, hc]

private lemma P_nonneg {v : ℝ} (h0 : 0 ≤ v) (hv : v ≤ π) :
    0 ≤ π ^ 2 * Real.sin (v / 2) ^ 2 - π * v + (π - v) * Real.sin v :=
  (le_total v (π / 2)).elim (P_small h0) (fun h => P_large h hv)

/-! ### Power bounds -/

/-- Harmonic-mean lower bound `t ≤ t^α (t + α (1 - t))` for `0 < t` and `0 ≤ α ≤ 1`. -/
private lemma rpow_hm {t α : ℝ} (ht : 0 < t) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    t ≤ t ^ α * (t + α * (1 - t)) := by
  have hq : 0 < t ^ α := Real.rpow_pos_of_pos ht α
  have hb := rpow_one_add_le_one_add_mul_self (s := t⁻¹ - 1)
    (by have := inv_pos.2 ht; linarith) hα hα1
  rw [show 1 + (t⁻¹ - 1) = t⁻¹ by ring, Real.inv_rpow ht.le] at hb
  have h2 := mul_le_mul_of_nonneg_right hb (mul_pos ht hq).le
  have e1 : (t ^ α)⁻¹ * (t * t ^ α) = t := by field_simp
  have e2 : (1 + α * (t⁻¹ - 1)) * (t * t ^ α) = t ^ α * (t + α * (1 - t)) := by
    field_simp
  rw [e1, e2] at h2
  exact h2

/-! ### The normalized inequality -/

/-- The normalized inequality on `[0, 1]`. -/
private lemma zz_aux_le {α t : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ t ^ α - (1 - Real.cos (π * t)) / 2 + α / π * Real.sin (π * t) := by
  have hπ := Real.pi_pos
  obtain ⟨v, hv⟩ : ∃ v, v = π * (1 - t) := ⟨_, rfl⟩
  have hv0 : 0 ≤ v := by rw [hv]; exact mul_nonneg hπ.le (by linarith)
  have hvπ : v ≤ π := by rw [hv]; nlinarith
  have hπt : π * t = π - v := by rw [hv]; ring
  have hcos : Real.cos (π * t) = - Real.cos v := by rw [hπt, Real.cos_pi_sub]
  have hsin : Real.sin (π * t) = Real.sin v := by rw [hπt, Real.sin_pi_sub]
  have hS : 0 ≤ Real.sin v := Real.sin_nonneg_of_nonneg_of_le_pi hv0 hvπ
  have hP := P_nonneg hv0 hvπ
  have hsq : Real.sin (v / 2) ^ 2 = (1 - Real.cos v) / 2 := by
    have h := Real.cos_two_mul (v / 2)
    rw [show 2 * (v / 2) = v by ring] at h
    nlinarith [Real.sin_sq_add_cos_sq (v / 2)]
  rw [hcos, hsin]
  -- the quantities of the proof
  obtain ⟨C, hC⟩ : ∃ C, C = (1 + Real.cos v) / 2 := ⟨_, rfl⟩
  have hC1 : 0 ≤ 1 - C := by
    rw [hC]; linarith [Real.cos_le_one v]
  have hY : 0 ≤ t - C + t * (Real.sin v / π) := by
    have e : π ^ 2 * (t - C + t * (Real.sin v / π))
        = π ^ 2 * Real.sin (v / 2) ^ 2 - π * v + (π - v) * Real.sin v := by
      rw [hsq, hC]
      have : v = π * (1 - t) := hv
      subst this
      field_simp
      ring
    have h2 : 0 ≤ π ^ 2 * (t - C + t * (Real.sin v / π)) := by rw [e]; exact hP
    exact (mul_nonneg_iff_of_pos_left (by positivity)).1 h2
  have hD : 0 < t + α * (1 - t) := by
    nlinarith [mul_nonneg ht0 (sub_nonneg.2 hα1), mul_nonneg hα.le (sub_nonneg.2 ht1)]
  have hHM : t ≤ t ^ α * (t + α * (1 - t)) := by
    rcases ht0.eq_or_lt with h | h
    · have := mul_nonneg (Real.rpow_nonneg ht0 α) hD.le
      linarith
    · exact rpow_hm h hα.le hα1
  have hSπ : 0 ≤ Real.sin v / π := by positivity
  have hF : 0 ≤ t - (t + α * (1 - t)) * (C - α * (Real.sin v / π)) := by
    have e : t - (t + α * (1 - t)) * (C - α * (Real.sin v / π))
        = (1 - α) * (t * (1 - C)) + α * (t - C + t * (Real.sin v / π))
          + α ^ 2 * ((1 - t) * (Real.sin v / π)) := by ring
    rw [e]
    have h1 : 0 ≤ (1 - α) * (t * (1 - C)) :=
      mul_nonneg (sub_nonneg.2 hα1) (mul_nonneg ht0 hC1)
    have h2 : 0 ≤ α * (t - C + t * (Real.sin v / π)) := mul_nonneg hα.le hY
    have h3 : 0 ≤ α ^ 2 * ((1 - t) * (Real.sin v / π)) :=
      mul_nonneg (sq_nonneg α) (mul_nonneg (sub_nonneg.2 ht1) hSπ)
    linarith
  have hG : 0 ≤ (t ^ α - (C - α * (Real.sin v / π))) * (t + α * (1 - t)) := by
    nlinarith
  have hGnn : 0 ≤ t ^ α - (C - α * (Real.sin v / π)) := by
    by_contra hneg
    push Not at hneg
    nlinarith [mul_neg_of_neg_of_pos hneg hD]
  have e : t ^ α - (1 - -Real.cos v) / 2 + α / π * Real.sin v
      = t ^ α - (C - α * (Real.sin v / π)) := by
    rw [hC]; ring
  rw [e]
  exact hGnn

/-- The normalized inequality on `[1, ∞)`. -/
private lemma zz_aux_ge {α t : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (ht : 1 ≤ t) :
    0 ≤ t ^ α - (1 - Real.cos (π * t)) / 2 + α / π * Real.sin (π * t) := by
  have hπ := Real.pi_pos
  have hp3 := Real.pi_gt_three
  have ht0 : 0 < t := by linarith
  have hq : 1 + α * (1 - t⁻¹) ≤ t ^ α := by
    rw [Real.rpow_def_of_pos ht0]
    have h1 := Real.add_one_le_exp (Real.log t * α)
    have h2 := Real.one_sub_inv_le_log_of_pos ht0
    nlinarith [mul_le_mul_of_nonneg_left h2 hα.le]
  obtain ⟨u, hu⟩ : ∃ u, u = π * (t - 1) := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; exact mul_nonneg hπ.le (by linarith)
  have hπt : π * t = u + π := by rw [hu]; ring
  have hcos : Real.cos (π * t) = - Real.cos u := by rw [hπt, Real.cos_add_pi]
  have hsin : Real.sin (π * t) = - Real.sin u := by rw [hπt, Real.sin_add_pi]
  rw [hcos, hsin]
  have hinv : 0 < t⁻¹ := inv_pos.2 ht0
  rcases le_total u π with huπ | huπ
  · -- t ≤ 2
    have hz : 0 ≤ t - 1 := by linarith
    have hs1 : t - 1 ≤ Real.sin (u / 2) := by
      have h := Real.mul_le_sin (x := u / 2) (by linarith) (by linarith)
      have e : 2 / π * (u / 2) = t - 1 := by rw [hu]; field_simp
      linarith
    have hs2 : (t - 1) ^ 2 ≤ Real.sin (u / 2) ^ 2 := pow_le_pow_left₀ hz hs1 2
    have hsq : Real.sin (u / 2) ^ 2 = (1 - Real.cos u) / 2 := by
      have h := Real.cos_two_mul (u / 2)
      rw [show 2 * (u / 2) = u by ring] at h
      nlinarith [Real.sin_sq_add_cos_sq (u / 2)]
    have hsl : Real.sin u / π ≤ t - 1 := by
      rw [div_le_iff₀ hπ]
      nlinarith [Real.sin_le hu0]
    have hinv2 : t⁻¹ ≤ t ^ 2 - 3 * t + 3 := by
      rw [← sub_nonneg]
      have e : t ^ 2 - 3 * t + 3 - t⁻¹ = (t - 1) ^ 3 / t := by
        field_simp
        ring
      rw [e]
      positivity
    have hB : -(t - 1) ^ 2 ≤ 1 - t⁻¹ - Real.sin u / π := by nlinarith
    have h1 := mul_le_mul_of_nonneg_left hB hα.le
    have h2 : α * (t - 1) ^ 2 ≤ 1 * (t - 1) ^ 2 :=
      mul_le_mul_of_nonneg_right hα1 (sq_nonneg _)
    have e : α / π * -Real.sin u = -(α * (Real.sin u / π)) := by ring
    rw [e]
    nlinarith
  · -- t ≥ 2
    have ht2 : 2 ≤ t := by
      by_contra h
      push Not at h
      nlinarith
    have hinv2 : t⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) ht2
    have hsl : Real.sin u / π ≤ 1 / 3 := by
      rw [div_le_iff₀ hπ]
      nlinarith [Real.sin_le_one u]
    have hB : 0 ≤ 1 - t⁻¹ - Real.sin u / π := by linarith
    have h1 : 0 ≤ α * (1 - t⁻¹ - Real.sin u / π) := mul_nonneg hα.le hB
    have e : α / π * -Real.sin u = -(α * (Real.sin u / π)) := by ring
    rw [e]
    nlinarith [Real.cos_le_one u]

private lemma zz_aux {α t : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (ht : 0 ≤ t) :
    0 ≤ t ^ α - (1 - Real.cos (π * t)) / 2 + α / π * Real.sin (π * t) :=
  (le_total t 1).elim (zz_aux_le hα hα1 ht) (zz_aux_ge hα hα1)

/-- **The Zieliński–Zych inequality** (their Eq. (9)): for `0 < α ≤ 1` and `x ≥ 0`,
`x^α - π^α/2 + (π^α/2) cos x + α π^{α-1} sin x ≥ 0`, with equality at `x = 0` and `x = π`. -/
theorem zz_inequality {α x : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hx : 0 ≤ x) :
    0 ≤ x ^ α - π ^ α / 2 + π ^ α / 2 * Real.cos x + α * π ^ (α - 1) * Real.sin x := by
  have hπ := Real.pi_pos
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ x = π * t :=
    ⟨x / π, div_nonneg hx hπ.le, by field_simp⟩
  have hG := zz_aux hα hα1 ht
  have e1 : (π * t) ^ α = π ^ α * t ^ α := Real.mul_rpow hπ.le ht
  have e2 : π ^ (α - 1) = π ^ α / π := Real.rpow_sub_one hπ.ne' α
  rw [e1, e2]
  have h := mul_nonneg (Real.rpow_nonneg hπ.le α) hG
  have e3 : π ^ α * (t ^ α - (1 - Real.cos (π * t)) / 2 + α / π * Real.sin (π * t))
      = π ^ α * t ^ α - π ^ α / 2 + π ^ α / 2 * Real.cos (π * t)
        + α * (π ^ α / π) * Real.sin (π * t) := by ring
  linarith

/-- **The Zieliński–Zych speed limit** (their Eq. (10), `ℏ = 1`): if the autocorrelation of a
normalized population distribution with energies `E n ≥ E₀` vanishes at `τ ≥ 0`, then
`π^α ≤ 2 M_α τ^α` with `M_α = ∑ p n (E n - E₀)^α`. -/
theorem zielinski_zych {p E : ℕ → ℝ} {E₀ α M τ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hp : ∀ n, 0 ≤ p n) (hE : ∀ n, E₀ ≤ E n) (hτ : 0 ≤ τ)
    (hsum : HasSum p 1)
    (hM : HasSum (fun n => p n * (E n - E₀) ^ α) M)
    (hRe : HasSum (fun n => p n * Real.cos (E n * τ)) 0)
    (hIm : HasSum (fun n => p n * Real.sin (E n * τ)) 0) :
    π ^ α ≤ 2 * M * τ ^ α := by
  have hc : HasSum (fun n => p n * Real.cos (E n * τ - E₀ * τ)) 0 := by
    have h := (hRe.mul_left (Real.cos (E₀ * τ))).add (hIm.mul_left (Real.sin (E₀ * τ)))
    rw [mul_zero, mul_zero, add_zero] at h
    convert h using 1
    funext n
    rw [Real.cos_sub]
    ring
  have hs : HasSum (fun n => p n * Real.sin (E n * τ - E₀ * τ)) 0 := by
    have h := (hIm.mul_left (Real.cos (E₀ * τ))).sub (hRe.mul_left (Real.sin (E₀ * τ)))
    rw [mul_zero, mul_zero, sub_zero] at h
    convert h using 1
    funext n
    rw [Real.sin_sub]
    ring
  have hT := (((hM.mul_left (τ ^ α)).sub (hsum.mul_left (π ^ α / 2))).add
    (hc.mul_left (π ^ α / 2))).add (hs.mul_left (α * π ^ (α - 1)))
  have hterm : ∀ n, 0 ≤ τ ^ α * (p n * (E n - E₀) ^ α) - π ^ α / 2 * p n
      + π ^ α / 2 * (p n * Real.cos (E n * τ - E₀ * τ))
      + α * π ^ (α - 1) * (p n * Real.sin (E n * τ - E₀ * τ)) := by
    intro n
    have h := zz_inequality hα hα1 (x := τ * (E n - E₀)) (mul_nonneg hτ (sub_nonneg.2 (hE n)))
    rw [Real.mul_rpow hτ (sub_nonneg.2 (hE n)),
      show τ * (E n - E₀) = E n * τ - E₀ * τ by ring] at h
    have := mul_nonneg (hp n) h
    nlinarith [this]
  have hnn := hasSum_le hterm hasSum_zero hT
  nlinarith [hnn]

/-- The same bound as a lower bound on the time: `π / (2 M_α)^{1/α} ≤ τ`. -/
theorem zielinski_zych_time {p E : ℕ → ℝ} {E₀ α M τ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hp : ∀ n, 0 ≤ p n) (hE : ∀ n, E₀ ≤ E n) (hτ : 0 ≤ τ)
    (hsum : HasSum p 1)
    (hM : HasSum (fun n => p n * (E n - E₀) ^ α) M)
    (hRe : HasSum (fun n => p n * Real.cos (E n * τ)) 0)
    (hIm : HasSum (fun n => p n * Real.sin (E n * τ)) 0) :
    π / (2 * M) ^ (1 / α) ≤ τ := by
  have hZ := zielinski_zych hα hα1 hp hE hτ hsum hM hRe hIm
  have hM0 : 0 ≤ M :=
    hasSum_le (fun n => mul_nonneg (hp n) (Real.rpow_nonneg (sub_nonneg.2 (hE n)) α))
      hasSum_zero hM
  have hπα : 0 < π ^ α := Real.rpow_pos_of_pos Real.pi_pos α
  have hMpos : 0 < M := by
    rcases hM0.eq_or_lt with h | h
    · exfalso
      rw [← h] at hZ
      have : 2 * (0 : ℝ) * τ ^ α = 0 := by ring
      linarith
    · exact h
  have h2M : 0 < 2 * M := by positivity
  have hcpos : 0 < (2 * M) ^ (1 / α) := Real.rpow_pos_of_pos h2M _
  have hca : ((2 * M) ^ (1 / α)) ^ α = 2 * M := by
    rw [← Real.rpow_mul h2M.le, one_div_mul_cancel hα.ne', Real.rpow_one]
  have h1 : π ^ α ≤ ((2 * M) ^ (1 / α) * τ) ^ α := by
    rw [Real.mul_rpow hcpos.le hτ, hca]
    exact hZ
  have h2 : π ≤ (2 * M) ^ (1 / α) * τ :=
    (Real.rpow_le_rpow_iff Real.pi_pos.le (mul_nonneg hcpos.le hτ) hα).1 h1
  rw [div_le_iff₀ hcpos]
  linarith

/-- **The fractional moments tend to `1 - p 0`.** If the level `0` is the lowest populated one
(`E 0 = E₀` and `E n > E₀` for `n ≠ 0`) and some moment of order `α₀ > 0` is finite, then
`∑ p n (E n - E₀)^α → 1 - p 0` as `α → 0⁺`. -/
theorem tendsto_fractionalMoment {p E : ℕ → ℝ} {E₀ α₀ : ℝ}
    (hp : ∀ n, 0 ≤ p n) (hsum : HasSum p 1)
    (h0 : E 0 = E₀) (hE : ∀ n, n ≠ 0 → E₀ < E n)
    (hα₀ : 0 < α₀) (hmom : Summable fun n => p n * (E n - E₀) ^ α₀) :
    Tendsto (fun α : ℝ => ∑' n, p n * (E n - E₀) ^ α) (𝓝[>] 0) (𝓝 (1 - p 0)) := by
  have hE' : ∀ n, 0 ≤ E n - E₀ := fun n => by
    by_cases h : n = 0
    · subst h
      rw [h0]
      simp
    · exact sub_nonneg.2 (hE n h).le
  have hbound : Summable fun n => p n * (1 + (E n - E₀) ^ α₀) := by
    have := hsum.summable.add hmom
    refine this.congr (fun n => ?_)
    ring
  have hg : HasSum (fun n => if n = 0 then (0 : ℝ) else p n) (1 - p 0) := by
    have := hsum.sub (hasSum_ite_eq 0 (p 0))
    convert this using 1
    funext n
    by_cases h : n = 0 <;> simp [h]
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ))
    (f := fun α n => p n * (E n - E₀) ^ α) (g := fun n => if n = 0 then (0 : ℝ) else p n)
    (bound := fun n => p n * (1 + (E n - E₀) ^ α₀)) hbound ?_ ?_
  · rw [hg.tsum_eq] at hlim
    exact hlim
  · intro k
    by_cases hk : k = 0
    · subst hk
      simp only [ite_true]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with a ha
      have ha' : 0 < a := ha
      rw [h0, sub_self, Real.zero_rpow ha'.ne', mul_zero]
    · simp only [hk, ite_false]
      have hpos : 0 < E k - E₀ := sub_pos.2 (hE k hk)
      have hc : ContinuousAt (fun a : ℝ => (E k - E₀) ^ a) 0 :=
        Real.continuousAt_const_rpow hpos.ne'
      have h := hc.tendsto.const_mul (p k)
      simpa using h.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsGT hα₀] with a ha k
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hp k) (Real.rpow_nonneg (hE' k) a))]
    apply mul_le_mul_of_nonneg_left _ (hp k)
    by_cases h1 : 1 ≤ E k - E₀
    · have := Real.rpow_le_rpow_of_exponent_le h1 ha.2.le
      have := Real.rpow_nonneg (hE' k) α₀
      linarith
    · push Not at h1
      have := Real.rpow_le_one (hE' k) h1.le ha.1.le
      have := Real.rpow_nonneg (hE' k) α₀
      linarith

/-- Core of the two limits: if `M → c` with `0 < c` and `2c < 1`, the bound diverges. -/
private lemma bound_atTop {M : ℝ → ℝ} {c : ℝ} (hM : Tendsto M (𝓝[>] 0) (𝓝 c))
    (hc0 : 0 < c) (hc1 : 2 * c < 1) :
    Tendsto (fun α => π / (2 * M α) ^ (1 / α)) (𝓝[>] 0) atTop := by
  have h2M : Tendsto (fun α => 2 * M α) (𝓝[>] 0) (𝓝 (2 * c)) := hM.const_mul 2
  have hlog : Tendsto (fun α => Real.log (2 * M α)) (𝓝[>] 0) (𝓝 (Real.log (2 * c))) :=
    h2M.log (by positivity)
  have hneg : Real.log (2 * c) < 0 := Real.log_neg (by positivity) hc1
  have hprod : Tendsto (fun α => α⁻¹ * Real.log (2 * M α)) (𝓝[>] 0) atBot :=
    tendsto_inv_nhdsGT_zero.atTop_mul_neg hneg hlog
  have hneg' : Tendsto (fun α => -(α⁻¹ * Real.log (2 * M α))) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp hprod
  have hexp := Real.tendsto_exp_atTop.comp hneg'
  have hfin := hexp.const_mul_atTop Real.pi_pos
  have hMpos : ∀ᶠ α in 𝓝[>] (0 : ℝ), 0 < M α := hM.eventually (lt_mem_nhds hc0)
  refine hfin.congr' ?_
  filter_upwards [hMpos] with a ha
  have h2 : 0 < 2 * M a := by positivity
  simp only [Function.comp]
  rw [Real.rpow_def_of_pos h2, div_eq_mul_inv, ← Real.exp_neg]
  congr 2
  ring

/-- Core of the two limits: if `M → c` with `1 < 2c`, the bound collapses. -/
private lemma bound_zero {M : ℝ → ℝ} {c : ℝ} (hM : Tendsto M (𝓝[>] 0) (𝓝 c))
    (hc1 : 1 < 2 * c) :
    Tendsto (fun α => π / (2 * M α) ^ (1 / α)) (𝓝[>] 0) (𝓝 0) := by
  have hc0 : 0 < c := by linarith
  have h2M : Tendsto (fun α => 2 * M α) (𝓝[>] 0) (𝓝 (2 * c)) := hM.const_mul 2
  have hlog : Tendsto (fun α => Real.log (2 * M α)) (𝓝[>] 0) (𝓝 (Real.log (2 * c))) :=
    h2M.log (by positivity)
  have hpos : 0 < Real.log (2 * c) := Real.log_pos hc1
  have hprod : Tendsto (fun α => α⁻¹ * Real.log (2 * M α)) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.atTop_mul_pos hpos hlog
  have hneg' : Tendsto (fun α => -(α⁻¹ * Real.log (2 * M α))) (𝓝[>] 0) atBot :=
    tendsto_neg_atTop_atBot.comp hprod
  have hexp := Real.tendsto_exp_atBot.comp hneg'
  have hfin := hexp.const_mul π
  rw [mul_zero] at hfin
  have hMpos : ∀ᶠ α in 𝓝[>] (0 : ℝ), 0 < M α := hM.eventually (lt_mem_nhds hc0)
  refine hfin.congr' ?_
  filter_upwards [hMpos] with a ha
  have h2 : 0 < 2 * M a := by positivity
  simp only [Function.comp]
  rw [Real.rpow_def_of_pos h2, div_eq_mul_inv, ← Real.exp_neg]
  congr 2
  ring

/-- **A dominant lowest level makes the Zieliński–Zych bound diverge**: if `1/2 < p 0 < 1`, then
`π / (2 M_α)^{1/α} → +∞` as `α → 0⁺`, so the family certifies that the state never becomes
orthogonal. -/
theorem zz_bound_tendsto_atTop {p E : ℕ → ℝ} {E₀ α₀ : ℝ}
    (hp : ∀ n, 0 ≤ p n) (hsum : HasSum p 1)
    (h0 : E 0 = E₀) (hE : ∀ n, n ≠ 0 → E₀ < E n)
    (hα₀ : 0 < α₀) (hmom : Summable fun n => p n * (E n - E₀) ^ α₀)
    (hhalf : 1 / 2 < p 0) (hone : p 0 < 1) :
    Tendsto (fun α : ℝ => π / (2 * ∑' n, p n * (E n - E₀) ^ α) ^ (1 / α)) (𝓝[>] 0) atTop :=
  bound_atTop (tendsto_fractionalMoment hp hsum h0 hE hα₀ hmom) (by linarith) (by linarith)

/-- **Without a dominant lowest level the bound collapses**: if `p 0 < 1/2`, then
`π / (2 M_α)^{1/α} → 0` as `α → 0⁺`. -/
theorem zz_bound_tendsto_zero {p E : ℕ → ℝ} {E₀ α₀ : ℝ}
    (hp : ∀ n, 0 ≤ p n) (hsum : HasSum p 1)
    (h0 : E 0 = E₀) (hE : ∀ n, n ≠ 0 → E₀ < E n)
    (hα₀ : 0 < α₀) (hmom : Summable fun n => p n * (E n - E₀) ^ α₀)
    (hhalf : p 0 < 1 / 2) :
    Tendsto (fun α : ℝ => π / (2 * ∑' n, p n * (E n - E₀) ^ α) ^ (1 / α)) (𝓝[>] 0) (𝓝 0) :=
  bound_zero (tendsto_fractionalMoment hp hsum h0 hE hα₀ hmom) (by linarith)

end QSL
