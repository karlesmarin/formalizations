/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Analysis.PSeries
public import Formalizations.Analysis.SpecialFunctions.Polylog.HausdorffFloor

/-!
# The floor of the zeta states

The zeta state of weight s > 1 has populations (n + 1)^{−s} / ζ(s) on the equally spaced levels n +
1; its autocorrelation is Li_s(z) / ζ(s) with z = e^{−iθ}. From η(s) ≤ |Li_s z| on the unit circle
(Polylog.polylog_circle_floor) and the classical identity η(s) = (1 − 2^{1−s}) ζ(s), proved here by
splitting the alternating series into even and odd terms, the autocorrelation never drops below 1 −
2^{1−s}, its value at θ = π. For s = 2 the floor is 1/2.

## Main results

* `Polylog.tendsto_partialEta_of_one_lt`: η(s) = (1 − 2^{1−s}) ζ(s) for s > 1
* `Polylog.zeta_floor`: (1 − 2^{1−s}) ζ(s) ≤ |Li_s z| on the whole unit circle, s > 1
* `Polylog.zetaState_floor`: the normalized zeta state has |S(θ)| ≥ 1 − 2^{1−s} for every θ

## References

* C. Marín, *The Clock That Never Ticks: a machine-checked path from the dilogarithm to quantum
  speed limits in Lean 4*, Zenodo (2026), doi:10.5281/zenodo.20675271, `thm:clock`.
-/

@[expose] public section

open Filter Topology Finset Complex

namespace Polylog

/-- Summability of `1 / (n+1)^s` for `s > 1`. -/
theorem summable_zeta_aux {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ s) := by
  have h := (Real.summable_one_div_nat_rpow (p := s)).2 hs
  have h2 := (summable_nat_add_iff 1).2 h
  refine h2.congr fun k ↦ ?_
  simp

/-- **`η(s) = (1 - 2^{1-s}) ζ(s)`** for `s > 1`, with `ζ(s) = ∑ (n+1)^{-s}`. -/
theorem tendsto_partialEta_of_one_lt {s : ℝ} (hs : 1 < s) :
    Tendsto (partialEta s) atTop
      (𝓝 ((1 - (2 : ℝ) ^ (1 - s)) * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s)) := by
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, a = fun k : ℕ ↦ 1 / ((k : ℝ) + 1) ^ s := ⟨_, rfl⟩
  have hgoal : ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s = ∑' n : ℕ, a n := by rw [ha]
  rw [hgoal]
  have hsum : Summable a := by rw [ha]; exact summable_zeta_aux hs
  have ha0 : ∀ k, 0 ≤ a k := fun k ↦ by rw [ha]; positivity
  have hb : Summable (fun k : ℕ ↦ (-1 : ℝ) ^ k * a k) := by
    refine hsum.of_norm_bounded fun k ↦ ?_
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_of_nonneg (ha0 k)]
  have hinj2 : Function.Injective (fun j : ℕ ↦ 2 * j) := fun x y h ↦ by simpa using h
  have hinj2' : Function.Injective (fun j : ℕ ↦ 2 * j + 1) := fun x y h ↦ by simpa using h
  have hE : Summable (fun j : ℕ ↦ a (2 * j)) := hsum.comp_injective hinj2
  have hO : Summable (fun j : ℕ ↦ a (2 * j + 1)) := hsum.comp_injective hinj2'
  have hZ := tsum_even_add_odd (f := a) hE hO
  have hbE : Summable (fun j : ℕ ↦ (-1 : ℝ) ^ (2 * j) * a (2 * j)) := hb.comp_injective hinj2
  have hbO : Summable (fun j : ℕ ↦ (-1 : ℝ) ^ (2 * j + 1) * a (2 * j + 1)) :=
    hb.comp_injective hinj2'
  have hA := tsum_even_add_odd (f := fun k : ℕ ↦ (-1 : ℝ) ^ k * a k) hbE hbO
  have hev : ∀ j : ℕ, (-1 : ℝ) ^ (2 * j) * a (2 * j) = a (2 * j) := fun j ↦ by
    rw [pow_mul]; simp
  have hod : ∀ j : ℕ, (-1 : ℝ) ^ (2 * j + 1) * a (2 * j + 1) = - a (2 * j + 1) := fun j ↦ by
    rw [pow_succ, pow_mul]; simp
  simp only [hev, hod, tsum_neg] at hA
  have hO' : ∑' j : ℕ, a (2 * j + 1) = (2 : ℝ) ^ (-s) * ∑' n : ℕ, a n := by
    rw [← tsum_mul_left]
    refine tsum_congr fun j ↦ ?_
    simp only [ha]
    have h1 : (((2 * j + 1 : ℕ) : ℝ) + 1) = 2 * ((j : ℝ) + 1) := by push_cast; ring
    rw [h1, Real.mul_rpow (by norm_num) (by positivity), Real.rpow_neg (by norm_num)]
    field_simp
  have h2s : (2 : ℝ) ^ (1 - s) = 2 * (2 : ℝ) ^ (-s) := by
    rw [sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_one]
  have hlim : HasSum (fun k : ℕ ↦ (-1 : ℝ) ^ k * a k) (∑' k : ℕ, (-1 : ℝ) ^ k * a k) :=
    hb.hasSum
  have hv : ∑' k : ℕ, (-1 : ℝ) ^ k * a k = (1 - (2 : ℝ) ^ (1 - s)) * ∑' n : ℕ, a n := by
    rw [← hA, h2s]
    rw [hO'] at hZ ⊢
    linarith
  rw [← hv]
  have := hlim.tendsto_sum_nat
  refine this.congr fun N ↦ ?_
  unfold partialEta
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [ha]
  exact mul_one_div _ _

/-- Partial sums of the circle series are `partialLi`, and the series is summable for `s > 1`. -/
theorem summable_circle_aux {s : ℝ} (hs : 1 < s) {z : ℂ} (hz : ‖z‖ = 1) :
    Summable (fun n : ℕ ↦ z ^ (n + 1) / ((((n : ℝ) + 1) ^ s : ℝ) : ℂ)) := by
  refine (summable_zeta_aux hs).of_norm_bounded fun n ↦ ?_
  rw [norm_div, norm_pow, hz, one_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-- **The floor of `Li_s` for `s > 1`**, on the whole unit circle (including `z = 1`):
`(1 - 2^{1-s}) ζ(s) ≤ ‖∑ z^{n+1} / (n+1)^s‖`. -/
theorem zeta_floor {s : ℝ} (hs : 1 < s) {z : ℂ} (hz : ‖z‖ = 1) :
    (1 - (2 : ℝ) ^ (1 - s)) * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s
      ≤ ‖∑' n : ℕ, z ^ (n + 1) / ((((n : ℝ) + 1) ^ s : ℝ) : ℂ)‖ := by
  have hsum := summable_circle_aux hs hz
  have hL : Tendsto (partialLi s z) atTop
      (𝓝 (∑' n : ℕ, z ^ (n + 1) / ((((n : ℝ) + 1) ^ s : ℝ) : ℂ))) :=
    hsum.hasSum.tendsto_sum_nat
  by_cases hz1 : z = 1
  · subst hz1
    have hpos : 0 < ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s :=
      (summable_zeta_aux hs).tsum_pos (fun n ↦ by positivity) 0 (by positivity)
    have heq : ∑' n : ℕ, (1 : ℂ) ^ (n + 1) / ((((n : ℝ) + 1) ^ s : ℝ) : ℂ)
        = ((∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum]
      refine tsum_congr fun n ↦ ?_
      simp
    rw [heq, Complex.norm_real, Real.norm_of_nonneg hpos.le]
    have : (0 : ℝ) < (2 : ℝ) ^ (1 - s) := by positivity
    nlinarith
  · have := polylog_circle_floor (by linarith) hz hL (tendsto_partialEta_of_one_lt hs)
    exact this

/-- **The zeta state never gets closer to orthogonality than `1 - 2^{1-s}`.** With populations
`p n = (n+1)^{-s} / ζ(s)` on the levels `n + 1`, the autocorrelation at every time `θ` has modulus at
least `1 - 2^{1-s}`. -/
theorem zetaState_floor {s : ℝ} (hs : 1 < s) (θ : ℝ) :
    1 - (2 : ℝ) ^ (1 - s) ≤
      ‖∑' n : ℕ, (((1 / ((n : ℝ) + 1) ^ s) / ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ s : ℝ) : ℂ) *
          Complex.exp (-(((n : ℝ) + 1) * θ : ℝ) * I)‖ := by
  set ζ : ℝ := ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ s with hζ
  have hpos : 0 < ζ :=
    (summable_zeta_aux hs).tsum_pos (fun n ↦ by positivity) 0 (by positivity)
  set z : ℂ := Complex.exp (-(θ : ℂ) * I) with hzdef
  have hz : ‖z‖ = 1 := by
    rw [hzdef, show -(θ : ℂ) * I = ((-θ : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hterm : ∀ n : ℕ, (((1 / ((n : ℝ) + 1) ^ s) / ζ : ℝ) : ℂ) *
      Complex.exp (-(((n : ℝ) + 1) * θ : ℝ) * I)
      = ((ζ : ℂ))⁻¹ * (z ^ (n + 1) / ((((n : ℝ) + 1) ^ s : ℝ) : ℂ)) := by
    intro n
    have h1 : Complex.exp (-(((n : ℝ) + 1) * θ : ℝ) * I) = z ^ (n + 1) := by
      rw [hzdef, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [h1]
    simp only [Complex.ofReal_div, Complex.ofReal_one]
    ring
  rw [tsum_congr hterm, tsum_mul_left, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg hpos.le]
  rw [inv_mul_eq_div, le_div_iff₀ hpos]
  have := zeta_floor hs hz
  linarith

end Polylog
