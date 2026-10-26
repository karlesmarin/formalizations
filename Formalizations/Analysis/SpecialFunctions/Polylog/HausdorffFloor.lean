/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The antipodal floor of moment power series on the unit circle, and |Li_s| ≥ η(s)

For a finite measure μ and a function τ with values in [0, 1) almost everywhere, the power series of
the moments q_k = ∫ τ^k dμ, wherever it converges on the unit circle (at every z ≠ 1, by Dirichlet's
test), has modulus at least ∫ 1/(1 + τ) dμ, which is the sum of the alternating series of the
moments. With the measure x^(s−1) e^(−x)/Γ(s) dx and τ = e^(−x), the moments are (k+1)^(−s): for
every real s > 0 and every z ≠ 1 on the unit circle, the polylogarithm series converges and its sum
has modulus at least η(s), with equality at z = −1. The polylogarithm is handled through its partial
sums (partialLi), because for s ≤ 1 the convergence on the circle is only conditional. Classical
mathematics: a consequence of Fejér's theorem on four times monotone coefficients (Acta Sci. Math.
Szeged 8 (1937), p. 104); for s = 2 stated in Boyer–Parry, arXiv:2111.12226, Appendix A, Lemma 8.
Generalises Dilog.antipode_floor (finite mixtures of geometric populations).

## Main results

* `Polylog.one_div_one_add_le_re`: Re(1/(1 − xz)) ≥ 1/(1 + x) for x ∈ [0, 1), |z| = 1
* `Polylog.le_norm_of_tendsto`: the moment series, if it converges at |z| = 1, has modulus ≥ ∫ 1/(1 + τ) dμ
* `Polylog.tendsto_alternating`: the alternating series of the moments sums to ∫ 1/(1 + τ) dμ
* `Polylog.exists_tendsto_circle`: the moment series converges at every z ≠ 1 of the unit circle
* `Polylog.exists_tendsto_eta`: η(s) converges to a positive number for s > 0
* `Polylog.exists_tendsto_partialLi`: the series of Li_s converges at every z ≠ 1 of the unit circle, s > 0
* `Polylog.polylog_circle_floor`: η(s) ≤ |Li_s z| on the unit circle, s > 0, z ≠ 1
* `Polylog.polylog_neg_one`: Li_s(−1) = −η(s): the floor is attained

## References

* C. Marín, *The Clock That Never Ticks: a machine-checked path from the dilogarithm to quantum
  speed limits in Lean 4*, Zenodo (2026), doi:10.5281/zenodo.20675271, `thm:clock`.
-/

@[expose] public section

open Filter Topology Finset MeasureTheory Complex

namespace Polylog

/-- **The per-term bound.** For `x ∈ [0, 1)` and `z` on the unit circle,
`1 / (1 + x) ≤ Re (1 / (1 - x z))`; the gap is `x (1 - x) (1 + Re z) / ((1 + x) |1 - x z|²)`. -/
theorem one_div_one_add_le_re {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    1 / (1 + x) ≤ (1 / (1 - (x : ℂ) * z)).re := by
  have habs : |z.re| ≤ 1 := by have h := Complex.abs_re_le_norm z; rwa [hz] at h
  have hre_lb : -1 ≤ z.re := (abs_le.mp habs).1
  have hnsq : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  have h1px : (0 : ℝ) < 1 + x := by linarith
  have hzne : (1 - (x : ℂ) * z) ≠ 0 := by
    intro h
    have hxz : (x : ℂ) * z = 1 := by linear_combination -h
    have hnorm : ‖(x : ℂ) * z‖ = 1 := by rw [hxz]; simp
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0, hz, mul_one]
      at hnorm
    linarith
  have hD : (0 : ℝ) < Complex.normSq (1 - (x : ℂ) * z) := Complex.normSq_pos.mpr hzne
  have hre1 : (1 - (x : ℂ) * z).re = 1 - x * z.re := by
    rw [Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul]
  have him1 : (1 - (x : ℂ) * z).im = -(x * z.im) := by
    rw [Complex.sub_im, Complex.one_im, Complex.im_ofReal_mul]; ring
  have hDval : Complex.normSq (1 - (x : ℂ) * z) = 1 - 2 * x * z.re + x ^ 2 := by
    rw [Complex.normSq_apply, hre1, him1]
    have hz1 : z.re * z.re + z.im * z.im = 1 := by rw [← Complex.normSq_apply]; exact hnsq
    linear_combination x ^ 2 * hz1
  have hterm : (1 / (1 - (x : ℂ) * z)).re
      = (1 - x * z.re) / Complex.normSq (1 - (x : ℂ) * z) := by
    rw [one_div, Complex.inv_re, hre1]
  rw [hterm, hDval]
  have hDpos : (0 : ℝ) < 1 - 2 * x * z.re + x ^ 2 := by rw [← hDval]; exact hD
  rw [div_le_div_iff₀ h1px hDpos]
  nlinarith [mul_nonneg (mul_nonneg hx0 (show (0 : ℝ) ≤ 1 + z.re by linarith))
    (show (0 : ℝ) ≤ 1 - x by linarith)]

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] (τ : α → ℝ)

/-- The moments `∫ τ ^ k ∂μ`. -/
noncomputable def moment (k : ℕ) : ℝ := ∫ a, τ a ^ k ∂μ

omit [IsFiniteMeasure μ] in
/-- Auxiliary: `τ ^ k` is integrable when `0 ≤ τ < 1` a.e. -/
theorem integrable_pow_aux [IsFiniteMeasure μ] (hτm : Measurable τ) (hτ0 : ∀ᵐ a ∂μ, 0 ≤ τ a)
    (hτ1 : ∀ᵐ a ∂μ, τ a < 1) (k : ℕ) : Integrable (fun a ↦ τ a ^ k) μ := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) (hτm.pow_const k).aestronglyMeasurable ?_
  filter_upwards [hτ0, hτ1] with a h0 h1
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 k)]
  exact pow_le_one₀ h0 h1.le

/-- Auxiliary: bounded measurable functions are integrable (version for `1 / (1 + τ r)`). -/
theorem integrable_inv_aux (hτm : Measurable τ) (hτ0 : ∀ᵐ a ∂μ, 0 ≤ τ a) {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun a ↦ 1 / (1 + τ a * r)) μ := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
  · exact (measurable_const.div (measurable_const.add (hτm.mul_const r))).aestronglyMeasurable
  · filter_upwards [hτ0] with a h0
    have : 0 < 1 + τ a * r := by positivity
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [div_le_one this]; nlinarith [mul_nonneg h0 hr]

/-- Auxiliary: the moments tend to `0`. -/
theorem tendsto_moment_zero (hτm : Measurable τ) (hτ0 : ∀ᵐ a ∂μ, 0 ≤ τ a)
    (hτ1 : ∀ᵐ a ∂μ, τ a < 1) : Tendsto (moment μ τ) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := μ) (F := fun k a ↦ τ a ^ k)
    (f := fun _ ↦ (0 : ℝ)) (fun _ ↦ (1 : ℝ))
    (fun k ↦ (hτm.pow_const k).aestronglyMeasurable) (integrable_const _)
    (fun k ↦ by
      filter_upwards [hτ0, hτ1] with a h0 h1
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 k)]
      exact pow_le_one₀ h0 h1.le)
    (by
      filter_upwards [hτ0, hτ1] with a h0 h1
      exact tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1)
  simp only [integral_zero] at h
  exact h

/-- **The antipodal floor.** If the moment series converges at a point `z` of the unit circle, its sum
has modulus at least `∫ 1 / (1 + τ) ∂μ`. -/
theorem le_norm_of_tendsto (hτm : Measurable τ) (hτ0 : ∀ᵐ a ∂μ, 0 ≤ τ a) (hτ1 : ∀ᵐ a ∂μ, τ a < 1)
    {z : ℂ} (hz : ‖z‖ = 1) {F : ℂ}
    (hF : Tendsto (fun N ↦ ∑ k ∈ range N, (moment μ τ k : ℂ) * z ^ k) atTop (𝓝 F)) :
    ∫ a, 1 / (1 + τ a) ∂μ ≤ ‖F‖ := by
  -- Abel
  have hA := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hF
  rw [tendsto_map'_iff] at hA
  have hA' : Tendsto (fun r : ℝ ↦ ‖∑' n, (moment μ τ n : ℂ) * z ^ n * (r : ℂ) ^ n‖)
      (𝓝[<] 1) (𝓝 ‖F‖) := hA.norm
  -- the integral side
  have hI : Tendsto (fun r : ℝ ↦ ∫ a, 1 / (1 + τ a * r) ∂μ) (𝓝[<] 1)
      (𝓝 (∫ a, 1 / (1 + τ a) ∂μ)) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝[<] (1 : ℝ))
      (F := fun (r : ℝ) a ↦ 1 / (1 + τ a * r)) (f := fun a ↦ 1 / (1 + τ a))
      (fun _ ↦ (1 : ℝ))
      (Eventually.of_forall fun r ↦ (measurable_const.div
        (measurable_const.add (hτm.mul_const r))).aestronglyMeasurable)
      (by
        filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
        filter_upwards [hτ0] with a h0
        have : 0 < 1 + τ a * r := by have := hr.1; positivity
        rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_one this]
        nlinarith [mul_nonneg h0 hr.1.le])
      (integrable_const _)
      (by
        filter_upwards [hτ0] with a h0
        have hc : ContinuousAt (fun r : ℝ ↦ 1 / (1 + τ a * r)) 1 := by
          apply ContinuousAt.div continuousAt_const (by fun_prop)
          have : 0 < 1 + τ a * 1 := by positivity
          exact this.ne'
        simpa using hc.tendsto.mono_left nhdsWithin_le_nhds)
    exact this
  -- the key inequality for r ∈ (0,1)
  have key : ∀ r : ℝ, 0 < r → r < 1 →
      ∫ a, 1 / (1 + τ a * r) ∂μ ≤ ‖∑' n, (moment μ τ n : ℂ) * z ^ n * (r : ℂ) ^ n‖ := by
    intro r hr0 hr1
    have hrz : ‖(r : ℂ) * z‖ = r := by
      rw [norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    -- terms
    let G : ℕ → α → ℂ := fun k a ↦ ((τ a ^ k : ℝ) : ℂ) * ((r : ℂ) * z) ^ k
    have hGm : ∀ k, AEStronglyMeasurable (G k) μ := fun k ↦
      (((hτm.pow_const k).complex_ofReal).mul_const _).aestronglyMeasurable
    have hGi : ∀ k, Integrable (G k) μ := fun k ↦
      (integrable_pow_aux μ τ hτm hτ0 hτ1 k).ofReal.mul_const _
    have hGint : ∀ k, ∫ a, G k a ∂μ = (moment μ τ k : ℂ) * z ^ k * (r : ℂ) ^ k := by
      intro k
      simp only [G]
      rw [integral_mul_const, integral_complex_ofReal, mul_pow]
      simp only [moment]; ring
    have hGnorm : ∀ k, ∫ a, ‖G k a‖ ∂μ ≤ μ.real Set.univ * r ^ k := by
      intro k
      have : ∀ᵐ a ∂μ, ‖G k a‖ ≤ r ^ k := by
        filter_upwards [hτ0, hτ1] with a h0 h1
        simp only [G]
        rw [norm_mul, norm_pow, hrz, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (pow_nonneg h0 k)]
        calc τ a ^ k * r ^ k ≤ 1 * r ^ k :=
              mul_le_mul_of_nonneg_right (pow_le_one₀ h0 h1.le) (by positivity)
          _ = r ^ k := one_mul _
      calc ∫ a, ‖G k a‖ ∂μ ≤ ∫ _, r ^ k ∂μ :=
            integral_mono_ae (hGi k).norm (integrable_const _) this
        _ = μ.real Set.univ * r ^ k := by
            rw [integral_const, smul_eq_mul]
    have hsum : Summable fun k ↦ ∫ a, ‖G k a‖ ∂μ :=
      Summable.of_nonneg_of_le (fun k ↦ integral_nonneg fun a ↦ norm_nonneg _) hGnorm
        ((summable_geometric_of_lt_one hr0.le hr1).mul_left _)
    have hHS := hasSum_integral_of_summable_integral_norm hGi hsum
    simp_rw [hGint] at hHS
    -- the pointwise sum
    have hpt : ∀ᵐ a ∂μ, ∑' k, G k a = 1 / (1 - (τ a : ℂ) * ((r : ℂ) * z)) := by
      filter_upwards [hτ0, hτ1] with a h0 h1
      have hn : ‖(τ a : ℂ) * ((r : ℂ) * z)‖ < 1 := by
        rw [norm_mul, hrz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
        nlinarith
      have := tsum_geometric_of_norm_lt_one hn
      rw [one_div, ← this]
      refine tsum_congr fun k ↦ ?_
      simp only [G]; push_cast; ring
    have hEq : ∑' n, (moment μ τ n : ℂ) * z ^ n * (r : ℂ) ^ n
        = ∫ a, 1 / (1 - (τ a : ℂ) * ((r : ℂ) * z)) ∂μ := by
      rw [hHS.tsum_eq]
      exact integral_congr_ae hpt
    rw [hEq]
    -- integrability of the resolvent
    have hint : Integrable (fun a ↦ 1 / (1 - (τ a : ℂ) * ((r : ℂ) * z))) μ := by
      refine Integrable.mono' (integrable_const (1 / (1 - r))) ?_ ?_
      · exact (measurable_const.div (measurable_const.sub
          (hτm.complex_ofReal.mul_const _))).aestronglyMeasurable
      · filter_upwards [hτ0, hτ1] with a h0 h1
        have hn : ‖(τ a : ℂ) * ((r : ℂ) * z)‖ ≤ r := by
          rw [norm_mul, hrz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
          nlinarith
        have h2 : 1 - r ≤ ‖1 - (τ a : ℂ) * ((r : ℂ) * z)‖ := by
          have := norm_sub_norm_le (1 : ℂ) ((τ a : ℂ) * ((r : ℂ) * z))
          rw [norm_one] at this; linarith
        rw [norm_div, norm_one]
        exact one_div_le_one_div_of_le (by linarith) h2
    calc ∫ a, 1 / (1 + τ a * r) ∂μ
        ≤ ∫ a, (1 / (1 - (τ a : ℂ) * ((r : ℂ) * z))).re ∂μ := by
          refine integral_mono_ae (integrable_inv_aux μ τ hτm hτ0 hr0.le)
            (by simpa using (Complex.reCLM.integrable_comp hint)) ?_
          filter_upwards [hτ0, hτ1] with a h0 h1
          have := one_div_one_add_le_re (x := τ a * r) (by positivity)
            (by nlinarith) (z := z) hz
          have e : ((τ a * r : ℝ) : ℂ) * z = (τ a : ℂ) * ((r : ℂ) * z) := by push_cast; ring
          rw [e] at this
          exact this
      _ = (∫ a, 1 / (1 - (τ a : ℂ) * ((r : ℂ) * z)) ∂μ).re := integral_re hint
      _ ≤ _ := by
          have := Complex.re_le_norm (∫ a, 1 / (1 - (τ a : ℂ) * ((r : ℂ) * z)) ∂μ)
          exact this
  refine le_of_tendsto_of_tendsto hI hA' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  exact key r hr.1 hr.2

/-- The alternating series of the moments sums to `∫ 1 / (1 + τ) ∂μ`: the floor is the value of the
series at `z = -1`. -/
theorem tendsto_alternating (hτm : Measurable τ) (hτ0 : ∀ᵐ a ∂μ, 0 ≤ τ a)
    (hτ1 : ∀ᵐ a ∂μ, τ a < 1) :
    Tendsto (fun N ↦ ∑ k ∈ range N, (-1) ^ k * moment μ τ k) atTop
      (𝓝 (∫ a, 1 / (1 + τ a) ∂μ)) := by
  have hsum : ∀ N, ∑ k ∈ range N, (-1 : ℝ) ^ k * moment μ τ k
      = ∫ a, ∑ k ∈ range N, (-τ a) ^ k ∂μ := by
    intro N
    have hnp : ∀ (k : ℕ) (a : α), (-τ a) ^ k = (-1 : ℝ) ^ k * τ a ^ k := by
      intro k a; rw [← neg_one_mul, mul_pow]
    have hi : ∀ k, Integrable (fun a ↦ (-τ a) ^ k) μ := by
      intro k
      simp_rw [hnp k]
      exact (integrable_pow_aux μ τ hτm hτ0 hτ1 k).const_mul ((-1 : ℝ) ^ k)
    rw [integral_finsetSum _ (fun k _ ↦ hi k)]
    refine sum_congr rfl fun k _ ↦ ?_
    simp_rw [hnp k]
    rw [integral_const_mul]
    rfl
  simp_rw [hsum]
  refine tendsto_integral_of_dominated_convergence (fun _ ↦ (2 : ℝ)) ?_ (integrable_const _) ?_ ?_
  · intro N
    exact (Finset.measurable_sum _ fun k _ ↦ (hτm.neg.pow_const k)).aestronglyMeasurable
  · intro N
    filter_upwards [hτ0, hτ1] with a h0 h1
    have hne : -τ a ≠ 1 := by linarith
    rw [geom_sum_eq hne, Real.norm_eq_abs, abs_div]
    have hden : 1 ≤ |-τ a - 1| := by
      rw [abs_of_nonpos (by linarith)]; linarith
    have hnum : |(-τ a) ^ N - 1| ≤ 2 := by
      calc |(-τ a) ^ N - 1| ≤ |(-τ a) ^ N| + |(1 : ℝ)| := abs_sub _ _
        _ ≤ 1 + 1 := by
            rw [abs_pow, abs_neg, abs_of_nonneg h0, abs_one]
            exact add_le_add (pow_le_one₀ h0 h1.le) le_rfl
        _ = 2 := by norm_num
    calc |(-τ a) ^ N - 1| / |-τ a - 1| ≤ |(-τ a) ^ N - 1| :=
          div_le_self (abs_nonneg _) hden
      _ ≤ 2 := hnum
  · filter_upwards [hτ0, hτ1] with a h0 h1
    have h := (hasSum_geometric_of_abs_lt_one (r := -τ a)
      (by rw [abs_neg, abs_of_nonneg h0]; exact h1)).tendsto_sum_nat
    have e : (1 - -τ a)⁻¹ = 1 / (1 + τ a) := by rw [one_div]; ring_nf
    rw [e] at h
    exact h

/-- The moment series converges at every point `z ≠ 1` of the unit circle (Dirichlet's test: the
moments decrease to `0`). -/
theorem exists_tendsto_circle (hτm : Measurable τ) (hτ0 : ∀ᵐ a ∂μ, 0 ≤ τ a)
    (hτ1 : ∀ᵐ a ∂μ, τ a < 1) {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ∃ F, Tendsto (fun N ↦ ∑ k ∈ range N, (moment μ τ k : ℂ) * z ^ k) atTop (𝓝 F) := by
  have hanti : Antitone (moment μ τ) := by
    refine antitone_nat_of_succ_le fun k ↦ ?_
    refine integral_mono_ae (integrable_pow_aux μ τ hτm hτ0 hτ1 (k + 1))
      (integrable_pow_aux μ τ hτm hτ0 hτ1 k) ?_
    filter_upwards [hτ0, hτ1] with a h0 h1
    exact pow_le_pow_of_le_one h0 h1.le (Nat.le_succ k)
  have hb : ∀ n, ‖∑ i ∈ range n, z ^ i‖ ≤ 2 / ‖z - 1‖ := by
    intro n
    rw [geom_sum_eq hz1, norm_div]
    have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
    refine div_le_div_of_nonneg_right ?_ hpos.le
    calc ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz]; norm_num
  have hc := hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded
    (tendsto_moment_zero μ τ hτm hτ0 hτ1) (z := fun i ↦ z ^ i) hb
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨F, by simpa [Complex.real_smul] using hF⟩

/-- The partial sums of the polylogarithm series `∑_{n ≥ 1} z ^ n / n ^ s`. -/
noncomputable def partialLi (s : ℝ) (z : ℂ) (N : ℕ) : ℂ :=
  ∑ k ∈ range N, z ^ (k + 1) / ((((k : ℝ) + 1) ^ s : ℝ) : ℂ)

/-- The partial sums of `η(s) = ∑_{n ≥ 1} (-1) ^ (n - 1) / n ^ s`. -/
noncomputable def partialEta (s : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ range N, (-1) ^ k / ((k : ℝ) + 1) ^ s

/-- `η(s)` converges for `s > 0`, to a positive number. -/
theorem exists_tendsto_eta {s : ℝ} (hs : 0 < s) :
    ∃ e, Tendsto (partialEta s) atTop (𝓝 e) ∧ 0 < e := by
  set f : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1) ^ s with hf
  have hanti : Antitone f := by
    intro a b hab
    have ha : (0 : ℝ) < (a : ℝ) + 1 := by positivity
    have hab' : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hab 1
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos ha s)
      (Real.rpow_le_rpow ha.le hab' hs.le)
  have hzero : Tendsto f atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ ↦ ((k : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have h2 := (tendsto_rpow_atTop hs).comp h1
    exact h2.inv_tendsto_atTop.congr fun k ↦ by simp [hf, Function.comp_def]
  have hpe : ∀ N, partialEta s N = ∑ i ∈ range N, (-1) ^ i * f i := by
    intro N
    simp only [partialEta, hf]
    exact Finset.sum_congr rfl fun i _ ↦ (mul_one_div _ _).symm
  obtain ⟨l, hl⟩ := hanti.tendsto_alternating_series_of_tendsto_zero hzero
  have hl' : Tendsto (partialEta s) atTop (𝓝 l) := by
    have : partialEta s = fun n ↦ ∑ i ∈ range n, (-1) ^ i * f i := funext hpe
    rw [this]; exact hl
  refine ⟨l, hl', ?_⟩
  have h2 := hanti.alternating_series_le_tendsto hl 1
  have h3 : 0 < ∑ i ∈ range (2 * 1), (-1 : ℝ) ^ i * f i := by
    have h4 : (1 : ℝ) < 2 ^ s := Real.one_lt_rpow (by norm_num) hs
    simp [Finset.sum_range_succ, hf]
    rw [one_add_one_eq_two, inv_lt_one_iff₀]; right; exact h4
  exact lt_of_lt_of_le h3 h2

/-- The floor is attained at `z = -1`: there `Li_s (-1) = -η(s)`. -/
theorem polylog_neg_one {s : ℝ} {e : ℝ} (he : Tendsto (partialEta s) atTop (𝓝 e)) :
    Tendsto (partialLi s (-1)) atTop (𝓝 (-(e : ℂ))) := by
  have h := ((Complex.continuous_ofReal.tendsto e).comp he).neg
  refine h.congr fun N ↦ ?_
  simp only [partialLi, partialEta, Function.comp_apply, Complex.ofReal_sum,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [pow_succ, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one]
  ring

/-! ### The Gamma measure -/

/-- The measure `x ^ (s - 1) e ^ (-x) / Γ(s) dx` on `(0, ∞)`. -/
noncomputable def gammaMeasure (s : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioi 0)).withDensity
    (fun x ↦ ENNReal.ofReal (Real.exp (-x) * x ^ (s - 1) / Real.Gamma s))

theorem gammaMeasure_univ {s : ℝ} (hs : 0 < s) : gammaMeasure s Set.univ = 1 := by
  unfold gammaMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal]
  · have : ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * x ^ (s - 1) / Real.Gamma s = 1 := by
      rw [integral_div, ← Real.Gamma_eq_integral hs]
      exact div_self (Real.Gamma_pos_of_pos hs).ne'
    rw [this]; simp
  · exact (Real.GammaIntegral_convergent hs).div_const _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have := Real.Gamma_pos_of_pos hs
    have : 0 < x := hx
    positivity

theorem gammaMeasure_isFinite {s : ℝ} (hs : 0 < s) : IsFiniteMeasure (gammaMeasure s) :=
  ⟨by rw [gammaMeasure_univ hs]; exact ENNReal.one_lt_top⟩

theorem gamma_ae {s : ℝ} (p : ℝ → Prop) (hp : ∀ x : ℝ, 0 < x → p x) :
    ∀ᵐ x ∂(gammaMeasure s), p x := by
  refine (withDensity_absolutelyContinuous _ _).ae_le ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact hp x hx

theorem gamma_moment {s : ℝ} (hs : 0 < s) (k : ℕ) :
    moment (gammaMeasure s) (fun x ↦ Real.exp (-x)) k = (((k : ℝ) + 1) ^ s)⁻¹ := by
  unfold moment gammaMeasure
  have hmeas : Measurable (fun x : ℝ ↦
      ENNReal.ofReal (Real.exp (-x) * x ^ (s - 1) / Real.Gamma s)) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  rw [integral_withDensity_eq_integral_toReal_smul hmeas
    (ae_of_all _ fun x ↦ ENNReal.ofReal_lt_top)]
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hG := Real.Gamma_pos_of_pos hs
  have h1 : ∫ x in Set.Ioi (0 : ℝ), (ENNReal.ofReal (Real.exp (-x) * x ^ (s - 1) /
      Real.Gamma s)).toReal • Real.exp (-x) ^ k =
      ∫ x in Set.Ioi (0 : ℝ), (1 / Real.Gamma s) *
        (x ^ (s - 1) * Real.exp (-(((k : ℝ) + 1) * x))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
    have hx' : 0 < x := hx
    have hnn : 0 ≤ Real.exp (-x) * x ^ (s - 1) / Real.Gamma s := by positivity
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal hnn]
    have e : Real.exp (-(((k : ℝ) + 1) * x)) = Real.exp (-x) * Real.exp (-x) ^ k := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
    rw [e]; ring
  rw [h1, integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hs hk]
  rw [Real.div_rpow zero_le_one hk.le, Real.one_rpow]
  field_simp

theorem gamma_hli {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : ‖z‖ = 1) (N : ℕ) :
    z⁻¹ * partialLi s z N =
      ∑ k ∈ range N, (moment (gammaMeasure s) (fun x ↦ Real.exp (-x)) k : ℂ) * z ^ k := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  unfold partialLi
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [gamma_moment hs k]
  generalize ((((k : ℝ) + 1) ^ s : ℝ)) = c
  rw [Complex.ofReal_inv, div_eq_mul_inv, pow_succ]
  have := inv_mul_cancel₀ hz0
  linear_combination (z ^ k * (c : ℂ)⁻¹) * this

theorem gamma_eta {s : ℝ} (hs : 0 < s) (N : ℕ) :
    partialEta s N =
      ∑ k ∈ range N, (-1) ^ k * moment (gammaMeasure s) (fun x ↦ Real.exp (-x)) k := by
  unfold partialEta
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [gamma_moment hs k, div_eq_mul_inv]

/-- The polylogarithm series converges at every `z ≠ 1` of the unit circle, for `s > 0`. -/
theorem exists_tendsto_partialLi {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ∃ L, Tendsto (partialLi s z) atTop (𝓝 L) := by
  have := gammaMeasure_isFinite hs
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  obtain ⟨F, hF⟩ := exists_tendsto_circle (gammaMeasure s) (fun x : ℝ ↦ Real.exp (-x))
    (by fun_prop) (gamma_ae _ fun x _ ↦ (Real.exp_pos _).le)
    (gamma_ae _ fun x hx ↦ by simpa using Real.exp_lt_exp.mpr (show -x < 0 by linarith)) hz hz1
  refine ⟨z * F, (hF.const_mul z).congr fun N ↦ ?_⟩
  rw [← gamma_hli hs hz N, ← mul_assoc, mul_inv_cancel₀ hz0, one_mul]

/-- **The floor of the polylogarithm on the unit circle.** For real `s > 0` and `z ≠ 1` on the unit
circle, `η(s) ≤ |Li_s z|`. -/
theorem polylog_circle_floor {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : ‖z‖ = 1) {L : ℂ}
    (hL : Tendsto (partialLi s z) atTop (𝓝 L)) {e : ℝ} (he : Tendsto (partialEta s) atTop (𝓝 e)) :
    e ≤ ‖L‖ := by
  have := gammaMeasure_isFinite hs
  have hτm : Measurable (fun x : ℝ ↦ Real.exp (-x)) := by fun_prop
  have h0 : ∀ᵐ x ∂(gammaMeasure s), 0 ≤ Real.exp (-x) :=
    gamma_ae _ fun x _ ↦ (Real.exp_pos _).le
  have h1 : ∀ᵐ x ∂(gammaMeasure s), Real.exp (-x) < 1 :=
    gamma_ae _ fun x hx ↦ by simpa using Real.exp_lt_exp.mpr (show -x < 0 by linarith)
  have hF := hL.const_mul z⁻¹
  have hF' : Tendsto (fun N ↦ ∑ k ∈ range N,
      (moment (gammaMeasure s) (fun x ↦ Real.exp (-x)) k : ℂ) * z ^ k) atTop (𝓝 (z⁻¹ * L)) :=
    hF.congr fun N ↦ gamma_hli hs hz N
  have hfl := le_norm_of_tendsto (gammaMeasure s) _ hτm h0 h1 hz hF'
  have halt := tendsto_alternating (gammaMeasure s) _ hτm h0 h1
  have he' : Tendsto (partialEta s) atTop (𝓝 (∫ a, 1 / (1 + Real.exp (-a)) ∂(gammaMeasure s))) :=
    halt.congr fun N ↦ (gamma_eta hs N).symm
  rw [tendsto_nhds_unique he he']
  simpa [hz] using hfl

end Polylog
