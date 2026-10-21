/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.Analysis.SpecialFunctions.Dilogarithm.ComplexBoundary
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The dilogarithm stays away from zero on the unit circle

On the unit circle `‖Li₂ z‖ ≥ π²/12 = |Li₂(−1)|`: the minimum modulus sits at the antipode. Hence the
weight-2 zeta state (populations `6/(π² n²)` on the levels `n`) never gets halfway to an orthogonal state,
`|S(θ)| ≥ 1/2` for every `θ`.

The proof writes `Li₂(w) = w ∫∫_{(0,1)²} dx dy / (1 − xyw)` on the open disk (the moments
`∫∫ (xy)ⁿ = 1/(n+1)²` and a sum–integral exchange), bounds each mode by
`Re (1 − tz)⁻¹ ≥ (1 + t)⁻¹` for `t ∈ [0,1)`, `‖z‖ = 1`, which gives `‖Li₂(rz)‖ ≥ −Li₂(−r)` for
`r < 1`, and lets `r → 1⁻` by continuity of `Li₂` on the closed disk.

## Main results

* `Dilog.Li₂c_eq_mul_integral`: the integral representation on the open unit disk.
* `Dilog.inv_one_add_le_re_inv`: the per-mode floor.
* `Dilog.norm_Li₂c_ge`: `π²/12 ≤ ‖Li₂c z‖` for `‖z‖ = 1`.
* `Dilog.zetaState_norm_ge_half`: `1/2 ≤ (6/π²) ‖Li₂c (e^{iθ})‖`.
-/

@[expose] public section

open MeasureTheory Set Complex Filter Topology
open scoped Real

noncomputable section

namespace Dilog

/-- The open unit square. -/
def unitSq : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioo 0 1

theorem measurableSet_unitSq : MeasurableSet unitSq := measurableSet_Ioo.prod measurableSet_Ioo

theorem volume_unitSq_ne_top : volume unitSq ≠ ⊤ := by
  rw [unitSq, Measure.volume_eq_prod, Measure.prod_prod]
  simp [Real.volume_Ioo]

instance : IsFiniteMeasure (volume.restrict unitSq) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact volume_unitSq_ne_top.lt_top⟩

theorem mem_unitSq {p : ℝ × ℝ} (hp : p ∈ unitSq) : 0 < p.1 * p.2 ∧ p.1 * p.2 < 1 := by
  obtain ⟨⟨a0, a1⟩, ⟨b0, b1⟩⟩ := hp
  exact ⟨mul_pos a0 b0, by nlinarith⟩

/-- `∫∫_{(0,1)²} (xy)ⁿ = 1/(n+1)²`. -/
theorem integral_mul_pow_unitSq (n : ℕ) :
    ∫ p in unitSq, (p.1 * p.2) ^ n = 1 / ((n : ℝ) + 1) ^ 2 := by
  have h1 : ∫ x in Ioo (0 : ℝ) 1, x ^ n = 1 / ((n : ℝ) + 1) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, integral_pow]
    simp
  simp_rw [mul_pow]
  rw [unitSq, Measure.volume_eq_prod, setIntegral_prod_mul (fun x : ℝ => x ^ n) (fun y : ℝ => y ^ n), h1]
  field_simp

/-- The per-mode floor: for `t ∈ [0, 1)` and `‖z‖ = 1`, `Re (1 - t z)⁻¹ ≥ (1 + t)⁻¹`. -/
theorem inv_one_add_le_re_inv {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    (1 + t)⁻¹ ≤ ((1 - (t : ℂ) * z)⁻¹).re := by
  have hr : -1 ≤ z.re := by
    have := Complex.abs_re_le_norm z; rw [hz] at this; exact (abs_le.mp this).1
  have hsq : z.re * z.re + z.im * z.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hz]; norm_num
  have hD : Complex.normSq (1 - (t : ℂ) * z) = 1 - 2 * t * z.re + t ^ 2 := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul, Complex.sub_im, Complex.one_im,
      Complex.im_ofReal_mul]
    linear_combination t ^ 2 * hsq
  have hr' : z.re ≤ 1 := by
    have := Complex.abs_re_le_norm z; rw [hz] at this; exact (abs_le.mp this).2
  have htr : t * z.re ≤ t := by nlinarith
  have hDpos : 0 < 1 - 2 * t * z.re + t ^ 2 := by nlinarith [pow_pos (by linarith : (0 : ℝ) < 1 - t) 2]
  rw [Complex.inv_re, hD]
  simp only [Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul]
  rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) hDpos]
  nlinarith [mul_nonneg (mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 1 + z.re)) (by linarith : (0 : ℝ) ≤ 1 - t)]

/-- `‖(1 - q w)⁻¹‖ ≤ (1 - ‖w‖)⁻¹` for `q ∈ (0, 1)` and `‖w‖ < 1`. -/
theorem norm_inv_one_sub_le {q : ℝ} (h0 : 0 < q) (h1 : q < 1) {w : ℂ} (hw : ‖w‖ < 1) :
    ‖(1 - (q : ℂ) * w)⁻¹‖ ≤ (1 - ‖w‖)⁻¹ := by
  have hqw : ‖(q : ℂ) * w‖ ≤ ‖w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0]
    exact mul_le_of_le_one_left (norm_nonneg w) h1.le
  have hlow : 1 - ‖w‖ ≤ ‖1 - (q : ℂ) * w‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((q : ℂ) * w)
    rw [norm_one] at this
    linarith
  rw [norm_inv]
  exact inv_anti₀ (by linarith) hlow

theorem aestronglyMeasurable_inv_one_sub (w : ℂ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => (1 - ((p.1 * p.2 : ℝ) : ℂ) * w)⁻¹) (volume.restrict unitSq) := by
  exact (by fun_prop : Measurable fun p : ℝ × ℝ => (1 - ((p.1 * p.2 : ℝ) : ℂ) * w)⁻¹).aestronglyMeasurable

/-- **`Li₂(w) = w ∫∫_{(0,1)²} dx dy / (1 - xyw)`** on the open unit disk. -/
theorem Li₂c_eq_mul_integral {w : ℂ} (hw : ‖w‖ < 1) :
    Li₂c w = w * ∫ p in unitSq, (1 - ((p.1 * p.2 : ℝ) : ℂ) * w)⁻¹ := by
  set F : ℕ → ℝ × ℝ → ℂ := fun n p => (((p.1 * p.2 : ℝ) : ℂ) * w) ^ n with hF
  have hmeas : ∀ n, AEStronglyMeasurable (F n) (volume.restrict unitSq) := fun n =>
    (by fun_prop : Continuous (F n)).aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ p ∂(volume.restrict unitSq), ‖F n p‖ ≤ ‖w‖ ^ n := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_unitSq] with p hp
    obtain ⟨h0, h1⟩ := mem_unitSq hp
    simp only [hF, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [← abs_mul, abs_of_pos h0]
    exact pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_left (norm_nonneg w) h1.le) n
  have hint : ∀ n, Integrable (F n) (volume.restrict unitSq) := fun n =>
    Integrable.of_bound (hmeas n) _ (hbound n)
  have hnorm_sum : Summable fun n => ∫ p in unitSq, ‖F n p‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun p => norm_nonneg _) (fun n => ?_)
      ((summable_geometric_of_lt_one (norm_nonneg w) hw).mul_right (volume.real unitSq))
    calc ∫ p in unitSq, ‖F n p‖ ≤ ∫ p in unitSq, ‖w‖ ^ n :=
          integral_mono_ae (hint n).norm (integrable_const _) (hbound n)
      _ = ‖w‖ ^ n * volume.real unitSq := by rw [setIntegral_const, smul_eq_mul, mul_comm]
  have hsum := hasSum_integral_of_summable_integral_norm hint hnorm_sum
  have hval : ∀ n : ℕ, ∫ p in unitSq, F n p = w ^ n / ((n : ℂ) + 1) ^ 2 := by
    intro n
    have : (fun p : ℝ × ℝ => F n p) = fun p => (((p.1 * p.2) ^ n : ℝ) : ℂ) * w ^ n := by
      funext p; simp only [hF]; push_cast; ring
    rw [this, integral_mul_const, integral_complex_ofReal, integral_mul_pow_unitSq]
    push_cast; ring
  have hlim : ∫ p in unitSq, (∑' n, F n p) = ∫ p in unitSq, (1 - ((p.1 * p.2 : ℝ) : ℂ) * w)⁻¹ := by
    refine setIntegral_congr_fun measurableSet_unitSq fun p hp => ?_
    obtain ⟨h0, h1⟩ := mem_unitSq hp
    have : ‖((p.1 * p.2 : ℝ) : ℂ) * w‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0]
      nlinarith [norm_nonneg w]
    exact tsum_geometric_of_norm_lt_one this
  rw [Li₂c, ← hlim, ← hsum.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [hval]
  ring

theorem Li₂c_ofReal (x : ℝ) : Li₂c (x : ℂ) = (Li₂ x : ℂ) := by
  rw [Li₂c, Li₂, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  push_cast
  ring

theorem neg_Li₂_neg_eq {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    -Li₂ (-r) = r * ∫ p in unitSq, (1 + p.1 * p.2 * r)⁻¹ := by
  have hw : ‖((-r : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hr0]; exact hr1
  have h := Li₂c_eq_mul_integral hw
  rw [Li₂c_ofReal] at h
  have hc : (fun p : ℝ × ℝ => (1 - ((p.1 * p.2 : ℝ) : ℂ) * ((-r : ℝ) : ℂ))⁻¹)
      = fun p => (((1 + p.1 * p.2 * r)⁻¹ : ℝ) : ℂ) := by
    funext p; push_cast; ring
  rw [hc, integral_complex_ofReal] at h
  have h' : Li₂ (-r) = -r * ∫ p in unitSq, (1 + p.1 * p.2 * r)⁻¹ := by exact_mod_cast h
  linarith

theorem floor_of_lt_one {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    -Li₂ (-r) ≤ ‖Li₂c ((r : ℂ) * z)‖ := by
  have hnr : ‖(r : ℂ) * z‖ = r := by
    rw [norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have hw : ‖(r : ℂ) * z‖ < 1 := by rw [hnr]; exact hr1
  set f : ℝ × ℝ → ℂ := fun p => (1 - ((p.1 * p.2 : ℝ) : ℂ) * ((r : ℂ) * z))⁻¹ with hf
  have hbd : ∀ᵐ p ∂(volume.restrict unitSq), ‖f p‖ ≤ (1 - ‖(r : ℂ) * z‖)⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_unitSq] with p hp
    obtain ⟨h0, h1⟩ := mem_unitSq hp
    exact norm_inv_one_sub_le h0 h1 hw
  have hfi : Integrable f (volume.restrict unitSq) :=
    Integrable.of_bound (aestronglyMeasurable_inv_one_sub _) _ hbd
  have hgi : Integrable (fun p : ℝ × ℝ => (1 + p.1 * p.2 * r)⁻¹) (volume.restrict unitSq) := by
    refine Integrable.of_bound ?_ 1 ?_
    · exact (by fun_prop : Measurable fun p : ℝ × ℝ => (1 + p.1 * p.2 * r)⁻¹).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_unitSq] with p hp
      obtain ⟨h0, h1⟩ := mem_unitSq hp
      have hpos : 0 < 1 + p.1 * p.2 * r := by positivity
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
      exact inv_le_one_of_one_le₀ (by nlinarith)
  have hmono : ∫ p in unitSq, (1 + p.1 * p.2 * r)⁻¹ ≤ ∫ p in unitSq, (f p).re := by
    refine integral_mono_ae hgi hfi.re ?_
    filter_upwards [ae_restrict_mem measurableSet_unitSq] with p hp
    obtain ⟨h0, h1⟩ := mem_unitSq hp
    have := inv_one_add_le_re_inv (t := p.1 * p.2 * r) (by positivity) (by nlinarith) hz
    have he : ((p.1 * p.2 * r : ℝ) : ℂ) * z = ((p.1 * p.2 : ℝ) : ℂ) * ((r : ℂ) * z) := by
      push_cast; ring
    rw [he] at this
    exact this
  have hre : ∫ p in unitSq, (f p).re = (∫ p in unitSq, f p).re := by
    have := integral_re hfi
    simpa using this
  rw [Li₂c_eq_mul_integral hw, neg_Li₂_neg_eq hr0 hr1, norm_mul, hnr]
  calc r * ∫ p in unitSq, (1 + p.1 * p.2 * r)⁻¹ ≤ r * (∫ p in unitSq, f p).re :=
        mul_le_mul_of_nonneg_left (hmono.trans hre.le) hr0.le
    _ ≤ r * ‖∫ p in unitSq, f p‖ := mul_le_mul_of_nonneg_left (Complex.re_le_norm _) hr0.le

/-- **The antipode floor for the dilogarithm**: on the unit circle `‖Li₂ z‖ ≥ π²/12 = |Li₂(−1)|`. -/
theorem norm_Li₂c_ge {z : ℂ} (hz : ‖z‖ = 1) : π ^ 2 / 12 ≤ ‖Li₂c z‖ := by
  have hev : ∀ᶠ r in 𝓝[<] (1 : ℝ), r ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
  have hL : Tendsto (fun r : ℝ => -Li₂ (-r)) (𝓝[<] 1) (𝓝 (-Li₂ (-1))) := by
    have hc : ContinuousWithinAt Li₂ (Icc (-1) 1) (-1) := continuousOn_Li₂ (-1) ⟨le_refl _, by norm_num⟩
    have hneg : Tendsto (fun r : ℝ => -r) (𝓝[<] 1) (𝓝[Icc (-1) 1] (-1)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact ((continuous_neg.tendsto 1).mono_left nhdsWithin_le_nhds)
      · filter_upwards [hev] with r hr
        exact ⟨by linarith [hr.2], by linarith [hr.1]⟩
    exact (hc.tendsto.comp hneg).neg
  have hR : Tendsto (fun r : ℝ => ‖Li₂c ((r : ℂ) * z)‖) (𝓝[<] 1) (𝓝 ‖Li₂c z‖) := by
    have hc : ContinuousWithinAt Li₂c (Metric.closedBall 0 1) z := continuousOn_Li₂c z (by simp [hz])
    have hmul : Tendsto (fun r : ℝ => (r : ℂ) * z) (𝓝[<] 1) (𝓝[Metric.closedBall 0 1] z) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have h1 : Tendsto (fun r : ℝ => (r : ℂ) * z) (𝓝 1) (𝓝 (((1 : ℝ) : ℂ) * z)) :=
          (Complex.continuous_ofReal.tendsto 1).mul_const z
        simpa using h1.mono_left nhdsWithin_le_nhds
      · filter_upwards [hev] with r hr
        simp only [Metric.mem_closedBall, dist_zero_right, norm_mul, hz, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hr.1]
        exact hr.2.le
    exact (hc.tendsto.comp hmul).norm
  have hle := le_of_tendsto_of_tendsto hL hR (by
    filter_upwards [hev] with r hr
    exact floor_of_lt_one hr.1 hr.2 hz)
  rw [Li₂_neg_one, neg_div, neg_neg] at hle
  exact hle

/-- The weight-2 zeta state never gets halfway to an orthogonal state: `|S(θ)| ≥ 1/2` for every `θ`,
with `S(θ) = (6/π²) Li₂(e^{iθ})` (the paper's Figure 3, there certified numerically). -/
theorem zetaState_norm_ge_half (θ : ℝ) : 1 / 2 ≤ 6 / π ^ 2 * ‖Li₂c (Complex.exp ((θ : ℂ) * I))‖ := by
  have h := norm_Li₂c_ge (z := Complex.exp ((θ : ℂ) * I)) (Complex.norm_exp_ofReal_mul_I θ)
  have hπ : 0 < π ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hπ]
  nlinarith

end Dilog
