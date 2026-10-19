/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Tactic.Ring

/-!
# The Gaussian–exponential scale mixture is Laplace

A centered Gaussian whose variance `v` is exponentially distributed with rate `λ` has a Laplace
marginal with rate `√(2λ)`:

`∫_{v > 0} (2πv)^{-1/2} e^{-x²/(2v)} · λ e^{-λv} dv = (√(2λ)/2) e^{-√(2λ)|x|}`.

The proof reduces the integral to the Glasser (modified Bessel `K_{1/2}`) integral
`∫_{v > 0} v^{-1/2} e^{-a/v - bv} dv = √(π/b) e^{-2√(ab)}`, which is proved through the substitution
`v = √(a/b) s²` and Schlömilch's change of variables `u = s - 1/s`.

## Main definitions

* `Superstatistics.laplacePDFReal rate x`: the Laplace density `(rate/2) e^{-rate |x|}`.

## Main results

* `Superstatistics.laplacePDFReal_integral_eq_one`: the density integrates to `1`.
* `Superstatistics.combined`: `∫_{s > 0} (1 + s⁻²) e^{-c (s - s⁻¹)²} ds = √(π/c)`.
* `Superstatistics.glasser_integral`: the Glasser integral.
* `Superstatistics.gaussian_exponential_mixture_laplace`: the scale-mixture identity.

## References

* D. F. Andrews, C. L. Mallows, *Scale mixtures of normal distributions*, J. Roy. Statist. Soc.
  Ser. B 36 (1974) 99–102.
* M. L. Glasser, *A remarkable property of definite integrals*, Math. Comp. 40 (1983) 561.
-/

@[expose] public section

open MeasureTheory Real Set

namespace Superstatistics

/-! ## The Laplace density (Mathlib defines none)

`laplacePDFReal rate x = (rate/2)·exp(−rate·|x|)` is the pdf of the centred
Laplace (double-exponential) law with the given rate. -/
noncomputable def laplacePDFReal (rate x : ℝ) : ℝ :=
  rate / 2 * Real.exp (-(rate * |x|))

/-- The Laplace density is strictly positive for a positive rate. -/
theorem laplacePDFReal_pos {rate : ℝ} (x : ℝ) (h : 0 < rate) :
    0 < laplacePDFReal rate x := by
  unfold laplacePDFReal
  positivity

/-- Rate identification: the mixture output constant `√(2λ)/2` equals the
    density-normalisation constant `√(λ/2) = √(λ/2)`; i.e. the marginal density
    reads `√(λ/2)·exp(−√(2λ)·|x|)`, a Laplace of rate `√(2λ)`. -/
theorem laplace_rate_eq (lam : ℝ) :
    Real.sqrt (2 * lam) / 2 = Real.sqrt (lam / 2) := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hrw : (2 : ℝ) * lam = 4 * (lam / 2) := by ring
  rw [hrw, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h4]
  ring

/-- The claimed mixture RHS is exactly the Laplace pdf of rate `√(2λ)`. -/
theorem rhs_eq_laplacePDF (lam x : ℝ) :
    Real.sqrt (2 * lam) / 2 * Real.exp (-(Real.sqrt (2 * lam) * |x|))
      = laplacePDFReal (Real.sqrt (2 * lam)) x := rfl

/-! ## Normalisation (the RHS is a genuine probability density) -/

/-- Scaled exponential tail integral `∫_{Ioi 0} exp(−b x) dx = 1/b` (b>0). -/
theorem integral_exp_neg_mul_Ioi_zero {b : ℝ} (hb : 0 < b) :
    ∫ x in Ioi (0 : ℝ), Real.exp (-(b * x)) = 1 / b := by
  have h := integral_comp_mul_left_Ioi (fun y : ℝ => Real.exp (-y)) 0 hb
  simp only [mul_zero, smul_eq_mul, integral_exp_neg_Ioi_zero, mul_one] at h
  rw [one_div]
  exact h

/-- The Laplace density integrates to 1 (rate > 0): it is a probability density. -/
theorem laplacePDFReal_integral_eq_one {b : ℝ} (hb : 0 < b) :
    ∫ x, laplacePDFReal b x = 1 := by
  have hcast : (∫ x, laplacePDFReal b x)
      = ∫ x, (fun t : ℝ => b / 2 * Real.exp (-(b * t))) |x| := rfl
  rw [hcast, integral_comp_abs (f := fun t : ℝ => b / 2 * Real.exp (-(b * t))),
      integral_const_mul, integral_exp_neg_mul_Ioi_zero hb]
  field_simp

/-! ## T1′ — the Gaussian/Exponential scale-mixture = Laplace (integral form)

Marginalising `X | V ~ N(0, V)` against `V ~ Exponential(λ)` yields the Laplace
law of rate `√(2λ)`.  In pure integral form (over the variance `v`):

  ∫_{Ioi 0} (√(2πv))⁻¹ · exp(−x²/(2v)) · (λ·exp(−λ v)) dv
      = (√(2λ)/2) · exp(−√(2λ)·|x|).

The Gaussian kernel is `gaussianPDFReal 0 v x`; the prior weight `λ·exp(−λ v)`
is `exponentialPDFReal λ v` on `v > 0`.

Proof:
Pull the constant `λ·(2π)^(−1/2)` out; the remaining integral is the Glasser /
modified-Bessel-K_{1/2} integral (`glasser_integral` below)
    ∫_{Ioi 0} v^(−1/2) · exp(−a/v − b v) dv = √(π/b) · exp(−2√(a b))   (a≥0,b>0)
with `a = x²/2`, `b = λ`.  Evaluating: `√(π/λ)·exp(−2√(x²λ/2)) =
√(π/λ)·exp(−√(2λ)·|x|)`, and `λ·(2π)^(−1/2)·√(π/λ) = √(λ/2) = √(2λ)/2`
(this last step is `laplace_rate_eq`).  `glasser_integral` is proved via the
substitution `v = √(a/b)·s²` and the Schlömilch change of variables
`u = s − 1/s : Ioi 0 → ℝ` (`combined`), both realised with the one-variable
Jacobian lemma `integral_image_eq_integral_abs_deriv_smul`. -/
/-! ### Schlömilch / Glasser kernel — the analytic core (now fully formalised)

The whole chain rests on the reflection `s ↦ 1/s` and the change of variables
`u = s − 1/s : Ioi 0 → univ`, both handled by the one-variable Jacobian lemma
`integral_image_eq_integral_abs_deriv_smul`. No modified Bessel `K` is needed. -/

/-- **Key step (Schlömilch).** `∫_{Ioi 0} (1 + 1/x²)·exp(−c(x−1/x)²) dx = √(π/c)`,
via the change of variables `u = x − 1/x` (a C¹ bijection `Ioi 0 → ℝ`, jacobian
`1 + 1/x²`) reducing to the Gaussian integral `∫_ℝ exp(−c u²) = √(π/c)`. -/
theorem combined (c : ℝ) :
    ∫ x in Ioi (0 : ℝ), (1 + (x ^ 2)⁻¹) * Real.exp (-c * (x - x⁻¹) ^ 2)
      = Real.sqrt (π / c) := by
  have hderiv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun s : ℝ => s - s⁻¹) (1 + (x ^ 2)⁻¹) (Ioi 0) x := by
    intro x hx
    have hx0 : x ≠ 0 := (mem_Ioi.mp hx).ne'
    have h := ((hasDerivAt_id' x).fun_sub (hasDerivAt_inv hx0)).hasDerivWithinAt (s := Ioi 0)
    convert h using 1
    ring
  have hinj : InjOn (fun s : ℝ => s - s⁻¹) (Ioi 0) := by
    intro a ha b hb hab
    simp only at hab
    have ha0 : (0 : ℝ) < a := ha
    have hb0 : (0 : ℝ) < b := hb
    have : (a - b) * (1 + 1 / (a * b)) = 0 := by field_simp at hab ⊢; nlinarith [hab]
    have hpos : 0 < 1 + 1 / (a * b) := by positivity
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · nlinarith [hpos]
  have himg : (fun s : ℝ => s - s⁻¹) '' Ioi 0 = univ := by
    ext u
    simp only [mem_image, mem_Ioi, mem_univ, iff_true]
    refine ⟨(u + Real.sqrt (u ^ 2 + 4)) / 2, ?_, ?_⟩
    · have hs : Real.sqrt (u ^ 2 + 4) > |u| := by
        rw [show |u| = Real.sqrt (u ^ 2) from (Real.sqrt_sq_eq_abs u).symm]
        apply Real.sqrt_lt_sqrt (by positivity); nlinarith
      have : Real.sqrt (u ^ 2 + 4) > -u := lt_of_le_of_lt (neg_le_abs u) hs
      linarith
    · set D := Real.sqrt (u ^ 2 + 4) with hD
      have hD2 : D ^ 2 = u ^ 2 + 4 := Real.sq_sqrt (by positivity)
      have hDgt : D > -u := by
        have : D > |u| := by
          rw [hD, show |u| = Real.sqrt (u ^ 2) from (Real.sqrt_sq_eq_abs u).symm]
          apply Real.sqrt_lt_sqrt (by positivity); nlinarith
        exact lt_of_le_of_lt (neg_le_abs u) this
      have hUD : (0 : ℝ) < u + D := by linarith
      rw [inv_div, div_sub_div _ _ (two_ne_zero) hUD.ne', div_eq_iff (by positivity)]
      linear_combination hD2
  have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (fun u => Real.exp (-c * u ^ 2))
  rw [himg] at hcov
  simp only [Measure.restrict_univ, smul_eq_mul] at hcov
  have habs : ∫ x in Ioi (0 : ℝ), |1 + (x ^ 2)⁻¹| * Real.exp (-c * (x - x⁻¹) ^ 2)
      = ∫ x in Ioi (0 : ℝ), (1 + (x ^ 2)⁻¹) * Real.exp (-c * (x - x⁻¹) ^ 2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only []
    rw [abs_of_nonneg (by positivity)]
  rw [← habs, ← hcov, integral_gaussian]

/-- Derivative of `x ↦ x⁻¹` on `Ioi 0` (used for the reflection). -/
theorem hderiv_inv : ∀ x ∈ Ioi (0 : ℝ),
    HasDerivWithinAt (fun s : ℝ => s⁻¹) (-(x ^ 2)⁻¹) (Ioi 0) x := by
  intro x hx
  exact (hasDerivAt_inv (mem_Ioi.mp hx).ne').hasDerivWithinAt

theorem hinj_inv : InjOn (fun s : ℝ => s⁻¹) (Ioi (0 : ℝ)) := fun _ _ _ _ h => inv_inj.mp h

theorem himg_inv : (fun s : ℝ => s⁻¹) '' Ioi (0 : ℝ) = Ioi 0 := by
  ext u
  simp only [mem_image, mem_Ioi]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact inv_pos.mpr hy
  · intro hu; exact ⟨u⁻¹, inv_pos.mpr hu, inv_inv u⟩

/-- Reflection `x ↦ 1/x` on `Ioi 0` (jacobian `1/x²`). -/
theorem refl_int (g : ℝ → ℝ) :
    ∫ x in Ioi (0 : ℝ), g x = ∫ x in Ioi (0 : ℝ), (x ^ 2)⁻¹ * g x⁻¹ := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv_inv hinj_inv g
  rw [himg_inv] at h
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  show |(-(x ^ 2)⁻¹)| • g x⁻¹ = (x ^ 2)⁻¹ * g x⁻¹
  rw [smul_eq_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (x ^ 2)⁻¹)]

theorem refl_integ (g : ℝ → ℝ) (hg : IntegrableOn g (Ioi (0 : ℝ))) :
    IntegrableOn (fun x => (x ^ 2)⁻¹ * g x⁻¹) (Ioi 0) := by
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    hderiv_inv hinj_inv g).mp
  rw [himg_inv] at h
  have h2 := h hg
  apply h2.congr_fun _ measurableSet_Ioi
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  show |(-(x ^ 2)⁻¹)| • g x⁻¹ = (x ^ 2)⁻¹ * g x⁻¹
  rw [smul_eq_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (x ^ 2)⁻¹)]

/-- `∫_{Ioi 0} exp(−c(x²+1/x²)) dx = (1/2)·exp(−2c)·√(π/c)` for `c > 0`
(reflection halves the `(1 + 1/x²)`-weighted `combined` integral). -/
theorem value_sq (c : ℝ) (hc : 0 < c) :
    ∫ x in Ioi (0 : ℝ), Real.exp (-c * (x ^ 2 + (x ^ 2)⁻¹))
      = 1 / 2 * (Real.exp (-2 * c) * Real.sqrt (π / c)) := by
  set h : ℝ → ℝ := fun x => Real.exp (-c * (x ^ 2 + (x ^ 2)⁻¹)) with hh
  have hsym : Set.EqOn (fun x => (x ^ 2)⁻¹ * h x⁻¹) (fun x => (x ^ 2)⁻¹ * h x) (Ioi 0) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    simp only [hh]
    congr 2
    field_simp
    ring
  have hInt : IntegrableOn h (Ioi (0 : ℝ)) := by
    apply Integrable.mono' (g := fun x => Real.exp (-c * x ^ 2))
      ((integrable_exp_neg_mul_sq hc).integrableOn)
      (Measurable.aestronglyMeasurable (by fun_prop))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hc.le (by positivity : (0 : ℝ) ≤ (x ^ 2)⁻¹)]
  have hInt2 : IntegrableOn (fun x => (x ^ 2)⁻¹ * h x) (Ioi 0) := by
    have := refl_integ h hInt
    exact this.congr_fun hsym measurableSet_Ioi
  have e1 : ∫ x in Ioi (0 : ℝ), (x ^ 2)⁻¹ * h x = ∫ x in Ioi (0 : ℝ), h x := by
    rw [← setIntegral_congr_fun measurableSet_Ioi hsym, ← refl_int h]
  have e2 : (∫ x in Ioi (0 : ℝ), h x) + (∫ x in Ioi (0 : ℝ), (x ^ 2)⁻¹ * h x)
      = ∫ x in Ioi (0 : ℝ), (1 + (x ^ 2)⁻¹) * h x := by
    rw [← integral_add hInt hInt2]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx; ring
  have e3 : ∫ x in Ioi (0 : ℝ), (1 + (x ^ 2)⁻¹) * h x
      = Real.exp (-2 * c) * Real.sqrt (π / c) := by
    have hpt : Set.EqOn (fun x => (1 + (x ^ 2)⁻¹) * h x)
        (fun x => Real.exp (-2 * c) * ((1 + (x ^ 2)⁻¹) * Real.exp (-c * (x - x⁻¹) ^ 2)))
        (Ioi 0) := by
      intro x hx
      have hx0 : (0 : ℝ) < x := hx
      simp only [hh]
      rw [show Real.exp (-2 * c) * ((1 + (x ^ 2)⁻¹) * Real.exp (-c * (x - x⁻¹) ^ 2))
            = (1 + (x ^ 2)⁻¹) * Real.exp (-2 * c + (-c * (x - x⁻¹) ^ 2)) from by
              rw [Real.exp_add]; ring]
      congr 2
      field_simp
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, combined c]
  have key : 2 * (∫ x in Ioi (0 : ℝ), h x) = Real.exp (-2 * c) * Real.sqrt (π / c) := by
    rw [two_mul]
    nth_rewrite 2 [← e1]
    rw [e2, e3]
  linarith [key]

/-- **Glasser / modified-Bessel-`K_{1/2}` integral** (the analytic kernel). For `a ≥ 0`, `b > 0`,
  `∫_{Ioi 0} v^(−1/2)·exp(−a/v − b·v) dv = √(π/b)·exp(−2·√(a·b))`.
`a = 0`: Gamma integral (`integral_rpow_mul_exp_neg_mul_Ioi`, `Real.Gamma_one_half_eq`).
`a > 0`: the substitution `v = √(a/b)·s²` (one-variable Jacobian CoV) reduces it
to `2·√(√(a/b))·value_sq(√(ab))`; `value_sq` in turn rests on `combined`
(the Schlömilch `u = s − 1/s` change of variables). -/
theorem glasser_integral {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    ∫ v in Ioi (0 : ℝ), v ^ (-(1 : ℝ) / 2) * Real.exp (-a / v - b * v)
      = Real.sqrt (π / b) * Real.exp (-(2 * Real.sqrt (a * b))) := by
  rcases eq_or_lt_of_le ha with h0 | ha'
  · subst h0
    have hcongr : ∀ v ∈ Ioi (0 : ℝ), v ^ (-(1 : ℝ) / 2) * Real.exp (-(0 : ℝ) / v - b * v)
        = v ^ ((1 : ℝ) / 2 - 1) * Real.exp (-(b * v)) := by
      intro v hv
      rw [show (-(1 : ℝ) / 2) = (1 : ℝ) / 2 - 1 from by norm_num]
      congr 2
      simp
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
        integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 1 / 2) hb,
        Real.Gamma_one_half_eq, show (0 : ℝ) * b = 0 from by ring, Real.sqrt_zero,
        mul_zero, neg_zero, Real.exp_zero, mul_one, ← Real.sqrt_eq_rpow,
        ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 1 / b)]
    congr 1
    field_simp
  · have hab : 0 < a * b := mul_pos ha' hb
    have hk : 0 < Real.sqrt (a / b) := Real.sqrt_pos.mpr (div_pos ha' hb)
    set k := Real.sqrt (a / b) with hkdef
    have hbk : b * k = Real.sqrt (a * b) := by
      rw [← Real.sqrt_sq (mul_pos hb hk).le]
      congr 1
      rw [mul_pow, hkdef, Real.sq_sqrt (div_pos ha' hb).le]
      field_simp
    have hak : a / k = Real.sqrt (a * b) := by
      rw [← Real.sqrt_sq (div_pos ha' hk).le]
      congr 1
      rw [div_pow, hkdef, Real.sq_sqrt (div_pos ha' hb).le]
      field_simp
    have hderiv_s : ∀ s ∈ Ioi (0 : ℝ),
        HasDerivWithinAt (fun t => k * t ^ 2) (k * (2 * s)) (Ioi 0) s := by
      intro s hs
      have := (((hasDerivAt_pow 2 s).const_mul k).hasDerivWithinAt (s := Ioi 0))
      convert this using 1
      norm_num
    have hinj_s : InjOn (fun t => k * t ^ 2) (Ioi (0 : ℝ)) := by
      intro p hp q hq hpq
      simp only at hpq
      have hp0 : (0 : ℝ) < p := hp
      have hq0 : (0 : ℝ) < q := hq
      have hsq : p ^ 2 = q ^ 2 := mul_left_cancel₀ hk.ne' hpq
      have : (p - q) * (p + q) = 0 := by nlinarith [hsq]
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    have himg_s : (fun t => k * t ^ 2) '' Ioi (0 : ℝ) = Ioi 0 := by
      ext v
      simp only [mem_image, mem_Ioi]
      constructor
      · rintro ⟨t, ht, rfl⟩; exact mul_pos hk (pow_pos ht 2)
      · intro hv
        refine ⟨Real.sqrt (v / k), Real.sqrt_pos.mpr (div_pos hv hk), ?_⟩
        show k * (Real.sqrt (v / k)) ^ 2 = v
        rw [Real.sq_sqrt (div_pos hv hk).le]
        field_simp
    have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv_s hinj_s
      (fun v => v ^ (-(1 : ℝ) / 2) * Real.exp (-a / v - b * v))
    rw [himg_s] at hcov
    rw [hcov]
    have hpt : Set.EqOn
        (fun s => |k * (2 * s)| • ((fun v => v ^ (-(1 : ℝ) / 2) * Real.exp (-a / v - b * v))
          (k * s ^ 2)))
        (fun s => 2 * Real.sqrt k * Real.exp (-Real.sqrt (a * b) * (s ^ 2 + (s ^ 2)⁻¹)))
        (Ioi 0) := by
      intro s hs
      have hs0 : (0 : ℝ) < s := hs
      show |k * (2 * s)| • ((k * s ^ 2) ^ (-(1 : ℝ) / 2)
            * Real.exp (-a / (k * s ^ 2) - b * (k * s ^ 2)))
          = 2 * Real.sqrt k * Real.exp (-Real.sqrt (a * b) * (s ^ 2 + (s ^ 2)⁻¹))
      rw [smul_eq_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k * (2 * s))]
      have hks : (k * s ^ 2) ^ (-(1 : ℝ) / 2) = (Real.sqrt k * s)⁻¹ := by
        rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) from by ring, Real.rpow_neg (by positivity),
            ← Real.sqrt_eq_rpow, Real.sqrt_mul hk.le, Real.sqrt_sq hs0.le]
      have hexparg : -a / (k * s ^ 2) - b * (k * s ^ 2)
          = -Real.sqrt (a * b) * (s ^ 2 + (s ^ 2)⁻¹) := by
        have e1 : a / (k * s ^ 2) = Real.sqrt (a * b) * (s ^ 2)⁻¹ := by
          rw [← hak]; field_simp
        have e2 : b * (k * s ^ 2) = Real.sqrt (a * b) * s ^ 2 := by
          rw [← hbk]; ring
        rw [show -a / (k * s ^ 2) = -(a / (k * s ^ 2)) from by ring, e1, e2]; ring
      have hk2 : k * (Real.sqrt k)⁻¹ = Real.sqrt k := by
        rw [← div_eq_mul_inv, div_eq_iff (Real.sqrt_pos.mpr hk).ne', Real.mul_self_sqrt hk.le]
      have hcoef : k * (2 * s) * (Real.sqrt k * s)⁻¹ = 2 * Real.sqrt k := by
        rw [mul_inv,
            show k * (2 * s) * ((Real.sqrt k)⁻¹ * s⁻¹)
              = 2 * (k * (Real.sqrt k)⁻¹) * (s * s⁻¹) from by ring,
            hk2, mul_inv_cancel₀ hs0.ne', mul_one]
      rw [hks, hexparg]
      rw [show k * (2 * s) * ((Real.sqrt k * s)⁻¹
              * Real.exp (-Real.sqrt (a * b) * (s ^ 2 + (s ^ 2)⁻¹)))
            = (k * (2 * s) * (Real.sqrt k * s)⁻¹)
              * Real.exp (-Real.sqrt (a * b) * (s ^ 2 + (s ^ 2)⁻¹)) from by ring,
          hcoef]
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
        value_sq (Real.sqrt (a * b)) (Real.sqrt_pos.mpr hab)]
    have hfin : Real.sqrt k * Real.sqrt (π / Real.sqrt (a * b)) = Real.sqrt (π / b) := by
      rw [← Real.sqrt_mul hk.le]
      congr 1
      rw [mul_div_assoc', div_eq_div_iff (Real.sqrt_pos.mpr hab).ne' hb.ne', ← hbk]
      ring
    rw [show (2 : ℝ) * Real.sqrt k
            * (1 / 2 * (Real.exp (-2 * Real.sqrt (a * b))
              * Real.sqrt (π / Real.sqrt (a * b))))
          = Real.sqrt k * Real.sqrt (π / Real.sqrt (a * b))
            * Real.exp (-2 * Real.sqrt (a * b)) from by ring,
        hfin, show -2 * Real.sqrt (a * b) = -(2 * Real.sqrt (a * b)) from by ring]

theorem gaussian_exponential_mixture_laplace (lam x : ℝ) (hlam : 0 < lam) :
    ∫ v in Ioi (0 : ℝ),
        (Real.sqrt (2 * π * v))⁻¹ * Real.exp (-x ^ 2 / (2 * v))
          * (lam * Real.exp (-(lam * v)))
      = Real.sqrt (2 * lam) / 2 * Real.exp (-(Real.sqrt (2 * lam) * |x|)) := by
  -- Rewrite the integrand as `C · (v^(−1/2)·exp(−a/v − b·v))`, `C = λ·(2π)^(−1/2)`.
  have hpt : Set.EqOn
      (fun v : ℝ => (Real.sqrt (2 * π * v))⁻¹ * Real.exp (-x ^ 2 / (2 * v))
          * (lam * Real.exp (-(lam * v))))
      (fun v : ℝ => lam * (Real.sqrt (2 * π))⁻¹
          * (v ^ (-(1 : ℝ) / 2) * Real.exp (-(x ^ 2 / 2) / v - lam * v)))
      (Ioi (0 : ℝ)) := by
    intro v hv
    have hv0 : (0 : ℝ) < v := hv
    have hsqrt : (Real.sqrt (2 * π * v))⁻¹
        = (Real.sqrt (2 * π))⁻¹ * v ^ (-(1 : ℝ) / 2) := by
      rw [show 2 * π * v = (2 * π) * v from by ring,
          Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * π) v, mul_inv]
      congr 1
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hv0.le]
      norm_num
    have hexp : Real.exp (-x ^ 2 / (2 * v)) * Real.exp (-(lam * v))
        = Real.exp (-(x ^ 2 / 2) / v - lam * v) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    simp only
    rw [hsqrt,
        show (Real.sqrt (2 * π))⁻¹ * v ^ (-(1 : ℝ) / 2) * Real.exp (-x ^ 2 / (2 * v))
              * (lam * Real.exp (-(lam * v)))
            = lam * (Real.sqrt (2 * π))⁻¹
              * (v ^ (-(1 : ℝ) / 2)
                * (Real.exp (-x ^ 2 / (2 * v)) * Real.exp (-(lam * v)))) from by ring,
        hexp]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
      glasser_integral (a := x ^ 2 / 2) (b := lam) (by positivity) hlam]
  -- Final constant + exponent bookkeeping.
  have hconst : lam * (Real.sqrt (2 * π))⁻¹ * Real.sqrt (π / lam)
      = Real.sqrt (2 * lam) / 2 := by
    rw [laplace_rate_eq]
    have hnn : 0 ≤ lam * (Real.sqrt (2 * π))⁻¹ * Real.sqrt (π / lam) := by positivity
    rw [← Real.sqrt_sq hnn]
    congr 1
    rw [mul_pow, mul_pow, ← Real.sqrt_inv, Real.sq_sqrt (by positivity),
        Real.sq_sqrt (by positivity)]
    field_simp
  have hexpo : 2 * Real.sqrt (x ^ 2 / 2 * lam) = Real.sqrt (2 * lam) * |x| := by
    have hL : Real.sqrt (2 * lam * x ^ 2) = 2 * Real.sqrt (x ^ 2 / 2 * lam) := by
      rw [show 2 * lam * x ^ 2 = 4 * (x ^ 2 / 2 * lam) from by ring,
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
          show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    have hR : Real.sqrt (2 * lam) * |x| = Real.sqrt (2 * lam * x ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * lam)]
    rw [hR, hL]
  rw [← mul_assoc, hconst, hexpo]

end Superstatistics
