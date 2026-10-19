/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The real Airy functions

The power series `F = Σ aₙ xⁿ` with `a_{k+3} = a_k / ((k + 2)(k + 3))`, `a₀ = c0`, `a₁ = c1`,
`a₂ = 0`, as a real function `airyFun c0 c1 : ℝ → ℝ`. It is entire, solves `F'' = x F` as a
functional identity, has zeros unbounded below, and does not decay at `+∞` when positive with
non-negative slope at some `x₀ > 0`. A decaying (recessive) solution is built by reduction of order,
`Ai_rec = f ∫ₓ^∞ f⁻²`, without the asymptotic expansions of DLMF §9.7, and is extended to an
entire Airy function. Applied to the quantum bouncer `ψ'' = α²(αx − β)ψ` on `[0, ∞)` with
`ψ(0) = 0`: there are infinitely many energy levels.

## Main results

* `Airy.airyFun_entire`: `airyFun c0 c1` is analytic on all of `ℝ` (radius of convergence `∞`).
* `Airy.airyFun_ode`: `deriv (deriv (airyFun c0 c1)) x = x * airyFun c0 c1 x`.
* `Airy.sturm_unbounded_zeros`, `Airy.airyFun_unbounded_zeros`: every solution has zeros
  unbounded below (Sturm comparison with `sin (√c (x − a))`, from Rolle and the intermediate value
  theorem).
* `Airy.airyFun_not_decaying`: a solution positive with non-negative slope at `x₀ > 0` does not
  tend to `0`.
* `Airy.exists_recessive_solution`: a non-trivial solution on `(0, ∞)` tending to `0` at `+∞`.
* `Airy.exists_entire_recessive`: an entire `airyFun c0 c1`, not identically zero, tending to `0`
  at `+∞` (through the basis Wronskian `W(f, g) = 1`).
* `Airy.bouncer_ode`, `Airy.bouncer_bc`, `Airy.bouncer_levels_infinite`: the quantum bouncer has
  infinitely many energy levels, the negatives of the zeros of an Airy function.

## Implementation notes

Mathlib has no Sturm–Liouville or Sturm comparison theory; the oscillation argument is built here
from Rolle's theorem, the mean value theorem and the intermediate value theorem.

## References

* NIST Digital Library of Mathematical Functions, Chapter 9 (Airy and Related Functions),
  https://dlmf.nist.gov/9.
* O. Vallée, M. Soares, *Airy Functions and Applications to Physics*, Imperial College Press (2010).
* E. A. Coddington, N. Levinson, *Theory of Ordinary Differential Equations*, McGraw–Hill (1955),
  Ch. 8.
* R. L. Gibbs, *The quantum bouncer*, Am. J. Phys. 43 (1975) 25–28.
* V. V. Nesvizhevsky et al., *Quantum states of neutrons in the Earth's gravitational field*,
  Nature 415 (2002) 297–299.
* C. Marín, *How a Falling Particle Counts Its Floors: the Airy function as a verified entire
  solution of y''=xy, its oscillation, and the quantum-bouncer spectrum, machine-checked in Lean 4*
  (2026), doi:10.5281/zenodo.20787671. Ported from `AiryReal.lean` of
  [karlesmarin/airy-bouncer-lean](https://github.com/karlesmarin/airy-bouncer-lean)
  (Lean v4.30.0-rc2).
-/

@[expose] public section

open FormalMultilinearSeries Filter ContinuousLinearMap Real Set MeasureTheory
open scoped Nat Real Topology

namespace Airy

/-- Real Airy coefficients: solution of y''=xy with y(0)=c0, y'(0)=c1. -/
noncomputable def coeffR (c0 c1 : ℝ) : ℕ → ℝ
  | 0       => c0
  | 1       => c1
  | 2       => 0
  | (k + 3) => coeffR c0 c1 k / (((k : ℝ) + 2) * ((k : ℝ) + 3))

theorem coeffR_succ3 (c0 c1 : ℝ) (k : ℕ) :
    coeffR c0 c1 (k + 3) = coeffR c0 c1 k / (((k : ℝ) + 2) * ((k : ℝ) + 3)) := rfl

/-- Recurrence cleared of its denominator: `(k+2)(k+3)·a(k+3) = a(k)`. This is the identity
`(k+2)(k+1)c_{k+2}=c_{k-1}` reindexed; it drives the F''=x·F coefficient match. -/
theorem coeffR_mul_succ3 (c0 c1 : ℝ) (k : ℕ) :
    (((k : ℝ) + 2) * ((k : ℝ) + 3)) * coeffR c0 c1 (k + 3) = coeffR c0 c1 k := by
  rw [coeffR_succ3]; field_simp

/-- **Coefficient bound.** `|aₙ| ≤ M / ⌊n/3⌋!` with `M = max |c0| |c1|`.
Each 3-step divides by `(k+2)(k+3) ≥ ⌊k/3⌋+1`, so the factorial grows one step per 3 indices. -/
theorem coeffR_abs_le (c0 c1 : ℝ) (n : ℕ) :
    |coeffR c0 c1 n| ≤ max |c0| |c1| / (n / 3).factorial := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hM : (0:ℝ) ≤ max |c0| |c1| := le_trans (abs_nonneg c0) (le_max_left _ _)
    rcases n with _ | _ | _ | k
    · simp [coeffR]
    · simp [coeffR]
    · simp [coeffR]
    · have hd : (0:ℝ) < ((k : ℝ) + 2) * ((k : ℝ) + 3) := by positivity
      have hk := ih k (by omega)
      have hFpos : (0:ℝ) < ((k / 3).factorial : ℝ) := by exact_mod_cast (k / 3).factorial_pos
      have hk' : |coeffR c0 c1 k| * ((k / 3).factorial : ℝ) ≤ max |c0| |c1| :=
        (le_div_iff₀ hFpos).mp hk
      have hfac : ((k + 3) / 3).factorial = (k / 3 + 1) * (k / 3).factorial := by
        rw [show (k + 3) / 3 = k / 3 + 1 from by omega, Nat.factorial_succ]
      have hb : ((k / 3 : ℕ) : ℝ) + 1 ≤ ((k : ℝ) + 2) * ((k : ℝ) + 3) := by
        have hle : ((k / 3 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.div_le_self k 3
        nlinarith [hle, Nat.cast_nonneg (α := ℝ) k]
      rw [coeffR_succ3, abs_div, abs_of_pos hd,
        div_le_div_iff₀ hd (by exact_mod_cast ((k + 3) / 3).factorial_pos), hfac]
      push_cast
      nlinarith [hk', hM, hFpos, hb, abs_nonneg (coeffR c0 c1 k),
        mul_nonneg (abs_nonneg (coeffR c0 c1 k)) hFpos.le]

/-- **Summability.** For every radius `r`, `∑ |aₙ|·rⁿ` converges. Comparison with the
regrouped series `∑ rⁿ/⌊n/3⌋! = (1+r+r²)·∑(r³)ᵐ/m! = (1+r+r²)·e^{r³}`. -/
theorem summable_coeffR_norm (c0 c1 : ℝ) (r : NNReal) :
    Summable (fun n => ‖coeffR c0 c1 n‖ * (r : ℝ) ^ n) := by
  have hMnonneg : (0:ℝ) ≤ max |c0| |c1| := le_trans (abs_nonneg c0) (le_max_left _ _)
  -- the dominating (exp r³)-type series, reindexed by (m,i) ↦ 3m+i
  have hg' : Summable
      (fun p : ℕ × Fin 3 => (r : ℝ) ^ (p.1 * 3 + (p.2 : ℕ)) / (p.1).factorial) := by
    rw [summable_prod_of_nonneg (fun p => by positivity)]
    refine ⟨fun m => Summable.of_finite, ?_⟩
    have hsum : ∀ m : ℕ,
        (∑' i : Fin 3, (r : ℝ) ^ (m * 3 + (i : ℕ)) / (m).factorial)
          = (1 + (r : ℝ) + (r : ℝ) ^ 2) * (((r : ℝ) ^ 3) ^ m / m.factorial) := by
      intro m
      rw [tsum_fintype, Fin.sum_univ_three]
      simp only [show ((0 : Fin 3) : ℕ) = 0 from rfl, show ((1 : Fin 3) : ℕ) = 1 from rfl,
        show ((2 : Fin 3) : ℕ) = 2 from rfl]
      ring
    simp_rw [hsum]
    exact (Real.summable_pow_div_factorial ((r : ℝ) ^ 3)).mul_left _
  -- ∑ rⁿ/⌊n/3⌋! converges (reindex n ↦ (n/3, n%3))
  have key : Summable (fun n : ℕ => (r : ℝ) ^ n / (n / 3).factorial) := by
    rw [← (Nat.divModEquiv 3).symm.summable_iff]
    refine hg'.congr fun p => ?_
    have hlt := p.2.isLt
    simp only [Function.comp_apply, Nat.divModEquiv_symm_apply]
    rw [show (p.1 * 3 + (p.2 : ℕ)) / 3 = p.1 from by omega]
  -- comparison: |aₙ|·rⁿ ≤ M·(rⁿ/⌊n/3⌋!)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (key.mul_left (max |c0| |c1|))
  rw [Real.norm_eq_abs]
  calc |coeffR c0 c1 n| * (r : ℝ) ^ n
      ≤ (max |c0| |c1| / (n / 3).factorial) * (r : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right (coeffR_abs_le c0 c1 n) (by positivity)
    _ = max |c0| |c1| * ((r : ℝ) ^ n / (n / 3).factorial) := by ring

/-- A scalar formal multilinear series is determined by its coefficients. -/
theorem scalar_fms_ext (p q : FormalMultilinearSeries ℝ ℝ ℝ)
    (h : ∀ n, p.coeff n = q.coeff n) : p = q := by
  ext n
  rw [← mkPiRing_coeff_eq p n, ← mkPiRing_coeff_eq q n, h n]

/-- **Term-by-term differentiation.** If `f` is the sum of `∑ aₙ xⁿ` on a ball, then `deriv f`
is the sum of `∑ (n+1) a_{n+1} xⁿ`. Built from `HasFPowerSeriesOnBall.fderiv` (the derivative's
power series is `derivSeries`) + evaluation at `1` + `derivSeries_coeff_one`. -/
theorem deriv_ofScalarsSum {a : ℕ → ℝ} {f : ℝ → ℝ}
    (hf : HasFPowerSeriesOnBall f (ofScalars ℝ a) 0 ⊤) :
    HasFPowerSeriesOnBall (deriv f)
      (ofScalars ℝ (fun n => ((n : ℝ) + 1) * a (n + 1))) 0 ⊤ := by
  have hcomp := (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).comp_hasFPowerSeriesOnBall hf.fderiv
  have hfun : (fun x => (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)) (fderiv ℝ f x)) = deriv f := by
    funext x; rw [ContinuousLinearMap.apply_apply]; rfl
  have hser : (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).compFormalMultilinearSeries
        ((ofScalars ℝ a).derivSeries) = ofScalars ℝ (fun n => ((n : ℝ) + 1) * a (n + 1)) := by
    apply scalar_fms_ext
    intro n
    rw [coeff_ofScalars]
    have hL : ((ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).compFormalMultilinearSeries
          (ofScalars ℝ a).derivSeries).coeff n = ((ofScalars ℝ a).derivSeries.coeff n) 1 := by
      rw [FormalMultilinearSeries.coeff, compFormalMultilinearSeries_apply',
        ContinuousLinearMap.apply_apply, FormalMultilinearSeries.coeff]
    rw [hL, derivSeries_coeff_one, coeff_ofScalars]
    ring
  rw [← hfun, ← hser]
  exact hcomp

/-- The Airy power series over ℝ as a `FormalMultilinearSeries`. -/
noncomputable def airySeries (c0 c1 : ℝ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  ofScalars ℝ (coeffR c0 c1)

/-- The real Airy solution `F : ℝ → ℝ` with `F(0)=c0`, `F'(0)=c1`. -/
noncomputable def airyFun (c0 c1 : ℝ) : ℝ → ℝ := (airySeries c0 c1).sum

/-- **Radius of convergence = ∞.** The Airy series is entire. -/
theorem airySeries_radius (c0 c1 : ℝ) : (airySeries c0 c1).radius = ⊤ := by
  rw [radius_eq_top_iff_summable_norm]
  intro r
  simpa [airySeries] using summable_coeffR_norm c0 c1 r

theorem airyFun_hasFPowerSeries (c0 c1 : ℝ) :
    HasFPowerSeriesOnBall (airyFun c0 c1) (airySeries c0 c1) 0 ⊤ := by
  have h := (airySeries c0 c1).hasFPowerSeriesOnBall
    (by rw [airySeries_radius]; exact ENNReal.zero_lt_top)
  rwa [airySeries_radius] at h

/-- **`F` is a real entire function** (analytic on all of ℝ). -/
theorem airyFun_entire (c0 c1 : ℝ) : AnalyticOnNhd ℝ (airyFun c0 c1) Set.univ := by
  have h := (airyFun_hasFPowerSeries c0 c1).analyticOnNhd
  simpa using h

/-- Coefficients of `F''`: `(n+1)(n+2)·a(n+2)` (= apply `deriv_ofScalarsSum` twice). -/
noncomputable def coeffR2 (c0 c1 : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) * ((n : ℝ) + 2) * coeffR c0 c1 (n + 2)

theorem coeffR2_zero (c0 c1 : ℝ) : coeffR2 c0 c1 0 = 0 := by
  simp [coeffR2, coeffR]

/-- The key shift: `F''` coefficient at `n+1` equals `F` coefficient at `n` — this IS the recurrence
`(n+2)(n+3)a(n+3)=a(n)`, i.e. the Airy ODE `y''=xy` read off coefficient-by-coefficient. -/
theorem coeffR2_succ (c0 c1 : ℝ) (n : ℕ) : coeffR2 c0 c1 (n + 1) = coeffR c0 c1 n := by
  have h := coeffR_mul_succ3 c0 c1 n
  simp only [coeffR2]; push_cast; linear_combination h

/-- **The Airy ODE `y'' = x·y`, as a real functional identity**. Every entire solution `F`
of the recurrence satisfies `deriv (deriv F) x = x · F x` at every real `x`. Proof:
term-by-term differentiation gives `F''` as the power series `∑ (n+1)(n+2)a(n+2) xⁿ`; the recurrence
`coeffR2_succ` reindexes it to `∑ aₙ xⁿ⁺¹ = x·F`. -/
theorem airyFun_ode (c0 c1 : ℝ) (x : ℝ) :
    deriv (deriv (airyFun c0 c1)) x = x * airyFun c0 c1 x := by
  have hF := airyFun_hasFPowerSeries c0 c1
  have hF1 := deriv_ofScalarsSum hF
  have hF2 : HasFPowerSeriesOnBall (deriv (deriv (airyFun c0 c1)))
      (ofScalars ℝ (coeffR2 c0 c1)) 0 ⊤ := by
    convert deriv_ofScalarsSum hF1 using 3 with n
    simp only [coeffR2]; push_cast; ring
  have hx : x ∈ Metric.eball (0 : ℝ) ⊤ := (edist_ne_top x 0).lt_top
  have hsumF := hF.hasSum hx
  have hsum2 := hF2.hasSum hx
  rw [zero_add] at hsumF hsum2
  simp only [airySeries, ofScalars_apply_eq, smul_eq_mul] at hsumF hsum2
  -- x·F as the shifted sum
  have hyF : HasSum (fun n => coeffR c0 c1 n * x ^ (n + 1)) (x * airyFun c0 c1 x) := by
    have h := hsumF.mul_left x
    convert h using 2 with n
    ring
  -- F'' sum = x·F (drop the zero head term, reindex by succ)
  have hshift : HasSum (fun n => coeffR2 c0 c1 n * x ^ n) (x * airyFun c0 c1 x) := by
    refine (Nat.succ_injective.hasSum_iff ?_).mp ?_
    · intro m hm
      rcases m with _ | k
      · simp [coeffR2_zero]
      · exact absurd ⟨k, rfl⟩ hm
    · convert hyF using 2 with n
      simp only [Function.comp_apply, Nat.succ_eq_add_one, coeffR2_succ]
  exact hsum2.unique hshift

/- ── Oscillation (Sturm comparison with `sin`, built from Rolle/MVT + IVT) ─────────────────── -/

/-- Sturm comparison core: a positive solution of y''=xy on an interval of length π/√c lying in
(−∞,−c] is impossible. Wronskian `W=f'z−fz'` vs `z=sin(√c(x−a))`: `W'=(x+c)·f·z ≤ 0` but the
endpoints force `W(a)<0<W(a+π/√c)`. -/
theorem sturm_pos_false (f f' : ℝ → ℝ) (a c : ℝ) (hc : 0 < c)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (x * f x) x)
    (hx : a + π / Real.sqrt c ≤ -c)
    (hpos : ∀ x ∈ Icc a (a + π / Real.sqrt c), 0 < f x) : False := by
  set s := Real.sqrt c with hsdef
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hc
  have hss : s * s = c := Real.mul_self_sqrt hc.le
  set d := a + π / s with hddef
  have hpis : 0 ≤ π / s := by positivity
  have had : a ≤ d := by rw [hddef]; linarith
  have hda : d - a = π / s := by rw [hddef]; ring
  have haff : ∀ x, HasDerivAt (fun y => s * (y - a)) s x := by
    intro x; simpa using ((hasDerivAt_id x).sub_const a).const_mul s
  set z : ℝ → ℝ := fun x => Real.sin (s * (x - a)) with hzdef
  set z' : ℝ → ℝ := fun x => s * Real.cos (s * (x - a)) with hz'def
  have hz_d : ∀ x, HasDerivAt z (z' x) x := by
    intro x
    have h : HasDerivAt (fun y => Real.sin (s * (y - a))) (Real.cos (s * (x - a)) * s) x := by
      simpa [Function.comp_def] using (Real.hasDerivAt_sin (s * (x - a))).comp x (haff x)
    simpa [hzdef, hz'def, mul_comm] using h
  have hz'_d : ∀ x, HasDerivAt z' (-c * z x) x := by
    intro x
    have h : HasDerivAt (fun y => Real.cos (s * (y - a))) (-Real.sin (s * (x - a)) * s) x := by
      simpa [Function.comp_def] using (Real.hasDerivAt_cos (s * (x - a))).comp x (haff x)
    have h2 := h.const_mul s
    convert h2 using 1
    simp only [hzdef]; rw [← hss]; ring
  set W : ℝ → ℝ := fun x => f' x * z x - f x * z' x with hWdef
  have hW_d : ∀ x, HasDerivAt W ((x + c) * f x * z x) x := by
    intro x
    have h := ((hf' x).mul (hz_d x)).sub ((hf x).mul (hz'_d x))
    convert h using 1
    ring
  have hWderiv : ∀ x, deriv W x = (x + c) * f x * z x := fun x => (hW_d x).deriv
  have hcont : ContinuousOn W (Icc a d) := fun x _ => (hW_d x).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ W (interior (Icc a d)) :=
    fun x _ => (hW_d x).differentiableAt.differentiableWithinAt
  have hnonpos : ∀ x ∈ interior (Icc a d), deriv W x ≤ 0 := by
    intro x hx_int
    rw [interior_Icc] at hx_int
    obtain ⟨hxa, hxd⟩ := hx_int
    rw [hWderiv]
    have hxc : x + c ≤ 0 := by have : x ≤ -c := le_trans hxd.le hx; linarith
    have hfx : 0 < f x := hpos x ⟨hxa.le, hxd.le⟩
    have hzx : 0 ≤ z x := by
      simp only [hzdef]
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · have : 0 ≤ x - a := by linarith
        positivity
      · have hle : x - a ≤ π / s := by rw [← hda]; linarith
        calc s * (x - a) ≤ s * (π / s) := by apply mul_le_mul_of_nonneg_left hle hs_pos.le
          _ = π := by field_simp
    rw [mul_assoc]
    nlinarith [mul_nonneg (neg_nonneg.2 hxc) (mul_nonneg hfx.le hzx)]
  have hanti : AntitoneOn W (Icc a d) :=
    antitoneOn_of_deriv_nonpos (convex_Icc a d) hcont hdiff hnonpos
  have hWda : W d ≤ W a := hanti (left_mem_Icc.mpr had) (right_mem_Icc.mpr had) had
  have hza : z a = 0 := by simp [hzdef]
  have hz'a : z' a = s := by simp [hz'def]
  have hWa : W a < 0 := by
    have hfa := hpos a ⟨le_refl a, had⟩
    rw [hWdef]; simp only [hza, hz'a, mul_zero, zero_sub, neg_lt_zero]
    exact mul_pos hfa hs_pos
  have hzd : z d = 0 := by
    simp only [hzdef]; rw [show s * (d - a) = π by rw [hda]; field_simp]; exact Real.sin_pi
  have hz'd : z' d = -s := by
    simp only [hz'def]; rw [show s * (d - a) = π by rw [hda]; field_simp, Real.cos_pi]; ring
  have hWd : 0 < W d := by
    have hfd := hpos d ⟨had, le_refl d⟩
    rw [hWdef]; simp only [hzd, hz'd, mul_zero, zero_sub, mul_neg, neg_neg]
    exact mul_pos hfd hs_pos
  linarith

/-- A continuous function with no zero on `[a,d]` has constant sign there (IVT). -/
theorem const_sign_of_no_zero {g : ℝ → ℝ} {a d : ℝ} (hg : ContinuousOn g (Icc a d))
    (hnz : ∀ x ∈ Icc a d, g x ≠ 0) (hax : a ≤ d) :
    (∀ x ∈ Icc a d, 0 < g x) ∨ (∀ x ∈ Icc a d, g x < 0) := by
  have key : ∀ u v, u ∈ Icc a d → v ∈ Icc a d → g u < 0 → 0 < g v → False := by
    intro u v hu hv hgu hgv
    rcases le_total u v with huv | hvu
    · have hsub : Icc u v ⊆ Icc a d := Icc_subset_Icc hu.1 hv.2
      obtain ⟨y, hy, hgy⟩ := intermediate_value_Icc huv (hg.mono hsub) ⟨hgu.le, hgv.le⟩
      exact hnz y (hsub hy) hgy
    · have hsub : Icc v u ⊆ Icc a d := Icc_subset_Icc hv.1 hu.2
      obtain ⟨y, hy, hgy⟩ := intermediate_value_Icc' hvu (hg.mono hsub) ⟨hgu.le, hgv.le⟩
      exact hnz y (hsub hy) hgy
  rcases lt_or_gt_of_ne (hnz a ⟨le_refl a, hax⟩) with hga | hga
  · right; intro x hx
    rcases lt_or_gt_of_ne (hnz x hx) with h | h
    · exact h
    · exact (key a x ⟨le_refl a, hax⟩ hx hga h).elim
  · left; intro x hx
    rcases lt_or_gt_of_ne (hnz x hx) with h | h
    · exact (key x a hx ⟨le_refl a, hax⟩ h hga).elim
    · exact h

/-- **Sturm zero existence**: any solution of y''=xy has a zero in `[a, a+π/√c]` when that interval
lies in `(−∞,−c]` (apply the positive-case contradiction to `f` or `−f`). -/
theorem sturm_has_zero (f f' : ℝ → ℝ) (a c : ℝ) (hc : 0 < c)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (x * f x) x)
    (hx : a + π / Real.sqrt c ≤ -c) :
    ∃ x ∈ Icc a (a + π / Real.sqrt c), f x = 0 := by
  by_contra hcon
  push Not at hcon
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hpis : (0:ℝ) ≤ π / Real.sqrt c := by positivity
  have had : a ≤ a + π / Real.sqrt c := by linarith
  have hcont : ContinuousOn f (Icc a (a + π / Real.sqrt c)) :=
    fun x _ => (hf x).continuousAt.continuousWithinAt
  rcases const_sign_of_no_zero hcont hcon had with hpos | hneg
  · exact sturm_pos_false f f' a c hc hf hf' hx hpos
  · exact sturm_pos_false (fun x => -f x) (fun x => -f' x) a c hc
      (fun x => (hf x).neg)
      (fun x => by have h := (hf' x).neg; convert h using 1; ring)
      hx
      (fun x hx2 => by have := hneg x hx2; linarith)

/-- **Oscillation (generic)**: any solution of y''=xy has zeros unbounded below — for every `M`
there is a zero `< M`. Intervals of length π/√c pushed into (−∞,−c] as c→∞. -/
theorem sturm_unbounded_zeros (f f' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (x * f x) x) (M : ℝ) :
    ∃ x, x < M ∧ f x = 0 := by
  set c := |M| + 1 with hcdef
  have hc : 0 < c := by rw [hcdef]; positivity
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  set a := -c - π / Real.sqrt c with hadef
  have hax : a + π / Real.sqrt c ≤ -c := by rw [hadef]; linarith
  obtain ⟨x, hxmem, hxzero⟩ := sturm_has_zero f f' a c hc hf hf' hax
  refine ⟨x, ?_, hxzero⟩
  have hxle : x ≤ a + π / Real.sqrt c := hxmem.2
  have heq : a + π / Real.sqrt c = -c := by rw [hadef]; ring
  rw [heq] at hxle
  have hcM : -c < M := by rw [hcdef]; have := neg_abs_le M; linarith
  linarith

/-- **The Airy function oscillates**: `airyFun c0 c1` has zeros unbounded below (infinitely many
zeros heading to −∞). For the quantum bouncer these are the gravitational energy levels. -/
theorem airyFun_unbounded_zeros (c0 c1 : ℝ) (M : ℝ) :
    ∃ x, x < M ∧ airyFun c0 c1 x = 0 := by
  refine sturm_unbounded_zeros (airyFun c0 c1) (deriv (airyFun c0 c1)) (fun x => ?_) (fun x => ?_) M
  · exact ((airyFun_entire c0 c1) x (mem_univ x)).differentiableAt.hasDerivAt
  · have hd := ((airyFun_entire c0 c1).deriv x (mem_univ x)).differentiableAt.hasDerivAt
    rwa [airyFun_ode c0 c1 x] at hd

/- ── Behaviour on (0,∞) — dominant (non-decaying) solutions ──────────────────────────────── -/

/-- If `f'' = g ≥ 0` on `[a,b]` and `f'(a) ≥ 0`, then `f` is non-decreasing on `[a,b]`
(`f'` non-decreasing ⟹ `f' ≥ f'(a) ≥ 0` ⟹ `f` non-decreasing). -/
theorem nondecr_of_deriv2_nonneg (f f' g : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (g x) x)
    (hg : ∀ x ∈ Icc a b, 0 ≤ g x) (hfa' : 0 ≤ f' a) :
    MonotoneOn f (Icc a b) := by
  have hf'mono : MonotoneOn f' (Icc a b) :=
    monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (fun x _ => (hf' x).continuousAt.continuousWithinAt)
      (fun x _ => (hf' x).differentiableAt.differentiableWithinAt)
      (fun x hx => by rw [(hf' x).deriv]; exact hg x (interior_subset hx))
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    (fun x _ => (hf x).continuousAt.continuousWithinAt)
    (fun x _ => (hf x).differentiableAt.differentiableWithinAt)
  intro x hx
  rw [(hf x).deriv]
  have hxmem : x ∈ Icc a b := interior_subset hx
  have hmono := hf'mono (left_mem_Icc.mpr hab) hxmem hxmem.1
  linarith

/-- **On (0,∞), a solution of y''=xy positive with non-negative slope stays positive.** It is convex
where positive, so once non-decreasing it cannot return to 0 (first-zero argument). -/
theorem ode_pos_Ici (f f' : ℝ → ℝ) {x0 : ℝ} (hx0 : 0 ≤ x0)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (x * f x) x)
    (hfx0 : 0 < f x0) (hfx0' : 0 ≤ f' x0) :
    ∀ x ∈ Ici x0, 0 < f x := by
  have hdiff : Differentiable ℝ f := fun x => (hf x).differentiableAt
  have hcontf : Continuous f := hdiff.continuous
  intro X hX
  by_contra hfX
  push Not at hfX
  have hx0X : x0 ≤ X := hX
  set S := Icc x0 X ∩ {x | f x = 0} with hSdef
  have hScompact : IsCompact S := isCompact_Icc.inter_right (isClosed_eq hcontf continuous_const)
  have hSne : S.Nonempty := by
    obtain ⟨y, hy, hfy⟩ := intermediate_value_Icc' hx0X hcontf.continuousOn ⟨hfX, hfx0.le⟩
    exact ⟨y, hy, hfy⟩
  obtain ⟨c, ⟨hcIcc, hfc⟩, hclb⟩ := hScompact.exists_isLeast hSne
  have hx0c : x0 < c := lt_of_le_of_ne hcIcc.1 (by rintro rfl; rw [hfc] at hfx0; exact lt_irrefl 0 hfx0)
  have hfpos : ∀ y ∈ Icc x0 c, 0 ≤ f y := by
    intro y hy
    rcases eq_or_lt_of_le hy.2 with hyc | hyc
    · rw [hyc]; exact le_of_eq hfc.symm
    · have hynz : ∀ z ∈ Icc x0 y, f z ≠ 0 := by
        intro z hz hfz
        have hzS : z ∈ S := ⟨⟨hz.1, le_trans hz.2 (le_trans hyc.le hcIcc.2)⟩, hfz⟩
        have := hclb hzS
        linarith [hz.2, hyc]
      rcases const_sign_of_no_zero hcontf.continuousOn hynz hy.1 with hp | hn
      · exact (hp y (right_mem_Icc.mpr hy.1)).le
      · exact absurd (hn x0 (left_mem_Icc.mpr hy.1)) (by linarith [hfx0])
  have hmono : MonotoneOn f (Icc x0 c) :=
    nondecr_of_deriv2_nonneg f f' (fun x => x * f x) x0 c hcIcc.1 hf hf'
      (fun x hx => mul_nonneg (by linarith [hx.1] : (0:ℝ) ≤ x) (hfpos x hx)) hfx0'
  have hle := hmono (left_mem_Icc.mpr hx0c.le) (right_mem_Icc.mpr hx0c.le) hx0c.le
  rw [hfc] at hle
  linarith

/-- Such a solution is non-decreasing on `[x0,∞)`. -/
theorem ode_nondecreasing_Ici (f f' : ℝ → ℝ) {x0 : ℝ} (hx0 : 0 < x0)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (x * f x) x)
    (hfx0 : 0 < f x0) (hfx0' : 0 ≤ f' x0) :
    MonotoneOn f (Ici x0) := by
  have hpos := ode_pos_Ici f f' hx0.le hf hf' hfx0 hfx0'
  intro u hu v hv huv
  have hmono : MonotoneOn f (Icc x0 v) :=
    nondecr_of_deriv2_nonneg f f' (fun x => x * f x) x0 v hv hf hf'
      (fun x hx => mul_nonneg (by linarith [hx.1] : (0:ℝ) ≤ x) (hpos x hx.1).le) hfx0'
  exact hmono ⟨hu, huv⟩ ⟨hv, le_refl v⟩ huv

/-- **A dominant solution does not decay**: positive with non-negative slope at some `x0>0` ⟹ it
stays `≥ f x0 > 0`, so it cannot tend to `0` at `+∞`. -/
theorem ode_not_tendsto_zero (f f' : ℝ → ℝ) {x0 : ℝ} (hx0 : 0 < x0)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (x * f x) x)
    (hfx0 : 0 < f x0) (hfx0' : 0 ≤ f' x0) :
    ¬ Tendsto f atTop (𝓝 0) := by
  intro hT
  have hmono := ode_nondecreasing_Ici f f' hx0 hf hf' hfx0 hfx0'
  have h1 : ∀ᶠ x in atTop, f x < f x0 := hT.eventually (Iio_mem_nhds hfx0)
  have h2 : ∀ᶠ x in atTop, f x0 ≤ f x :=
    (eventually_ge_atTop x0).mono (fun x hx => hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx)
  obtain ⟨x, hx1, hx2⟩ := (h1.and h2).exists
  linarith

/-- `airyFun` and its derivative as `HasDerivAt` facts (from entire + the ODE). -/
theorem airyFun_hasDerivAt (c0 c1 : ℝ) (x : ℝ) :
    HasDerivAt (airyFun c0 c1) (deriv (airyFun c0 c1) x) x :=
  ((airyFun_entire c0 c1) x (mem_univ x)).differentiableAt.hasDerivAt

theorem airyFun_deriv_hasDerivAt (c0 c1 : ℝ) (x : ℝ) :
    HasDerivAt (deriv (airyFun c0 c1)) (x * airyFun c0 c1 x) x := by
  have hd := ((airyFun_entire c0 c1).deriv x (mem_univ x)).differentiableAt.hasDerivAt
  rwa [airyFun_ode c0 c1 x] at hd

/-- **Dominant Airy solutions.** If `F = airyFun c0 c1` is positive with non-negative slope at
some `x0>0`, then on `[x0,∞)` it is positive and non-decreasing, and it does NOT decay to 0 at `+∞`.
(The recessive solution, which does decay, is constructed below by reduction of order:
`exists_recessive_solution`, `exists_entire_recessive`.) -/
theorem airyFun_not_decaying (c0 c1 : ℝ) {x0 : ℝ} (hx0 : 0 < x0)
    (hpos : 0 < airyFun c0 c1 x0) (hslope : 0 ≤ deriv (airyFun c0 c1) x0) :
    (∀ x ∈ Ici x0, 0 < airyFun c0 c1 x) ∧ MonotoneOn (airyFun c0 c1) (Ici x0) ∧
      ¬ Tendsto (airyFun c0 c1) atTop (𝓝 0) :=
  ⟨ode_pos_Ici _ _ hx0.le (airyFun_hasDerivAt c0 c1) (airyFun_deriv_hasDerivAt c0 c1) hpos hslope,
   ode_nondecreasing_Ici _ _ hx0 (airyFun_hasDerivAt c0 c1) (airyFun_deriv_hasDerivAt c0 c1) hpos hslope,
   ode_not_tendsto_zero _ _ hx0 (airyFun_hasDerivAt c0 c1) (airyFun_deriv_hasDerivAt c0 c1) hpos hslope⟩

/- ── The quantum bouncer ──────────────────────────────────────────────────────────────────
   H = −(ℏ²/2m)∂² + mgx on [0,∞), ψ(0)=0.  Rescaling ξ = α(x − E/(mg)) with α=(2m²g/ℏ²)^{1/3} turns
   Hψ=Eψ into the Airy equation; the eigenfunction is `ψ(x) = F(αx − β)` with β ∝ E, and the
   Dirichlet wall ψ(0)=0 becomes `Ai(−β)=0`. So the gravitational levels are (−) the zeros of Ai. -/

/-- **Bridge**: `ψ(x) = F(αx − β)` (F any Airy solution) solves the rescaled Airy/bouncer equation
`ψ'' = α²(αx − β)·ψ`. Pure chain rule on `airyFun_ode`. -/
theorem bouncer_ode (c0 c1 α β : ℝ) (x : ℝ) :
    deriv (deriv (fun y => airyFun c0 c1 (α * y - β))) x
      = α ^ 2 * (α * x - β) * airyFun c0 c1 (α * x - β) := by
  have hg : ∀ y, HasDerivAt (fun y => α * y - β) α y :=
    fun y => by simpa using ((hasDerivAt_id y).const_mul α).sub_const β
  have hψ' : ∀ y, HasDerivAt (fun y => airyFun c0 c1 (α * y - β))
      (deriv (airyFun c0 c1) (α * y - β) * α) y :=
    fun y => by
      simpa [Function.comp_def] using (airyFun_hasDerivAt c0 c1 (α * y - β)).comp y (hg y)
  have hderivψ : deriv (fun y => airyFun c0 c1 (α * y - β))
      = fun y => deriv (airyFun c0 c1) (α * y - β) * α := funext fun y => (hψ' y).deriv
  rw [hderivψ]
  have hψ'' : HasDerivAt (fun y => deriv (airyFun c0 c1) (α * y - β) * α)
      ((α * x - β) * airyFun c0 c1 (α * x - β) * α * α) x := by
    have h1 : HasDerivAt (fun y => deriv (airyFun c0 c1) (α * y - β))
        ((α * x - β) * airyFun c0 c1 (α * x - β) * α) x := by
      simpa [Function.comp_def] using (airyFun_deriv_hasDerivAt c0 c1 (α * x - β)).comp x (hg x)
    simpa using h1.mul_const α
  rw [hψ''.deriv]; ring

/-- **Boundary wall**: the Dirichlet condition `ψ(0)=0` is exactly `Ai(−β)=0`. -/
theorem bouncer_bc (c0 c1 α β : ℝ) :
    (fun y => airyFun c0 c1 (α * y - β)) 0 = airyFun c0 c1 (-β) := by
  simp

/-- **Infinitely many bound-state energies.** For every bound `B` there is a (rescaled) energy
`β > B` with `Ai(−β)=0`, i.e. the quantum bouncer has infinitely many gravitational levels, given by
the (negatives of the) Airy zeros. This is a consequence of the oscillation theorem. -/
theorem bouncer_levels_infinite (c0 c1 : ℝ) (B : ℝ) :
    ∃ β, B < β ∧ airyFun c0 c1 (-β) = 0 := by
  obtain ⟨z, hz, hfz⟩ := airyFun_unbounded_zeros c0 c1 (-B)
  exact ⟨-z, by linarith, by simpa using hfz⟩

/- ── Existence of the decaying (recessive) Airy solution ────────────────────────
   Reduction of order from the dominant solution f = airyFun 1 0 (which does not decay):
   Ai_rec(x) = f(x)·∫_x^∞ dt/f(t)²  is a positive solution decaying to 0. Validated numerically
   (Ai_rec/Ai ≡ const, Ai_rec ≤ 1/f', Ai_rec'' = x·Ai_rec). -/

/-- `airyFun c0 c1` at 0 is `c0` (the constant term of the series). -/
theorem airyFun_zero (c0 c1 : ℝ) : airyFun c0 c1 0 = c0 := by
  have h : airyFun c0 c1 0 = ofScalarsSum (coeffR c0 c1) 0 := rfl
  rw [h, ofScalarsSum_zero]; simp [coeffR]

/-- `(airyFun c0 c1)'(0) = c1` (the linear coefficient). -/
theorem deriv_airyFun_zero (c0 c1 : ℝ) : deriv (airyFun c0 c1) 0 = c1 := by
  have h : HasDerivAt (airyFun c0 c1) ((airySeries c0 c1) 1 (fun _ => 1)) 0 :=
    (airyFun_hasFPowerSeries c0 c1).hasFPowerSeriesAt.hasDerivAt
  rw [h.deriv]
  simp [airySeries, coeffR]

/-- The dominant solution `f = airyFun 1 0` is strictly positive on `[0,∞)`
(it has `f(0)=1>0`, `f'(0)=0`, and `f''=xf≥0`, so the first-zero argument applies from `x0=0`). -/
theorem airyFun10_pos : ∀ x ∈ Ici (0:ℝ), 0 < airyFun 1 0 x :=
  ode_pos_Ici (airyFun 1 0) (deriv (airyFun 1 0)) (le_refl 0)
    (airyFun_hasDerivAt 1 0) (airyFun_deriv_hasDerivAt 1 0)
    (by rw [airyFun_zero]; exact one_pos)
    (le_of_eq (deriv_airyFun_zero 1 0).symm)

/- ── Recessive solution, prerequisites: f = airyFun 1 0 is dominant on [0,∞) ──────────────────────── -/

theorem airyFun10_diff : Differentiable ℝ (airyFun 1 0) :=
  fun x => (airyFun_hasDerivAt 1 0 x).differentiableAt

theorem airyFun10_deriv_diff : Differentiable ℝ (deriv (airyFun 1 0)) :=
  fun x => (airyFun_deriv_hasDerivAt 1 0 x).differentiableAt

/-- `f'` is non-negative on `[0,∞)` (it is non-decreasing, with `f'(0)=0`). -/
theorem airyFun10_deriv_nonneg : ∀ x ∈ Ici (0:ℝ), 0 ≤ deriv (airyFun 1 0) x := by
  have hmono : MonotoneOn (deriv (airyFun 1 0)) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      airyFun10_deriv_diff.continuous.continuousOn airyFun10_deriv_diff.differentiableOn
    intro x hx
    rw [interior_Ici] at hx
    rw [(airyFun_deriv_hasDerivAt 1 0 x).deriv]
    exact mul_nonneg hx.le (airyFun10_pos x (mem_Ici.mpr hx.le)).le
  intro x hx
  have h := hmono self_mem_Ici hx (mem_Ici.mp hx)
  rwa [deriv_airyFun_zero] at h

/-- `f ≥ 1` on `[0,∞)` (non-decreasing, with `f(0)=1`). -/
theorem airyFun10_ge_one : ∀ x ∈ Ici (0:ℝ), 1 ≤ airyFun 1 0 x := by
  have hmono : MonotoneOn (airyFun 1 0) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      airyFun10_diff.continuous.continuousOn airyFun10_diff.differentiableOn
    intro x hx
    rw [interior_Ici] at hx
    exact airyFun10_deriv_nonneg x (mem_Ici.mpr hx.le)
  intro x hx
  have h := hmono self_mem_Ici hx (mem_Ici.mp hx)
  rwa [airyFun_zero] at h

/-- `f` is convex on `[0,∞)` (since `f'' = x·f ≥ 0`). -/
theorem airyFun10_convex : ConvexOn ℝ (Ici (0:ℝ)) (airyFun 1 0) := by
  apply convexOn_of_deriv2_nonneg (convex_Ici 0) airyFun10_diff.continuous.continuousOn
    airyFun10_diff.differentiableOn airyFun10_deriv_diff.differentiableOn
  intro x hx
  rw [interior_Ici] at hx
  have he : deriv^[2] (airyFun 1 0) x = x * airyFun 1 0 x := by
    have : deriv^[2] (airyFun 1 0) = deriv (deriv (airyFun 1 0)) := by
      funext y; rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply]
    rw [this, (airyFun_deriv_hasDerivAt 1 0 x).deriv]
  rw [he]; exact mul_nonneg hx.le (airyFun10_pos x (mem_Ici.mpr hx.le)).le

/-- `f'(x) ≥ x²/2` on `[0,∞)` (so `f' → ∞`). From `h=f'−x²/2`, `h(0)=0`, `h'=x(f−1)≥0`. -/
theorem airyFun10_deriv_ge_sq : ∀ x ∈ Ici (0:ℝ), x ^ 2 / 2 ≤ deriv (airyFun 1 0) x := by
  have hd : ∀ x, HasDerivAt (fun y => deriv (airyFun 1 0) y - y ^ 2 / 2)
      (x * airyFun 1 0 x - x) x := by
    intro x
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
      simpa using (hasDerivAt_pow 2 x).div_const 2
    simpa using (airyFun_deriv_hasDerivAt 1 0 x).fun_sub h2
  have hmono : MonotoneOn (fun y => deriv (airyFun 1 0) y - y ^ 2 / 2) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [interior_Ici] at hx
    rw [(hd x).deriv]
    nlinarith [airyFun10_ge_one x (mem_Ici.mpr (mem_Ioi.mp hx).le), (mem_Ioi.mp hx).le]
  intro x hx
  have h := hmono self_mem_Ici hx (mem_Ici.mp hx)
  simp only [deriv_airyFun_zero] at h
  linarith [h]

/- ── Recessive solution: integrability of 1/f² on (x,∞) ──────────────────────────────────────────── -/

/-- `(z⁻¹)²` as a real power, for `z>0`. -/
theorem inv_sq_eq_rpow {z : ℝ} (_hz : 0 < z) : (z⁻¹) ^ 2 = z ^ (-2:ℝ) := by
  rw [show (-2:ℝ) = ((-2:ℤ):ℝ) by norm_num, Real.rpow_intCast, zpow_neg, zpow_two, mul_inv]; ring

/-- The affine tangent bound `(c+m(t−x))⁻²` is integrable on `(x,∞)` for `c,m>0`. -/
theorem integrableOn_affine_inv_sq (x c m : ℝ) (hc : 0 < c) (hm : 0 < m) :
    IntegrableOn (fun t => ((c + m * (t - x))⁻¹) ^ 2) (Ioi x) := by
  have hcm : 0 < c / m := div_pos hc hm
  have hrpow : IntegrableOn (fun t : ℝ => (t + (c / m - x)) ^ (-2:ℝ)) (Ioi x) :=
    integrableOn_add_rpow_Ioi_of_lt (by norm_num) (by linarith)
  have hg : IntegrableOn (fun t : ℝ => m ^ (-2:ℝ) * (t + (c / m - x)) ^ (-2:ℝ)) (Ioi x) :=
    hrpow.const_mul _
  refine hg.congr_fun ?_ measurableSet_Ioi
  intro t ht
  have hxt : x < t := ht
  have hb : 0 < t + (c / m - x) := by have := hcm; linarith
  show m ^ (-2:ℝ) * (t + (c / m - x)) ^ (-2:ℝ) = ((c + m * (t - x))⁻¹) ^ 2
  rw [show c + m * (t - x) = m * (t + (c / m - x)) by field_simp; ring,
    mul_inv, mul_pow, inv_sq_eq_rpow hm, inv_sq_eq_rpow hb]

/-- **`1/f²` is integrable on `(x,∞)` for `x>0`** (f = airyFun 1 0): dominated by the convexity
tangent bound `f(t) ≥ f(x)+f'(x)(t−x)`, which is integrable. -/
theorem integrableOn_airyFun10_inv_sq {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => (airyFun 1 0 t)⁻¹ ^ 2) (Ioi x) := by
  have hfx : 0 < airyFun 1 0 x := airyFun10_pos x (mem_Ici.mpr hx.le)
  have hfx' : 0 < deriv (airyFun 1 0) x :=
    lt_of_lt_of_le (by positivity) (airyFun10_deriv_ge_sq x (mem_Ici.mpr hx.le))
  have hdom := integrableOn_affine_inv_sq x (airyFun 1 0 x) (deriv (airyFun 1 0) x) hfx hfx'
  have hcont : ContinuousOn (fun t => (airyFun 1 0 t)⁻¹ ^ 2) (Ioi x) :=
    ((airyFun10_diff.continuous.continuousOn.inv₀
      (fun t ht => (airyFun10_pos t (mem_Ici.mpr (le_of_lt (lt_trans hx ht)))).ne')).pow 2)
  refine hdom.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hxt : x < t := ht
  have htx : 0 < t - x := by linarith
  have hft : 0 < airyFun 1 0 t := airyFun10_pos t (mem_Ici.mpr (le_of_lt (lt_trans hx ht)))
  have hAt : 0 < airyFun 1 0 x + deriv (airyFun 1 0) x * (t - x) := by
    have := mul_pos hfx' htx; linarith
  have hAle : airyFun 1 0 x + deriv (airyFun 1 0) x * (t - x) ≤ airyFun 1 0 t := by
    have hsl := airyFun10_convex.le_slope_of_hasDerivAt (mem_Ici.mpr hx.le)
      (mem_Ici.mpr (le_of_lt (lt_trans hx ht))) hxt (airyFun_hasDerivAt 1 0 x)
    rw [slope_def_field, le_div_iff₀ htx] at hsl
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hinv : (airyFun 1 0 t)⁻¹ ≤ (airyFun 1 0 x + deriv (airyFun 1 0) x * (t - x))⁻¹ := by
    rw [← one_div, ← one_div]; exact one_div_le_one_div_of_le hAt hAle
  exact pow_le_pow_left₀ (by positivity) hinv 2

/- ── Recessive solution: the construction Ai_rec = f·∫_x^∞ 1/f² ──────────────────────────────────── -/

/-- FTC on a half-line (reference `b`): `d/dx ∫_x^∞ h = -h(a)` for `a > b`, `h` continuous on
`[b,∞)` and integrable on `(b,∞)`. -/
theorem hasDerivAt_integral_Ioi {h : ℝ → ℝ} {b a : ℝ} (hba : b < a)
    (hcont : ContinuousOn h (Ici b)) (hint : IntegrableOn h (Ioi b)) :
    HasDerivAt (fun x => ∫ t in Ioi x, h t) (-(h a)) a := by
  have key : ∀ x ∈ Ioi b, (∫ t in Ioi x, h t) = (∫ t in Ioi b, h t) - ∫ t in b..x, h t := by
    intro x hx
    have hbx : b ≤ x := le_of_lt hx
    have hu : Ioc b x ∪ Ioi x = Ioi b := Ioc_union_Ioi_eq_Ioi hbx
    have hIoc : IntegrableOn h (Ioc b x) := hint.mono_set (hu ▸ subset_union_left)
    have hIoix : IntegrableOn h (Ioi x) := hint.mono_set (hu ▸ subset_union_right)
    have hsplit := setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hIoc hIoix
    rw [hu] at hsplit
    rw [intervalIntegral.integral_of_le hbx]; linarith
  have hInt : IntervalIntegrable h volume b a :=
    (hcont.mono (by rw [Set.uIcc_of_le hba.le]; exact Set.Icc_subset_Ici_self)).intervalIntegrable
  have hMeas : StronglyMeasurableAtFilter h (𝓝 a) volume :=
    ⟨Ici b, Ici_mem_nhds hba, hcont.aestronglyMeasurable measurableSet_Ici⟩
  have hftc : HasDerivAt (fun x => ∫ t in b..x, h t) (h a) a :=
    intervalIntegral.integral_hasDerivAt_right hInt hMeas (hcont.continuousAt (Ici_mem_nhds hba))
  have hcomb : HasDerivAt (fun x => (∫ t in Ioi b, h t) - ∫ t in b..x, h t) (-(h a)) a := by
    simpa using (hasDerivAt_const a (∫ t in Ioi b, h t)).fun_sub hftc
  exact hcomb.congr_of_eventuallyEq
    (by filter_upwards [Ioi_mem_nhds hba] with x hx using key x hx)

/-- The reduction-of-order integral `∫_x^∞ dt/f(t)²`. -/
noncomputable def airyRecInt (x : ℝ) : ℝ := ∫ t in Ioi x, (airyFun 1 0 t)⁻¹ ^ 2

/-- The recessive Airy solution on `(0,∞)`: `Ai_rec(x) = f(x)·∫_x^∞ dt/f(t)²`. -/
noncomputable def airyRec (x : ℝ) : ℝ := airyFun 1 0 x * airyRecInt x

/-- `1/f²` is continuous on `[b,∞)` for `b>0`. -/
theorem continuousOn_airyFun10_inv_sq {b : ℝ} (hb : 0 < b) :
    ContinuousOn (fun t => (airyFun 1 0 t)⁻¹ ^ 2) (Ici b) :=
  (airyFun10_diff.continuous.continuousOn.inv₀
    (fun t ht => (airyFun10_pos t (mem_Ici.mpr (le_trans hb.le ht))).ne')).pow 2

/-- `d/dx airyRecInt = -1/f(x)²` for `x>0`. -/
theorem airyRecInt_hasDerivAt {a : ℝ} (ha : 0 < a) :
    HasDerivAt airyRecInt (-(airyFun 1 0 a)⁻¹ ^ 2) a :=
  hasDerivAt_integral_Ioi (by linarith : a / 2 < a)
    (continuousOn_airyFun10_inv_sq (by linarith : (0:ℝ) < a / 2))
    (integrableOn_airyFun10_inv_sq (by linarith : (0:ℝ) < a / 2))

/-- First derivative of `Ai_rec`: `Ai_rec' = f'·g − 1/f` (product rule; `f·(1/f²) = 1/f`). -/
theorem airyRec_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt airyRec (deriv (airyFun 1 0) x * airyRecInt x - (airyFun 1 0 x)⁻¹) x := by
  have hfx : airyFun 1 0 x ≠ 0 := (airyFun10_pos x (mem_Ici.mpr hx.le)).ne'
  have h := (airyFun_hasDerivAt 1 0 x).mul (airyRecInt_hasDerivAt hx)
  convert h using 1
  · ext y; simp only [airyRec, Pi.mul_apply]
  · field_simp; ring

/-- **Reduction of order**: `Ai_rec'' = x·Ai_rec` — the `1/f²` terms cancel, leaving `f''·g = xf·g`.
So `Ai_rec` solves `y''=xy` on `(0,∞)`. -/
theorem airyRec_deriv_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => deriv (airyFun 1 0) y * airyRecInt y - (airyFun 1 0 y)⁻¹)
      (x * airyRec x) x := by
  have hfx : airyFun 1 0 x ≠ 0 := (airyFun10_pos x (mem_Ici.mpr hx.le)).ne'
  have h := ((airyFun_deriv_hasDerivAt 1 0 x).mul (airyRecInt_hasDerivAt hx)).sub
    ((airyFun_hasDerivAt 1 0 x).inv hfx)
  convert h using 1
  simp only [airyRec]
  field_simp
  ring

/-- The convexity integral bound: `∫_x^∞ 1/f² ≤ 1/(f'(x)·f(x))` for `x>0`. The tangent bound
dominates by the affine `(c+m(t−x))⁻²`, whose exact tail integral is `1/(mc)`. -/
theorem airyRecInt_le {x : ℝ} (hx : 0 < x) :
    airyRecInt x ≤ (deriv (airyFun 1 0) x * airyFun 1 0 x)⁻¹ := by
  set c := airyFun 1 0 x with hc
  set m := deriv (airyFun 1 0) x with hm
  have hcp : 0 < c := airyFun10_pos x (mem_Ici.mpr hx.le)
  have hmp : 0 < m := lt_of_lt_of_le (by positivity) (airyFun10_deriv_ge_sq x (mem_Ici.mpr hx.le))
  -- exact tail integral of the affine bound
  have hAval : (∫ t in Ioi x, ((c + m * (t - x))⁻¹) ^ 2) = (m * c)⁻¹ := by
    have hderiv : ∀ t ∈ Ici x,
        HasDerivAt (fun s => -m⁻¹ * (c + m * (s - x))⁻¹) (((c + m * (t - x))⁻¹) ^ 2) t := by
      intro t ht
      have hAt : (0:ℝ) < c + m * (t - x) := by have : x ≤ t := ht; nlinarith
      have hA : HasDerivAt (fun s : ℝ => c + m * (s - x)) m t := by
        simpa using (((hasDerivAt_id t).sub_const x).const_mul m).const_add c
      have hAinv := hA.inv hAt.ne'
      have hres := hAinv.const_mul (-m⁻¹)
      convert hres using 1
      field_simp [hmp.ne', hAt.ne']
    have hAtop : Tendsto (fun t : ℝ => c + m * (t - x)) atTop atTop := by
      apply tendsto_atTop_add_const_left atTop c
      simpa [sub_eq_add_neg] using Filter.Tendsto.const_mul_atTop hmp
        (tendsto_atTop_add_const_right atTop (-x) tendsto_id)
    have htend : Tendsto (fun t : ℝ => -m⁻¹ * (c + m * (t - x))⁻¹) atTop (𝓝 0) := by
      have := ((tendsto_inv_atTop_zero.comp hAtop).const_mul m⁻¹).neg
      simpa using this
    have key := integral_Ioi_of_hasDerivAt_of_tendsto'
      hderiv (integrableOn_affine_inv_sq x c m hcp hmp) htend
    rw [key]; simp [mul_comm]
  -- comparison 1/f² ≤ 1/A² and conclude
  rw [airyRecInt, ← hAval]
  refine setIntegral_mono_on (integrableOn_airyFun10_inv_sq hx)
    (integrableOn_affine_inv_sq x c m hcp hmp) measurableSet_Ioi (fun t ht => ?_)
  have hxt : x < t := ht
  have htx : 0 < t - x := by linarith
  have hft : 0 < airyFun 1 0 t := airyFun10_pos t (mem_Ici.mpr (le_of_lt (lt_trans hx ht)))
  have hAt : 0 < c + m * (t - x) := by have := mul_pos hmp htx; linarith
  have hAle : c + m * (t - x) ≤ airyFun 1 0 t := by
    have hsl := airyFun10_convex.le_slope_of_hasDerivAt (mem_Ici.mpr hx.le)
      (mem_Ici.mpr (le_of_lt (lt_trans hx ht))) hxt (airyFun_hasDerivAt 1 0 x)
    rw [slope_def_field, le_div_iff₀ htx] at hsl
    linarith
  have hinv : (airyFun 1 0 t)⁻¹ ≤ (c + m * (t - x))⁻¹ := by
    rw [← one_div, ← one_div]; exact one_div_le_one_div_of_le hAt hAle
  exact pow_le_pow_left₀ (by positivity) hinv 2

/-- `Ai_rec(x) ≤ 1/f'(x)` for `x>0` (from the integral bound: `f·1/(f'f) = 1/f'`). -/
theorem airyRec_le_inv_deriv {x : ℝ} (hx : 0 < x) :
    airyRec x ≤ (deriv (airyFun 1 0) x)⁻¹ := by
  have hfx : 0 < airyFun 1 0 x := airyFun10_pos x (mem_Ici.mpr hx.le)
  have hmp : 0 < deriv (airyFun 1 0) x :=
    lt_of_lt_of_le (by positivity) (airyFun10_deriv_ge_sq x (mem_Ici.mpr hx.le))
  rw [airyRec]
  calc airyFun 1 0 x * airyRecInt x
      ≤ airyFun 1 0 x * (deriv (airyFun 1 0) x * airyFun 1 0 x)⁻¹ :=
        mul_le_mul_of_nonneg_left (airyRecInt_le hx) hfx.le
    _ = (deriv (airyFun 1 0) x)⁻¹ := by field_simp

/-- `Ai_rec ≥ 0` on `(0,∞)`. -/
theorem airyRec_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ airyRec x := by
  rw [airyRec]
  refine mul_nonneg (airyFun10_pos x (mem_Ici.mpr hx.le)).le ?_
  rw [airyRecInt]
  exact setIntegral_nonneg measurableSet_Ioi (fun t _ => by positivity)

/-- **The recessive solution decays**: `Ai_rec(x) → 0` as `x → +∞`
(`0 ≤ Ai_rec ≤ 1/f' ≤ 2/x² → 0`). -/
theorem airyRec_tendsto_zero : Tendsto airyRec atTop (𝓝 0) := by
  have hg : Tendsto (fun x : ℝ => 2 / x ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx using airyRec_nonneg hx
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    have hsq : (0:ℝ) < x ^ 2 / 2 := by positivity
    have hbd : (deriv (airyFun 1 0) x)⁻¹ ≤ 2 / x ^ 2 := by
      have h1 : (deriv (airyFun 1 0) x)⁻¹ ≤ (x ^ 2 / 2)⁻¹ := by
        rw [← one_div, ← one_div]
        exact one_div_le_one_div_of_le hsq (airyFun10_deriv_ge_sq x (mem_Ici.mpr hx.le))
      rwa [show (x ^ 2 / 2)⁻¹ = 2 / x ^ 2 by rw [inv_div]] at h1
    exact le_trans (airyRec_le_inv_deriv hx) hbd

/-- **The Wronskian `W(f, Ai_rec) = f·Ai_rec' − f'·Ai_rec = −1`** (constant; the synthesis identity).
The `f·g` terms cancel, leaving `−f·(1/f) = −1`. -/
theorem airyRec_wronskian {x : ℝ} (hx : 0 < x) :
    airyFun 1 0 x * (deriv (airyFun 1 0) x * airyRecInt x - (airyFun 1 0 x)⁻¹)
      - deriv (airyFun 1 0) x * airyRec x = -1 := by
  have hfx : airyFun 1 0 x ≠ 0 := (airyFun10_pos x (mem_Ici.mpr hx.le)).ne'
  rw [airyRec]; field_simp; ring

/-- **Existence of the recessive solution.** There is a non-trivial real solution `y` of `y''=xy`
on `(0,∞)` that decays to `0` at `+∞`. (`y = Ai_rec`; non-triviality from `W(1)=−1≠0`.) This is the
decaying solution whose existence the DLMF §9.7 asymptotics classically guarantee — here built and
verified by reduction of order, with no asymptotics. -/
theorem exists_recessive_solution :
    ∃ y y' : ℝ → ℝ, (y 1 ≠ 0 ∨ y' 1 ≠ 0) ∧ Tendsto y atTop (𝓝 0) ∧
      (∀ x, 0 < x → HasDerivAt y (y' x) x) ∧ (∀ x, 0 < x → HasDerivAt y' (x * y x) x) := by
  refine ⟨airyRec,
    fun x => deriv (airyFun 1 0) x * airyRecInt x - (airyFun 1 0 x)⁻¹,
    ?_, airyRec_tendsto_zero,
    fun x hx => airyRec_hasDerivAt hx, fun x hx => airyRec_deriv_hasDerivAt hx⟩
  by_contra h
  push Not at h
  obtain ⟨h1, h2'⟩ := h
  have h2 : deriv (airyFun 1 0) 1 * airyRecInt 1 - (airyFun 1 0 1)⁻¹ = 0 := h2'
  have hW := airyRec_wronskian one_pos
  rw [h1, h2] at hW
  norm_num at hW

/-! ### Entire extension of the recessive solution (linearity + Wronskian + quotient identity) -/

/-- **Linearity of the Airy coefficient recurrence.** `coeffR` is linear in the initial data,
because the recurrence `a_{k+3}=a_k/((k+2)(k+3))` is linear. -/
theorem coeffR_linear (c0 c1 : ℝ) (n : ℕ) :
    coeffR c0 c1 n = c0 * coeffR 1 0 n + c1 * coeffR 0 1 n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | _ | k
    · simp [coeffR]
    · simp [coeffR]
    · simp [coeffR]
    · rw [coeffR_succ3, coeffR_succ3, coeffR_succ3, ih k (by omega)]; ring

/-- The Airy power-series terms are summable at every point (entire). -/
theorem summable_coeffR_term (c0 c1 x : ℝ) : Summable (fun n => coeffR c0 c1 n * x ^ n) := by
  apply Summable.of_norm
  have h := summable_coeffR_norm c0 c1 (Real.toNNReal |x|)
  refine h.congr (fun n => ?_)
  simp [norm_mul, norm_pow, Real.norm_eq_abs]

/-- **Linearity of `airyFun`** in the initial data: `airyFun c0 c1 = c0·f + c1·g` with
`f = airyFun 1 0`, `g = airyFun 0 1`. -/
theorem airyFun_linear (c0 c1 x : ℝ) :
    airyFun c0 c1 x = c0 * airyFun 1 0 x + c1 * airyFun 0 1 x := by
  show ofScalarsSum (coeffR c0 c1) x
    = c0 * ofScalarsSum (coeffR 1 0) x + c1 * ofScalarsSum (coeffR 0 1) x
  rw [ofScalars_sum_eq, ofScalars_sum_eq, ofScalars_sum_eq]
  simp only [smul_eq_mul]
  rw [← tsum_mul_left, ← tsum_mul_left,
    ← Summable.tsum_add ((summable_coeffR_term 1 0 x).mul_left c0)
      ((summable_coeffR_term 0 1 x).mul_left c1)]
  apply tsum_congr; intro n
  rw [coeffR_linear c0 c1 n]; ring

/-- **The basis Wronskian `W(f,g) = f·g' − f'·g ≡ 1`** (Abel's identity): constant because both
solve `y''=x·y`, and `=1` at `0` from `f(0)=1, f'(0)=0, g(0)=0, g'(0)=1`. -/
theorem wronskian_fg (x : ℝ) :
    airyFun 1 0 x * deriv (airyFun 0 1) x - deriv (airyFun 1 0) x * airyFun 0 1 x = 1 := by
  set W : ℝ → ℝ := fun y =>
    airyFun 1 0 y * deriv (airyFun 0 1) y - deriv (airyFun 1 0) y * airyFun 0 1 y with hWdef
  have hderiv : ∀ y, HasDerivAt W 0 y := by
    intro y
    have h := ((airyFun_hasDerivAt 1 0 y).mul (airyFun_deriv_hasDerivAt 0 1 y)).sub
      ((airyFun_deriv_hasDerivAt 1 0 y).mul (airyFun_hasDerivAt 0 1 y))
    convert h using 1
    ring
  have hconst : W x = W 0 :=
    is_const_of_deriv_eq_zero (fun y => (hderiv y).differentiableAt) (fun y => (hderiv y).deriv) x 0
  rw [show airyFun 1 0 x * deriv (airyFun 0 1) x - deriv (airyFun 1 0) x * airyFun 0 1 x = W x from rfl,
    hconst]
  show airyFun 1 0 0 * deriv (airyFun 0 1) 0 - deriv (airyFun 1 0) 0 * airyFun 0 1 0 = 1
  rw [airyFun_zero 1 0, airyFun_zero 0 1, deriv_airyFun_zero 0 1, deriv_airyFun_zero 1 0]
  norm_num

/-- Derivative form of `airyFun` linearity. -/
theorem deriv_airyFun_linear (c0 c1 x : ℝ) :
    deriv (airyFun c0 c1) x = c0 * deriv (airyFun 1 0) x + c1 * deriv (airyFun 0 1) x := by
  have hh : HasDerivAt (fun y => c0 * airyFun 1 0 y + c1 * airyFun 0 1 y)
      (c0 * deriv (airyFun 1 0) x + c1 * deriv (airyFun 0 1) x) x :=
    ((airyFun_hasDerivAt 1 0 x).const_mul c0).add ((airyFun_hasDerivAt 0 1 x).const_mul c1)
  rw [show airyFun c0 c1 = fun y => c0 * airyFun 1 0 y + c1 * airyFun 0 1 y from
    funext (airyFun_linear c0 c1)]
  exact hh.deriv

/-- **The entire recessive solution exists.** There is a non-trivial *entire* `airyFun c0 c1`
(with `c1 = −1`, `c0 = (Ai_rec(1)+g(1))/f(1)` the synthesis constant) that decays to `0` at `+∞` —
the recessive Airy solution, now an honest entire power series rather than an imported asymptotic
object. Proof: choosing `c1=−1` forces `W(f, airyFun c0 (−1)) = c1·W(f,g) = −1 = W(f, Ai_rec)`, so the
difference has Wronskian `0` with `f`; hence `(airyFun c0 (−1) − Ai_rec)/f` has derivative `0` on
`(0,∞)`, is constant, and vanishes at `1` (by the choice of `c0`). Thus `airyFun c0 (−1) = Ai_rec` on
`(0,∞)` and inherits its decay. -/
theorem exists_entire_recessive :
    ∃ c0 c1 : ℝ, (c0 ≠ 0 ∨ c1 ≠ 0) ∧ Tendsto (airyFun c0 c1) atTop (𝓝 0) := by
  have hf1 : airyFun 1 0 1 ≠ 0 := (airyFun10_pos 1 (by norm_num)).ne'
  set c0 : ℝ := (airyRec 1 + airyFun 0 1 1) / airyFun 1 0 1 with hc0
  refine ⟨c0, -1, Or.inr (by norm_num), ?_⟩
  -- u := airyFun c0 (-1) equals airyRec on (0,∞)
  have hmatch : airyFun c0 (-1) 1 = airyRec 1 := by
    rw [airyFun_linear c0 (-1) 1, hc0]; field_simp; ring
  -- φ = (u - Ai_rec)/f has derivative 0 on (0,∞)
  have hφ : ∀ y ∈ Ioi (0:ℝ),
      HasDerivAt (fun z => (airyFun c0 (-1) z - airyRec z) / airyFun 1 0 z) 0 y := by
    intro y hy
    have hyp : (0:ℝ) < y := hy
    have hfy : airyFun 1 0 y ≠ 0 := (airyFun10_pos y (mem_Ici.mpr hyp.le)).ne'
    have hd := ((airyFun_hasDerivAt c0 (-1) y).sub (airyRec_hasDerivAt hyp)).div
      (airyFun_hasDerivAt 1 0 y) hfy
    have hWu : airyFun 1 0 y * deriv (airyFun c0 (-1)) y
        - deriv (airyFun 1 0) y * airyFun c0 (-1) y = -1 := by
      rw [airyFun_linear c0 (-1) y, deriv_airyFun_linear c0 (-1) y]
      linear_combination -(wronskian_fg y)
    have hWr := airyRec_wronskian hyp
    convert hd using 1
    rw [eq_comm, div_eq_zero_iff]; left
    simp only [Pi.sub_apply]
    linear_combination hWu - hWr
  -- φ constant on (0,∞), value 0 at 1
  have hconst : (airyFun c0 (-1) 1 - airyRec 1) / airyFun 1 0 1 = 0 := by
    rw [hmatch]; simp
  have hEq : Set.EqOn (airyFun c0 (-1)) airyRec (Ioi 0) := by
    intro x hx
    have hxp : (0:ℝ) < x := hx
    have hfx : airyFun 1 0 x ≠ 0 := (airyFun10_pos x (mem_Ici.mpr hxp.le)).ne'
    have hcx : (airyFun c0 (-1) x - airyRec x) / airyFun 1 0 x
        = (airyFun c0 (-1) 1 - airyRec 1) / airyFun 1 0 1 :=
      IsOpen.is_const_of_deriv_eq_zero isOpen_Ioi isPreconnected_Ioi
        (fun z hz => (hφ z hz).differentiableAt.differentiableWithinAt)
        (fun z hz => (hφ z hz).deriv) hx (by norm_num : (1:ℝ) ∈ Ioi 0)
    rw [hconst, div_eq_zero_iff] at hcx
    rcases hcx with h | h
    · linarith [sub_eq_zero.mp h]
    · exact absurd h hfx
  -- transfer decay
  refine airyRec_tendsto_zero.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx using (hEq hx).symm

end Airy
