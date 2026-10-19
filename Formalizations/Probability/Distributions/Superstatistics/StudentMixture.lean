/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian variance mixtures: Student-t marginals and excess kurtosis

Marginalizing a centered Gaussian of precision `β` against a `Gamma(a, b)` law on `β` gives the
Student-t density, normalized by `b^a`. For any variance mixture `X = √V · Z` with `Z` standard
normal and independent of `V ≥ 0`, the kurtosis is `3 E[V²] / E[V]²`, so the excess kurtosis
`3 Var(V) / E[V]²` is nonnegative.

## Main results

* `Superstatistics.gaussian_gamma_mixture_studentt`: the Gaussian–Gamma mixture integral.
* `Superstatistics.std_normal_second_moment`, `Superstatistics.std_normal_fourth_moment`:
  `E[Z²] = 1` and `E[Z⁴] = 3`, from the moment generating function.
* `Superstatistics.sq_expectation_le_expectation_sq`: `E[V]² ≤ E[V²]`.
* `Superstatistics.variance_mixture_kurtosis_identity`: the kurtosis identity, given the moment
  factorization.
* `Superstatistics.variance_mixture_kurtosis_identity'`: the same on the product space
  `μV.prod (gaussianReal 0 1)`, with the factorization derived from `integral_prod_mul`.

## References

* C. Beck, E. G. D. Cohen, *Superstatistics*, Physica A 322 (2003) 267–275.
* D. F. Andrews, C. L. Mallows, *Scale mixtures of normal distributions*, J. Roy. Statist. Soc.
  Ser. B 36 (1974) 99–102.
-/

@[expose] public section

open MeasureTheory Real Set
open scoped ENNReal

namespace Superstatistics

open ProbabilityTheory

/-! ## T1 — Gaussian/Gamma scale-mixture = Student-t (pure analytic / integral form)

Marginalising a zero-mean Gaussian of precision `β` against a `Gamma(a,b)` prior on `β`
yields the (unnormalised) Student-t density.  In Mathlib pieces:
  `Real.Gamma`, `ProbabilityTheory.gaussianPDFReal`, `ProbabilityTheory.gammaPDFReal`
exist, but no MIXTURE / compound / subordination identity does.
Setting `a = ν/2`, `b = ν σ²/2` recovers `Student-t_ν(scale σ)` ∝ (1 + x²/(νσ²))^(−(ν+1)/2).
Proof: substitute `u = β (b + x²/2)`, pull constants, recognise `Real.Gamma (a+1/2)`
via `Real.Gamma_eq_integral` / `integral_rpow_mul_exp_neg_mul_Ioi`-style Gamma integrals.

The right-hand side carries the Gamma normalization `b^a`; with `a=ν/2, b=νσ²/2` this is the properly normalised Student-t_ν
density (`b^a·(b+x²/2)^(-(a+1/2))` collapses to the standard `(1+x²/(νσ²))^(-(ν+1)/2)`
shape times the `σ`/normalisation constants). -/
theorem gaussian_gamma_mixture_studentt (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ β in Ioi (0 : ℝ),
        Real.sqrt (β / (2 * π)) * Real.exp (-(β * x ^ 2) / 2)
          * (b ^ a / Real.Gamma a) * β ^ (a - 1) * Real.exp (-(b * β))
      = b ^ a * Real.Gamma (a + 1 / 2) / (Real.Gamma a * Real.sqrt (2 * π))
          * (b + x ^ 2 / 2) ^ (-(a + 1 / 2)) := by
  have hc : (0 : ℝ) < b + x ^ 2 / 2 := by positivity
  set C : ℝ := b ^ a / Real.Gamma a * (Real.sqrt (2 * π))⁻¹ with hC
  -- Collapse the integrand to `C · (β^((a+1/2)-1) · exp(−(b+x²/2)·β))`.
  have hpt : Set.EqOn
      (fun β : ℝ => Real.sqrt (β / (2 * π)) * Real.exp (-(β * x ^ 2) / 2)
          * (b ^ a / Real.Gamma a) * β ^ (a - 1) * Real.exp (-(b * β)))
      (fun β : ℝ => C * (β ^ ((a + 1 / 2) - 1) * Real.exp (-((b + x ^ 2 / 2) * β))))
      (Ioi (0 : ℝ)) := by
    intro β hβ
    have hβ0 : (0 : ℝ) < β := hβ
    have hsqrt : Real.sqrt (β / (2 * π)) = (Real.sqrt (2 * π))⁻¹ * β ^ ((1 : ℝ) / 2) := by
      rw [Real.sqrt_div hβ0.le, Real.sqrt_eq_rpow]; ring
    have hrpow : β ^ ((1 : ℝ) / 2) * β ^ (a - 1) = β ^ ((a + 1 / 2) - 1) := by
      rw [← Real.rpow_add hβ0]; congr 1; ring
    have hexp : Real.exp (-(β * x ^ 2) / 2) * Real.exp (-(b * β))
        = Real.exp (-((b + x ^ 2 / 2) * β)) := by
      rw [← Real.exp_add]; congr 1; ring
    simp only
    rw [hsqrt,
        show (Real.sqrt (2 * π))⁻¹ * β ^ ((1 : ℝ) / 2) * Real.exp (-(β * x ^ 2) / 2)
              * (b ^ a / Real.Gamma a) * β ^ (a - 1) * Real.exp (-(b * β))
            = C * (β ^ ((1 : ℝ) / 2) * β ^ (a - 1)
                * (Real.exp (-(β * x ^ 2) / 2) * Real.exp (-(b * β)))) from by rw [hC]; ring,
        hrpow, hexp]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
      integral_rpow_mul_exp_neg_mul_Ioi (by positivity : (0 : ℝ) < a + 1 / 2) hc]
  -- `(1/c)^(a+1/2) = c^(-(a+1/2))`, then reassemble constants.
  rw [one_div, Real.inv_rpow hc.le, ← Real.rpow_neg hc.le, hC]
  ring

/-! ## T2 — Gaussian variance-mixture is leptokurtic (excess kurtosis ≥ 0)

If `X = √V · Z` with `Z ~ N(0,1) ⟂ V ≥ 0`, then `kurtosis(X) = 3 · E[V²]/E[V]² ≥ 3`,
equality iff `V` a.s. constant; excess kurtosis `= 3 · Var(V)/E[V]²`.
Mathlib DEFINES no `kurtosis`, so the whole claim reduces to the Jensen core
`E[V]² ≤ E[V²]`, which is exactly `variance_nonneg` unfolded via `variance_eq_sub`
(`Var V = E[V²] − E[V]²`).  This lemma IS the leptokurtic engine. -/
theorem sq_expectation_le_expectation_sq
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (V : Ω → ℝ) (hV : MemLp V 2 μ) :
    (∫ ω, V ω ∂μ) ^ 2 ≤ ∫ ω, (V ^ 2) ω ∂μ := by
  have h := ProbabilityTheory.variance_nonneg V μ
  rw [ProbabilityTheory.variance_eq_sub hV] at h
  linarith

/-- Explicit leptokurtic form: excess kurtosis `= 3·Var(V)/E[V]² ≥ 0`.
    Stated as the nonnegativity of `Var(V)/E[V]²` (the `3·` and the `√V·Z`
    kurtosis identity are downstream).  Leans on `variance_nonneg`. -/
theorem variance_mixture_excess_kurtosis_nonneg
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (V : Ω → ℝ) :
    0 ≤ ProbabilityTheory.variance V μ := ProbabilityTheory.variance_nonneg V μ

/-! ### Standard-normal moments `E[Z²]=1`, `E[Z⁴]=3` (the leptokurtic inputs)

Computed via the moment-generating function: with `Z ~ N(0,1)` the mgf is
`t ↦ exp(t²/2)`, and `E[Z^n] = (d/dt)^n mgf |₀` (`iteratedDeriv_mgf_zero`).
Differentiating `exp(t²/2)` four times gives the polynomial-times-Gaussian tower
`t·e`, `(1+t²)·e`, `(3t+t³)·e`, `(3+6t²+t⁴)·e`; evaluating at `0` yields `1` and `3`. -/

/-- `HasDerivAt` for `t ↦ exp(t²/2)`, derivative `t·exp(t²/2)`. -/
private theorem hasDerivAt_gaussKernel (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (s ^ 2 / 2)) (t * Real.exp (t ^ 2 / 2)) t := by
  have h1 : HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t := by
    have := (hasDerivAt_pow 2 t).div_const 2
    convert this using 1; ring
  have := h1.exp
  convert this using 1; ring

/-- Standard-normal second moment: `E[Z²] = 1`. -/
theorem std_normal_second_moment :
    ∫ z, z ^ 2 ∂(gaussianReal (0 : ℝ) 1) = 1 := by
  have hmgf : mgf id (gaussianReal (0 : ℝ) 1) = fun t => Real.exp (t ^ 2 / 2) := by
    rw [mgf_id_gaussianReal]; funext t; congr 1; push_cast; ring
  have hset : (0 : ℝ) ∈ interior (integrableExpSet id (gaussianReal (0 : ℝ) 1)) := by
    rw [integrableExpSet_id_gaussianReal, interior_univ]; exact mem_univ _
  have d1 : deriv (fun s : ℝ => Real.exp (s ^ 2 / 2)) = fun t => t * Real.exp (t ^ 2 / 2) := by
    funext t; exact (hasDerivAt_gaussKernel t).deriv
  have hP2 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s * Real.exp (s ^ 2 / 2))
      ((1 + t ^ 2) * Real.exp (t ^ 2 / 2)) t := by
    intro t
    have := (hasDerivAt_id' t).fun_mul (hasDerivAt_gaussKernel t)
    convert this using 1; ring
  have key : iteratedDeriv 2 (fun s : ℝ => Real.exp (s ^ 2 / 2)) 0 = 1 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, d1, (hP2 0).deriv]; norm_num
  have h := iteratedDeriv_mgf_zero hset 2
  rw [hmgf, key] at h
  have hint : ∫ z, z ^ 2 ∂(gaussianReal (0 : ℝ) 1) = (gaussianReal (0 : ℝ) 1)[id ^ 2] := by
    simp [Pi.pow_apply]
  rw [hint]; exact h.symm

/-- Standard-normal fourth moment: `E[Z⁴] = 3`. -/
theorem std_normal_fourth_moment :
    ∫ z, z ^ 4 ∂(gaussianReal (0 : ℝ) 1) = 3 := by
  have hmgf : mgf id (gaussianReal (0 : ℝ) 1) = fun t => Real.exp (t ^ 2 / 2) := by
    rw [mgf_id_gaussianReal]; funext t; congr 1; push_cast; ring
  have hset : (0 : ℝ) ∈ interior (integrableExpSet id (gaussianReal (0 : ℝ) 1)) := by
    rw [integrableExpSet_id_gaussianReal, interior_univ]; exact mem_univ _
  have d1 : deriv (fun s : ℝ => Real.exp (s ^ 2 / 2)) = fun t => t * Real.exp (t ^ 2 / 2) := by
    funext t; exact (hasDerivAt_gaussKernel t).deriv
  have hP2 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s * Real.exp (s ^ 2 / 2))
      ((1 + t ^ 2) * Real.exp (t ^ 2 / 2)) t := by
    intro t
    have := (hasDerivAt_id' t).fun_mul (hasDerivAt_gaussKernel t)
    convert this using 1; ring
  have d2 : deriv (fun s : ℝ => s * Real.exp (s ^ 2 / 2))
      = fun t => (1 + t ^ 2) * Real.exp (t ^ 2 / 2) := by
    funext t; exact (hP2 t).deriv
  have hP3 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (1 + s ^ 2) * Real.exp (s ^ 2 / 2))
      ((3 * t + t ^ 3) * Real.exp (t ^ 2 / 2)) t := by
    intro t
    have hpoly : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * t) t := by
      have := (hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_pow 2 t)
      convert this using 1; ring
    have := hpoly.mul (hasDerivAt_gaussKernel t)
    convert this using 1; ring
  have d3 : deriv (fun s : ℝ => (1 + s ^ 2) * Real.exp (s ^ 2 / 2))
      = fun t => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2) := by
    funext t; exact (hP3 t).deriv
  have hP4 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (3 * s + s ^ 3) * Real.exp (s ^ 2 / 2))
      ((3 + 6 * t ^ 2 + t ^ 4) * Real.exp (t ^ 2 / 2)) t := by
    intro t
    have hpoly : HasDerivAt (fun s : ℝ => 3 * s + s ^ 3) (3 + 3 * t ^ 2) t := by
      have := ((hasDerivAt_id' t).const_mul (3 : ℝ)).fun_add (hasDerivAt_pow 3 t)
      convert this using 1; ring
    have := hpoly.fun_mul (hasDerivAt_gaussKernel t)
    convert this using 1; ring
  have key : iteratedDeriv 4 (fun s : ℝ => Real.exp (s ^ 2 / 2)) 0 = 3 := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one,
        d1, d2, d3, (hP4 0).deriv]
    norm_num
  have h := iteratedDeriv_mgf_zero hset 4
  rw [hmgf, key] at h
  have hint : ∫ z, z ^ 4 ∂(gaussianReal (0 : ℝ) 1) = (gaussianReal (0 : ℝ) 1)[id ^ 4] := by
    simp [Pi.pow_apply]
  rw [hint]; exact h.symm

/-- **Leptokurtic identity for a variance-mixture Gaussian.** Writing `X = √V·Z`
    with `Z ~ N(0,1) ⟂ V ≥ 0`, the independence factorisation gives
    `E[X²] = E[V]·E[Z²] = E[V]` and `E[X⁴] = E[V²]·E[Z⁴] = 3·E[V²]`, the
    standard-normal moments `E[Z²]=1`, `E[Z⁴]=3` being `std_normal_second_moment`
    and `std_normal_fourth_moment`.  Given those two moment facts (as `hX2`, `hX4`)
    and `E[V] > 0`, the kurtosis is `E[X⁴]/E[X²]² = 3·E[V²]/E[V]²`, the EXCESS
    kurtosis equals `3·Var(V)/E[V]²`, and (since `Var(V) ≥ 0`) the kurtosis is `≥ 3`:
    the mixture is leptokurtic.

    The independence-factorisation step `E[V·Z²] = E[V]·E[Z²]`,
    `E[V²·Z⁴] = E[V²]·E[Z⁴]` (which produces `hX2`, `hX4` from `X = √V·Z`) is taken
    as a hypothesis here; `variance_mixture_kurtosis_identity'` derives it on a concrete
    product space. -/
theorem variance_mixture_kurtosis_identity
    (eX2 eX4 eV eV2 varV : ℝ)
    (hX2 : eX2 = eV) (hX4 : eX4 = 3 * eV2)
    (hvar : varV = eV2 - eV ^ 2) (heV : 0 < eV) (hJ : eV ^ 2 ≤ eV2) :
    eX4 / eX2 ^ 2 = 3 * eV2 / eV ^ 2
      ∧ eX4 / eX2 ^ 2 - 3 = 3 * varV / eV ^ 2
      ∧ 3 ≤ eX4 / eX2 ^ 2 := by
  have heVne : eV ≠ 0 := heV.ne'
  have heV2 : eV ^ 2 ≠ 0 := pow_ne_zero 2 heVne
  rw [hX2, hX4, hvar]
  refine ⟨by ring, by field_simp, ?_⟩
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < eV ^ 2)]
  nlinarith [hJ]

/-! ### Self-contained version: the factorisation DERIVED from a product space

`variance_mixture_kurtosis_identity` above took the independence factorisation
`E[X²]=E[V]`, `E[X⁴]=3·E[V²]` as hypotheses (`hX2`, `hX4`).  Here we DISCHARGE them:
we build the concrete independent product space `μ := μV.prod (gaussianReal 0 1)` on
`ℝ × ℝ`, set `V ω = ω.1`, `Z ω = ω.2`, `X ω = √(ω.1)·ω.2`, and derive both moment
identities from Mathlib's Fubini factorisation `integral_prod_mul`
(`∫ f(z.1)·g(z.2) ∂(μ.prod ν) = (∫f ∂μ)·(∫g ∂ν)`, unconditional) together with the
standard-normal moments `std_normal_second_moment`/`std_normal_fourth_moment`.

The ONLY remaining hypotheses are legitimate ones on the mixing law `μV`:
its second `L²`-integrability (`MemLp (·) 2 μV`, needed for the Jensen step `E[V]²≤E[V²]`),
`V ≥ 0` a.e. (`hVnn`, so `(√V)²=V`), and `E[V] > 0` (`heV`).  No factorisation
hypothesis remains — it is now a THEOREM (via `integral_prod_mul`). -/
theorem variance_mixture_kurtosis_identity'
    (μV : Measure ℝ) [IsProbabilityMeasure μV]
    (hV2 : MemLp (fun v : ℝ => v) 2 μV)
    (hVnn : ∀ᵐ v ∂μV, 0 ≤ v)
    (heV : 0 < ∫ v, v ∂μV) :
    (∫ ω, (Real.sqrt ω.1 * ω.2) ^ 4 ∂(μV.prod (gaussianReal 0 1)))
        / (∫ ω, (Real.sqrt ω.1 * ω.2) ^ 2 ∂(μV.prod (gaussianReal 0 1))) ^ 2
      = 3 * (∫ v, v ^ 2 ∂μV) / (∫ v, v ∂μV) ^ 2
    ∧ (∫ ω, (Real.sqrt ω.1 * ω.2) ^ 4 ∂(μV.prod (gaussianReal 0 1)))
          / (∫ ω, (Real.sqrt ω.1 * ω.2) ^ 2 ∂(μV.prod (gaussianReal 0 1))) ^ 2 - 3
      = 3 * ((∫ v, v ^ 2 ∂μV) - (∫ v, v ∂μV) ^ 2) / (∫ v, v ∂μV) ^ 2
    ∧ 3 ≤ (∫ ω, (Real.sqrt ω.1 * ω.2) ^ 4 ∂(μV.prod (gaussianReal 0 1)))
          / (∫ ω, (Real.sqrt ω.1 * ω.2) ^ 2 ∂(μV.prod (gaussianReal 0 1))) ^ 2 := by
  -- lift `V ≥ 0` a.e. from `μV` to the product measure along the (measure-preserving) `fst`
  have hae : ∀ᵐ ω ∂(μV.prod (gaussianReal 0 1)), 0 ≤ ω.1 :=
    (measurePreserving_fst (μ := μV)
      (ν := gaussianReal 0 1)).quasiMeasurePreserving.tendsto_ae.eventually hVnn
  -- `E[X²] = E[V·Z²] = E[V]·E[Z²] = E[V]·1 = E[V]`
  have hX2 : ∫ ω, (Real.sqrt ω.1 * ω.2) ^ 2 ∂(μV.prod (gaussianReal 0 1)) = ∫ v, v ∂μV := by
    have e1 : (fun ω : ℝ × ℝ => (Real.sqrt ω.1 * ω.2) ^ 2)
        =ᵐ[μV.prod (gaussianReal 0 1)] (fun ω => ω.1 * ω.2 ^ 2) := by
      filter_upwards [hae] with ω hω
      have hs : Real.sqrt ω.1 ^ 2 = ω.1 := Real.sq_sqrt hω
      have h2 : (Real.sqrt ω.1 * ω.2) ^ 2 = Real.sqrt ω.1 ^ 2 * ω.2 ^ 2 := by ring
      rw [h2, hs]
    calc ∫ ω, (Real.sqrt ω.1 * ω.2) ^ 2 ∂(μV.prod (gaussianReal 0 1))
        = ∫ ω, ω.1 * ω.2 ^ 2 ∂(μV.prod (gaussianReal 0 1)) := integral_congr_ae e1
      _ = (∫ x, x ∂μV) * ∫ y, y ^ 2 ∂(gaussianReal 0 1) :=
            integral_prod_mul (fun x => x) (fun z => z ^ 2)
      _ = ∫ v, v ∂μV := by rw [std_normal_second_moment, mul_one]
  -- `E[X⁴] = E[V²·Z⁴] = E[V²]·E[Z⁴] = E[V²]·3 = 3·E[V²]`
  have hX4 : ∫ ω, (Real.sqrt ω.1 * ω.2) ^ 4 ∂(μV.prod (gaussianReal 0 1)) = 3 * ∫ v, v ^ 2 ∂μV := by
    have e2 : (fun ω : ℝ × ℝ => (Real.sqrt ω.1 * ω.2) ^ 4)
        =ᵐ[μV.prod (gaussianReal 0 1)] (fun ω => ω.1 ^ 2 * ω.2 ^ 4) := by
      filter_upwards [hae] with ω hω
      have hs : Real.sqrt ω.1 ^ 2 = ω.1 := Real.sq_sqrt hω
      have h4 : (Real.sqrt ω.1 * ω.2) ^ 4 = (Real.sqrt ω.1 ^ 2) ^ 2 * ω.2 ^ 4 := by ring
      rw [h4, hs]
    calc ∫ ω, (Real.sqrt ω.1 * ω.2) ^ 4 ∂(μV.prod (gaussianReal 0 1))
        = ∫ ω, ω.1 ^ 2 * ω.2 ^ 4 ∂(μV.prod (gaussianReal 0 1)) := integral_congr_ae e2
      _ = (∫ x, x ^ 2 ∂μV) * ∫ y, y ^ 4 ∂(gaussianReal 0 1) :=
            integral_prod_mul (fun x => x ^ 2) (fun z => z ^ 4)
      _ = 3 * ∫ v, v ^ 2 ∂μV := by rw [std_normal_fourth_moment]; ring
  -- Jensen: `E[V]² ≤ E[V²]` from `variance_nonneg`
  have hJ : (∫ v, v ∂μV) ^ 2 ≤ ∫ v, v ^ 2 ∂μV := by
    have h := sq_expectation_le_expectation_sq (μ := μV) (fun v : ℝ => v) hV2
    simpa [Pi.pow_apply] using h
  -- feed the derived moments into the kurtosis algebra
  exact variance_mixture_kurtosis_identity
    (∫ ω, (Real.sqrt ω.1 * ω.2) ^ 2 ∂(μV.prod (gaussianReal 0 1)))
    (∫ ω, (Real.sqrt ω.1 * ω.2) ^ 4 ∂(μV.prod (gaussianReal 0 1)))
    (∫ v, v ∂μV) (∫ v, v ^ 2 ∂μV)
    ((∫ v, v ^ 2 ∂μV) - (∫ v, v ∂μV) ^ 2)
    hX2 hX4 rfl heV hJ

end Superstatistics
