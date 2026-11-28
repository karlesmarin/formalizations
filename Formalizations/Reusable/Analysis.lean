/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.Physics.QuantumMechanics.SpeedLimit.MandelstamTamm
public import Formalizations.Probability.Distributions.Superstatistics.StudentMixture
public import Formalizations.Analysis.SpecialFunctions.Airy.Basic
public import Formalizations.Analysis.SpecialFunctions.Dilogarithm.ComplexBoundary
public import Formalizations.Analysis.SpecialFunctions.Dilogarithm.FiveTerm
public import Formalizations.Analysis.Polynomial.EnestromKakeya
public import Formalizations.Probability.Distributions.Superstatistics.LaplaceMixture
public import Formalizations.RepresentationTheory.SpinRhoLine
public import Formalizations.Reusable.Polynomial
public import Formalizations.Analysis.InnerProductSpace.Hlawka
public import Formalizations.Physics.QuantumMechanics.SpeedLimit.ZielinskiZych
public import Formalizations.Physics.QuantumMechanics.SpeedLimit.MargolusLevitin

/-!
# Reusable layer: analysis

Stable names for analysis results of the archive. Each theorem is proved by the archive theorem it
re-exposes (no proof is copied).

Since v0.2.0 the real-rootedness result `splits_of_alternating_sign` (and its bridge
`realRooted_iff_splits`) lives in `Formalizations.Reusable.Polynomial`, with the other results on
real roots; this module imports it, so `import Formalizations.Reusable.Analysis` still provides it
under the same name.

## Main results

* `Formalizations.Reusable.margolus_levitin`: the Margolus–Levitin quantum speed limit
  `π ≤ 2 ⟨E⟩ τ` for the orthogonalization time `τ` (archive: `QSL.margolus_levitin`).
* `Formalizations.Reusable.zielinski_zych_inequality`: `x^α − π^α/2 + (π^α/2) cos x + α π^(α−1) sin x ≥ 0` for every
  `α > 0` and `x ≥ 0` (archive: `QSL.zz_inequality_all`).
* `Formalizations.Reusable.hlawka_generalised`: the generalised Hlawka inequality for `n ≥ 3` vectors of a real
  inner product space (archive: `Hlawka.generalised`).
* `Formalizations.Reusable.airy_eq_zeros_unbounded_below`: every solution of `y'' = x y` has zeros
  unbounded below (archive: `Airy.sturm_unbounded_zeros`).
* `Formalizations.Reusable.glasser_integral`: `∫_{v>0} v^{-1/2} e^{-a/v - b v} dv = √(π/b) e^{-2√(ab)}`
  (archive: `Superstatistics.glasser_integral`).
* `Formalizations.Reusable.prod_two_sin_mul_pi_div`: `∏_{k=1}^{n-1} 2 sin(kπ/n) = n`
  (archive: `SpinRhoLine.prod_two_sin`).
* `Formalizations.Reusable.enestrom_kakeya_ne_zero`: a polynomial with positive non-increasing
  real coefficients has no zero in the open unit disc (archive: `Dilog.enestrom_kakeya`).
* `Formalizations.Reusable.Li₂_add_Li₂_one_sub`, `Formalizations.Reusable.Li₂_landen`,
  `Formalizations.Reusable.Li₂_sq`: reflection, Landen and duplication for the real dilogarithm.
* `Formalizations.Reusable.rogersL_fiveterm`: the five-term relation for the Rogers dilogarithm.
* `Formalizations.Reusable.Li₂c_I`: the complex dilogarithm at the imaginary unit.
-/

@[expose] public section

open Real Set Filter

namespace Formalizations.Reusable

/-- **Oscillation of the Airy equation.** If `f` is differentiable with derivative `f'`, and `f'`
is differentiable with derivative `x ↦ x f x` (that is, `f'' = x f` everywhere), then `f` has a
zero below every bound: for every `M` there is `x < M` with `f x = 0`. This holds for every
solution, including the zero solution; the proof is a Sturm comparison with `sin (√c (x − a))`
built from Rolle's theorem and the intermediate value theorem (Mathlib has no Sturm theory).

* Archive: `Airy.sturm_unbounded_zeros` (`Formalizations.Analysis.SpecialFunctions.Airy.Basic`).
* Paper: C. Marín, *How a Falling Particle Counts Its Floors* (2026), doi:10.5281/zenodo.20787671.
* Classical reference: DLMF §9.9 (zeros of the Airy functions); E. A. Coddington, N. Levinson,
  *Theory of Ordinary Differential Equations*, ch. 8 (Sturm comparison).
* Example: for a solution `f` with `hf, hf'`, `airy_eq_zeros_unbounded_below f f' hf hf' 0` gives a
  negative zero of `f`. -/
theorem airy_eq_zeros_unbounded_below (f f' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (x * f x) x) (M : ℝ) :
    ∃ x, x < M ∧ f x = 0 :=
  Airy.sturm_unbounded_zeros f f' hf hf' M

/-- **Glasser's integral** (the modified Bessel `K_{1/2}` integral). For `a ≥ 0` and `b > 0`,
`∫_{v > 0} v^{-1/2} exp(−a/v − b v) dv = √(π/b) · exp(−2 √(a b))`. The case `a = 0` is the Gamma
integral; for `a > 0` the proof substitutes `v = √(a/b) s²` and uses Schlömilch's change of
variables `u = s − 1/s`.

* Archive: `Superstatistics.glasser_integral`
  (`Formalizations.Probability.Distributions.Superstatistics.LaplaceMixture`, where it gives the
  Laplace law as a Gaussian scale mixture); the module cites no paper DOI of ours.
* Classical reference: M. L. Glasser, *A remarkable property of definite integrals*, Math. Comp. 40
  (1983) 561; D. F. Andrews, C. L. Mallows, J. Roy. Statist. Soc. Ser. B 36 (1974) 99–102.
* Example: `glasser_integral le_rfl one_pos` is `∫ v^{-1/2} e^{-v} = √π` (the Gamma value
  `Γ(1/2)`), after simplification. -/
theorem glasser_integral {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    ∫ v in Ioi (0 : ℝ), v ^ (-(1 : ℝ) / 2) * Real.exp (-a / v - b * v)
      = Real.sqrt (π / b) * Real.exp (-(2 * Real.sqrt (a * b))) :=
  Superstatistics.glasser_integral ha hb

/-- **Product of sines.** For every `n ≥ 1`, `∏_{k=1}^{n-1} 2 sin(kπ/n) = n`. The proof goes through
`IsPrimitiveRoot.prod_pow_sub_one_eq_order` and `|e^{2πik/n} − 1| = 2 sin(πk/n)`.

* Archive: `SpinRhoLine.prod_two_sin` (`Formalizations.RepresentationTheory.SpinRhoLine`, used for
  the spin values on the ρ-line); the module cites no paper DOI of ours.
* Classical reference: the identity `∏_{k=1}^{n-1} sin(kπ/n) = n / 2^{n-1}` (folklore; it is the
  value at `1` of `(Xⁿ − 1)/(X − 1) = ∏ (X − ζᵏ)`).
* Example: `prod_two_sin_mul_pi_div 4 (by norm_num)` gives
  `(2 sin(π/4)) (2 sin(2π/4)) (2 sin(3π/4)) = 4`. -/
theorem prod_two_sin_mul_pi_div (n : ℕ) (hn : 1 ≤ n) :
    ∏ k ∈ Finset.Ico 1 n, 2 * Real.sin (k * π / n) = n :=
  SpinRhoLine.prod_two_sin n hn

/-- **The Eneström–Kakeya theorem.** A polynomial `∑_{k=0}^n a_k z^k` with real coefficients
`a_0 ≥ a_1 ≥ ⋯ ≥ a_n > 0` has no zero in the open unit disc `‖z‖ < 1`. The proof multiplies by
`1 − z`, telescopes and applies the triangle inequality. (In the other common form, increasing
positive coefficients give no zero outside the closed unit disc; it follows by reversing the
polynomial.)

* Archive: `Dilog.enestrom_kakeya` (`Formalizations.Analysis.Polynomial.EnestromKakeya`, in the
  namespace of the dilogarithm notes of the same archive; the module also has the boundary case,
  `Dilog.enestrom_kakeya_boundary`).
* Classical reference: G. Eneström (1893), S. Kakeya, Tôhoku Math. J. 2 (1912);
  Q. I. Rahman, G. Schmeisser, *Analytic Theory of Polynomials* (2002).
* Example: `1 + z/2 + z²/3` (coefficients `1 ≥ 1/2 ≥ 1/3 > 0`) has no zero with `‖z‖ < 1`. -/
theorem enestrom_kakeya_ne_zero {n : ℕ} (a : ℕ → ℝ) (hpos : ∀ k ≤ n, 0 < a k)
    (hmono : ∀ k, k < n → a (k + 1) ≤ a k) {z : ℂ} (hz : ‖z‖ < 1) :
    ∑ k ∈ Finset.range (n + 1), (a k : ℂ) * z ^ k ≠ 0 :=
  Dilog.enestrom_kakeya a hpos hmono hz


/-- **Generalised Hlawka inequality (Djoković 1963; Smiley–Smiley 1964).** For `n ≥ 3` vectors of a real
inner product space, write `d_k` for the sum of the norms of all `k`-element subsums. Then
`d_2 + ⋯ + d_{n-1} ≤ (2^(n-2) - 1) (d_1 + d_n)`. For `n = 3` this is Hlawka's inequality
`‖x+y‖ + ‖y+z‖ + ‖z+x‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ + ‖x+y+z‖`.

* Archive: `Hlawka.generalised` (`Formalizations.Analysis.InnerProductSpace.Hlawka`; the case `n = 3` is
  `Hlawka.norm_add_add_le`); the module cites no paper DOI of ours.
* Classical reference: D. Ž. Djoković, *Generalizations of Hlawka's inequality*, Glasnik Mat.-Fiz. Astronom.
  18 (1963) 169–175; D. M. Smiley, M. F. Smiley, *The polygonal inequalities*, Amer. Math. Monthly 71 (1964)
  755–760.
* Example: four vectors of `ℝ`, `n = 4`: `d_2 + d_3 ≤ 3 (d_1 + d_4)`. -/
theorem hlawka_generalised {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    (hn : 3 ≤ n) (x : Fin n → E) :
    ∑ k ∈ Finset.Icc 2 (n - 1), ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ‖∑ i ∈ S, x i‖
      ≤ (2 ^ (n - 2) - 1 : ℝ) * (∑ i, ‖x i‖ + ‖∑ i, x i‖) :=
  Hlawka.generalised hn x


/-- **The Zieliński–Zych inequality.** For every `α > 0` and `x ≥ 0`,
`0 ≤ x^α − π^α/2 + (π^α/2) cos x + α π^(α−1) sin x`. It is the analytic core of the fractional-moment
quantum speed limit `π^α ≤ 2 M_α τ^α`; `α = 1` is the Margolus–Levitin case.

* Archive: `QSL.zz_inequality_all` (`Formalizations.Physics.QuantumMechanics.SpeedLimit.ZielinskiZych`; the
  archive proves it for `0 < α ≤ 1` by a harmonic-mean bound and for `α ≥ 1` by Bernoulli plus a split of
  `tan`); the module cites no paper DOI of ours.
* Classical reference: the inequality is stated (without proof) in M. Zieliński, M. Zych, Phys. Rev. A 74,
  034301 (2006), as cited in the archive module.
* Example: `α = 1`, the inequality `0 ≤ x − π/2 + (π/2) cos x + sin x` behind the Margolus–Levitin bound. -/
theorem zielinski_zych_inequality {α x : ℝ} (hα : 0 < α) (hx : 0 ≤ x) :
    0 ≤ x ^ α - Real.pi ^ α / 2 + Real.pi ^ α / 2 * Real.cos x +
      α * Real.pi ^ (α - 1) * Real.sin x :=
  QSL.zz_inequality_all hα hx

/-- **The Margolus–Levitin theorem** (`ℏ = 1`). If a normalized population distribution `p` over
nonnegative energies `E` has mean energy `Ebar` and its autocorrelation `S(τ) = ∑ₙ pₙ e^(−i Eₙ τ)`
vanishes at a time `τ ≥ 0` (real and imaginary parts given separately), then `π ≤ 2 · Ebar · τ`:
a state needs at least `π / (2 ⟨E⟩)` to evolve into an orthogonal one.

* Archive: `QSL.margolus_levitin` (`Formalizations.Physics.QuantumMechanics.SpeedLimit.MargolusLevitin`,
  through the cosine inequality `1 − (2/π)(x + sin x) ≤ cos x` for `x ≥ 0`); the module cites no paper DOI
  of ours.
* Classical reference: N. Margolus, L. B. Levitin, *The maximum speed of dynamical evolution*, Physica D
  120 (1998) 188–195.
* Example: the orthogonalization time is at least `π / (2 Ebar)` when `Ebar > 0`. -/
theorem margolus_levitin {p E : ℕ → ℝ} {Ebar τ : ℝ} (hp : ∀ n, 0 ≤ p n) (hE : ∀ n, 0 ≤ E n)
    (hτ : 0 ≤ τ) (hsum : HasSum p 1) (hmean : HasSum (fun n => p n * E n) Ebar)
    (hRe : HasSum (fun n => p n * Real.cos (E n * τ)) 0)
    (hIm : HasSum (fun n => p n * Real.sin (E n * τ)) 0) :
    Real.pi ≤ 2 * Ebar * τ :=
  QSL.margolus_levitin hp hE hτ hsum hmean hRe hIm

/-- The Mandelstam–Tamm-type speed limit in L¹ form (ℏ = 1). If the autocorrelation vanishes at
a nonnegative time `τ`, then `1 ≤ D1 * τ`, where `D1` is the mean absolute energy deviation from
the reference energy `Ebar`. Archive: `QSL.mandelstam_tamm_L1`. -/
theorem mandelstam_tamm_L1 {p E : ℕ → ℝ} {Ebar D1 τ : ℝ}
    (hp : ∀ n, 0 ≤ p n) (hτ : 0 ≤ τ) (hsum : HasSum p 1)
    (hdev : HasSum (fun n => p n * |E n - Ebar|) D1)
    (horth : HasSum
      (fun n => (p n : ℂ) * Complex.exp ((-(E n * τ) : ℝ) * Complex.I)) 0) :
    1 ≤ D1 * τ :=
  QSL.mandelstam_tamm_L1 hp hτ hsum hdev horth

open MeasureTheory ProbabilityTheory in
/-- The kurtosis of `√V * Z`, for independent nonnegative `V` and standard normal `Z`, is
`3 E[V²] / E[V]²`. Its excess kurtosis is `3 Var(V) / E[V]²` and is nonnegative.
Archive: `Superstatistics.variance_mixture_kurtosis_identity'`. -/
theorem variance_mixture_kurtosis_identity
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
          / (∫ ω, (Real.sqrt ω.1 * ω.2) ^ 2 ∂(μV.prod (gaussianReal 0 1))) ^ 2 :=
  Superstatistics.variance_mixture_kurtosis_identity' μV hV2 hVnn heV

/-- **Euler's reflection formula** for the real dilogarithm on `(0, 1)`:
`Li₂(x) + Li₂(1 − x) = π²/6 − log(x) log(1 − x)`.
Archive: `Dilog.Li₂_add_Li₂_one_sub`. -/
theorem Li₂_add_Li₂_one_sub {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Dilog.Li₂ x + Dilog.Li₂ (1 - x) = π ^ 2 / 6 - Real.log x * Real.log (1 - x) :=
  Dilog.Li₂_add_Li₂_one_sub hx

/-- **Landen's identity** for the real dilogarithm on `(0, 1/2)`:
`Li₂(x) + Li₂(x / (x − 1)) = −log²(1 − x)/2`.
Archive: `Dilog.Li₂_landen`. -/
theorem Li₂_landen {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) :
    Dilog.Li₂ x + Dilog.Li₂ (x / (x - 1)) = -Real.log (1 - x) ^ 2 / 2 :=
  Dilog.Li₂_landen hx

/-- **Duplication** for the real dilogarithm on `[-1, 1]`:
`Li₂(x²) = 2 (Li₂(x) + Li₂(−x))`. Archive: `Dilog.Li₂_sq`. -/
theorem Li₂_sq {x : ℝ} (hx : |x| ≤ 1) :
    Dilog.Li₂ (x ^ 2) = 2 * (Dilog.Li₂ x + Dilog.Li₂ (-x)) :=
  Dilog.Li₂_sq hx

/-- **Abel's five-term relation** for the Rogers dilogarithm. For `x, y ∈ (0, 1)`,
`L(x) + L(y) = L(xy) + L(x(1 − y)/(1 − xy)) + L(y(1 − x)/(1 − xy))`.
Archive: `Dilog.rogersL_fiveterm`. -/
theorem rogersL_fiveterm {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    Dilog.rogersL x + Dilog.rogersL y =
      Dilog.rogersL (x * y) + Dilog.rogersL (x * (1 - y) / (1 - x * y))
        + Dilog.rogersL (y * (1 - x) / (1 - x * y)) :=
  Dilog.rogersL_fiveterm hx hy

/-- **The dilogarithm at the imaginary unit** is `Li₂(i) = −π²/48 + i G`, where `G`
is Catalan's constant. Archive: `Dilog.Li₂c_I`. -/
theorem Li₂c_I :
    Dilog.Li₂c Complex.I = ((-(π ^ 2) / 48 : ℝ) : ℂ) + (Dilog.catalanConst : ℂ) * Complex.I :=
  Dilog.Li₂c_I

end Formalizations.Reusable
