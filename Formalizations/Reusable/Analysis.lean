/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.Analysis.SpecialFunctions.Airy.Basic
public import Formalizations.Analysis.Polynomial.EnestromKakeya
public import Formalizations.Probability.Distributions.Superstatistics.LaplaceMixture
public import Formalizations.RepresentationTheory.SpinRhoLine
public import Formalizations.Reusable.Polynomial

/-!
# Reusable layer: analysis

Stable names for analysis results of the archive. Each theorem is proved by the archive theorem it
re-exposes (no proof is copied).

Since v0.2.0 the real-rootedness result `splits_of_alternating_sign` (and its bridge
`realRooted_iff_splits`) lives in `Formalizations.Reusable.Polynomial`, with the other results on
real roots; this module imports it, so `import Formalizations.Reusable.Analysis` still provides it
under the same name.

## Main results

* `Formalizations.Reusable.airy_eq_zeros_unbounded_below`: every solution of `y'' = x y` has zeros
  unbounded below (archive: `Airy.sturm_unbounded_zeros`).
* `Formalizations.Reusable.glasser_integral`: `∫_{v>0} v^{-1/2} e^{-a/v - b v} dv = √(π/b) e^{-2√(ab)}`
  (archive: `Superstatistics.glasser_integral`).
* `Formalizations.Reusable.prod_two_sin_mul_pi_div`: `∏_{k=1}^{n-1} 2 sin(kπ/n) = n`
  (archive: `SpinRhoLine.prod_two_sin`).
* `Formalizations.Reusable.enestrom_kakeya_ne_zero`: a polynomial with positive non-increasing
  real coefficients has no zero in the open unit disc (archive: `Dilog.enestrom_kakeya`).
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

end Formalizations.Reusable
