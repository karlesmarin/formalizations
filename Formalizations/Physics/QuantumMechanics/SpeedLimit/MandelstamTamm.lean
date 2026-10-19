/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Formalizations.Physics.QuantumMechanics.SpeedLimit.MargolusLevitin

/-!
# A Mandelstam–Tamm speed limit in `L¹` form

With the notation of `MargolusLevitin`, if the autocorrelation vanishes at `τ ≥ 0` then
`1 ≤ D₁ τ`, where `D₁ = ∑ pₙ |Eₙ - ⟨E⟩|` is the mean absolute deviation of the energy (`ℏ = 1`).

The centered autocorrelation `g(t) = e^{i⟨E⟩t} S(t)` goes from `g(0) = 1` to `g(τ) = 0` with speed
`‖g′‖ ≤ D₁`. Since `D₁ ≤ ΔE` by the Cauchy–Schwarz inequality, this implies the weak form
`τ ≥ 1/ΔE` of the Mandelstam–Tamm bound `τ ≥ π/(2ΔE)`, which is not proved here.

## Main results

* `QSL.mandelstam_tamm_L1`: `1 ≤ D₁ τ`.

## References

* L. Mandelstam, I. Tamm, *The uncertainty relation between energy and time in non-relativistic
  quantum mechanics*, J. Phys. USSR 9 (1945) 249–254.
-/

@[expose] public section

noncomputable section
open scoped Real
open Set

namespace QSL

/-- **Mandelstam–Tamm-type speed limit, L¹ form** (`ℏ = 1`): if a normalized population
distribution `p` over energies `E` has mean absolute energy deviation
`D₁ = ∑ pₙ·|Eₙ − Ebar|` around any reference energy `Ebar`, and the autocorrelation
`S(τ) = ∑ pₙ·e^{−i·Eₙ·τ}` vanishes at some `τ ≥ 0`, then `1 ≤ D₁·τ`, i.e.
`τ ≥ 1/D₁`. With `Ebar = ⟨E⟩` and Cauchy–Schwarz this implies the textbook weak
Mandelstam–Tamm bound `τ ≥ 1/ΔE`. -/
theorem mandelstam_tamm_L1 {p E : ℕ → ℝ} {Ebar D1 τ : ℝ}
    (hp : ∀ n, 0 ≤ p n) (hτ : 0 ≤ τ)
    (hsum : HasSum p 1)
    (hdev : HasSum (fun n => p n * |E n - Ebar|) D1)
    (horth : HasSum
      (fun n => (p n : ℂ) * Complex.exp ((-(E n * τ) : ℝ) * Complex.I)) 0) :
    1 ≤ D1 * τ := by
  set d : ℕ → ℂ := fun n => -((E n - Ebar : ℝ) : ℂ) * Complex.I with hd
  set f : ℕ → ℝ → ℂ := fun n t => (p n : ℂ) * Complex.exp (d n * (t : ℂ)) with hf
  set f' : ℕ → ℝ → ℂ := fun n t => (p n : ℂ) * (Complex.exp (d n * (t : ℂ)) * d n) with hf'
  set u : ℕ → ℝ := fun n => p n * |E n - Ebar| with hu_def
  -- termwise derivative
  have hderiv : ∀ (n : ℕ) (t : ℝ), HasDerivAt (f n) (f' n t) t := by
    intro n t
    have h1 : HasDerivAt (fun s : ℝ => d n * (s : ℂ)) (d n) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (d n)
    exact h1.cexp.const_mul _
  -- the exponential has unit norm (purely imaginary exponent)
  have hexp_norm : ∀ (n : ℕ) (t : ℝ), ‖Complex.exp (d n * (t : ℂ))‖ = 1 := by
    intro n t
    have harg : d n * (t : ℂ) = ((-(E n - Ebar) * t : ℝ) : ℂ) * Complex.I := by
      rw [hd]; push_cast; ring
    rw [harg, Complex.norm_exp_ofReal_mul_I]
  -- norm of the term derivatives
  have hnorm : ∀ (n : ℕ) (t : ℝ), ‖f' n t‖ = u n := by
    intro n t
    rw [hf', hu_def]
    simp only
    rw [norm_mul, norm_mul, hexp_norm, one_mul, hd]
    simp only [norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hp n)]
  have hu_sum : Summable u := hdev.summable
  have hf0 : Summable fun n => f n 0 := by
    have hfun : (fun n => f n 0) = fun n => (p n : ℂ) := by
      funext n
      rw [hf]
      simp
    rw [hfun]
    exact (Complex.hasSum_ofReal.mpr hsum).summable
  -- derivative of the summed centered autocorrelation
  have hg_deriv : ∀ t : ℝ, HasDerivAt (fun y : ℝ => ∑' n, f n y) (∑' n, f' n t) t := by
    intro t
    exact hasDerivAt_tsum_of_isPreconnected hu_sum isOpen_univ isPreconnected_univ
      (fun n x _ => hderiv n x) (fun n x _ => le_of_eq (hnorm n x)) (mem_univ (0 : ℝ))
      hf0 (mem_univ t)
  -- the speed bound `‖g'‖ ≤ D₁`
  have hgbound : ∀ t : ℝ, ‖∑' n, f' n t‖ ≤ D1 := by
    intro t
    have hfun : (fun n => ‖f' n t‖) = u := funext fun n => hnorm n t
    have hsn : Summable fun n => ‖f' n t‖ := by rw [hfun]; exact hu_sum
    calc ‖∑' n, f' n t‖ ≤ ∑' n, ‖f' n t‖ := norm_tsum_le_tsum_norm hsn
      _ = ∑' n, u n := tsum_congr fun n => hnorm n t
      _ = D1 := hdev.tsum_eq
  -- endpoint values
  have hG0 : (∑' n, f n 0) = 1 := by
    have hfun : (fun n => f n 0) = fun n => (p n : ℂ) := by
      funext n
      rw [hf]
      simp
    rw [hfun, (Complex.hasSum_ofReal.mpr hsum).tsum_eq]
    norm_num
  have hGτ : (∑' n, f n τ) = 0 := by
    set c : ℂ := Complex.exp ((Ebar * τ : ℝ) * Complex.I) with hc
    have h := horth.mul_left c
    have hfun : (fun n => c * ((p n : ℂ) * Complex.exp ((-(E n * τ) : ℝ) * Complex.I)))
        = fun n => f n τ := by
      funext n
      simp only [hf, hc]
      have harg : d n * (τ : ℂ)
          = ((-(E n * τ) : ℝ) : ℂ) * Complex.I + ((Ebar * τ : ℝ) : ℂ) * Complex.I := by
        rw [hd]; push_cast; ring
      rw [harg, Complex.exp_add]
      ring
    rw [hfun] at h
    rw [h.tsum_eq]
    simp
  -- mean value inequality on `[0, τ]`
  have hineq := (convex_Icc (0 : ℝ) τ).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t : ℝ => ∑' n, f n t) (f' := fun t => ∑' n, f' n t)
    (fun x _ => (hg_deriv x).hasDerivWithinAt)
    (fun x _ => hgbound x) (left_mem_Icc.mpr hτ) (right_mem_Icc.mpr hτ)
  have hfinal : (1 : ℝ) ≤ D1 * |τ| := by
    have h1 : ‖(0 : ℂ) - 1‖ ≤ D1 * ‖τ - (0 : ℝ)‖ := by
      simpa [hG0, hGτ] using hineq
    simpa using h1
  rwa [abs_of_nonneg hτ] at hfinal

end QSL
