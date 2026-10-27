/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.MvPolynomial.Polynomial
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Cotes' harmonic means theorem

Let `f(x, y) = 0` be a plane algebraic curve, `p` a point not on it, and `L = {p + t v}` a line
through `p` meeting the curve in `d` real points `p + tᵢ v`, i.e. `g(t) = f(p + t v)` splits with
roots `tᵢ`. The harmonic-mean point `p + t* v`, `d / t* = Σ 1/tᵢ`, lies on the line
`∇f(p) · (x - p) = -d f(p)` (the polar of `p`), which does not depend on `L` (Cotes, 1722). The
proof computes `g(0) = f(p)` and `g'(0) = ∇f(p) · v` by induction on `f`, and `Σ 1/tᵢ = -g'(0)/g(0)`
from Mathlib's logarithmic-derivative formula for split polynomials
(`Splits.eval_derivative_div_eval_of_ne_zero`).

## Main results

* `Cotes.sum_inv_roots_eq`: sum of reciprocal roots of the restriction g(t) = f(p + t v) is -g'(0)/g(0)
* `Cotes.harmonic_mean_polar`: the harmonic mean point of the intersections lies on the polar line of p

## References

* R. Cotes, *Harmonia Mensurarum*, Cambridge, 1722 (published by R. Smith).
* C. Maclaurin, *De linearum geometricarum proprietatibus generalibus*, 1748.
-/

@[expose] public section

namespace Cotes

open Polynomial

/-- For a split polynomial `g` with `g(0) ≠ 0`: `Σ 1/rᵢ = -g'(0)/g(0)` over its roots. -/
theorem sum_inv_roots_eq (g : Polynomial ℝ) (hsplit : g.roots.card = g.natDegree)
    (h0 : g.eval 0 ≠ 0) :
    (g.roots.map (fun r => r⁻¹)).sum = -(g.derivative.eval 0 / g.eval 0) := by
  have hs : g.Splits := splits_iff_card_roots.mpr hsplit
  have e : g.roots.map (fun r => r⁻¹) = g.roots.map (fun z => -(1 / (0 - z))) :=
    Multiset.map_congr rfl (fun z _ => by simp)
  rw [hs.eval_derivative_div_eval_of_ne_zero h0, e, Multiset.sum_map_neg]

/-- Value and derivative at `t = 0` of the restriction of `f` to the line `p + t v`. -/
theorem line_value_deriv (p v : Fin 2 → ℝ) (f : MvPolynomial (Fin 2) ℝ) :
    (Polynomial.eval 0 (MvPolynomial.aeval
        (fun i => Polynomial.C (p i) + Polynomial.C (v i) * Polynomial.X) f)
      = MvPolynomial.eval p f) ∧
    (Polynomial.eval 0 (Polynomial.derivative (MvPolynomial.aeval
        (fun i => Polynomial.C (p i) + Polynomial.C (v i) * Polynomial.X) f))
      = ∑ i, MvPolynomial.eval p (MvPolynomial.pderiv i f) * v i) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg =>
    refine ⟨by simp [hf.1, hg.1], ?_⟩
    simp [hf.2, hg.2, add_mul, Finset.sum_add_distrib]
  | mul_X f j ih =>
    refine ⟨by simp [ih.1], ?_⟩
    simp [ih.2, ih.1, add_mul, Finset.sum_add_distrib, MvPolynomial.pderiv_X, Pi.single_apply]
    fin_cases j <;> simp <;> ring

/-- **Cotes' harmonic means theorem.** -/
theorem harmonic_mean_polar (f : MvPolynomial (Fin 2) ℝ) (p v : Fin 2 → ℝ)
    (hp : MvPolynomial.eval p f ≠ 0)
    (g : Polynomial ℝ)
    (hg : g = MvPolynomial.aeval (fun i => Polynomial.C (p i) + Polynomial.C (v i) * Polynomial.X) f)
    (hsplit : g.roots.card = g.natDegree) (hd : 1 ≤ g.natDegree)
    (hH : (g.roots.map (fun r => r⁻¹)).sum ≠ 0) :
    ∑ i, MvPolynomial.eval p (MvPolynomial.pderiv i f) *
        ((g.natDegree : ℝ) / (g.roots.map (fun r => r⁻¹)).sum * v i)
      = -(g.natDegree : ℝ) * MvPolynomial.eval p f := by
  have key := line_value_deriv p v f
  rw [← hg] at key
  have h0 : g.eval 0 ≠ 0 := by rw [key.1]; exact hp
  have hsum := sum_inv_roots_eq g hsplit h0
  rw [key.1, key.2] at hsum
  set S := ∑ i, MvPolynomial.eval p (MvPolynomial.pderiv i f) * v i with hS
  have h1 : ∑ i, MvPolynomial.eval p (MvPolynomial.pderiv i f) *
        ((g.natDegree : ℝ) / (g.roots.map (fun r => r⁻¹)).sum * v i)
      = (g.natDegree : ℝ) / (g.roots.map (fun r => r⁻¹)).sum * S := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [h1]
  rw [hsum] at hH ⊢
  have hS0 : S ≠ 0 := by
    intro h; apply hH; rw [h]; simp
  field_simp

end Cotes
