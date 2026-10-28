/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Lin McMullin's theorem: inflection points of a quartic and the golden ratio

Let `p` be a real quartic whose second derivative vanishes at `a ≠ b` (its two inflection points).
The line through `(a, p a)` and `(b, p b)` meets the graph exactly at `a`, `b`, `φa − b/φ` and
`φb − a/φ`, `φ` the golden ratio. If `a < b` these are ordered `φa − b/φ < a < b < φb − a/φ`, and
`b − a = φ (a − (φa − b/φ)) = φ ((φb − a/φ) − b)`. Proof: `p'' = 12c (X − a)(X − b)`, so
`p = c (X⁴ − 2(a + b)X³ + 6ab X²) + dX + e`, and
`p − line = c (X − a)(X − b)(X² − (a + b)X + a² + b² − 3ab)`, whose quadratic factor has roots
`φa − b/φ`, `φb − a/φ` because `φ² = φ + 1`.

## Main results

* `McMullin.line_inter_iff`: the line through the inflection points meets the quartic exactly at a, b, φa − b/φ, φb − a/φ
* `McMullin.order`: if a < b: φa − b/φ < a < b < φb − a/φ
* `McMullin.golden_ratio_gaps`: b − a = φ (a − P) = φ (Q − b)

## References

* R. Whitty, Theorem of the Day, «Lin McMullin's Theorem» (Analysis/McMullin).
* L. McMullin (2004); A. Bogomolny, cut-the-knot, «Fourth Degree Polynomials and the Golden Ratio».
-/

@[expose] public section

open Polynomial Real

namespace McMullin

/-- `y / φ = y (φ − 1)`. -/
theorem div_golden (y : ℝ) : y / goldenRatio = y * (goldenRatio - 1) := by
  have h0 : goldenRatio ≠ 0 := goldenRatio_ne_zero
  have hsq : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  generalize goldenRatio = g at *
  field_simp
  linear_combination -y * hsq

/-- **Lin McMullin's theorem.** Let `p` be a real polynomial of degree 4 whose second derivative vanishes at two
distinct points `a ≠ b` (the two inflection points `A`, `B`). The line through `(a, p a)` and `(b, p b)` meets the
graph exactly at the abscissae `a`, `b`, `φa - b/φ` and `φb - a/φ` (`φ` the golden ratio). -/
theorem line_inter_iff (p : ℝ[X]) (hp : p.natDegree = 4) (a b : ℝ) (hab : a ≠ b)
    (ha : (derivative (derivative p)).eval a = 0) (hb : (derivative (derivative p)).eval b = 0) (x : ℝ) :
    p.eval x = p.eval a + (p.eval b - p.eval a) / (b - a) * (x - a) ↔
      x = a ∨ x = b ∨ x = goldenRatio * a - b / goldenRatio ∨ x = goldenRatio * b - a / goldenRatio := by
  have hsum := p.as_sum_range_C_mul_X_pow
  rw [hp] at hsum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hsum
  have hc4 : p.coeff 4 ≠ 0 := by
    have : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (by rintro rfl; simp at hp)
    rwa [leadingCoeff, hp] at this
  set c0 := p.coeff 0
  set c1 := p.coeff 1
  set c2 := p.coeff 2
  set c3 := p.coeff 3
  set c4 := p.coeff 4
  have hd : ∀ y : ℝ, (derivative (derivative p)).eval y = 12 * c4 * y ^ 2 + 6 * c3 * y + 2 * c2 := by
    intro y
    rw [hsum]
    simp
    ring
  have he : ∀ y : ℝ, p.eval y = c4 * y ^ 4 + c3 * y ^ 3 + c2 * y ^ 2 + c1 * y + c0 := by
    intro y
    rw [hsum]
    simp
    ring
  rw [hd] at ha hb
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have h3 : c3 = -2 * c4 * (a + b) := by
    have : (a - b) * (6 * c3 + 12 * c4 * (a + b)) = 0 := by linear_combination ha - hb
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hab
    · linarith
  have h2 : c2 = 6 * c4 * a * b := by
    rw [h3] at ha
    linear_combination (1 / 2) * ha
  have hφ : goldenRatio ≠ 0 := goldenRatio_ne_zero
  have hsq : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  have hdiv : ∀ y : ℝ, y / goldenRatio = y * (goldenRatio - 1) := fun y => div_golden y
  have hs : (p.eval b - p.eval a) / (b - a) = c4 * (a + b) * (4 * a * b - a ^ 2 - b ^ 2) + c1 := by
    rw [div_eq_iff hba, he, he, h3, h2]
    ring
  have key : p.eval x - (p.eval a + (p.eval b - p.eval a) / (b - a) * (x - a)) =
      c4 * ((x - a) * (x - b) * ((x - (goldenRatio * a - b / goldenRatio)) *
        (x - (goldenRatio * b - a / goldenRatio)))) := by
    rw [hs, he, he, h3, h2, hdiv, hdiv]
    generalize goldenRatio = g at *
    linear_combination c4 * (x - a) * (x - b) * (a - b) ^ 2 * hsq
  rw [← sub_eq_zero, key]
  simp only [mul_eq_zero, hc4, false_or, sub_eq_zero]
  tauto

/-- If `a < b`: `φa − b/φ < a < b < φb − a/φ`. -/
theorem order (a b : ℝ) (hab : a < b) :
    goldenRatio * a - b / goldenRatio < a ∧ a < b ∧ b < goldenRatio * b - a / goldenRatio := by
  have h1 : 1 < goldenRatio := one_lt_goldenRatio
  rw [div_golden, div_golden]
  generalize goldenRatio = g at *
  refine ⟨?_, hab, ?_⟩ <;> nlinarith

/-- The gaps are in the golden ratio: `b − a = φ (a − P) = φ (Q − b)`. -/
theorem golden_ratio_gaps (a b : ℝ) :
    b - a = goldenRatio * (a - (goldenRatio * a - b / goldenRatio)) ∧
      b - a = goldenRatio * ((goldenRatio * b - a / goldenRatio) - b) := by
  have hsq : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  rw [div_golden, div_golden]
  generalize goldenRatio = g at *
  constructor
  · linear_combination (a - b) * hsq
  · linear_combination (a - b) * hsq

end McMullin
