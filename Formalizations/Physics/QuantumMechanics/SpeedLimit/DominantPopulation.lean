/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Complex.Basic

/-!
# A dominant population keeps a state away from orthogonality

For a probability distribution p on ℕ and complex numbers u k of modulus one (the phases e^{−i E_k
t} of a state with populations p k), 2 p j − 1 ≤ ‖∑ p k u k‖ for every index j, by the triangle
inequality: a level that carries more than half of the population keeps the autocorrelation away
from zero at every time, whatever the energy moments. This is the cut-off inequality |A(t)| ≥
α|Ā(t)| − (1 − α) of Uffink, in the form of M. Andrews, Phys. Rev. A 75, 062112 (2007), Eq. (21),
with the cut-off isolating one level.

## Main results

* `Dilog.two_mul_sub_one_le_norm_tsum`: 2 p j − 1 ≤ ‖∑ p k u k‖ for phases of modulus one
* `Dilog.tsum_ne_zero_of_half_lt`: the autocorrelation never vanishes when some p j > 1/2

## References

* C. Marín, *The Clock That Never Ticks: a machine-checked path from the dilogarithm to quantum
  speed limits in Lean 4*, Zenodo (2026), doi:10.5281/zenodo.20675271, `thm:clock`.
-/

@[expose] public section

open Complex

namespace Dilog

/-- **The dominant-population floor.** For a probability distribution `p` and phases `u k` of
modulus one, `2 p j - 1 ≤ ‖∑ p k u k‖` for every index `j`. -/
theorem two_mul_sub_one_le_norm_tsum (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hs : HasSum p 1)
    (u : ℕ → ℂ) (hu : ∀ k, ‖u k‖ = 1) (j : ℕ) :
    2 * p j - 1 ≤ ‖∑' k, (p k : ℂ) * u k‖ := by
  have hnorm : ∀ k, ‖(p k : ℂ) * u k‖ = p k := fun k ↦ by
    rw [norm_mul, hu k, mul_one, Complex.norm_real, Real.norm_of_nonneg (hp k)]
  have hsn : Summable fun k ↦ ‖(p k : ℂ) * u k‖ := by
    simpa only [hnorm] using hs.summable
  have hsc : Summable fun k ↦ (p k : ℂ) * u k := hsn.of_norm
  -- the rest of the sum, without the term `j`
  set R : ℂ := ∑' k, if k = j then 0 else (p k : ℂ) * u k with hR
  have hsplit : ∑' k, (p k : ℂ) * u k = (p j : ℂ) * u j + R := hsc.tsum_eq_add_tsum_ite j
  have hrest : ∑' k, (if k = j then 0 else p k) = 1 - p j := by
    have := hs.summable.tsum_eq_add_tsum_ite j
    rw [hs.tsum_eq] at this
    linarith
  have hRle : ‖R‖ ≤ 1 - p j := by
    have hsn' : Summable fun k ↦ ‖if k = j then (0 : ℂ) else (p k : ℂ) * u k‖ := by
      refine hsn.of_nonneg_of_le (fun k ↦ norm_nonneg _) (fun k ↦ ?_)
      split_ifs
      · rw [norm_zero]; exact norm_nonneg _
      · exact le_rfl
    calc ‖R‖ ≤ ∑' k, ‖if k = j then (0 : ℂ) else (p k : ℂ) * u k‖ := norm_tsum_le_tsum_norm hsn'
      _ = ∑' k, (if k = j then 0 else p k) := by
          congr 1; funext k; split_ifs
          · exact norm_zero
          · exact hnorm k
      _ = 1 - p j := hrest
  have htri : ‖(p j : ℂ) * u j‖ - ‖R‖ ≤ ‖(p j : ℂ) * u j + R‖ := by
    have := norm_sub_norm_le ((p j : ℂ) * u j) (-R)
    simpa [sub_neg_eq_add, norm_neg] using this
  rw [hsplit]
  rw [hnorm j] at htri
  linarith

/-- **A dominant population forbids orthogonality.** If some population exceeds `1/2`, the
autocorrelation `∑ p k u k` never vanishes. -/
theorem tsum_ne_zero_of_half_lt (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hs : HasSum p 1)
    (u : ℕ → ℂ) (hu : ∀ k, ‖u k‖ = 1) {j : ℕ} (hj : 1 / 2 < p j) :
    ∑' k, (p k : ℂ) * u k ≠ 0 := by
  intro h
  have := two_mul_sub_one_le_norm_tsum p hp hs u hu j
  rw [h, norm_zero] at this
  linarith

end Dilog
