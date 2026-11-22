/-
Usage examples of the reusable layer, area Analysis, with the minimal import of that area: the
same code a user pastes into a file of their own project (README, section "Reusable layer").
-/
import Formalizations.Reusable.Analysis

open Formalizations.Reusable Real Set

/-- The zero set of a solution of `y'' = x y` is not bounded below. -/
example (f f' : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (x * f x) x) : ¬ BddBelow {x | f x = 0} := by
  rintro ⟨m, hm⟩
  obtain ⟨x, hx, h0⟩ := airy_eq_zeros_unbounded_below f f' hf hf' m
  exact absurd (hm h0) (not_le.2 hx)

/-- Glasser's integral at `a = 0`, `b = 1`: `∫_{v>0} v^{-1/2} e^{-v} dv = √π`. -/
example : ∫ v in Ioi (0 : ℝ), v ^ (-(1 : ℝ) / 2) * Real.exp (-0 / v - 1 * v) = Real.sqrt π := by
  simpa using glasser_integral (a := 0) (b := 1) le_rfl one_pos

/-- The product of sines for `n = 6`. -/
example : ∏ k ∈ Finset.Ico (1 : ℕ) 6, 2 * Real.sin (k * π / 6) = 6 := by
  have := prod_two_sin_mul_pi_div 6 (by norm_num)
  push_cast at this
  exact this

/-- Eneström–Kakeya: `1 + z/2 + z²/3` (coefficients `1 ≥ 1/2 ≥ 1/3 > 0`) has no zero in the open
unit disc. -/
example {z : ℂ} (hz : ‖z‖ < 1) : (1 : ℂ) + z / 2 + z ^ 2 / 3 ≠ 0 := by
  have h := enestrom_kakeya_ne_zero (n := 2) (fun k => 1 / ((k : ℝ) + 1))
    (fun k _ => by positivity)
    (fun k _ => one_div_le_one_div_of_le (by positivity) (by push_cast; linarith)) hz
  convert h using 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  ring

/-- Generalised Hlawka for `n = 4` vectors of `ℝ`: `d₂ + d₃ ≤ 3 (d₁ + d₄)`. -/
example (x : Fin 4 → ℝ) :
    ∑ k ∈ Finset.Icc 2 (4 - 1), ∑ S ∈ (Finset.univ : Finset (Fin 4)).powersetCard k, ‖∑ i ∈ S, x i‖
      ≤ (2 ^ (4 - 2) - 1 : ℝ) * (∑ i, ‖x i‖ + ‖∑ i, x i‖) :=
  hlawka_generalised (by norm_num) x


/-- Zieliński–Zych at `α = 1` (the Margolus–Levitin case): `0 ≤ x − π/2 + (π/2) cos x + sin x` for `x ≥ 0`. -/
example {x : ℝ} (hx : 0 ≤ x) : 0 ≤ x - π / 2 + π / 2 * Real.cos x + Real.sin x := by
  have h := zielinski_zych_inequality one_pos hx
  simpa using h
