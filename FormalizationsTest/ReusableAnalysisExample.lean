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

/-- `X² − 1` splits over `ℝ`: its signs at `−2, 0, 2` are `+, −, +`. -/
example : (Polynomial.X ^ 2 - 1 : Polynomial ℝ).Splits := by
  refine splits_of_alternating_sign _ ?_ 2 ?_ ![-2, 0, 2] ?_ ?_
  · intro h
    have := congrArg (Polynomial.eval 0) h
    simp at this
  · compute_degree!
  · refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i <;> norm_num
  · intro i
    fin_cases i <;> norm_num
