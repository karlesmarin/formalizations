/-
Usage example of the reusable layer, area MeasureTheory, with the minimal import of that area: the
same code a user pastes into a file of their own project (README, section "Reusable layer").
-/
import Formalizations.Reusable.MeasureTheory

open Formalizations.Reusable MeasureTheory

/-- Torricelli's trumpet has finite volume. -/
example :
    volume {q : (ℝ × ℝ) × ℝ | 1 ≤ q.2 ∧ Real.sqrt (q.1.1 ^ 2 + q.1.2 ^ 2) ≤ 1 / q.2} ≠ ⊤ := by
  rw [torricelli_trumpet.1]
  exact ENNReal.ofReal_ne_top
