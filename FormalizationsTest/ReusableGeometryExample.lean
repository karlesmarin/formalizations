/-
Usage examples of the reusable layer, area Geometry, with the minimal import of that area: the
same code a user pastes into a file of their own project (README, section "Reusable layer").
-/
import Formalizations.Reusable.Geometry

open Formalizations.Reusable Matrix Real

/-- Pappus over `ℚ`: the three meets are collinear. -/
example (A B C a b c : Fin 3 → ℚ) (h₁ : A ⬝ᵥ (B ⨯₃ C) = 0) (h₂ : a ⬝ᵥ (b ⨯₃ c) = 0) :
    ((A ⨯₃ b) ⨯₃ (a ⨯₃ B)) ⬝ᵥ (((A ⨯₃ c) ⨯₃ (a ⨯₃ C)) ⨯₃ ((B ⨯₃ c) ⨯₃ (b ⨯₃ C))) = 0 :=
  pappus_hexagon A B C a b c h₁ h₂

/-- Wolstenholme's inequality, from the defect identity. -/
example (x y z A B C : ℝ) (h : A + B + C = π) :
    2 * y * z * Real.cos A + 2 * z * x * Real.cos B + 2 * x * y * Real.cos C
      ≤ x ^ 2 + y ^ 2 + z ^ 2 := by
  have := wolstenholme_defect_eq_sq_add_sq x y z A B C h
  nlinarith [sq_nonneg (x - z * Real.cos B - y * Real.cos C),
    sq_nonneg (z * Real.sin B - y * Real.sin C)]
