/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Wolstenholme's inequality for the angles of a triangle

If `A + B + C = π` then `2yz cos A + 2zx cos B + 2xy cos C ≤ x² + y² + z²` for all real `x, y, z`
(no sign conditions on the angles are needed). The defect is a sum of two squares:
`x² + y² + z² - (2yz cos A + 2zx cos B + 2xy cos C) = (x - z cos B - y cos C)² + (z sin B - y sin C)²`,
using `cos A = -cos (B + C)`.

## Main results

* `WolstenholmeInequality.sub_eq_sq_add_sq`: the defect is (x - z cos B - y cos C)^2 + (z sin B - y sin C)^2
* `WolstenholmeInequality.cos_le`: x^2+y^2+z^2 >= 2yz cos A + 2zx cos B + 2xy cos C when A+B+C = pi

## References

* J. Wolstenholme, *A Book of Mathematical Problems*, Macmillan, 1867.
-/

@[expose] public section

namespace WolstenholmeInequality

/-- The defect of Wolstenholme's inequality is a sum of two squares when `A + B + C = π`. -/
theorem sub_eq_sq_add_sq (x y z A B C : ℝ) (h : A + B + C = Real.pi) :
    x ^ 2 + y ^ 2 + z ^ 2 - (2 * y * z * Real.cos A + 2 * z * x * Real.cos B
        + 2 * x * y * Real.cos C) =
      (x - z * Real.cos B - y * Real.cos C) ^ 2 + (z * Real.sin B - y * Real.sin C) ^ 2 := by
  have hA : A = Real.pi - (B + C) := by linarith
  have hcos : Real.cos A = -(Real.cos B * Real.cos C - Real.sin B * Real.sin C) := by
    rw [hA, Real.cos_pi_sub, Real.cos_add]
  have hB := Real.sin_sq_add_cos_sq B
  have hC := Real.sin_sq_add_cos_sq C
  rw [hcos]
  linear_combination (-z ^ 2) * hB + (-y ^ 2) * hC

/-- **Wolstenholme's inequality.** If `A + B + C = π` (the angles of a triangle), then for all real
`x, y, z`: `2yz cos A + 2zx cos B + 2xy cos C ≤ x² + y² + z²`. -/
theorem cos_le (x y z A B C : ℝ) (h : A + B + C = Real.pi) :
    2 * y * z * Real.cos A + 2 * z * x * Real.cos B + 2 * x * y * Real.cos C
      ≤ x ^ 2 + y ^ 2 + z ^ 2 := by
  have := sub_eq_sq_add_sq x y z A B C h
  nlinarith [sq_nonneg (x - z * Real.cos B - y * Real.cos C),
    sq_nonneg (z * Real.sin B - y * Real.sin C)]

end WolstenholmeInequality
