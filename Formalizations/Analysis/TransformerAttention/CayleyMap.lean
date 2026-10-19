/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The Cayley map `γ(z) = (2 − z)/(2 + z)` and its fixed point

The Padé decay exponent `γ_Padé(z) = −(z − 2)/(z + 2)` is a Cayley map. Its positive fixed point is
`z* = (√17 − 3)/2`, with susceptibility `χ = (5 + √17)/4` and Floquet multiplier
`μ = γ'(z*) = (√17 − 9)/8`.

## Main results

* `cayley_fixed_point_iff`: `γ(z) = z ↔ z² + 3z − 2 = 0` (for `z ≠ −2`).
* `cayley_root`, `cayley_root_pos`: `z* = (√17 − 3)/2` is a positive root of `z² + 3z − 2`.
* `chi_root`: `χ = (5 + √17)/4` satisfies `2χ² − 5χ + 1 = 0`.
* `floquet_multiplier`, `cayley_floquet_form_equivalence`: `μ = (√17 − 9)/8`, in the cleared form
  `μ (2 + z*)² = −4` and in the table's form `−4(√17 + 1)/(5√17 + 13)`.
* `cayley_floquet_stable`: `|μ| < 1`.
* `cayley_at_zero`, `cayley_at_two`: `γ(0) = 1` (Hagedorn), `γ(2) = 0`.

## References

* C. Marín, *Predicting How Transformers Attend* (2026), §20 of the formula toolkit,
  Zenodo 19826343. Ported from `Taf/RGFlow.lean` and `Taf/ScalingLawIdentities.lean` of
  [karlesmarin/lean-taf](https://github.com/karlesmarin/lean-taf) (Lean v4.30.0-rc2).
-/

@[expose] public section

namespace TransformerAttention.CayleyMap

/-- `γ(z) = −(z − 2)/(z + 2) = z ↔ z² + 3z − 2 = 0`. -/
theorem cayley_fixed_point_iff (z : ℝ) (h : z + 2 ≠ 0) :
    -(z - 2) / (z + 2) = z ↔ z ^ 2 + 3 * z - 2 = 0 := by
  rw [div_eq_iff h]
  constructor
  · intro hz; nlinarith
  · intro hz; nlinarith

/-- `z* = (√17 − 3)/2` is a root of `z² + 3z − 2`. -/
theorem cayley_root : ((Real.sqrt 17 - 3) / 2) ^ 2 + 3 * ((Real.sqrt 17 - 3) / 2) - 2 = 0 := by
  have h : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  linear_combination h / 4

/-- `χ = (5 + √17)/4` satisfies `2χ² − 5χ + 1 = 0`. -/
theorem chi_root : 2 * ((5 + Real.sqrt 17) / 4) ^ 2 - 5 * ((5 + Real.sqrt 17) / 4) + 1 = 0 := by
  have h : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  linear_combination h / 8

/-- `z* = (√17 − 3)/2 > 0`: the physical root. -/
theorem cayley_root_pos : (0 : ℝ) < (Real.sqrt 17 - 3) / 2 := by
  have h_pos : Real.sqrt 17 > 3 := by
    have : Real.sqrt 9 < Real.sqrt 17 :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [show Real.sqrt 9 = 3 from by
          rw [show (9 : ℝ) = 3 ^ 2 from by norm_num]
          exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)] at this
  linarith

/-- Floquet multiplier in cleared form: `((√17 − 9)/8) (2 + z*)² = −4`, i.e.
`γ'(z*) = −4/(2 + z*)² = (√17 − 9)/8`. -/
theorem floquet_multiplier :
    ((Real.sqrt 17 - 9) / 8) * (2 + (Real.sqrt 17 - 3) / 2) ^ 2 = -4 := by
  have h : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  linear_combination (Real.sqrt 17 - 7) / 32 * h

/-- The table's form of the Floquet multiplier: `−4(√17 + 1)/(5√17 + 13) = (√17 − 9)/8`. -/
theorem cayley_floquet_form_equivalence :
    -4 * (Real.sqrt 17 + 1) / (5 * Real.sqrt 17 + 13) = (Real.sqrt 17 - 9) / 8 := by
  have h17 : (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 17)
  have h17_pos : (0 : ℝ) < Real.sqrt 17 := Real.sqrt_pos.mpr (by norm_num)
  have hdenom : 5 * Real.sqrt 17 + 13 ≠ 0 := by
    intro h
    have : (0 : ℝ) < 5 * Real.sqrt 17 + 13 := by
      have : (0 : ℝ) < 5 * Real.sqrt 17 := by positivity
      linarith
    linarith
  rw [div_eq_div_iff hdenom (by norm_num : (8 : ℝ) ≠ 0)]
  nlinarith [h17, h17_pos, sq_nonneg (Real.sqrt 17)]

/-- Stability of the fixed point: `|(√17 − 9)/8| < 1`. -/
theorem cayley_floquet_stable : |(Real.sqrt 17 - 9) / 8| < 1 := by
  have h17_gt_1 : (1 : ℝ) < Real.sqrt 17 := by
    have : Real.sqrt 1 < Real.sqrt 17 :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [Real.sqrt_one] at this
  have h17_lt_5 : Real.sqrt 17 < 5 := by
    have : Real.sqrt 17 < Real.sqrt 25 :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [show Real.sqrt 25 = 5 from by
          rw [show (25 : ℝ) = 5 ^ 2 from by norm_num]
          exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5)] at this
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
  rw [div_lt_one (by norm_num : (0 : ℝ) < 8)]
  rw [abs_of_neg (by linarith : Real.sqrt 17 - 9 < 0)]
  linarith

/-- `γ(0) = 1` (the Hagedorn point). -/
theorem cayley_at_zero : -((0 : ℝ) - 2) / (0 + 2) = 1 := by norm_num

/-- `γ(2) = 0`. -/
theorem cayley_at_two : -((2 : ℝ) - 2) / (2 + 2) = 0 := by norm_num

end TransformerAttention.CayleyMap
