/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# `2^a 3^b = 1` forces `a = b = 0`

Proposition 4 of the su7-certified-gap paper: with integer exponents, `2^a 3^b = 1` only for `a = b = 0`; hence
`ΔU log 2 + ΔV log 3 = 0` has only the trivial integer solution and the fibre of `81` is exact (§5). The proof
reads the `2`-adic and the `3`-adic valuations of both sides.

## Main results

* `two_zpow_mul_three_zpow_eq_one`: `(2 : ℚ)^a * 3^b = 1 → a = 0 ∧ b = 0` for `a b : ℤ`.

## References

* C. Marín, *A certified gap for SU(7) grand gauge-Higgs unification*, Proposition 4 (`prop:four`).
-/

@[expose] public section

namespace GaugeHiggsUnification.TwoThreeIndependence

/-- `2^a 3^b = 1` with integer exponents forces `a = b = 0` (compare the `2`-adic and `3`-adic valuations). -/
theorem two_zpow_mul_three_zpow_eq_one {a b : ℤ} (h : (2 : ℚ) ^ a * 3 ^ b = 1) : a = 0 ∧ b = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha : (2 : ℚ) ^ a ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hb : (3 : ℚ) ^ b ≠ 0 := zpow_ne_zero _ (by norm_num)
  have v2 := congrArg (padicValRat 2) h
  have v3 := congrArg (padicValRat 3) h
  rw [padicValRat.mul ha hb, padicValRat.zpow, padicValRat.zpow, padicValRat.one] at v2 v3
  have s2 : padicValRat 2 (2 : ℚ) = 1 := by simpa using padicValRat.self (p := 2) (by norm_num)
  have s3 : padicValRat 3 (3 : ℚ) = 1 := by simpa using padicValRat.self (p := 3) (by norm_num)
  have c23 : padicValRat 2 (3 : ℚ) = 0 := by
    have := padicValRat.of_nat (p := 2) (n := 3)
    simp only [Nat.cast_ofNat] at this
    rw [this, padicValNat.eq_zero_of_not_dvd (by norm_num)]
    rfl
  have c32 : padicValRat 3 (2 : ℚ) = 0 := by
    have := padicValRat.of_nat (p := 3) (n := 2)
    simp only [Nat.cast_ofNat] at this
    rw [this, padicValNat.eq_zero_of_not_dvd (by norm_num)]
    rfl
  rw [s2, c23] at v2
  rw [c32, s3] at v3
  constructor <;> linarith

end GaugeHiggsUnification.TwoThreeIndependence
