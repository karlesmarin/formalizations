/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.MusicTheory.Fourier

/-!
# Tritone symmetry is a phase fact

A pitch-class set `A ⊆ ℤ/12` is fixed by the tritone transposition `T₆` iff its discrete Fourier
transform `Â` vanishes at every odd frequency. The engine is `Â (T₆ A) t = (-1)ᵗ · Â A t`
(`Fourier.Ahat_tpose` at `k = 6`) together with injectivity of `Â` (`Fourier.Ahat_injective`).

## Main results

* `stdAddChar_neg_six_mul_of_odd`, `stdAddChar_neg_six_mul_of_not_odd`: the tritone character
  `t ↦ exp(-2πi·6t/12)` is `-1` at odd `t` and `1` at even `t`.
* `tpose_six_eq_iff`: `T₆ A = A ↔ ∀ t, Odd t.val → Â A t = 0`.

## References

* C. Marín, *The phase taxonomy of pitch-class set invariants*, Zenodo (2026),
  doi:10.5281/zenodo.20826773, §7 (P4).
-/

@[expose] public section

namespace MusicTheory

open ZMod

namespace TritoneFixedFourier

open _root_.MusicTheory.Fourier

/-- `6t` reduces to `0` at even `t` and to `6` at odd `t` (finite check in `ZMod 12`). -/
lemma neg_six_mul_cases (t : ZMod 12) :
    (¬ Odd t.val → -(6 * t) = 0) ∧ (Odd t.val → -(6 * t) = 6) := by
  revert t
  decide

/-- The value of the standard character at the tritone is `-1`. -/
lemma stdAddChar_six : stdAddChar (6 : ZMod 12) = -1 := by
  have hsq : stdAddChar (6 : ZMod 12) * stdAddChar (6 : ZMod 12) = 1 := by
    rw [← AddChar.map_add_eq_mul, show (6 : ZMod 12) + 6 = 0 by decide, AddChar.map_zero_eq_one]
  have hne : stdAddChar (6 : ZMod 12) ≠ 1 := by
    rw [← (stdAddChar (N := 12)).map_zero_eq_one, injective_stdAddChar.ne_iff]
    decide
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · exact absurd h hne
  · exact h

/-- The tritone character: `exp(-2πi·6t/12) = (-1)ᵗ`. -/
theorem stdAddChar_neg_six_mul_of_odd {t : ZMod 12} (ht : Odd t.val) :
    stdAddChar (-(6 * t)) = -1 := by
  rw [(neg_six_mul_cases t).2 ht, stdAddChar_six]

/-- The tritone character is `1` at even frequencies. -/
theorem stdAddChar_neg_six_mul_of_not_odd {t : ZMod 12} (ht : ¬ Odd t.val) :
    stdAddChar (-(6 * t)) = 1 := by
  rw [(neg_six_mul_cases t).1 ht, AddChar.map_zero_eq_one]

/-- **Tritone symmetry is a phase fact.** `T₆ A = A` iff `Â A` vanishes at every odd frequency. -/
theorem tpose_six_eq_iff (A : Finset (ZMod 12)) :
    tpose 6 A = A ↔ ∀ t : ZMod 12, Odd t.val → Ahat A t = 0 := by
  constructor
  · intro h t ht
    have h1 := Ahat_tpose 6 A t
    rw [h, stdAddChar_neg_six_mul_of_odd ht] at h1
    have h2 : (2 : ℂ) * Ahat A t = 0 := by linear_combination h1
    simpa using h2
  · intro h
    apply Ahat_injective
    funext t
    rw [Ahat_tpose]
    by_cases ht : Odd t.val
    · rw [h t ht, mul_zero]
    · rw [stdAddChar_neg_six_mul_of_not_odd ht, one_mul]

end TritoneFixedFourier

end MusicTheory
