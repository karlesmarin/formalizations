/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.MusicTheory.CyclicHuddlingGeometry

/-!
# The Huddling constant in closed form

From Euler's formula and the chord length `‖exp (I * x) - 1‖ = ‖2 sin (x / 2)‖`, the arc of
`m` consecutive classes in `ZMod N`, `1 < N`, has `‖Ahat (arc m) 1‖ = sin (π m / N) / sin (π / N)`.
This gives the sharp bound for every unit frequency, its equality case, and the symmetry
`m ↔ N - m`.

## Main results

* `norm_Ahat_arc_sine_ratio`.
* `norm_Ahat_unit_le_sine_ratio`, `norm_Ahat_unit_eq_sine_ratio_iff`.
* `sine_ratio_complement`.

## References

* C. Marín, *Huddling, diatonic and pentatonic scales in Z12: Fourier maxima and convex-energy
  minima formalized in Lean 4*, Zenodo (2026), doi:10.5281/zenodo.23121103.
-/

@[expose] public section

namespace MusicTheory

open Finset ZMod Complex AddChar

namespace CyclicHuddling

variable {N : ℕ} [NeZero N]

/-- A cyclic character value is Euler's exponential at its negative angle. -/
lemma character_neg_nat_exp (m : ℕ) :
    stdAddChar (-(m : ZMod N)) =
      Complex.exp (I * ((-(2 * Real.pi * m / N) : ℝ) : ℂ)) := by
  have hc := ZMod.stdAddChar_coe (N := N) (-(m : ℤ))
  simp only [Int.cast_neg, Int.cast_natCast] at hc
  rw [hc]
  congr 1
  push_cast
  ring

/-- Euler's chord-length formula at an `N`th root of unity. -/
lemma norm_character_neg_nat_sub_one (m : ℕ) :
    ‖stdAddChar (-(m : ZMod N)) - 1‖ =
      2 * |Real.sin (Real.pi * m / N)| := by
  rw [character_neg_nat_exp, Complex.norm_exp_I_mul_ofReal_sub_one]
  have he : -(2 * Real.pi * m / N) / 2 = -(Real.pi * m / N) := by ring
  rw [he, Real.sin_neg]
  simp [Real.norm_eq_abs]

/-- The exact Fourier magnitude of a consecutive cyclic arc. -/
theorem norm_Ahat_arc_sine_ratio (hN : 1 < N) (m : ℕ) (hm : m ≤ N) :
    ‖Ahat (arc (N := N) m) 1‖ =
      Real.sin (Real.pi * m / N) / Real.sin (Real.pi / N) := by
  have hN₀ : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hN₁ : (1 : ℝ) < N := by exact_mod_cast hN
  have hmR : (m : ℝ) ≤ N := by exact_mod_cast hm
  have hden : 0 < Real.sin (Real.pi / N) := by
    apply Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos hN₀)
    rw [div_lt_iff₀ hN₀]
    nlinarith [Real.pi_pos]
  have hnum : 0 ≤ Real.sin (Real.pi * m / N) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
    rw [div_le_iff₀ hN₀]
    exact mul_le_mul_of_nonneg_left hmR Real.pi_pos.le
  have hp : (stdAddChar (-(1 : ZMod N))) ^ m =
      stdAddChar (-(m : ZMod N)) := by
    rw [← map_nsmul_eq_pow]
    congr 1
    simp [nsmul_eq_mul]
  have h := congrArg norm (Ahat_arc_mul_sub (N := N) m hm 1)
  rw [norm_mul, hp, norm_character_neg_nat_sub_one m] at h
  have hd := norm_character_neg_nat_sub_one (N := N) 1
  simp only [Nat.cast_one, mul_one] at hd
  rw [hd, abs_of_nonneg hnum, abs_of_pos hden] at h
  apply (eq_div_iff hden.ne').mpr
  nlinarith

/-- Huddling with its explicit sine-ratio constant at every primitive frequency. -/
theorem norm_Ahat_unit_le_sine_ratio (hN : 1 < N)
    (B : Finset (ZMod N)) (k : ZMod N) (hk : IsUnit k) :
    ‖Ahat B k‖ ≤ Real.sin (Real.pi * B.card / N) / Real.sin (Real.pi / N) := by
  have hm : B.card ≤ N := by simpa using B.card_le_univ
  rw [← norm_Ahat_arc_sine_ratio hN B.card hm]
  exact norm_Ahat_unit_le_arc B k hk

/-- Equality in the sine-ratio bound is exactly the frequency-image arc condition. -/
theorem norm_Ahat_unit_eq_sine_ratio_iff (hN : 1 < N)
    (B : Finset (ZMod N)) (k : ZMod N) (hk : IsUnit k) :
    ‖Ahat B k‖ = Real.sin (Real.pi * B.card / N) / Real.sin (Real.pi / N) ↔
      ∃ s : ZMod N, B.image (· * k) = tpose s (arc (N := N) B.card) := by
  have hm : B.card ≤ N := by simpa using B.card_le_univ
  rw [← norm_Ahat_arc_sine_ratio hN B.card hm]
  exact norm_Ahat_unit_eq_arc_iff B k hk

/-- Complementary cardinalities have the same sine-ratio bound. -/
theorem sine_ratio_complement (m : ℕ) (hm : m ≤ N) :
    Real.sin (Real.pi * (N - m : ℕ) / N) / Real.sin (Real.pi / N) =
      Real.sin (Real.pi * m / N) / Real.sin (Real.pi / N) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have he : Real.pi * (N - m : ℕ) / N = Real.pi - Real.pi * m / N := by
    rw [Nat.cast_sub hm]
    field_simp
  rw [he, Real.sin_pi_sub]

end CyclicHuddling

end MusicTheory
