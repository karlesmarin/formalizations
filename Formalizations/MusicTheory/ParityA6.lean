/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.MusicTheory.Fourier
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Tactic.Ring

/-!
# The sixth Fourier coefficient is the parity imbalance

For a pitch-class set `A ⊆ ℤ/12`, `Ahat A 6 = ∑ a ∈ A, (-1) ^ a.val`, the number of even minus
the number of odd pitch classes in `A`; so `Ahat A 6 = 0` iff `A` has as many even as odd pitch
classes. The same holds at the frequency `m` of `ℤ/(2m)`.

## Main results

* `Ahat_six_eq_sum_neg_one_pow`, `Ahat_six_eq_card_sub`, `Ahat_six_eq_zero_iff`.
* `dftN_half_eq_sum_neg_one_pow`: the general even modulus.

## References

* E. Amiot, *The torii of phases*, in Mathematics and Computation in Music (MCM 2013).
* J. Hoffman, *On pitch-class set cartography*, J. Music Theory 52 (2008).
* C. Marín, *The per-voice Fourier signature: the bass is the spectrally purest voice*,
  Zenodo (2026), doi:10.5281/zenodo.20971089.
-/

@[expose] public section

namespace MusicTheory

open Finset ZMod AddChar
open scoped ZMod
open MusicTheory.Fourier

namespace ParityA6

/-! ### Part 1 — the half-cycle coefficient is the even−odd parity imbalance. -/

/-- **FC-K, evenSet form.** `Â A 6 = Σ_{a∈A} (±1)` with `+1` on even pcs and `−1` on odd pcs.
    Immediate from `Ahat_apply` and the order-2 character value `stdAddChar(−(a·6)) = ±1`
    (`Fourier.stdAddChar_neg_mul_six`). -/
theorem Ahat_six_eq_even_sub_odd (A : Finset (ZMod 12)) :
    Ahat A 6 = ∑ a ∈ A, (if a ∈ evenSet then (1 : ℂ) else -1) := by
  rw [Ahat_apply]
  exact Finset.sum_congr rfl fun a _ => stdAddChar_neg_mul_six a

/-- The ±1 sign at frequency 6 IS `(−1)^a.val`: even residues `↦ +1`, odd residues `↦ −1`.
    `a ∈ evenSet ⟺ Even a.val` is decidable over `ZMod 12`; then `Even/Odd.neg_one_pow`. -/
lemma neg_one_pow_val (a : ZMod 12) :
    ((-1 : ℂ)) ^ a.val = if a ∈ evenSet then (1 : ℂ) else -1 := by
  have h : (a ∈ evenSet) ↔ Even a.val := by revert a; decide
  by_cases he : Even a.val
  · rw [ite_eq_left (h.mpr he), he.neg_one_pow]
  · rw [ite_eq_right (fun hc => he (h.mp hc)), (Nat.not_even_iff_odd.mp he).neg_one_pow]

/-- **FC-K, the headline `(−1)^a` form.** `Â A 6 = Σ_{a∈A} (−1)^a` — the half-cycle coefficient
    equals the signed pitch-class count (`+1` even, `−1` odd). -/
theorem Ahat_six_eq_sum_neg_one_pow (A : Finset (ZMod 12)) :
    Ahat A 6 = ∑ a ∈ A, ((-1 : ℂ)) ^ a.val := by
  rw [Ahat_six_eq_even_sub_odd]
  exact Finset.sum_congr rfl fun a _ => (neg_one_pow_val a).symm

/-- **FC-K, the card form.** `Â A 6 = #(even pcs of A) − #(odd pcs of A)` as a complex number.
    Split the ±1 sum over the parity partition. -/
theorem Ahat_six_eq_card_sub (A : Finset (ZMod 12)) :
    Ahat A 6 = ((A.filter (· ∈ evenSet)).card : ℂ)
                - ((A.filter (fun a => a ∉ evenSet)).card : ℂ) := by
  rw [Ahat_six_eq_even_sub_odd, Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg_one]
  ring

/-! ### Part 2 — a₆ vanishes iff the pc-set is parity-balanced. -/

/-- **FC-K characterization.** `Â A 6 = 0 ⟺ #(even pcs) = #(odd pcs)` — the half-cycle coefficient
    vanishes exactly when `A` carries equally many even and odd pitch classes (parity balance). -/
theorem Ahat_six_eq_zero_iff (A : Finset (ZMod 12)) :
    Ahat A 6 = 0 ↔ (A.filter (· ∈ evenSet)).card = (A.filter (fun a => a ∉ evenSet)).card := by
  rw [Ahat_six_eq_card_sub, sub_eq_zero, Nat.cast_inj]

/-! ### Witnesses. -/

/-- C major triad `{0,4,7}`: even pcs `{0,4}`, odd pc `{7}`, so `a₆ = 2 − 1 = 1`. -/
example : Ahat {0, 4, 7} 6 = 1 := by
  rw [Ahat_six_eq_card_sub,
      show (({0, 4, 7} : Finset (ZMod 12)).filter (· ∈ evenSet)).card = 2 from by decide,
      show (({0, 4, 7} : Finset (ZMod 12)).filter (fun a => a ∉ evenSet)).card = 1 from by decide]
  norm_num

/-- Whole-tone scale `{0,2,4,6,8,10}` is all-even, maximally imbalanced: `a₆ = 6`. -/
example : Ahat {0, 2, 4, 6, 8, 10} 6 = 6 := by
  rw [Ahat_six_eq_card_sub,
      show (({0, 2, 4, 6, 8, 10} : Finset (ZMod 12)).filter (· ∈ evenSet)).card = 6 from by decide,
      show (({0, 2, 4, 6, 8, 10} : Finset (ZMod 12)).filter (fun a => a ∉ evenSet)).card = 0
        from by decide]
  norm_num

/-- The diatonic scale `{0,2,4,5,7,9,11}` (3 even `{0,2,4}`, 4 odd) has `a₆ = −1 ≠ 0`. -/
example : Ahat {0, 2, 4, 5, 7, 9, 11} 6 = -1 := by
  rw [Ahat_six_eq_card_sub,
      show (({0, 2, 4, 5, 7, 9, 11} : Finset (ZMod 12)).filter (· ∈ evenSet)).card = 3 from by decide,
      show (({0, 2, 4, 5, 7, 9, 11} : Finset (ZMod 12)).filter (fun a => a ∉ evenSet)).card = 4
        from by decide]
  norm_num

/-- A parity-balanced set, the chromatic tetrachord `{0,1,2,3}` (even `{0,2}`, odd `{1,3}`),
    has `a₆ = 0` — the characterization in action. -/
example : Ahat ({0, 1, 2, 3} : Finset (ZMod 12)) 6 = 0 := by
  rw [Ahat_six_eq_zero_iff]; decide

/-! ### Part 3 — the general `ZMod (2*m)` case: the order-2 element `m` reads parity.

Frequency `m` of `ZMod (2*m)` is the unique element of order 2 (`2·m = 0`); its character value
`stdAddChar(−(a·m)) = (−1)^a` is the parity sign, so the `m`-th DFT coefficient of a pc-set over
`ℤ_{2m}` is again the even−odd imbalance `Σ_{a∈A} (−1)^a`. (The `ℤ₁₂` case above is `m = 6`.) -/

section General

/-- General 0/1 indicator on `ZMod N`. -/
noncomputable def indN {N : ℕ} (A : Finset (ZMod N)) : ZMod N → ℂ := fun j => if j ∈ A then 1 else 0

/-- `𝓕 (indN A) t = Σ_{a∈A} stdAddChar(−(a·t))` (the indicator collapses the sum to `A`). -/
lemma dftN_apply {N : ℕ} [NeZero N] (A : Finset (ZMod N)) (t : ZMod N) :
    𝓕 (indN A) t = ∑ a ∈ A, stdAddChar (-(a * t)) := by
  unfold indN
  rw [dft_apply]
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]

/-- The order-2 element `m` has character value `−1`: `stdAddChar (m : ZMod (2m)) = exp(πi) = −1`. -/
lemma stdAddChar_half {m : ℕ} [NeZero (2 * m)] :
    stdAddChar ((m : ℕ) : ZMod (2 * m)) = (-1 : ℂ) := by
  have h2m : 2 * m ≠ 0 := NeZero.ne (2 * m)
  have hm0 : ((m : ℕ) : ℂ) ≠ 0 := by
    have : m ≠ 0 := by omega
    exact_mod_cast this
  have hcast : ((m : ℕ) : ZMod (2 * m)) = ((m : ℤ) : ZMod (2 * m)) := by push_cast; ring
  rw [hcast, stdAddChar_coe,
      show (2 * Real.pi * Complex.I * ((m : ℤ) : ℂ) / ((2 * m : ℕ) : ℂ)) = Real.pi * Complex.I from by
        push_cast; field_simp,
      Complex.exp_pi_mul_I]

/-- The order-2 element is its own negative: `−(a·m) = a·m` in `ZMod (2m)`. -/
lemma neg_mul_half {m : ℕ} (a : ZMod (2 * m)) :
    -(a * ((m : ℕ) : ZMod (2 * m))) = a * ((m : ℕ) : ZMod (2 * m)) := by
  rw [← mul_neg]
  congr 1
  have h2 : ((m : ℕ) : ZMod (2 * m)) + ((m : ℕ) : ZMod (2 * m)) = 0 := by
    rw [← Nat.cast_add, ← two_mul, ZMod.natCast_self]
  exact (eq_neg_of_add_eq_zero_left h2).symm

/-- **FC-K, general `ZMod (2m)`.** The `m`-th DFT coefficient (the half-cycle / order-2 frequency) of
    a pc-set over `ℤ_{2m}` is the even−odd parity imbalance `Σ_{a∈A} (−1)^a`. The `ℤ₁₂` headline
    `Ahat_six_eq_sum_neg_one_pow` is the case `m = 6`. -/
theorem dftN_half_eq_sum_neg_one_pow {m : ℕ} [NeZero (2 * m)] (A : Finset (ZMod (2 * m))) :
    𝓕 (indN A) ((m : ℕ) : ZMod (2 * m)) = ∑ a ∈ A, ((-1 : ℂ)) ^ a.val := by
  rw [dftN_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [neg_mul_half a]
  have hsmul : a.val • ((m : ℕ) : ZMod (2 * m)) = a * ((m : ℕ) : ZMod (2 * m)) := by
    rw [nsmul_eq_mul, ZMod.natCast_rightInverse a]
  rw [← hsmul, map_nsmul_eq_pow, stdAddChar_half]

end General

end ParityA6

end MusicTheory
