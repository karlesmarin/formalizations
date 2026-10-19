/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.Ring

/-!
# The shift rule for the Fermat quotient

For the Fermat quotient `q(l) = (l^(p−1) − 1)/p`:
`(l + p t)^(p−1) ≡ l^(p−1) − p t l^(p−2) (mod p²)`, hence `q(l + p t) ≡ q(l) − t / l (mod p)`.
The binomial step is Mathlib's `sq_dvd_add_pow_sub_sub`.

## Main results

* `ConjeturaC.sq_dvd_shift`, `ConjeturaC.pow_shift_zmod_sq`: the congruence modulo `p²`.
* `ConjeturaC.fermatQuot_shift`: `q(l + p t) ≡ q(l) − t l⁻¹ (mod p)` for `p ∤ l`.
-/

@[expose] public section

namespace ConjeturaC

/-- Fermat quotient (integer division; exact when `p` is prime and `p ∤ l`). -/
def fermatQuot (p : ℕ) (l : ℤ) : ℤ := (l ^ (p - 1) - 1) / p

/-- `p² ∣ (l + p t)^(p-1) - (l^(p-1) - p t l^(p-2))`, for any `p ≥ 1`. -/
theorem sq_dvd_shift {p : ℕ} (hp : 1 ≤ p) (l t : ℤ) :
    (p : ℤ) ^ 2 ∣ (l + p * t) ^ (p - 1) - (l ^ (p - 1) - p * t * l ^ (p - 2)) := by
  have h := sq_dvd_add_pow_sub_sub ((p : ℤ) * t) l (p - 1)
  have h2 : (p : ℤ) ^ 2 ∣ ((p : ℤ) * t) ^ 2 := ⟨t ^ 2, by ring⟩
  have hc : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by push_cast [Nat.cast_sub hp]; ring
  have he : p - 1 - 1 = p - 2 := by omega
  rw [he, hc] at h
  have key : (l + p * t) ^ (p - 1) - (l ^ (p - 1) - p * t * l ^ (p - 2)) =
      ((l + p * t) ^ (p - 1) - l ^ (p - 2) * (p * t) * ((p : ℤ) - 1) - l ^ (p - 1)) +
        (p : ℤ) ^ 2 * (t * l ^ (p - 2)) := by ring
  rw [key]
  exact dvd_add (h2.trans h) (dvd_mul_right _ _)

/-- Same statement as an identity in `ZMod (p^2)`. -/
theorem pow_shift_zmod_sq {p : ℕ} (hp : 1 ≤ p) (l t : ℤ) :
    ((l : ZMod (p ^ 2)) + p * t) ^ (p - 1) = (l : ZMod (p ^ 2)) ^ (p - 1) - p * t * l ^ (p - 2) := by
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ 2)).2 (by exact_mod_cast sq_dvd_shift hp l t)
  push_cast at h
  exact sub_eq_zero.1 h

variable {p : ℕ} [hp : Fact p.Prime]

theorem mul_fermatQuot {l : ℤ} (hl : ¬ (p : ℤ) ∣ l) :
    (p : ℤ) * fermatQuot p l = l ^ (p - 1) - 1 := by
  have hd : (p : ℤ) ∣ l ^ (p - 1) - 1 := by
    have h1 : ((l ^ (p - 1) - 1 : ℤ) : ZMod p) = 0 := by
      have hl' : (l : ZMod p) ≠ 0 := fun h => hl ((ZMod.intCast_zmod_eq_zero_iff_dvd l p).1 h)
      push_cast
      rw [ZMod.pow_card_sub_one_eq_one hl', sub_self]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h1
  exact Int.mul_ediv_cancel' hd

/-- Shift rule: `q(l + p t) ≡ q(l) - t · l⁻¹ (mod p)`. -/
theorem fermatQuot_shift {l : ℤ} (t : ℤ) (hl : ¬ (p : ℤ) ∣ l) :
    (fermatQuot p (l + p * t) : ZMod p) = (fermatQuot p l : ZMod p) - (t : ZMod p) * (l : ZMod p)⁻¹ := by
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hl2 : ¬ (p : ℤ) ∣ l + p * t := by
    intro h; exact hl (by simpa using dvd_sub h (dvd_mul_right (p : ℤ) t))
  have hA := mul_fermatQuot (p := p) hl2
  have hB := mul_fermatQuot (p := p) hl
  have hS := sq_dvd_shift hp1 l t
  -- p² ∣ p * (A - B + t l^(p-2))  ⇒  p ∣ A - B + t l^(p-2)
  have hdiv : (p : ℤ) ∣ fermatQuot p (l + p * t) - fermatQuot p l + t * l ^ (p - 2) := by
    have : (p : ℤ) * (fermatQuot p (l + p * t) - fermatQuot p l + t * l ^ (p - 2)) =
        (l + p * t) ^ (p - 1) - (l ^ (p - 1) - p * t * l ^ (p - 2)) := by
      linear_combination hA - hB
    rw [← this, pow_two] at hS
    exact (mul_dvd_mul_iff_left hp0).1 hS
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hdiv
  push_cast at hz
  have hl' : (l : ZMod p) ≠ 0 := fun h => hl ((ZMod.intCast_zmod_eq_zero_iff_dvd l p).1 h)
  have hinv : (l : ZMod p) ^ (p - 2) = (l : ZMod p)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← pow_succ', show p - 2 + 1 = p - 1 by have := hp.out.two_le; omega]
    exact ZMod.pow_card_sub_one_eq_one hl'
  rw [hinv] at hz
  linear_combination hz

end ConjeturaC
