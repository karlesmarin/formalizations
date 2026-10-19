/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# Odd powers of `2` equal to `1` and even powers equal to `−1` modulo `p`

Let `p ≥ 5` be prime and `t` the order of `2` in `ZMod p`. There is an odd `j ≤ p − 4` with
`2^j = 1`, or an even `j ≤ p − 3` with `2^j = −1`, iff `t ≢ 2 (mod 4)`.

## Main results

* `ConjeturaC.euler_n3`: the equivalence above.
-/

@[expose] public section

namespace ConjeturaC

variable {p : ℕ} [hp : Fact p.Prime]

theorem natCast_ne_zero_of_lt {k : ℕ} (hk0 : 0 < k) (hk : k < p) : (k : ZMod p) ≠ 0 := by
  intro h
  have := Nat.le_of_dvd hk0 ((ZMod.natCast_eq_zero_iff k p).1 h)
  omega

theorem euler_n3 (h5 : 5 ≤ p) :
    ((∃ j, Odd j ∧ j ≤ p - 4 ∧ (2 : ZMod p) ^ j = 1) ∨
      (∃ j, Even j ∧ j ≤ p - 3 ∧ (2 : ZMod p) ^ j = -1)) ↔
      ¬ (orderOf (2 : ZMod p) % 4 = 2) := by
  set t := orderOf (2 : ZMod p) with ht
  -- basic facts in ZMod p
  have h2 : (2 : ZMod p) ≠ 0 := by
    have := natCast_ne_zero_of_lt (p := p) (k := 2) (by norm_num) (by omega)
    simpa using this
  have hneg : (-1 : ZMod p) ≠ 1 := haveI : Fact (2 < p) := ⟨by omega⟩; ZMod.neg_one_ne_one
  have hdvd : t ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one h2
  have hpodd : p % 2 = 1 := hp.out.eq_two_or_odd.resolve_left (by omega)
  have ht0 : t ≠ 0 := by
    intro h0; rw [h0, zero_dvd_iff] at hdvd; omega
  have ht1 : t ≠ 1 := by
    intro h1
    rw [ht, orderOf_eq_one_iff] at h1
    exact one_ne_zero (by linear_combination h1 : (1 : ZMod p) = 0)
  have ht2 : t ≠ 2 := by
    intro h2'
    have h4 : (2 : ZMod p) ^ 2 = 1 := by rw [← h2']; exact pow_orderOf_eq_one 2
    exact natCast_ne_zero_of_lt (p := p) (k := 3) (by norm_num) (by omega)
      (by push_cast; linear_combination h4)
  obtain ⟨k, hk⟩ := hdvd
  constructor
  · rintro (⟨j, hj, -, hj1⟩ | ⟨j, hj, -, hj1⟩)
    · -- t ∣ j with j odd ⇒ t odd
      obtain ⟨c, hc⟩ := orderOf_dvd_of_pow_eq_one hj1
      obtain ⟨r, hr⟩ := hj
      intro hmod
      have : t % 2 = 0 := by omega
      have : j % 2 = 0 := by rw [hc, Nat.mul_mod, this]; simp
      omega
    · -- 2^(2j) = 1, 2^j ≠ 1
      have h2j : (2 : ZMod p) ^ (2 * j) = 1 := by
        rw [mul_comm, pow_mul, hj1]; norm_num
      obtain ⟨c, hc⟩ := orderOf_dvd_of_pow_eq_one h2j
      have hnd : ¬ t ∣ j := by
        intro hd
        exact hneg (hj1 ▸ (orderOf_dvd_iff_pow_eq_one.1 hd))
      intro hmod
      -- t = 2u, u odd; 2j = 2u c ⇒ j = u c; j even, u odd ⇒ c even ⇒ t ∣ j
      obtain ⟨u, hu⟩ : ∃ u, t = 2 * u := ⟨t / 2, by omega⟩
      have hu2 : u % 2 = 1 := by omega
      have hc' : 2 * j = t * c := hc
      have hjc : j = u * c := by
        rw [hu, mul_assoc] at hc'
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) hc'
      obtain ⟨r, hr⟩ := hj
      have hc2 : c % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one c with h | h
        · exact h
        · exfalso
          have : (u * c) % 2 = 1 := by rw [Nat.mul_mod, hu2, h]
          omega
      apply hnd
      obtain ⟨d, hd⟩ : ∃ d, c = 2 * d := ⟨c / 2, by omega⟩
      exact ⟨d, by rw [hjc, hd, hu]; ring⟩
  · intro hmod
    rcases Nat.mod_two_eq_zero_or_one t with he | ho
    · -- t ≡ 0 mod 4: j = t/2
      right
      obtain ⟨u, hu⟩ : ∃ u, t = 2 * u := ⟨t / 2, by omega⟩
      have hsq : ((2 : ZMod p) ^ u) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm, ← hu, ht]; exact pow_orderOf_eq_one 2
      have hne1 : (2 : ZMod p) ^ u ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
      have hk1 : 1 ≤ k := by
        rcases k with _ | k
        · simp at hk; omega
        · omega
      have hle : t ≤ p - 1 := by rw [hk]; exact Nat.le_mul_of_pos_right t hk1
      refine ⟨u, ⟨u / 2, by omega⟩, by omega, ?_⟩
      exact (sq_eq_one_iff.mp hsq).resolve_left hne1
    · -- t odd: j = t
      left
      have hk2 : 2 ≤ k := by
        rcases k with _ | _ | k
        · simp at hk; omega
        · simp at hk; omega
        · omega
      have hle : 2 * t ≤ p - 1 := by rw [hk, mul_comm 2]; exact Nat.mul_le_mul_left t hk2
      refine ⟨t, ⟨t / 2, by omega⟩, by omega, ?_⟩
      rw [ht]; exact pow_orderOf_eq_one 2

end ConjeturaC
