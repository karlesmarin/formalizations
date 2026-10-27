/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Combinatorics.Derangements.Finite
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.Data.ZMod.Basic

/-!
# Catalan, central binomial and derangement numbers at primes

For every prime `p`: `C(2p, p) ≡ 2`, `Catalan(p) ≡ 2` and the number of derangements
`D(p) ≡ -1 (mod p)`. The first follows from Vandermonde's identity `C(2p, p) = Σ C(p, i)²` and
`p ∣ C(p, i)` for `0 < i < p`; the second from `(p + 1) Catalan(p) = C(2p, p)`; the third from the
recurrence of `numDerangements` (`p = 2` checked directly, odd `p` by parity).

## Main results

* `PrimeCongruences.centralBinom_prime`: C(2p, p) = 2 in ZMod p
* `PrimeCongruences.catalan_prime`: Catalan(p) = 2 in ZMod p
* `PrimeCongruences.numDerangements_prime`: D(p) = -1 in ZMod p

## References

* Classical congruences; found missing from Mathlib by excovery.identidades_mathlib (28-oct-2026).
-/

@[expose] public section

namespace PrimeCongruences

/-- The central binomial coefficient `C(2p, p)` is `≡ 2 (mod p)` for a prime `p`. -/
theorem centralBinom_prime (p : ℕ) [hp : Fact p.Prime] :
    (Nat.centralBinom p : ZMod p) = 2 := by
  have h1 : Nat.centralBinom p = ∑ i ∈ Finset.range (p + 1), (p.choose i) ^ 2 := by
    rw [Nat.centralBinom_eq_two_mul_choose, Nat.sum_range_choose_sq]
  have h2 : ∑ i ∈ Finset.range (p + 1), ((p.choose i : ℕ) : ZMod p) ^ 2 = 1 + 1 := by
    rw [Finset.sum_eq_add_of_mem 0 p (by simp) (by simp) hp.out.ne_zero.symm]
    · simp
    · intro c hc hne
      have hc' : c < p + 1 := Finset.mem_range.mp hc
      have hlt : c < p := by lia
      have hpos : 0 < c := Nat.pos_of_ne_zero hne.1
      have : (p.choose c : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.Prime.dvd_choose_self hp.out hpos.ne' hlt)
      simp [this]
  rw [h1]; push_cast; rw [h2]; norm_num

/-- `Catalan(p) ≡ 2 (mod p)` for a prime `p`. -/
theorem catalan_prime (p : ℕ) [hp : Fact p.Prime] : (catalan p : ZMod p) = 2 := by
  have h := congrArg (fun n : ℕ => (n : ZMod p)) (succ_mul_catalan_eq_centralBinom p)
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add, one_mul] at h
  rw [h, centralBinom_prime]

/-- The number of derangements satisfies `D(p) ≡ -1 (mod p)` for a prime `p`. -/
theorem numDerangements_prime (p : ℕ) [hp : Fact p.Prime] :
    ((numDerangements p : ℤ) : ZMod p) = -1 := by
  rcases hp.out.eq_two_or_odd' with rfl | hodd
  · decide
  · obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.out.pos; lia⟩
    have h := congrArg (fun n : ℤ => (n : ZMod p)) (numDerangements_succ m)
    have hev : Even m := by rcases hodd with ⟨k, hk⟩; exact ⟨k, by lia⟩
    subst hm
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_natCast, Int.cast_one,
      hev.neg_one_pow] at h
    have hz : ((m : ZMod (m + 1)) + 1) = 0 := by exact_mod_cast ZMod.natCast_self (m + 1)
    rw [Int.cast_natCast, h, hz]; simp

end PrimeCongruences
