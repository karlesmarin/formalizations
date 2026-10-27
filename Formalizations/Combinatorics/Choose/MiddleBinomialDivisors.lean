/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Divisors of the middle binomial coefficient (Pomerance)

C. Pomerance, *Divisors of the middle binomial coefficient*, Amer. Math. Monthly 122 (2015) 636–644,
studies when `n + k` divides `C(2n, n)`; for `k = 1` it always does (Catalan numbers). Everything
here comes from Kummer's theorem (`padicValNat_choose`: the `p`-adic valuation of a binomial
coefficient counts the carries of the addition in base `p`).

* Theorem 1 of the paper: for every integer `k ≠ 1`, `n + k ∤ C(2n, n)` for infinitely many `n`.
* The key inequality (4) in the proof of Theorem 2: for a prime `p ≥ 2k`,
  `v_p(n + k) ≤ v_p(C(2n, n))` (for `k = 1` this is the integrality of the Catalan numbers).
* The construction behind the first half of Theorem 3, left to the reader in the paper: if `p < q`
  are primes with `k < p` and `3p/2 < q < 2p`, then `pq ∣ C(2n, n)` for `n = pq + k`.

## Main results

* `MiddleBinomial.infinite_not_dvd_centralBinom`: for k != 1, infinitely many n with n + k not dividing C(2n, n) (Theorem 1)
* `MiddleBinomial.padicValNat_add_le`: v_p(n + k) <= v_p(C(2n, n)) for primes p >= 2k (inequality (4))
* `MiddleBinomial.mul_dvd_centralBinom`: pq divides C(2n, n) for n = pq + k, k < p, 3p/2 < q < 2p
* `MiddleBinomial.sub_dvd_centralBinom_of_primes`: hence n - k divides C(2n, n) for n = pq + k (Theorem 3, first half, for one pair)

## References

* C. Pomerance, Divisors of the middle binomial coefficient, Amer. Math. Monthly 122 (2015) 636–644,
  doi:10.4169/amer.math.monthly.122.7.636.
-/

@[expose] public section

namespace MiddleBinomial

open Nat

/-- Kummer for the central binomial coefficient. -/
private lemma central_val {p : ℕ} [Fact p.Prime] (n b : ℕ) (hb : Nat.log p (2 * n) < b) :
    padicValNat p (centralBinom n) =
      (Finset.filter (fun i => p ^ i ≤ 2 * (n % p ^ i)) (Finset.Ico 1 b)).card := by
  rw [Nat.centralBinom_eq_two_mul_choose, padicValNat_choose (by omega) hb]
  have h : 2 * n - n = n := by omega
  rw [h]
  congr 1
  apply Finset.filter_congr
  intro i _
  omega

/-- A carry at an index `i ≥ 1` forces `r ∣ C(2n, n)`. -/
private lemma dvd_centralBinom_of_carry {r : ℕ} (hr : r.Prime) (n i : ℕ) (hi : 1 ≤ i)
    (h : r ^ i ≤ 2 * (n % r ^ i)) : r ∣ centralBinom n := by
  have : Fact r.Prime := ⟨hr⟩
  apply dvd_of_one_le_padicValNat
  rw [central_val n (max (Nat.log r (2 * n) + 1) (i + 1))
    (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _))]
  apply Finset.card_pos.2
  refine ⟨i, Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨hi, ?_⟩, h⟩⟩
  exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)

/-- **Pomerance, Theorem 1.** For every integer `k ≠ 1` there are infinitely many `n` with
`n + k > 0` and `n + k ∤ C(2n, n)`. -/
theorem infinite_not_dvd_centralBinom (k : ℤ) (hk : k ≠ 1) :
    {n : ℕ | 0 < (n : ℤ) + k ∧ ¬ ((n : ℤ) + k ∣ (centralBinom n : ℤ))}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  rcases (by omega : 2 ≤ k ∨ k ≤ 0) with h2 | h0
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ k)
    have hm : 2 ≤ m := by omega
    set p := m.minFac with hpdef
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have : Fact p.Prime := ⟨hp⟩
    have hpm : p ∣ m := Nat.minFac_dvd m
    set j := N + m + 1 with hj
    have hlt : j < p ^ j :=
      lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_left hp.two_le j)
    have hmle : m ≤ p ^ j := by omega
    have hpj : p ∣ p ^ j := dvd_pow_self p (by omega)
    set n := p ^ j - m with hn
    have hnat : n + m = p ^ j := by omega
    have hpn : p ∣ n := Nat.dvd_sub hpj hpm
    refine ⟨n, ⟨?_, ?_⟩, by omega⟩
    · have : ((n + m : ℕ) : ℤ) = (p ^ j : ℕ) := by rw [hnat]
      push_cast at this
      have : (0 : ℤ) < (p : ℤ) ^ j := by exact_mod_cast pow_pos hp.pos j
      omega
    · intro hdvd
      have h1 : ((n + m : ℕ) : ℤ) = (p ^ j : ℕ) := by rw [hnat]
      have h2 : (((p ^ j : ℕ) : ℤ)) ∣ ((centralBinom n : ℕ) : ℤ) := by
        rw [← h1]; push_cast; exact hdvd
      have h3 : p ^ j ∣ centralBinom n := Int.natCast_dvd_natCast.1 h2
      have h4 := (padicValNat_dvd_iff_le (centralBinom_pos n).ne').1 h3
      have hn0 : n ≠ 0 := by omega
      rw [central_val n (j + 1) (Nat.log_lt_of_lt_pow (by omega) (by
        calc 2 * n < 2 * p ^ j := by omega
          _ ≤ p * p ^ j := Nat.mul_le_mul_right _ hp.two_le
          _ = p ^ (j + 1) := by ring))] at h4
      have hsub : Finset.filter (fun i => p ^ i ≤ 2 * (n % p ^ i)) (Finset.Ico 1 (j + 1)) ⊆
          Finset.Ico 2 (j + 1) := by
        intro i hi
        rw [Finset.mem_filter, Finset.mem_Ico] at hi
        rw [Finset.mem_Ico]
        refine ⟨?_, hi.1.2⟩
        by_contra hcon
        have hi1 : i = 1 := by omega
        subst hi1
        have := hi.2
        rw [pow_one, Nat.mod_eq_zero_of_dvd hpn] at this
        have := hp.pos
        omega
      have := Finset.card_le_card hsub
      simp at this
      omega
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ -k)
    have hk : k = -(m : ℤ) := by omega
    subst hk
    obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (N + 2 * m + 3)
    have : Fact p.Prime := ⟨hp⟩
    refine ⟨p + m, ⟨by omega, ?_⟩, by omega⟩
    intro hdvd
    have h2 : p ∣ centralBinom (p + m) := by
      have : ((p + m : ℕ) : ℤ) + -(m : ℤ) = (p : ℤ) := by push_cast; ring
      rw [this] at hdvd
      exact Int.natCast_dvd_natCast.1 hdvd
    have h4 := one_le_padicValNat_of_dvd (centralBinom_pos (p + m)).ne' h2
    have hlog : Nat.log p (2 * (p + m)) < 2 :=
      Nat.log_lt_of_lt_pow (by omega) (by nlinarith [hp.two_le])
    rw [central_val (p + m) 2 hlog] at h4
    have hem : Finset.filter (fun i => p ^ i ≤ 2 * ((p + m) % p ^ i)) (Finset.Ico 1 2) = ∅ := by
      apply Finset.filter_eq_empty_iff.2
      intro i hi
      rw [Finset.mem_Ico] at hi
      have hi1 : i = 1 := by omega
      subst hi1
      rw [pow_one, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hem] at h4
    simp at h4

/-- **Pomerance, inequality (4).** For a prime `p ≥ 2k` with `k ≥ 1`, the power of `p` in `n + k`
divides `C(2n, n)`. -/
theorem padicValNat_add_le {p k : ℕ} [Fact p.Prime] (hk : 1 ≤ k) (hp : 2 * k ≤ p) (n : ℕ) :
    padicValNat p (n + k) ≤ padicValNat p (centralBinom n) := by
  have hp1 : p.Prime := Fact.out
  set j := padicValNat p (n + k) with hj
  rw [central_val n (max (Nat.log p (2 * n) + 1) (j + 1))
    (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _))]
  calc j = (Finset.Ico 1 (j + 1)).card := by simp
    _ ≤ _ := by
      apply Finset.card_le_card
      intro i hi
      rw [Finset.mem_Ico] at hi
      rw [Finset.mem_filter, Finset.mem_Ico]
      refine ⟨⟨hi.1, lt_of_lt_of_le hi.2 (le_max_right _ _)⟩, ?_⟩
      have hdvd : p ^ i ∣ n + k :=
        (pow_dvd_pow p (by omega : i ≤ j)).trans pow_padicValNat_dvd
      obtain ⟨m, hm⟩ := hdvd
      have hP : p ≤ p ^ i := Nat.le_self_pow (by omega) p
      have hm0 : m ≠ 0 := by
        rintro rfl
        omega
      obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
      have hn : n = (p ^ i - k) + p ^ i * m' := by
        rw [Nat.mul_succ] at hm
        omega
      have hmod : n % p ^ i = p ^ i - k := by
        rw [hn, Nat.add_mul_mod_self_left]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hmod]
      omega

/-- The construction behind **Pomerance, Theorem 3** (first half): for primes `p < q` with `k < p`
and `3p/2 < q < 2p`, the product `pq` divides `C(2n, n)` for `n = pq + k`. -/
theorem mul_dvd_centralBinom {p q k : ℕ} (hp : p.Prime) (hq : q.Prime) (hkp : k < p)
    (h₁ : 3 * p < 2 * q) (h₂ : q < 2 * p) : p * q ∣ centralBinom (p * q + k) := by
  have hpq : p < q := by omega
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 (by omega)
  apply hcop.mul_dvd_of_dvd_of_dvd
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hpq
    have hd : d + 1 ≤ p := by omega
    have hd2 : p < 2 * (d + 1) := by omega
    apply dvd_centralBinom_of_carry hp _ 2 (by norm_num)
    have : (p * (p + d + 1) + k) % p ^ 2 = (d + 1) * p + k := by
      have e : p * (p + d + 1) + k = ((d + 1) * p + k) + p ^ 2 * 1 := by ring
      rw [e, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by nlinarith)
    rw [this]
    nlinarith
  · apply dvd_centralBinom_of_carry hq _ 2 (by norm_num)
    have hlt : p * q + k < q ^ 2 := by nlinarith
    rw [Nat.mod_eq_of_lt hlt]
    nlinarith

/-- The same in the paper's form: `n - k ∣ C(2n, n)` for `n = pq + k`. -/
theorem sub_dvd_centralBinom_of_primes {p q k : ℕ} (hp : p.Prime) (hq : q.Prime) (hkp : k < p)
    (h₁ : 3 * p < 2 * q) (h₂ : q < 2 * p) :
    (p * q + k) - k ∣ centralBinom (p * q + k) := by
  rw [Nat.add_sub_cancel]
  exact mul_dvd_centralBinom hp hq hkp h₁ h₂

end MiddleBinomial
