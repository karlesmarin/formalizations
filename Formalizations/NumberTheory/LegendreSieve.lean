/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.Primorial

/-!
# The Eratosthenes–Legendre sieve

For `P ≠ 0`, the number of `n ∈ [1, x]` coprime to `P` is `Σ_{d ∣ P} μ(d) ⌊x/d⌋`
(inclusion–exclusion by Möbius inversion; `P` need not be squarefree). With `P` the primorial of
`⌊√x⌋`, the integers in `[1, x]` with no prime factor `≤ √x` are `1` and the primes in `(√x, x]`,
which gives Legendre's formula `π(x) - π(√x) + 1 = Σ_{d ∣ P(√x)} μ(d) ⌊x/d⌋` for `x ≥ 1`.

## Main results

* `LegendreSieve.card_coprime_eq_sum_moebius`: integers in [1, x] coprime to P counted by sum of mu(d) floor(x/d)
* `LegendreSieve.primeCounting_sub_add_one`: pi(x) - pi(sqrt x) + 1 = sum over d | primorial(sqrt x) of mu(d) floor(x/d)

## References

* A.-M. Legendre, *Essai sur la théorie des nombres*, Paris, 1798 (2nd ed. 1808).
-/

@[expose] public section

open Finset

namespace LegendreSieve

/-- Möbius inversion: `Σ_{d ∣ n} μ d = [n = 1]`. -/
lemma sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, ArithmeticFunction.moebius d = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n)
    (ArithmeticFunction.moebius_mul_coe_zeta)
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact h

/-- **Exact sieve.** For `P ≠ 0`, the integers in `[1, x]` coprime to `P` are counted by
inclusion–exclusion: `Σ_{d ∣ P} μ(d) ⌊x/d⌋`. -/
theorem card_coprime_eq_sum_moebius (x P : ℕ) (hP : P ≠ 0) :
    (((Ioc 0 x).filter (fun n => Nat.Coprime n P)).card : ℤ) =
      ∑ d ∈ P.divisors, ArithmeticFunction.moebius d * ((x / d : ℕ) : ℤ) := by
  have h1 : ∀ d, ((x / d : ℕ) : ℤ) = ∑ n ∈ Ioc 0 x, if d ∣ n then 1 else 0 := by
    intro d
    rw [← Nat.Ioc_filter_dvd_card_eq_div, Finset.sum_boole]
  simp_rw [h1, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have key : ∑ d ∈ P.divisors, ArithmeticFunction.moebius d * (if d ∣ n then (1 : ℤ) else 0)
      = ∑ d ∈ (Nat.gcd n P).divisors, ArithmeticFunction.moebius d := by
    have e1 : P.divisors.filter (fun d => d ∣ n) = (Nat.gcd n P).divisors := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      have : Nat.gcd n P ≠ 0 := Nat.gcd_ne_zero_right hP
      tauto
    rw [← e1, Finset.sum_filter]
    exact Finset.sum_congr rfl fun d _ => by split_ifs <;> simp
  rw [key, sum_moebius_divisors]
  simp [Nat.Coprime]

/-- Coprime to the primorial iff no prime factor `≤ z`. -/
lemma coprime_primorial_iff (n z : ℕ) :
    Nat.Coprime n (primorial z) ↔ ∀ p, p.Prime → p ≤ z → ¬ p ∣ n := by
  rw [Nat.coprime_comm, primorial, Nat.coprime_prod_left_iff]
  simp only [Finset.mem_filter, Finset.mem_range, and_imp]
  refine forall_congr' fun p => ?_
  constructor
  · intro h hp hz
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 (h (by omega) hp)
  · intro h hlt hp
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 (h hp (by omega))

/-- The sifted set is `{1} ∪ {primes in (z, x]}`. -/
lemma sifted_eq (x : ℕ) (hx : 1 ≤ x) :
    (Ioc 0 x).filter (fun n => Nat.Coprime n (primorial (Nat.sqrt x))) =
      insert 1 ((Ioc (Nat.sqrt x) x).filter Nat.Prime) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_insert, coprime_primorial_iff]
  constructor
  · rintro ⟨⟨hn0, hnx⟩, h⟩
    by_cases hn1 : n = 1
    · exact Or.inl hn1
    · right
      have hp : n.Prime := by
        by_contra hnp
        have hsq := Nat.minFac_sq_le_self hn0 hnp
        have hm : (Nat.minFac n).Prime := Nat.minFac_prime hn1
        have hle : Nat.minFac n ≤ Nat.sqrt x := by
          rw [Nat.le_sqrt']; exact hsq.trans hnx
        exact h _ hm hle (Nat.minFac_dvd n)
      refine ⟨⟨?_, hnx⟩, hp⟩
      by_contra hle
      exact h n hp (by omega) dvd_rfl
  · rintro (rfl | ⟨⟨hz, hnx⟩, hp⟩)
    · refine ⟨⟨by norm_num, hx⟩, fun p hp _ hd => ?_⟩
      exact hp.one_lt.ne' (Nat.dvd_one.1 hd)
    · refine ⟨⟨hp.pos, hnx⟩, fun q hq hqz hd => ?_⟩
      have := (Nat.prime_dvd_prime_iff_eq hq hp).1 hd
      omega

/-- **Legendre's sieve.** For `x ≥ 1`,
`π(x) - π(⌊√x⌋) + 1 = Σ_{d ∣ P(⌊√x⌋)} μ(d) ⌊x/d⌋`. -/
theorem primeCounting_sub_add_one (x : ℕ) (hx : 1 ≤ x) :
    ((Nat.primeCounting x - Nat.primeCounting (Nat.sqrt x) + 1 : ℕ) : ℤ) =
      ∑ d ∈ (primorial (Nat.sqrt x)).divisors,
        ArithmeticFunction.moebius d * ((x / d : ℕ) : ℤ) := by
  rw [← card_coprime_eq_sum_moebius x _ (primorial_ne_zero _), sifted_eq x hx]
  have hz : Nat.sqrt x ≤ x := Nat.sqrt_le_self x
  have hsub : (Ioc (Nat.sqrt x) x).filter Nat.Prime =
      (range (x + 1)).filter Nat.Prime \ (range (Nat.sqrt x + 1)).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff, Finset.mem_range]
    by_cases hp : p.Prime <;> simp [hp]; omega
  have hcard : ((Ioc (Nat.sqrt x) x).filter Nat.Prime).card =
      Nat.primeCounting x - Nat.primeCounting (Nat.sqrt x) := by
    rw [hsub, Finset.card_sdiff_of_subset]
    · simp [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    · intro p
      simp only [Finset.mem_filter, Finset.mem_range]
      intro h
      exact ⟨by omega, h.2⟩
  rw [Finset.card_insert_of_notMem, hcard]
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  rintro ⟨⟨hz1, _⟩, _⟩
  have : 1 ≤ Nat.sqrt x := Nat.sqrt_pos.2 hx
  omega

end LegendreSieve
