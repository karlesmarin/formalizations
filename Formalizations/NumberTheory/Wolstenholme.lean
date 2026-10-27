/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# Wolstenholme's theorem

For a prime `p ≥ 5`: the harmonic sum `Σ_{k=1}^{p-1} 1/k` vanishes in `ZMod (p²)`, and
`C(2p - 1, p - 1) ≡ 1 (mod p³)`, `C(2p, p) ≡ 2 (mod p³)` (Wolstenholme, 1862). The harmonic lemma
pairs `k` with `p - k`, giving `2H = -p Σ 1/k²`, and `Σ 1/k² ≡ Σ k² ≡ 0 (mod p)` because inversion
permutes the units of `ZMod p`. For the binomial, `(p - 1)! · C(2p - 1, p - 1) = Π (p + k)` is
expanded in `ZMod (p³)` as `(p - 1)! (1 + pS + p²(S² - Q)/2)` with `S ≡ 0 (mod p²)` and
`Q ≡ 0 (mod p)`.

## Main results

* `Wolstenholme.harmonic_sum_eq_zero`: sum of 1/k for k < p vanishes in ZMod (p^2), p >= 5 prime
* `Wolstenholme.choose_modEq`: C(2p-1, p-1) = 1 and C(2p, p) = 2 mod p^3 for primes p >= 5

## References

* J. Wolstenholme, *On certain properties of prime numbers*, Quart. J. Pure Appl. Math. 5 (1862), 35–39.
* The harmonic form (mod p²) is also in facebookresearch/atlas-lean, `MathlibExt.NumberTheory.Wolstenholme.wolstenholme`; the proof here is independent.
-/

@[expose] public section

namespace Wolstenholme

open Finset

private theorem coprime_pow (p k m : ℕ) (hp : p.Prime) (h0 : 0 < k) (hk : k < p) :
    k.Coprime (p ^ m) := by
  have h : ¬ p ∣ k := fun h => by have := Nat.le_of_dvd h0 h; omega
  exact (((Nat.Prime.coprime_iff_not_dvd hp).mpr h).symm).pow_right m

private theorem mul_eq_zero_of_castHom (m n c : ℕ) [NeZero n] (hmn : m ∣ n) (hc : n ∣ m * c)
    (x : ZMod n) (hx : ZMod.castHom hmn (ZMod m) x = 0) : (c : ZMod n) * x = 0 := by
  have h1 : ((x.val : ℕ) : ZMod n) = x := ZMod.natCast_zmod_val x
  have h2 : ((x.val : ℕ) : ZMod m) = 0 := by
    have h := map_natCast (ZMod.castHom hmn (ZMod m)) x.val
    rw [h1, hx] at h
    exact h.symm
  obtain ⟨t, ht⟩ := (ZMod.natCast_eq_zero_iff _ _).mp h2
  have h3 : (c : ZMod n) * x = ((c * x.val : ℕ) : ZMod n) := by rw [Nat.cast_mul, h1]
  rw [h3, ZMod.natCast_eq_zero_iff]
  obtain ⟨s, hs⟩ := hc
  refine ⟨s * t, ?_⟩
  rw [ht]
  calc c * (m * t) = (m * c) * t := by ring
    _ = n * s * t := by rw [hs]
    _ = n * (s * t) := by ring

private theorem castHom_inv (m n k : ℕ) (hmn : m ∣ n) (hk : k.Coprime n) :
    ZMod.castHom hmn (ZMod m) ((k : ZMod n)⁻¹) = (k : ZMod m)⁻¹ := by
  have hk' : k.Coprime m := hk.coprime_dvd_right hmn
  have h1 := ZMod.coe_mul_inv_eq_one k hk
  have h2 := ZMod.coe_mul_inv_eq_one k hk'
  have h3 := congrArg (ZMod.castHom hmn (ZMod m)) h1
  rw [map_mul, map_one, map_natCast] at h3
  linear_combination (-(ZMod.castHom hmn (ZMod m) ((k : ZMod n)⁻¹))) * h2 + (k : ZMod m)⁻¹ * h3

private theorem pair_inv_add {R : Type*} [CommRing R] (p k u v : R) (hp : p ^ 2 = 0)
    (hu : k * u = 1) (hv : (p - k) * v = 1) : u + v = -(p * u ^ 2) := by
  linear_combination (1 + p * u) * (-u * hv - v * hu) + u ^ 2 * v * hp

private theorem two_mul_prod {R : Type*} [CommRing R] (p : R) (hp : p ^ 3 = 0) (x : ℕ → R)
    (n : ℕ) :
    2 * ∏ i ∈ range n, (1 + p * x i) = 2 + 2 * p * (∑ i ∈ range n, x i)
      + p ^ 2 * ((∑ i ∈ range n, x i) ^ 2 - ∑ i ∈ range n, (x i) ^ 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, sum_range_succ, sum_range_succ]
    linear_combination (1 + p * x n) * ih
      + x n * ((∑ i ∈ range n, x i) ^ 2 - ∑ i ∈ range n, (x i) ^ 2) * hp

private theorem sum_inv_sq_zmodp (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    ∑ i ∈ range (p - 1), ((((i + 1 : ℕ) : ZMod p)⁻¹)) ^ 2 = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hsq : ∑ x : ZMod p, x ^ 2 = 0 :=
    FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) 2 (by rw [ZMod.card]; omega)
  have hinv : ∑ x : ZMod p, (x⁻¹) ^ 2 = ∑ x : ZMod p, x ^ 2 :=
    Equiv.sum_comp (inv_involutive (G := ZMod p)).toPerm (fun x => x ^ 2)
  have hrange : ∀ g : ZMod p → ZMod p,
      ∑ x : ZMod p, g x = ∑ i ∈ range p, g (i : ZMod p) := by
    intro g
    have : NeZero p := ⟨hp.ne_zero⟩
    exact Finset.sum_nbij' (fun x => x.val) (fun n => (n : ZMod p))
      (fun x _ => mem_range.mpr (ZMod.val_lt x)) (fun n _ => mem_univ _)
      (fun x _ => ZMod.natCast_zmod_val x)
      (fun n hn => ZMod.val_natCast_of_lt (mem_range.mp hn))
      (fun x _ => by rw [ZMod.natCast_zmod_val])
  have h := hrange (fun x => (x⁻¹) ^ 2)
  rw [hinv, hsq] at h
  have e : p - 1 + 1 = p := by omega
  have h3 := sum_range_succ' (fun i : ℕ => (((i : ℕ) : ZMod p)⁻¹) ^ 2) (p - 1)
  rw [e, ← h] at h3
  simpa using h3.symm

/-- **Wolstenholme's harmonic lemma.** For a prime `p ≥ 5`, `∑_{k=1}^{p-1} 1/k = 0` in `ℤ/p²`. -/
theorem harmonic_sum_eq_zero (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    ∑ i ∈ range (p - 1), (((i + 1 : ℕ) : ZMod (p ^ 2))⁻¹) = 0 := by
  have : NeZero (p ^ 2) :=⟨(pow_pos hp.pos 2).ne'⟩
  set f : ℕ → ZMod (p ^ 2) := fun j => (((j + 1 : ℕ) : ZMod (p ^ 2))⁻¹) with hf
  have hp2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
    have h0 : ((p ^ 2 : ℕ) : ZMod (p ^ 2)) = 0 := ZMod.natCast_self _
    rwa [Nat.cast_pow] at h0
  have key : ∀ i ∈ range (p - 1),
      f i + f (p - 1 - 1 - i) = -((p : ZMod (p ^ 2)) * (f i) ^ 2) := by
    intro i hi
    have hi' := mem_range.mp hi
    have hu := ZMod.coe_mul_inv_eq_one (n := p ^ 2) (i + 1)
      (coprime_pow p (i + 1) 2 hp (by omega) (by omega))
    have hv := ZMod.coe_mul_inv_eq_one (n := p ^ 2) (p - 1 - 1 - i + 1)
      (coprime_pow p _ 2 hp (by omega) (by omega))
    have e : ((p - 1 - 1 - i + 1 : ℕ) : ZMod (p ^ 2))
        = (p : ZMod (p ^ 2)) - ((i + 1 : ℕ) : ZMod (p ^ 2)) := by
      have : p - 1 - 1 - i + 1 = p - (i + 1) := by omega
      rw [this, Nat.cast_sub (by omega)]
    have hv' : ((p : ZMod (p ^ 2)) - ((i + 1 : ℕ) : ZMod (p ^ 2))) * f (p - 1 - 1 - i) = 1 := by
      rw [← e]
      exact hv
    exact pair_inv_add (p : ZMod (p ^ 2)) _ _ _ hp2 hu hv'
  have hr := sum_range_reflect f (p - 1)
  have h2 : 2 * ∑ i ∈ range (p - 1), f i
      = -((p : ZMod (p ^ 2)) * ∑ i ∈ range (p - 1), (f i) ^ 2) := by
    calc 2 * ∑ i ∈ range (p - 1), f i
        = ∑ i ∈ range (p - 1), (f i + f (p - 1 - 1 - i)) := by
          rw [sum_add_distrib, hr]; ring
      _ = ∑ i ∈ range (p - 1), -((p : ZMod (p ^ 2)) * (f i) ^ 2) := sum_congr rfl key
      _ = _ := by rw [sum_neg_distrib, mul_sum]
  have hdvd : p ∣ p ^ 2 := dvd_pow_self p (by norm_num)
  have hQ : ZMod.castHom hdvd (ZMod p) (∑ i ∈ range (p - 1), (f i) ^ 2) = 0 := by
    rw [map_sum]
    rw [← sum_inv_sq_zmodp p hp h5]
    refine sum_congr rfl (fun i hi => ?_)
    have hi' := mem_range.mp hi
    rw [map_pow, hf]
    simp only
    rw [castHom_inv p (p ^ 2) (i + 1) hdvd (coprime_pow p (i + 1) 2 hp (by omega) (by omega))]
  have hpQ := mul_eq_zero_of_castHom p (p ^ 2) p hdvd (dvd_of_eq (by ring)) _ hQ
  rw [hpQ, neg_zero] at h2
  have hu2 : IsUnit (2 : ZMod (p ^ 2)) := by
    have hc : Nat.Coprime 2 (p ^ 2) := by
      refine Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ?_)
      intro h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h
      omega
    simpa using (ZMod.isUnit_iff_coprime 2 (p ^ 2)).mpr hc
  exact (hu2.mul_right_eq_zero).mp h2

private theorem prod_eq_one (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    ∏ i ∈ range (p - 1), (1 + (p : ZMod (p ^ 3)) * (((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹)) = 1 := by
  have : NeZero (p ^ 3) := ⟨(pow_pos hp.pos 3).ne'⟩
  set u : ℕ → ZMod (p ^ 3) := fun j => (((j + 1 : ℕ) : ZMod (p ^ 3))⁻¹) with hu
  have hp3 : (p : ZMod (p ^ 3)) ^ 3 = 0 := by
    have h0 : ((p ^ 3 : ℕ) : ZMod (p ^ 3)) = 0 := ZMod.natCast_self _
    rwa [Nat.cast_pow] at h0
  have hdvd2 : p ^ 2 ∣ p ^ 3 := pow_dvd_pow p (by norm_num)
  have hdvd1 : p ∣ p ^ 3 := dvd_pow_self p (by norm_num)
  have hS : (p : ZMod (p ^ 3)) * ∑ i ∈ range (p - 1), u i = 0 := by
    refine mul_eq_zero_of_castHom (p ^ 2) (p ^ 3) p hdvd2 (dvd_of_eq (by ring)) _ ?_
    rw [map_sum, ← harmonic_sum_eq_zero p hp h5]
    refine sum_congr rfl (fun i hi => ?_)
    have hi' := mem_range.mp hi
    rw [hu]
    simp only
    rw [castHom_inv (p ^ 2) (p ^ 3) (i + 1) hdvd2
      (coprime_pow p (i + 1) 3 hp (by omega) (by omega))]
  have hQ : ((p ^ 2 : ℕ) : ZMod (p ^ 3)) * ∑ i ∈ range (p - 1), (u i) ^ 2 = 0 := by
    refine mul_eq_zero_of_castHom p (p ^ 3) (p ^ 2) hdvd1 (dvd_of_eq (by ring)) _ ?_
    rw [map_sum, ← sum_inv_sq_zmodp p hp h5]
    refine sum_congr rfl (fun i hi => ?_)
    have hi' := mem_range.mp hi
    rw [map_pow, hu]
    simp only
    rw [castHom_inv p (p ^ 3) (i + 1) hdvd1 (coprime_pow p (i + 1) 3 hp (by omega) (by omega))]
  rw [Nat.cast_pow] at hQ
  have h := two_mul_prod (p : ZMod (p ^ 3)) hp3 u (p - 1)
  have h2 : 2 * ∏ i ∈ range (p - 1), (1 + (p : ZMod (p ^ 3)) * u i) = 2 * 1 := by
    linear_combination h + 2 * hS + ((p : ZMod (p ^ 3)) * ∑ i ∈ range (p - 1), u i) * hS - hQ
  have hu2 : IsUnit (2 : ZMod (p ^ 3)) := by
    have hc : Nat.Coprime 2 (p ^ 3) := by
      refine Nat.Coprime.pow_right 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ?_)
      intro h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h
      omega
    simpa using (ZMod.isUnit_iff_coprime 2 (p ^ 3)).mpr hc
  exact hu2.mul_left_cancel h2

private theorem choose_cast (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    ((Nat.choose (2 * p - 1) (p - 1) : ℕ) : ZMod (p ^ 3)) = 1 := by
  have : NeZero (p ^ 3) := ⟨(pow_pos hp.pos 3).ne'⟩
  have hasc := Nat.ascFactorial_eq_factorial_mul_choose p (p - 1)
  have e : p + (p - 1) = 2 * p - 1 := by omega
  rw [e, Nat.ascFactorial_eq_prod_range] at hasc
  have hasc' := congrArg (fun n : ℕ => (n : ZMod (p ^ 3))) hasc
  simp only [Nat.cast_prod, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hasc'
  have hfac : (((p - 1).factorial : ℕ) : ZMod (p ^ 3))
      = ∏ i ∈ range (p - 1), ((i + 1 : ℕ) : ZMod (p ^ 3)) := by
    rw [← prod_range_add_one_eq_factorial, Nat.cast_prod]
  have hprod : ∏ i ∈ range (p - 1), ((p : ZMod (p ^ 3)) + 1 + (i : ZMod (p ^ 3)))
      = (∏ i ∈ range (p - 1), ((i + 1 : ℕ) : ZMod (p ^ 3)))
        * ∏ i ∈ range (p - 1),
            (1 + (p : ZMod (p ^ 3)) * (((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹)) := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl (fun i hi => ?_)
    have hi' := mem_range.mp hi
    have hu := ZMod.coe_mul_inv_eq_one (n := p ^ 3) (i + 1)
      (coprime_pow p (i + 1) 3 hp (by omega) (by omega))
    push_cast at hu ⊢
    linear_combination (-(p : ZMod (p ^ 3))) * hu
  rw [hprod, prod_eq_one p hp h5, mul_one, ← hfac] at hasc'
  have hunit : IsUnit (((p - 1).factorial : ℕ) : ZMod (p ^ 3)) := by
    rw [ZMod.isUnit_iff_coprime]
    have hnd : ¬ p ∣ (p - 1).factorial := by
      rw [Nat.Prime.dvd_factorial hp]
      omega
    exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd).symm.pow_right 3
  exact hunit.mul_left_cancel (by rw [← hasc', mul_one])

/-- **Wolstenholme's theorem (1862).** For a prime `p ≥ 5`, `C(2p - 1, p - 1) ≡ 1 (mod p³)`;
equivalently `C(2p, p) ≡ 2 (mod p³)`. -/
theorem choose_modEq (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    Nat.choose (2 * p - 1) (p - 1) ≡ 1 [MOD p ^ 3] ∧ Nat.choose (2 * p) p ≡ 2 [MOD p ^ 3] := by
  have h1 : Nat.choose (2 * p - 1) (p - 1) ≡ 1 [MOD p ^ 3] := by
    rw [← ZMod.natCast_eq_natCast_iff, choose_cast p hp h5, Nat.cast_one]
  refine ⟨h1, ?_⟩
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have e1 : 2 * (q + 1) - 1 = 2 * q + 1 := by omega
  have e2 : q + 1 - 1 = q := by omega
  have e3 : 2 * (q + 1) = (2 * q + 1) + 1 := by omega
  rw [e1, e2] at h1
  have h : Nat.choose (2 * (q + 1)) (q + 1) = 2 * Nat.choose (2 * q + 1) q := by
    rw [e3, Nat.choose_succ_succ, Nat.choose_symm_half]
    ring
  rw [h]
  simpa using Nat.ModEq.mul_left 2 h1

end Wolstenholme
