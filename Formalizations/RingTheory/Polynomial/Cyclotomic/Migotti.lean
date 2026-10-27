/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Ring.GeomSum

/-!
# Migotti's theorem on binary cyclotomic polynomials

For distinct primes `p ≠ q`, every coefficient of `Φ_{pq}` is `-1`, `0` or `1` (Migotti, 1883); for
three primes it fails (`Φ_{105}` has a coefficient `-2`). Following Lam–Leung, with
`a p + b q = p q + 1` (`1 ≤ a ≤ q`, `1 ≤ b ≤ p`, from Bézout), `Φ_{pq} = A B - X C D` where
`A, B, C, D` are geometric sums in `X^p` and `X^q`; the identity is checked after multiplying by
`(X^p - 1)(X^q - 1)`, using `(X^p - 1)(X^q - 1) Φ_{pq} = (X - 1)(X^{pq} - 1)` from Mathlib's
`prod_cyclotomic_eq_X_pow_sub_one`. The exponents `ip + jq` in each product are distinct, so its
coefficients are `0` or `1`, and the two supports are disjoint.

## Main results

* `Migotti.coeff_cyclotomic_mul_mem`: coefficients of Phi_pq are -1, 0 or 1 for distinct primes p, q

## References

* A. Migotti, *Zur Theorie der Kreisteilungsgleichung*, Sitzungsber. Akad. Wiss. Wien 87 (1883), 7–14.
* T. Y. Lam and K. H. Leung, *On the cyclotomic polynomial Φ_pq(X)*, Amer. Math. Monthly 103 (1996), 562–564.
-/

@[expose] public section

open Polynomial Finset

namespace Migotti

/-- `(X^p - 1) (X^q - 1) Φ_{pq} = (X - 1)(X^{pq} - 1)` over `ℤ`, for distinct primes. -/
private lemma cyclo_mul (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (X ^ p - 1) * (X ^ q - 1) * cyclotomic (p * q) ℤ = (X - 1) * (X ^ (p * q) - 1) := by
  have hpq0 : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  have h1 := prod_cyclotomic_eq_X_pow_sub_one hp.pos ℤ
  have h2 := prod_cyclotomic_eq_X_pow_sub_one hq.pos ℤ
  have h3 := prod_cyclotomic_eq_X_pow_sub_one hpq0 ℤ
  have hd : (p * q).divisors = {1, p, q, p * q} := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hd, -⟩
      obtain ⟨k1, k2, h1', h2', rfl⟩ := Nat.dvd_mul.mp hd
      rcases (Nat.dvd_prime hp).mp h1' with rfl | rfl <;>
        rcases (Nat.dvd_prime hq).mp h2' with rfl | rfl <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨one_dvd _, hpq0.ne'⟩
      · exact ⟨dvd_mul_right _ _, hpq0.ne'⟩
      · exact ⟨dvd_mul_left _ _, hpq0.ne'⟩
      · exact ⟨dvd_rfl, hpq0.ne'⟩
  rw [hd] at h3
  rw [hp.divisors] at h1
  rw [hq.divisors] at h2
  have n1p : (1 : ℕ) ≠ p := hp.one_lt.ne
  have n1q : (1 : ℕ) ≠ q := hq.one_lt.ne
  have n1pq : (1 : ℕ) ≠ p * q := by nlinarith [hp.one_lt, hq.one_lt]
  have npq : p ≠ p * q := by nlinarith [hp.one_lt, hq.one_lt, hq.pos, hp.pos]
  have nqpq : q ≠ p * q := by nlinarith [hp.one_lt, hq.one_lt, hq.pos, hp.pos]
  rw [Finset.prod_insert (by simp [n1p, n1q, n1pq]), Finset.prod_insert (by simp [hpq, npq]),
    Finset.prod_insert (by simp [nqpq]), Finset.prod_singleton] at h3
  rw [Finset.prod_insert (by simp [n1p]), Finset.prod_singleton] at h1
  rw [Finset.prod_insert (by simp [n1q]), Finset.prod_singleton] at h2
  rw [cyclotomic_one] at h1 h2 h3
  rw [← h3, ← h1, ← h2]
  ring

/-- Natural numbers `a, b` with `1 ≤ a ≤ q`, `1 ≤ b ≤ p`, `a p + b q = p q + 1`. -/
private lemma exists_ab (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∃ a b : ℕ, 1 ≤ a ∧ a ≤ q ∧ 1 ≤ b ∧ b ≤ p ∧ a * p + b * q = p * q + 1 := by
  have hc : IsCoprime (p : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hpq)
  obtain ⟨u, v, huv⟩ := hc
  have hq2 := hq.two_le
  have hp2 := hp.two_le
  have hqpos : (0 : ℤ) < q := by exact_mod_cast hq.pos
  have hppos : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have h0 : 0 ≤ u % (q : ℤ) := Int.emod_nonneg _ hqpos.ne'
  have h1 : u % (q : ℤ) < q := Int.emod_lt_of_pos _ hqpos
  have h2 := Int.mul_ediv_add_emod u q
  set a : ℤ := u % (q : ℤ) with ha
  set w : ℤ := v + (u / q) * p with hw
  have hrel : a * p + w * q = 1 := by
    rw [hw]; rw [← h2] at huv; linear_combination huv
  have ha1 : 1 ≤ a := by
    by_contra hcon
    have ha0 : a = 0 := by omega
    rw [ha0] at hrel
    have hd : (q : ℤ) ∣ 1 := ⟨w, by linarith⟩
    have := Int.eq_one_of_dvd_one hqpos.le hd
    omega
  have hb1 : 1 ≤ w + p := by
    by_contra hcon
    have : (w + p) * q ≤ 0 := by nlinarith
    nlinarith
  have hb2 : w + p ≤ p := by
    by_contra hcon
    have : p + 1 ≤ w + p := by omega
    nlinarith
  refine ⟨a.toNat, (w + p).toNat, by omega, by omega, by omega, by omega, ?_⟩
  have e1 : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg h0
  have e2 : (((w + p).toNat : ℕ) : ℤ) = w + p := Int.toNat_of_nonneg (by omega)
  zify
  rw [e1, e2]
  linear_combination hrel

private lemma key (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (u v : ℤ)
    (h : (p : ℤ) * u = q * v) (hu : |u| < q) : u = 0 := by
  have hd : (q : ℤ) ∣ (p : ℤ) * u := ⟨v, h⟩
  have hqp : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  rcases hqp.dvd_or_dvd hd with h1 | h1
  · exfalso
    have : q ∣ p := Int.natCast_dvd_natCast.mp h1
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp this).symm
  · exact Int.eq_zero_of_abs_lt_dvd h1 hu

private lemma inj (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (i i' j j' : ℕ)
    (hi : i < q) (hi' : i' < q) (_hj : j < p) (_hj' : j' < p)
    (h : p * i + q * j = p * i' + q * j') : i = i' ∧ j = j' := by
  have h1 : (p : ℤ) * ((i : ℤ) - i') = q * ((j' : ℤ) - j) := by
    have : ((p * i + q * j : ℕ) : ℤ) = ((p * i' + q * j' : ℕ) : ℤ) := by rw [h]
    push_cast at this; linarith
  have h2 := key p q hp hq hpq _ _ h1 (by rw [abs_lt]; constructor <;> omega)
  have hii : i = i' := by omega
  subst hii
  refine ⟨rfl, ?_⟩
  exact Nat.eq_of_mul_eq_mul_left hq.pos (by omega)

private lemma disj (p q a b : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hab : a * p + b * q = p * q + 1) (i j i' j' : ℕ) (hi : i < a) (_hj : j < b)
    (hi' : i' < q - a) (_hj' : j' < p - b) (haq : a ≤ q) (hbp : b ≤ p) :
    p * i + q * j ≠ p * i' + q * j' + 1 := by
  intro h
  have h1 : (p : ℤ) * ((i : ℤ) - i' - a) = q * ((j' : ℤ) + b - j - p) := by
    have e1 : ((p * i + q * j : ℕ) : ℤ) = ((p * i' + q * j' + 1 : ℕ) : ℤ) := by rw [h]
    have e2 : ((a * p + b * q : ℕ) : ℤ) = ((p * q + 1 : ℕ) : ℤ) := by rw [hab]
    push_cast at e1 e2; linear_combination e1 - e2
  have h2 := key p q hp hq hpq _ _ h1 (by rw [abs_lt]; constructor <;> omega)
  omega

/-- The exponent `p i + q j + e` determines the pair `(i, j)` in the box `[0,q) × [0,p)`. -/
private lemma card_le_one (p q A B e k : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hA : A ≤ q) (hB : B ≤ p) :
    ((range A ×ˢ range B).filter (fun x : ℕ × ℕ => k = p * x.1 + q * x.2 + e)).card ≤ 1 := by
  rw [Finset.card_le_one]
  rintro ⟨i, j⟩ h ⟨i', j'⟩ h'
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h h'
  have := inj p q hp hq hpq i i' j j' (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [Prod.mk.injEq]; exact this

private lemma coeff_term (p q A B e k : ℕ) :
    ((X ^ e * ((∑ i ∈ range A, ((X : ℤ[X]) ^ p) ^ i) * (∑ j ∈ range B, ((X : ℤ[X]) ^ q) ^ j))).coeff k)
      = (((range A ×ˢ range B).filter (fun x : ℕ × ℕ => k = p * x.1 + q * x.2 + e)).card : ℤ) := by
  have h : X ^ e * ((∑ i ∈ range A, ((X : ℤ[X]) ^ p) ^ i) * (∑ j ∈ range B, ((X : ℤ[X]) ^ q) ^ j))
      = ∑ x ∈ range A ×ˢ range B, (X : ℤ[X]) ^ (p * x.1 + q * x.2 + e) := by
    rw [Finset.sum_mul_sum, ← Finset.sum_product', Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, add_comm e]
  rw [h, finsetSum_coeff]
  simp only [coeff_X_pow]
  rw [Finset.sum_boole]

private lemma identity (p q a b : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (haq : a ≤ q) (hbp : b ≤ p) (hab : a * p + b * q = p * q + 1) :
    cyclotomic (p * q) ℤ =
      (∑ i ∈ range a, ((X : ℤ[X]) ^ p) ^ i) * (∑ j ∈ range b, ((X : ℤ[X]) ^ q) ^ j)
      - X * ((∑ i ∈ range (q - a), ((X : ℤ[X]) ^ p) ^ i) *
          (∑ j ∈ range (p - b), ((X : ℤ[X]) ^ q) ^ j)) := by
  have hu : (X : ℤ[X]) ^ p - 1 ≠ 0 := by
    simpa using X_pow_sub_C_ne_zero hp.pos (1 : ℤ)
  have hv : (X : ℤ[X]) ^ q - 1 ≠ 0 := by
    simpa using X_pow_sub_C_ne_zero hq.pos (1 : ℤ)
  apply mul_left_cancel₀ (mul_ne_zero hu hv)
  rw [cyclo_mul p q hp hq hpq]
  have hA := geom_sum_mul ((X : ℤ[X]) ^ p) a
  have hB := geom_sum_mul ((X : ℤ[X]) ^ q) b
  have hC := geom_sum_mul ((X : ℤ[X]) ^ p) (q - a)
  have hD := geom_sum_mul ((X : ℤ[X]) ^ q) (p - b)
  generalize (∑ i ∈ range a, ((X : ℤ[X]) ^ p) ^ i) = A at *
  generalize (∑ i ∈ range b, ((X : ℤ[X]) ^ q) ^ i) = B at *
  generalize (∑ i ∈ range (q - a), ((X : ℤ[X]) ^ p) ^ i) = C at *
  generalize (∑ i ∈ range (p - b), ((X : ℤ[X]) ^ q) ^ i) = D at *
  have e1 : (X : ℤ[X]) ^ p - 1 = (X ^ p - 1) := rfl
  have key1 : (X ^ p - 1) * (X ^ q - 1) * (A * B - X * (C * D))
      = (A * (X ^ p - 1)) * (B * (X ^ q - 1)) - X * ((C * (X ^ p - 1)) * (D * (X ^ q - 1))) := by
    ring
  rw [key1, hA, hB, hC, hD]
  -- arithmetic on exponents
  have x1 : p * (q - a) + 1 = q * b := by
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le haq
    simp only [Nat.add_sub_cancel_left]
    nlinarith
  have x2 : q * (p - b) + 1 = p * a := by
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hbp
    simp only [Nat.add_sub_cancel_left]
    nlinarith
  have hXU : (X : ℤ[X]) * ((X ^ p) ^ (q - a)) = (X ^ q) ^ b := by
    rw [← pow_mul, ← pow_mul, ← pow_succ', ← x1]
  have hXV : (X : ℤ[X]) * ((X ^ q) ^ (p - b)) = (X ^ p) ^ a := by
    rw [← pow_mul, ← pow_mul, ← pow_succ', ← x2]
  have hUU : ((X : ℤ[X]) ^ p) ^ a * (X ^ p) ^ (q - a) = X ^ (p * q) := by
    rw [← pow_add, Nat.add_sub_cancel' haq, ← pow_mul]
  have hVV : ((X : ℤ[X]) ^ q) ^ b * (X ^ q) ^ (p - b) = X ^ (p * q) := by
    rw [← pow_add, Nat.add_sub_cancel' hbp, ← pow_mul, mul_comm]
  generalize ((X : ℤ[X]) ^ p) ^ a = U at *
  generalize ((X : ℤ[X]) ^ q) ^ b = V at *
  generalize ((X : ℤ[X]) ^ p) ^ (q - a) = U' at *
  generalize ((X : ℤ[X]) ^ q) ^ (p - b) = V' at *
  generalize (X : ℤ[X]) ^ (p * q) = N at *
  have hUV : U * V = X * N := by
    rw [← hXU]; linear_combination X * hUU
  have h3 : X * U' * V' = N := by rw [hXU]; exact hVV
  linear_combination (-1) * hUV + h3 - hXU - hXV

/-- **Migotti (1883).** For distinct primes `p ≠ q`, every coefficient of the cyclotomic polynomial
`Φ_{pq}` over `ℤ` is `-1`, `0` or `1`.  Proof: Lam–Leung (1996). -/
theorem coeff_cyclotomic_mul_mem (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (k : ℕ) :
    (cyclotomic (p * q) ℤ).coeff k ∈ ({-1, 0, 1} : Set ℤ) := by
  obtain ⟨a, b, ha1, haq, hb1, hbp, hab⟩ := exists_ab p q hp hq hpq
  rw [identity p q a b hp hq hpq haq hbp hab, coeff_sub]
  have h1 := coeff_term p q a b 0 k
  have h2 := coeff_term p q (q - a) (p - b) 1 k
  simp only [pow_zero, one_mul, pow_one, add_zero] at h1 h2
  rw [h1, h2]
  have c1 : ((range a ×ˢ range b).filter (fun x : ℕ × ℕ => k = p * x.1 + q * x.2)).card ≤ 1 := by
    simpa using card_le_one p q a b 0 k hp hq hpq haq hbp
  have c2 := card_le_one p q (q - a) (p - b) 1 k hp hq hpq (by omega) (by omega)
  have hd : ¬ (0 < ((range a ×ˢ range b).filter
        (fun x : ℕ × ℕ => k = p * x.1 + q * x.2)).card ∧
      0 < ((range (q - a) ×ˢ range (p - b)).filter
        (fun x : ℕ × ℕ => k = p * x.1 + q * x.2 + 1)).card) := by
    rintro ⟨hc1, hc2⟩
    obtain ⟨⟨i, j⟩, hx⟩ := Finset.card_pos.mp hc1
    obtain ⟨⟨i', j'⟩, hy⟩ := Finset.card_pos.mp hc2
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx hy
    exact disj p q a b hp hq hpq hab i j i' j' hx.1.1 hx.1.2 hy.1.1 hy.1.2 haq hbp
      (by omega)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

end Migotti
