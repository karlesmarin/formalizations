/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Algebra.Ring.GeomSum

/-!
# A 2-adic constraint on σ(n) = 2·σ*(n) (OEIS A063880)

If `σ(n) = 2 · usigma(n)` (`usigma` the sum of unitary divisors), some odd prime `p` divides `n`
with exponent `≡ 3 (mod 4)`; in particular `p³ ∣ n` (for `n = 108 = 2²·3³` it is `p = 3`). For every
prime power `p^k ∥ n`, `v₂(σ(p^k)) ≤ v₂(1 + p^k)` unless `p` is odd and `k ≡ 3 (mod 4)`; both `σ`
and `usigma` are multiplicative, so without such a prime `v₂(σ n) ≤ v₂(usigma n)`, against
`σ n = 2 · usigma n`. This is a partial result towards the OPEN statements of formal-conjectures (`n
≡ 108 (mod 216)` and `108` the only primitive term), which are not proved here.

## Main results

* `OeisA63880.usigma_mul`: the sum of unitary divisors is multiplicative
* `OeisA63880.usigma_prime_pow`: usigma(p^k) = 1 + p^k
* `OeisA63880.exists_odd_prime_factorization_mod_four`: sigma n = 2 usigma n forces an odd prime with exponent 3 mod 4
* `OeisA63880.exists_odd_prime_cube_dvd`: sigma n = 2 usigma n forces p^3 | n for some odd prime p

## References

* OEIS A063880 (numbers n with sigma(n) = 2 usigma(n)); R. Stephan's observation that all terms are 108 mod 216 (2003), checked to 10^7 (R. G. Wilson v) and the uniqueness of the primitive 108 below 10^18 (A. Eldar, 2024) are conjectures/computations, not proofs.
* Definitions copied verbatim from google-deepmind/formal-conjectures, FormalConjectures/OEIS/63880.lean (open there).
-/

@[expose] public section

namespace OeisA63880

open scoped ArithmeticFunction.sigma

/-- The set of unitary divisors of $n$: divisors $d$ such that $\gcd(d, n/d) = 1$. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ n.divisors | d.Coprime (n / d)}

/-- The sum of unitary divisors of $n$, denoted $\text{usigma}(n)$. -/
def usigma (n : ℕ) : ℕ :=
  ∑ d ∈ unitaryDivisors n, d

/-- A number $n$ is in the sequence A063880 if $\sigma(n) = 2 \cdot \text{usigma}(n)$. -/
def A (n : ℕ) : Prop :=
  0 < n ∧ σ 1 n = 2 * usigma n

theorem mem_unitaryDivisors {n d : ℕ} :
    d ∈ unitaryDivisors n ↔ (d ∣ n ∧ n ≠ 0) ∧ d.Coprime (n / d) := by
  simp [unitaryDivisors, Nat.mem_divisors]

theorem one_mem_unitaryDivisors {n : ℕ} (hn : 0 < n) : 1 ∈ unitaryDivisors n := by
  rw [mem_unitaryDivisors]
  exact ⟨⟨one_dvd n, hn.ne'⟩, Nat.coprime_one_left _⟩

theorem usigma_pos {n : ℕ} (hn : 0 < n) : 0 < usigma n := by
  have := Finset.single_le_sum (f := fun d : ℕ => d) (fun _ _ => Nat.zero_le _)
    (one_mem_unitaryDivisors hn)
  unfold usigma
  omega

/-- `usigma` is multiplicative. -/
theorem usigma_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    usigma (a * b) = usigma a * usigma b := by
  unfold usigma
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun x => x.1 * x.2) (fun d => (d.gcd a, d.gcd b)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨d₁, d₂⟩ hx
    simp only [Finset.mem_product, mem_unitaryDivisors] at hx ⊢
    obtain ⟨⟨⟨⟨a', rfl⟩, -⟩, h₁⟩, ⟨⟨b', rfl⟩, -⟩, h₂⟩ := hx
    have hd₁ : 0 < d₁ := Nat.pos_of_mul_pos_right ha
    have hd₂ : 0 < d₂ := Nat.pos_of_mul_pos_right hb
    rw [Nat.mul_div_cancel_left _ hd₁] at h₁
    rw [Nat.mul_div_cancel_left _ hd₂] at h₂
    refine ⟨⟨mul_dvd_mul (dvd_mul_right _ _) (dvd_mul_right _ _), (Nat.mul_pos ha hb).ne'⟩, ?_⟩
    rw [show d₁ * a' * (d₂ * b') = d₁ * d₂ * (a' * b') by ring,
      Nat.mul_div_cancel_left _ (Nat.mul_pos hd₁ hd₂)]
    have c12 : d₁.Coprime b' :=
      (hab.coprime_dvd_left (dvd_mul_right _ _)).coprime_dvd_right (dvd_mul_left _ _)
    have c21 : d₂.Coprime a' :=
      (hab.symm.coprime_dvd_left (dvd_mul_right _ _)).coprime_dvd_right (dvd_mul_left _ _)
    exact Nat.Coprime.mul_left (Nat.Coprime.mul_right h₁ c12) (Nat.Coprime.mul_right c21 h₂)
  · intro d hd
    simp only [mem_unitaryDivisors] at hd
    simp only [Finset.mem_product, mem_unitaryDivisors]
    obtain ⟨⟨hdab, -⟩, hcop⟩ := hd
    have hsplit : d = d.gcd a * d.gcd b := by
      rw [← Nat.Coprime.gcd_mul d hab, Nat.gcd_eq_left hdab]
    obtain ⟨a', ha'⟩ := Nat.gcd_dvd_right d a
    obtain ⟨b', hb'⟩ := Nat.gcd_dvd_right d b
    have hg : 0 < d.gcd a := Nat.gcd_pos_of_pos_right _ ha
    have hh : 0 < d.gcd b := Nat.gcd_pos_of_pos_right _ hb
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdab (Nat.mul_pos ha hb)
    have e1 : a * b = (d.gcd a * a') * (d.gcd b * b') := by rw [← ha', ← hb']
    have e2 : a * b = a' * b' * d := by
      rw [e1]
      conv_rhs => rw [hsplit]
      ring
    have hq : a * b / d = a' * b' := Nat.div_eq_of_eq_mul_left hdpos e2
    rw [hq] at hcop
    refine ⟨⟨⟨Nat.gcd_dvd_right d a, ha.ne'⟩, ?_⟩, ⟨⟨Nat.gcd_dvd_right d b, hb.ne'⟩, ?_⟩⟩
    · have e : a / d.gcd a = a' := Nat.div_eq_of_eq_mul_left hg (by rw [mul_comm]; exact ha')
      rw [e]
      exact (hcop.coprime_dvd_left (Nat.gcd_dvd_left d a)).coprime_dvd_right (dvd_mul_right _ _)
    · have e : b / d.gcd b = b' := Nat.div_eq_of_eq_mul_left hh (by rw [mul_comm]; exact hb')
      rw [e]
      exact (hcop.coprime_dvd_left (Nat.gcd_dvd_left d b)).coprime_dvd_right (dvd_mul_left _ _)
  · rintro ⟨d₁, d₂⟩ hx
    simp only [Finset.mem_product, mem_unitaryDivisors] at hx
    obtain ⟨⟨⟨h₁, -⟩, -⟩, ⟨h₂, -⟩, -⟩ := hx
    have c2a : d₂.Coprime a := (hab.symm.coprime_dvd_left h₂)
    have c1b : d₁.Coprime b := (hab.coprime_dvd_left h₁)
    simp only [Prod.mk.injEq]
    exact ⟨by rw [Nat.Coprime.gcd_mul_right_cancel d₁ c2a, Nat.gcd_eq_left h₁],
      by rw [Nat.Coprime.gcd_mul_left_cancel d₂ c1b, Nat.gcd_eq_left h₂]⟩
  · intro d hd
    simp only [mem_unitaryDivisors] at hd
    show d.gcd a * d.gcd b = d
    rw [← Nat.Coprime.gcd_mul d hab, Nat.gcd_eq_left hd.1.1]
  · intro x _
    rfl

/-- `usigma (p ^ k) = 1 + p ^ k` for `k ≥ 1`. -/
theorem usigma_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    usigma (p ^ k) = 1 + p ^ k := by
  have hne : (1 : ℕ) ≠ p ^ k := (Nat.one_lt_pow hk.ne' hp.one_lt).ne
  have hset : unitaryDivisors (p ^ k) = {1, p ^ k} := by
    ext d
    rw [mem_unitaryDivisors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hd, -⟩, hc⟩
      obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).1 hd
      rw [Nat.pow_div hi hp.pos] at hc
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · left; simp
      rcases Nat.eq_zero_or_pos (k - i) with hki | hki
      · right; congr 1; omega
      exfalso
      exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt (dvd_pow_self p hi0.ne')
        (dvd_pow_self p hki.ne') hc
    · rintro (rfl | rfl)
      · exact ⟨⟨one_dvd _, (pow_pos hp.pos k).ne'⟩, Nat.coprime_one_left _⟩
      · refine ⟨⟨dvd_rfl, (pow_pos hp.pos k).ne'⟩, ?_⟩
        rw [Nat.div_self (pow_pos hp.pos k)]
        exact Nat.coprime_one_right _
  unfold usigma
  rw [hset, Finset.sum_pair hne]

/-- A sum of `n` odd numbers has the parity of `n`. -/
theorem sum_range_mod_two (f : ℕ → ℕ) (hf : ∀ i, f i % 2 = 1) (n : ℕ) :
    (∑ i ∈ Finset.range n, f i) % 2 = n % 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, hf n]
    omega

theorem geom_even_split (p m : ℕ) :
    ∑ i ∈ Finset.range (2 * m), p ^ i = (1 + p) * ∑ j ∈ Finset.range m, p ^ (2 * j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, pow_succ]
    ring

/-- Local 2-adic inequality: `v₂(σ(p^k)) ≤ v₂(1 + p^k)` unless `p` is odd and `k ≡ 3 (mod 4)`. -/
theorem padicValNat_two_local {p k : ℕ} (hp : p.Prime) (h : ¬ (p ≠ 2 ∧ k % 4 = 3)) :
    padicValNat 2 (∑ i ∈ Finset.range (k + 1), p ^ i) ≤ padicValNat 2 (1 + p ^ k) := by
  by_cases h2 : p = 2
  · subst h2
    have hodd : (∑ i ∈ Finset.range (k + 1), 2 ^ i) % 2 = 1 := by
      rw [Finset.sum_range_succ', pow_zero]
      have : ∑ i ∈ Finset.range k, 2 ^ (i + 1) = 2 * ∑ i ∈ Finset.range k, 2 ^ i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
      omega
    rw [padicValNat.eq_zero_of_not_dvd (by omega)]
    exact Nat.zero_le _
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two h2)
  have hpow : ∀ i, p ^ i % 2 = 1 := fun i => by rw [Nat.pow_mod, hpodd, one_pow]; norm_num
  have hk4 : k % 4 ≠ 3 := fun hk => h ⟨h2, hk⟩
  rcases Nat.even_or_odd k with ⟨r, hr⟩ | ⟨r, hr⟩
  · -- k even: σ(p^k) is odd
    have hodd : (∑ i ∈ Finset.range (k + 1), p ^ i) % 2 = 1 := by
      rw [sum_range_mod_two _ hpow]; omega
    rw [padicValNat.eq_zero_of_not_dvd (by omega)]
    exact Nat.zero_le _
  · -- k = 2r+1 with r even: σ(p^k) = (1+p)·T, T odd, and 1+p ∣ 1+p^k
    have hr2 : (r + 1) % 2 = 1 := by omega
    have hsplit : ∑ i ∈ Finset.range (k + 1), p ^ i
        = (1 + p) * ∑ j ∈ Finset.range (r + 1), p ^ (2 * j) := by
      rw [show k + 1 = 2 * (r + 1) by omega, geom_even_split]
    have hT : (∑ j ∈ Finset.range (r + 1), p ^ (2 * j)) % 2 = 1 := by
      rw [sum_range_mod_two _ (fun j => hpow (2 * j))]; exact hr2
    have hdvd : 1 + p ∣ 1 + p ^ k := by
      have hko : Odd k := ⟨r, hr⟩
      have := hko.nat_add_dvd_pow_add_pow 1 p
      simpa using this
    have hT0 : ∑ j ∈ Finset.range (r + 1), p ^ (2 * j) ≠ 0 := by omega
    have hp0 : 1 + p ≠ 0 := by omega
    have hvT : padicValNat 2 (∑ j ∈ Finset.range (r + 1), p ^ (2 * j)) = 0 :=
      padicValNat.eq_zero_of_not_dvd (by omega)
    rw [hsplit, padicValNat.mul hp0 hT0, hvT, add_zero]
    have hne : 1 + p ^ k ≠ 0 := by positivity
    exact (padicValNat_dvd_iff_le hne).1 ((pow_padicValNat_dvd).trans hdvd)

/-- The global inequality, by multiplicativity. -/
theorem padicValNat_two_le (n : ℕ) :
    0 < n → (∀ p, p.Prime → p ≠ 2 → n.factorization p % 4 ≠ 3) →
      padicValNat 2 (σ 1 n) ≤ padicValNat 2 (usigma n) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro _ h
    have hf : (p ^ k).factorization p = k := by simp [hp.factorization_pow]
    have h' : ¬ (p ≠ 2 ∧ k % 4 = 3) := fun ⟨h2, hk3⟩ => h p hp h2 (by rw [hf]; exact hk3)
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hp, usigma_prime_pow hp hk]
    exact padicValNat_two_local hp h'
  | zero => intro h; omega
  | one => intro _ _; simp [usigma, unitaryDivisors]
  | coprime a b ha hb hab iha ihb =>
    intro _ h
    have ha0 : 0 < a := by omega
    have hb0 : 0 < b := by omega
    have hfa : ∀ p, p.Prime → p ≠ 2 → a.factorization p % 4 ≠ 3 := by
      intro p hp h2 h3
      have hpa : p ∣ a := Nat.dvd_of_factorization_pos (by omega)
      have hpb : ¬ p ∣ b := fun hpb =>
        Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpa hpb hab
      apply h p hp h2
      rw [Nat.factorization_mul ha0.ne' hb0.ne', Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hpb, add_zero]
      exact h3
    have hfb : ∀ p, p.Prime → p ≠ 2 → b.factorization p % 4 ≠ 3 := by
      intro p hp h2 h3
      have hpb : p ∣ b := Nat.dvd_of_factorization_pos (by omega)
      have hpa : ¬ p ∣ a := fun hpa =>
        Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpa hpb hab
      apply h p hp h2
      rw [Nat.factorization_mul ha0.ne' hb0.ne', Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hpa, zero_add]
      exact h3
    have hsa : σ 1 a ≠ 0 := (ArithmeticFunction.sigma_pos 1 a ha0.ne').ne'
    have hsb : σ 1 b ≠ 0 := (ArithmeticFunction.sigma_pos 1 b hb0.ne').ne'
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hab,
      usigma_mul ha0 hb0 hab, padicValNat.mul hsa hsb,
      padicValNat.mul (usigma_pos ha0).ne' (usigma_pos hb0).ne']
    exact Nat.add_le_add (iha ha0 hfa) (ihb hb0 hfb)

/-- **Main result.** Every term of A063880 has an odd prime factor whose exponent is
`≡ 3 (mod 4)`. -/
theorem exists_odd_prime_factorization_mod_four {n : ℕ} (hA : A n) :
    ∃ p, p.Prime ∧ p ≠ 2 ∧ n.factorization p % 4 = 3 := by
  by_contra hcon
  push Not at hcon
  have key := padicValNat_two_le n hA.1 hcon
  rw [hA.2, padicValNat.mul two_ne_zero (usigma_pos hA.1).ne', padicValNat_self] at key
  omega

/-- Corollary: every term of A063880 is divisible by the cube of an odd prime. -/
theorem exists_odd_prime_cube_dvd {n : ℕ} (hA : A n) : ∃ p, p.Prime ∧ p ≠ 2 ∧ p ^ 3 ∣ n := by
  obtain ⟨p, hp, h2, h3⟩ := exists_odd_prime_factorization_mod_four hA
  refine ⟨p, hp, h2, (hp.pow_dvd_iff_le_factorization hA.1.ne').2 (by omega)⟩

end OeisA63880
