/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.ArithmeticFunction.Zeta
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Algebra.Polynomial.Reverse

/-!
# Cyclotomic polynomials: size of Φ_n(x) and the parity of ω(n) (Jameson, Prop. 1.20)

For `n ≥ 2` and real `0 < x ≤ 1/2`, `Φ_n(x)` lies in `(1 - x, 1)` when `n` has an even number of
distinct prime factors and in `(1, 1/(1 - x))` when it has an odd number. Via the palindromy
`X^φ(n) Φ_n(1/X) = Φ_n(X)` (proved here as `reverse_cyclotomic`), the matching bounds around
`x^φ(n)` hold for `x ≥ 2`.

## Main results

* `CycloParity.cyclotomic_eval_parity`: n ≥ 2, 0 < x ≤ 1/2: ω(n) even ⇒ 1 - x < Φ_n(x) < 1; odd ⇒ 1 < Φ_n(x) < 1/(1-x)
* `CycloParity.cyclotomic_eval_lt_one_of_even`: ω(n) even ⇒ Φ_n(x) < 1 for 0 < x ≤ 1/2
* `CycloParity.one_lt_cyclotomic_eval_of_odd`: ω(n) odd ⇒ 1 < Φ_n(x) for 0 < x ≤ 1/2
* `CycloParity.reverse_cyclotomic`: Φ_n is palindromic over ℝ for n ≥ 2
* `CycloParity.cyclotomic_eval_reciprocal`: Φ_n(x) = x^φ(n) Φ_n(1/x) for n ≥ 2, x ≠ 0
* `CycloParity.cyclotomic_eval_parity_ge_two`: n ≥ 2, x ≥ 2: ω(n) even ⇒ (x-1)x^(φ-1) < Φ_n(x) < x^φ; odd ⇒ x^φ < Φ_n(x) < x^(φ+1)/(x-1)

## References

* R. Whitty, Theorem of the Day, «The Bungers–Lehmer Theorem on Cyclotomic Coefficients» (Cyclotomic).
* G. J. O. Jameson, «The cyclotomic polynomials», lecture notes (Lancaster University), §1: Proposition 1.20 and Proposition 1.3 (palindromy).
-/

@[expose] public section

open Polynomial ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.omega

@[expose] public section

namespace CycloParity

/-- Weierstrass: `1 - Σ aᵢ ≤ ∏ (1 - aᵢ)` for `aᵢ ∈ [0,1]`. -/
lemma one_sub_sum_le_prod (s : Finset ℕ) (a : ℕ → ℝ) (h : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have hj' := h j (Finset.mem_insert_self j s)
    have ih' := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hS : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg (fun i hi => (h i (Finset.mem_insert_of_mem hi)).1)
    nlinarith [mul_le_mul_of_nonneg_left ih' (sub_nonneg.2 hj'.2), mul_nonneg hj'.1 hS]

/-- `Σ_{d ∈ S} x^d < x^m / (1-x)` if all `d ∈ S` are `≥ m` (distinct powers). -/
lemma sum_pow_lt (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (S : Finset ℕ) (m : ℕ) (hS : ∀ d ∈ S, m ≤ d) :
    ∑ d ∈ S, x ^ d < x ^ m / (1 - x) := by
  set N := m + S.sup id + 1 with hN
  have hsub : S ⊆ Finset.Ico m N := by
    intro d hd
    have h1 := hS d hd
    have h2 : d ≤ S.sup id := Finset.le_sup (f := id) hd
    rw [Finset.mem_Ico]; omega
  have h1 : ∑ d ∈ S, x ^ d ≤ ∑ d ∈ Finset.Ico m N, x ^ d :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => (pow_pos hx0 i).le)
  have hmN : m ≤ N := by omega
  have h2 := geom_sum_Ico (ne_of_lt hx1) hmN
  have h1x : (0:ℝ) < 1 - x := by linarith
  have h3 : (x ^ N - x ^ m) / (x - 1) = (x ^ m - x ^ N) / (1 - x) := by
    have : x - 1 ≠ 0 := by linarith
    field_simp
    ring
  have h4 : (x ^ m - x ^ N) / (1 - x) < x ^ m / (1 - x) := by
    apply div_lt_div_of_pos_right _ h1x
    have := pow_pos hx0 N
    linarith
  linarith

/-- Abstract inequalities of Jameson's proof of 1.20. -/
lemma ratio_bounds (x : ℝ) (hx0 : 0 < x) (hx2 : x ≤ 1 / 2) (A B : Finset ℕ) (p : ℕ)
    (hA1 : 1 ∈ A) (hApos : ∀ a ∈ A, 1 ≤ a) (hB2 : ∀ b ∈ B, 2 ≤ b) (hpB : p ∈ B)
    (hA : ∀ a ∈ A, a ≠ 1 → p + 2 ≤ a) :
    0 < ∏ d ∈ B, (1 - x ^ d) ∧ (1 - x) * ∏ d ∈ B, (1 - x ^ d) < ∏ d ∈ A, (1 - x ^ d) ∧
      ∏ d ∈ A, (1 - x ^ d) < ∏ d ∈ B, (1 - x ^ d) := by
  have hx1 : x < 1 := by linarith
  have h1x : (0:ℝ) < 1 - x := by linarith
  have hxp : ∀ d : ℕ, 0 < d → 0 < 1 - x ^ d := fun d hd => by
    have := pow_lt_one₀ hx0.le hx1 hd.ne'
    linarith
  have hxp' : ∀ d : ℕ, x ^ d ≤ 1 := fun d => pow_le_one₀ hx0.le hx1.le
  have hpB2 := hB2 p hpB
  have hBpos : 0 < ∏ d ∈ B, (1 - x ^ d) :=
    Finset.prod_pos (fun d hd => hxp d (by have := hB2 d hd; omega))
  refine ⟨hBpos, ?_, ?_⟩
  · -- (1-x) PB < PA
    have hsplitA := Finset.mul_prod_erase A (fun d => 1 - x ^ d) hA1
    have hsplitB := Finset.mul_prod_erase B (fun d => 1 - x ^ d) hpB
    have hRle : 1 - ∑ d ∈ A.erase 1, x ^ d ≤ ∏ d ∈ A.erase 1, (1 - x ^ d) :=
      one_sub_sum_le_prod _ _ (fun i _ => ⟨(pow_pos hx0 i).le, hxp' i⟩)
    have hgeo := sum_pow_lt x hx0 hx1 (A.erase 1) (p + 2)
      (fun d hd => hA d (Finset.mem_of_mem_erase hd) (Finset.ne_of_mem_erase hd))
    have hQle : ∏ d ∈ B.erase p, (1 - x ^ d) ≤ 1 :=
      Finset.prod_le_one₀ (fun i hi => (hxp i (by have := hB2 i (Finset.mem_of_mem_erase hi); omega)).le)
        (fun i _ => by have := pow_pos hx0 i; linarith)
    have hQpos : 0 ≤ ∏ d ∈ B.erase p, (1 - x ^ d) :=
      Finset.prod_nonneg (fun i hi => (hxp i (by have := hB2 i (Finset.mem_of_mem_erase hi); omega)).le)
    have hxpp : 0 < x ^ p := pow_pos hx0 p
    have hB' : ∏ d ∈ B, (1 - x ^ d) ≤ 1 - x ^ p := by
      rw [← hsplitB]
      exact mul_le_of_le_one_right (hxp p (by omega)).le hQle
    -- x^(p+2)/(1-x) ≤ x^p
    have hk : x ^ (p + 2) / (1 - x) ≤ x ^ p := by
      rw [div_le_iff₀ h1x, pow_add]
      have : x ^ 2 ≤ 1 - x := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this hxpp.le]
    have hR : 1 - x ^ p < ∏ d ∈ A.erase 1, (1 - x ^ d) := by linarith
    rw [← hsplitA]
    have hx' : 1 - x ^ 1 = 1 - x := by simp
    rw [hx']
    have h5 : (1 - x) * ∏ d ∈ B, (1 - x ^ d) ≤ (1 - x) * (1 - x ^ p) :=
      mul_le_mul_of_nonneg_left hB' h1x.le
    nlinarith [mul_lt_mul_of_pos_left hR h1x]
  · -- PA < PB
    have hsplitA := Finset.mul_prod_erase A (fun d => 1 - x ^ d) hA1
    have hRle1 : ∏ d ∈ A.erase 1, (1 - x ^ d) ≤ 1 :=
      Finset.prod_le_one₀ (fun i hi => (hxp i (hApos i (Finset.mem_of_mem_erase hi))).le)
        (fun i _ => by have := pow_pos hx0 i; linarith)
    have hRnn : 0 ≤ ∏ d ∈ A.erase 1, (1 - x ^ d) :=
      Finset.prod_nonneg (fun i hi => (hxp i (hApos i (Finset.mem_of_mem_erase hi))).le)
    have hPA : ∏ d ∈ A, (1 - x ^ d) ≤ 1 - x := by
      rw [← hsplitA]
      have hx' : 1 - x ^ 1 = 1 - x := by simp
      rw [hx']
      nlinarith
    have hBle : 1 - ∑ d ∈ B, x ^ d ≤ ∏ d ∈ B, (1 - x ^ d) :=
      one_sub_sum_le_prod _ _ (fun i _ => ⟨(pow_pos hx0 i).le, hxp' i⟩)
    have hgeo := sum_pow_lt x hx0 hx1 B 2 hB2
    have hk : x ^ 2 / (1 - x) ≤ x := by
      rw [div_le_iff₀ h1x]
      nlinarith
    linarith

/-- Möbius inversion for the real evaluation of `Φ_n`. -/
lemma eval_cyclotomic_moebius (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (n : ℕ) (hn : 0 < n) :
    (cyclotomic n ℝ).eval x = ∏ d ∈ n.divisors, (x ^ d - 1) ^ (μ (n / d)) := by
  have hg : ∀ m : ℕ, 0 < m → x ^ m - 1 ≠ 0 := fun m hm => by
    have := pow_lt_one₀ hx0.le hx1 hm.ne'
    exact ne_of_lt (by linarith)
  have hprod : ∀ m : ℕ, 0 < m → ∏ i ∈ m.divisors, (cyclotomic i ℝ).eval x = x ^ m - 1 := by
    intro m hm
    have := prod_cyclotomic_eq_X_pow_sub_one hm ℝ
    have h2 := congrArg (eval x) this
    simpa [eval_prod] using h2
  have hf : ∀ m : ℕ, 0 < m → (cyclotomic m ℝ).eval x ≠ 0 := by
    intro m hm h0
    have := hprod m hm
    rw [Finset.prod_eq_zero (Nat.mem_divisors_self m hm.ne') h0] at this
    exact hg m hm this.symm
  have key := (prod_eq_iff_prod_pow_moebius_eq_of_nonzero (R := ℝ)
    (f := fun m => (cyclotomic m ℝ).eval x) (g := fun m => x ^ m - 1) hf hg).1 hprod n hn
  rw [← key, Nat.prod_divisorsAntidiagonal (fun a b => (x ^ b - 1) ^ μ a)]
  rw [← Nat.prod_div_divisors n (fun d => (x ^ d - 1) ^ μ (n / d))]
  apply Finset.prod_congr rfl
  intro i hi
  simp [Nat.div_div_self (Nat.dvd_of_mem_divisors hi) hn.ne']

lemma moebius_div_eq (n d : ℕ) (hn : Squarefree n) (hd : d ∣ n) :
    μ (n / d) = μ n * μ d := by
  have hcop : Nat.Coprime d (n / d) := by
    apply Nat.coprime_of_squarefree_mul
    rwa [Nat.mul_div_cancel' hd]
  have h1 : μ n = μ d * μ (n / d) := by
    conv_lhs => rw [← Nat.mul_div_cancel' hd]
    exact isMultiplicative_moebius.map_mul_of_coprime hcop
  have hdsq : Squarefree d := Squarefree.squarefree_of_dvd hd hn
  rcases moebius_ne_zero_iff_eq_or.1 (moebius_ne_zero_iff_squarefree.2 hdsq) with h | h
  · rw [h1, h]; ring
  · rw [h1, h]; ring

/-- Squarefree case of Jameson 1.20. -/
lemma main_squarefree (x : ℝ) (hx0 : 0 < x) (hx2 : x ≤ 1 / 2) (n : ℕ) (hn : Squarefree n)
    (hn1 : 2 ≤ n) :
    (μ n = 1 → 1 - x < (cyclotomic n ℝ).eval x ∧ (cyclotomic n ℝ).eval x < 1) ∧
    (μ n = -1 → 1 < (cyclotomic n ℝ).eval x ∧ (cyclotomic n ℝ).eval x < 1 / (1 - x)) := by
  classical
  have hx1 : x < 1 := by linarith
  have hn0 : n ≠ 0 := by omega
  set D := n.divisors.filter (fun d => μ d = 1) with hD
  set E := n.divisors.filter (fun d => ¬ μ d = 1) with hE
  set p := n.minFac with hp
  have hpp : p.Prime := Nat.minFac_prime (by omega)
  have hp2 := hpp.two_le
  have hpn : p ∣ n := Nat.minFac_dvd n
  have h1D : 1 ∈ D := by simp [hD, hn0]
  have hDpos : ∀ a ∈ D, 1 ≤ a := fun a ha => Nat.pos_of_mem_divisors (Finset.mem_filter.1 ha).1
  have hE2 : ∀ b ∈ E, 2 ≤ b := by
    intro b hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_filter.1 hb
    have h0 : 0 < b := Nat.pos_of_mem_divisors hb1
    by_contra hlt
    have : b = 1 := by omega
    subst this
    exact hb2 (by simp)
  have hpE : p ∈ E := by
    rw [hE, Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨hpn, hn0⟩, by rw [moebius_apply_prime hpp]; norm_num⟩
  have hDp : ∀ a ∈ D, a ≠ 1 → p + 2 ≤ a := by
    intro a ha ha1
    obtain ⟨ha', hμ⟩ := Finset.mem_filter.1 ha
    have hadvd : a ∣ n := Nat.dvd_of_mem_divisors ha'
    have ha0 : 0 < a := Nat.pos_of_mem_divisors ha'
    have hqp : (a.minFac).Prime := Nat.minFac_prime ha1
    have hqa : a.minFac ∣ a := Nat.minFac_dvd a
    have hpq : p ≤ a.minFac := Nat.minFac_le_of_dvd hqp.two_le (hqa.trans hadvd)
    obtain ⟨r, hr⟩ := hqa
    have hr1 : r ≠ 1 := by
      intro h1
      rw [h1, mul_one] at hr
      rw [hr, moebius_apply_prime hqp] at hμ
      omega
    have hr0 : r ≠ 0 := by
      rintro rfl
      omega
    have hrn : r ∣ n := (Dvd.intro_left _ hr.symm).trans hadvd
    have hpr : p ≤ r := Nat.minFac_le_of_dvd (by omega) hrn
    rw [hr]
    nlinarith
  obtain ⟨hBpos, hlow, hhigh⟩ := ratio_bounds x hx0 hx2 D E p h1D hDpos hE2 hpE hDp
  set PA := ∏ d ∈ D, (1 - x ^ d) with hPA
  set PB := ∏ d ∈ E, (1 - x ^ d) with hPB
  -- Φ as a product with integer exponents
  have hΦ : (cyclotomic n ℝ).eval x =
      (∏ d ∈ n.divisors, (x ^ d - 1) ^ (μ d)) ^ (μ n) := by
    rw [eval_cyclotomic_moebius x hx0 hx1 n (by omega), ← Finset.prod_zpow]
    apply Finset.prod_congr rfl
    intro d hd
    rw [moebius_div_eq n d hn (Nat.dvd_of_mem_divisors hd), mul_comm (μ n) (μ d), zpow_mul]
  have hsq : ∀ d ∈ n.divisors, μ d = 1 ∨ μ d = -1 := fun d hd =>
    moebius_ne_zero_iff_eq_or.1 (moebius_ne_zero_iff_squarefree.2
      (Squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd) hn))
  have hT1 : ∏ d ∈ n.divisors, (x ^ d - 1) ^ (μ d) =
      (∏ d ∈ D, (x ^ d - 1)) * (∏ d ∈ E, (x ^ d - 1))⁻¹ := by
    have h : ∀ d ∈ n.divisors, (x ^ d - 1) ^ (μ d) =
        if μ d = 1 then (x ^ d - 1) else (x ^ d - 1)⁻¹ := by
      intro d hd
      split_ifs with h1
      · rw [h1, zpow_one]
      · rcases hsq d hd with h2 | h2
        · exact absurd h2 h1
        · rw [h2, zpow_neg_one]
    rw [Finset.prod_congr rfl h, Finset.prod_ite, Finset.prod_inv_distrib]
  have hsumμ : ∑ d ∈ n.divisors, μ d = 0 := by
    have h := coe_mul_zeta_apply (f := μ) (x := n)
    rw [moebius_mul_coe_zeta, one_apply_ne (by omega)] at h
    exact h.symm
  have hcard : (D.card : ℤ) = E.card := by
    have h : ∑ d ∈ D, μ d + ∑ d ∈ E, μ d = ∑ d ∈ n.divisors, μ d :=
      Finset.sum_filter_add_sum_filter_not n.divisors (fun d => μ d = 1) (fun d => μ d)
    have hsD : ∑ d ∈ D, μ d = D.card := by
      rw [Finset.sum_congr rfl (fun d hd => (Finset.mem_filter.1 hd).2)]
      simp
      rfl
    have hsE : ∑ d ∈ E, μ d = -(E.card : ℤ) := by
      rw [Finset.sum_congr rfl (g := fun _ => (-1 : ℤ)) (fun d hd => by
        rcases hsq d (Finset.mem_filter.1 hd).1 with h2 | h2
        · exact absurd h2 (Finset.mem_filter.1 hd).2
        · exact h2)]
      simp
    rw [hsumμ] at h
    linarith
  have hcard' : D.card = E.card := by exact_mod_cast hcard
  have hT : ∏ d ∈ n.divisors, (x ^ d - 1) ^ (μ d) = PA / PB := by
    rw [hT1]
    have hD' : ∏ d ∈ D, (x ^ d - 1) = (-1) ^ D.card * PA := by
      rw [hPA, ← Finset.prod_neg]
      apply Finset.prod_congr rfl
      intro d _
      ring
    have hE' : ∏ d ∈ E, (x ^ d - 1) = (-1) ^ E.card * PB := by
      rw [hPB, ← Finset.prod_neg]
      apply Finset.prod_congr rfl
      intro d _
      ring
    rw [hD', hE', hcard']
    rcases neg_one_pow_eq_or ℝ E.card with h | h <;> rw [h] <;> field_simp
  have hPApos : 0 < PA := by nlinarith [mul_pos (by linarith : (0:ℝ) < 1 - x) hBpos]
  rw [hΦ, hT]
  constructor
  · intro h
    rw [h, zpow_one]
    exact ⟨(lt_div_iff₀ hBpos).2 (by linarith), (div_lt_one hBpos).2 hhigh⟩
  · intro h
    rw [h, zpow_neg_one, inv_div]
    refine ⟨(one_lt_div hPApos).2 hhigh, ?_⟩
    rw [div_lt_div_iff₀ hPApos (by linarith)]
    linarith

lemma omega_eq_card (n : ℕ) : ω n = n.primeFactors.card := by
  rw [cardDistinctFactors_apply]
  exact (List.card_toFinset _).symm

lemma moebius_eq_pow_card (n : ℕ) (hn : Squarefree n) : μ n = (-1) ^ n.primeFactors.card := by
  rw [moebius_apply_of_squarefree hn, ← omega_eq_card,
    ((cardDistinctFactors_eq_cardFactors_iff_squarefree hn.ne_zero).2 hn)]

/-- Jameson, Proposition 1.20 for `0 < x ≤ 1/2`: both parities, all `n ≥ 2`. -/
theorem cyclotomic_eval_parity (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx0 : 0 < x) (hx2 : x ≤ 1 / 2) :
    (Even n.primeFactors.card →
      1 - x < (cyclotomic n ℝ).eval x ∧ (cyclotomic n ℝ).eval x < 1) ∧
    (Odd n.primeFactors.card →
      1 < (cyclotomic n ℝ).eval x ∧ (cyclotomic n ℝ).eval x < 1 / (1 - x)) := by
  induction n using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    by_cases hsq : Squarefree n
    · obtain ⟨h1, h2⟩ := main_squarefree x hx0 hx2 n hsq hn
      refine ⟨fun he => h1 ?_, fun ho => h2 ?_⟩
      · rw [moebius_eq_pow_card n hsq]; exact he.neg_one_pow
      · rw [moebius_eq_pow_card n hsq]; exact ho.neg_one_pow
    · rw [Nat.squarefree_iff_prime_squarefree] at hsq
      push Not at hsq
      obtain ⟨p, hp, ⟨m', hm'⟩⟩ := hsq
      have hn0 : n ≠ 0 := by omega
      have hm'0 : m' ≠ 0 := by
        rintro rfl
        simp at hm'
        omega
      have hp2 := hp.two_le
      set m := p * m' with hm
      have hpm : p ∣ m := Dvd.intro _ rfl
      have hnm : n = m * p := by rw [hm']; ring
      have hm0 : m ≠ 0 := by positivity
      have hm2 : 2 ≤ m := by
        have : 1 ≤ m' := Nat.one_le_iff_ne_zero.2 hm'0
        nlinarith
      have hlt : m < n := by nlinarith
      have hx1 : x < 1 := by linarith
      have hy0 : 0 < x ^ p := pow_pos hx0 p
      have hyx : x ^ p ≤ x := pow_le_of_le_one hx0.le hx1.le hp.ne_zero
      have hy2 : x ^ p ≤ 1 / 2 := hyx.trans hx2
      have hev : (cyclotomic n ℝ).eval x = (cyclotomic m ℝ).eval (x ^ p) := by
        rw [hnm, ← cyclotomic_expand_eq_cyclotomic hp hpm ℝ, expand_eval]
      have hpf : n.primeFactors = m.primeFactors := by
        rw [hnm, Nat.primeFactors_mul hm0 hp.ne_zero, hp.primeFactors]
        exact Finset.union_eq_left.2
          (Finset.singleton_subset_iff.2 (Nat.mem_primeFactors.2 ⟨hp, hpm, hm0⟩))
      obtain ⟨ih1, ih2⟩ := ih m hlt hm2 (x ^ p) hy0 hy2
      rw [hev, hpf]
      have hxy : 1 - x ≤ 1 - x ^ p := by linarith
      have hxy0 : 0 < 1 - x := by linarith
      refine ⟨fun he => ?_, fun ho => ?_⟩
      · obtain ⟨a, b⟩ := ih1 he
        exact ⟨by linarith, b⟩
      · obtain ⟨a, b⟩ := ih2 ho
        exact ⟨a, b.trans_le (one_div_le_one_div_of_le hxy0 hxy)⟩

theorem cyclotomic_eval_lt_one_of_even (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx0 : 0 < x) (hx2 : x ≤ 1 / 2)
    (he : Even n.primeFactors.card) :
    1 - x < (cyclotomic n ℝ).eval x ∧ (cyclotomic n ℝ).eval x < 1 :=
  (cyclotomic_eval_parity n hn x hx0 hx2).1 he

theorem one_lt_cyclotomic_eval_of_odd (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx0 : 0 < x) (hx2 : x ≤ 1 / 2)
    (ho : Odd n.primeFactors.card) :
    1 < (cyclotomic n ℝ).eval x ∧ (cyclotomic n ℝ).eval x < 1 / (1 - x) :=
  (cyclotomic_eval_parity n hn x hx0 hx2).2 ho


/-! ## Reciprocity and the part `x ≥ 2` -/

lemma reverse_one_real : (1 : ℝ[X]).reverse = 1 := by
  have := reverse_C (1 : ℝ)
  rwa [map_one] at this

lemma reverse_prod_dom {ι : Type*} (s : Finset ι) (f : ι → ℝ[X]) :
    (∏ i ∈ s, f i).reverse = ∏ i ∈ s, (f i).reverse := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using reverse_one_real
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.prod_insert hj, reverse_mul_of_domain, ih]

lemma reverse_X_pow_sub_one (n : ℕ) : ((X : ℝ[X]) ^ n - 1).reverse = -((X : ℝ[X]) ^ n - 1) := by
  have h : ((X : ℝ[X]) ^ n - 1) = X ^ n + C (-1) := by simp [sub_eq_add_neg]
  rw [h, reverse_add_C]
  have h1 : (X : ℝ[X]) ^ n = 1 * X ^ n := by simp
  have h2 : ((X : ℝ[X]) ^ n).reverse = 1 := by
    rw [h1, reverse_mul_X_pow]; exact reverse_one_real
  rw [h2, natDegree_X_pow]
  simp [add_comm]

/-- Polynomial reciprocity: `reverse Φ_n = Φ_n` for `n ≥ 2`. -/
theorem reverse_cyclotomic (n : ℕ) (hn : 2 ≤ n) : (cyclotomic n ℝ).reverse = cyclotomic n ℝ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn0 : n ≠ 0 := by omega
    set P := ∏ d ∈ n.properDivisors, cyclotomic d ℝ with hP
    have hprod : P * cyclotomic n ℝ = X ^ n - 1 := by
      rw [← prod_cyclotomic_eq_X_pow_sub_one (by omega) ℝ, ← Nat.cons_self_properDivisors hn0,
        Finset.prod_cons, mul_comm]
    have hP0 : P ≠ 0 :=
      Finset.prod_ne_zero_iff.2 (fun d _ => cyclotomic_ne_zero d ℝ)
    have hrevd : ∀ d ∈ n.properDivisors, (cyclotomic d ℝ).reverse =
        (if d = 1 then (-1 : ℝ[X]) else 1) * cyclotomic d ℝ := by
      intro d hd
      by_cases hd1 : d = 1
      · subst hd1
        have h := reverse_X_pow_sub_one 1
        rw [pow_one] at h
        rw [cyclotomic_one, h]
        simp
      · simp only [hd1, ↓reduceIte, one_mul]
        have hd2 : 2 ≤ d := by
          have := Nat.pos_of_mem_properDivisors hd
          omega
        exact ih d (Nat.mem_properDivisors.1 hd).2 hd2
    have hrevP : P.reverse = -P := by
      rw [hP, reverse_prod_dom, Finset.prod_congr rfl hrevd, Finset.prod_mul_distrib,
        Finset.prod_ite_eq']
      have h1 : 1 ∈ n.properDivisors := Nat.one_mem_properDivisors_iff_one_lt.2 (by omega)
      simp [h1]
    have key := congrArg Polynomial.reverse hprod
    rw [reverse_mul_of_domain, hrevP, reverse_X_pow_sub_one, ← hprod] at key
    have : (-P) * ((cyclotomic n ℝ).reverse - cyclotomic n ℝ) = 0 := by
      linear_combination key
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (neg_eq_zero.1 h) hP0
    · exact sub_eq_zero.1 h

/-- Reciprocity evaluated: `Φ_n(x) = x^φ(n) Φ_n(1/x)` for `n ≥ 2`, `x ≠ 0`. -/
theorem cyclotomic_eval_reciprocal (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : x ≠ 0) :
    (cyclotomic n ℝ).eval x = x ^ (Nat.totient n) * (cyclotomic n ℝ).eval (1 / x) := by
  let _ : Invertible x := invertibleOfNonzero hx
  have h := eval₂_reverse_mul_pow (RingHom.id ℝ) x (cyclotomic n ℝ)
  rw [reverse_cyclotomic n hn, natDegree_cyclotomic] at h
  simp only [eval₂_id, invOf_eq_inv] at h
  rw [← h, one_div]; ring

/-- Jameson, Proposition 1.20 for `x ≥ 2`, `m = φ(n)`, `n ≥ 2`. -/
theorem cyclotomic_eval_parity_ge_two (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : 2 ≤ x) :
    (Even n.primeFactors.card →
      (x - 1) * x ^ (Nat.totient n - 1) < (cyclotomic n ℝ).eval x ∧
        (cyclotomic n ℝ).eval x < x ^ (Nat.totient n)) ∧
    (Odd n.primeFactors.card →
      x ^ (Nat.totient n) < (cyclotomic n ℝ).eval x ∧
        (cyclotomic n ℝ).eval x < x ^ (Nat.totient n + 1) / (x - 1)) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < 1 / x := by positivity
  have hy2 : 1 / x ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hx
  have hR := cyclotomic_eval_reciprocal n hn x hx0.ne'
  obtain ⟨k, hk⟩ : ∃ k, Nat.totient n = k + 1 :=
    ⟨Nat.totient n - 1, by have := Nat.totient_pos.2 (by omega : 0 < n); omega⟩
  obtain ⟨h1, h2⟩ := cyclotomic_eval_parity n hn (1 / x) hy0 hy2
  have hxk : 0 < x ^ (Nat.totient n) := pow_pos hx0 _
  have hx1 : 0 < x - 1 := by linarith
  have hid1 : x ^ (Nat.totient n) * (1 - 1 / x) = (x - 1) * x ^ (Nat.totient n - 1) := by
    rw [hk]; simp only [Nat.add_sub_cancel]; field_simp; ring
  have hid2 : x ^ (Nat.totient n) * (1 / (1 - 1 / x)) = x ^ (Nat.totient n + 1) / (x - 1) := by
    have : 1 - 1 / x = (x - 1) / x := by field_simp
    rw [this]; field_simp; ring
  refine ⟨fun he => ?_, fun ho => ?_⟩
  · obtain ⟨a, b⟩ := h1 he
    rw [hR]
    refine ⟨?_, ?_⟩
    · rw [← hid1]; exact mul_lt_mul_of_pos_left a hxk
    · calc _ < x ^ (Nat.totient n) * 1 := mul_lt_mul_of_pos_left b hxk
        _ = _ := mul_one _
  · obtain ⟨a, b⟩ := h2 ho
    rw [hR]
    refine ⟨?_, ?_⟩
    · calc x ^ (Nat.totient n) = x ^ (Nat.totient n) * 1 := (mul_one _).symm
        _ < _ := mul_lt_mul_of_pos_left a hxk
    · rw [← hid2]; exact mul_lt_mul_of_pos_left b hxk

end CycloParity

end
