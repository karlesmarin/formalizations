/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.Combinatorics.Choose.MiddleBinomialDivisors
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Nat.Count
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# `n + k` usually divides `C(2n, n)` (Pomerance, Theorem 2)

C. Pomerance, *Divisors of the middle binomial coefficient*, Amer. Math. Monthly 122 (2015) 636–644,
Theorem 2: for every positive integer `k`, the set of `n` with `n + k ∣ C(2n, n)` has asymptotic
density `1`. For primes `p ≥ 2k` the power of `p` in `n + k` always divides `C(2n, n)` (inequality (4),
`MiddleBinomial.padicValNat_add_le`); for each of the finitely many primes `p < 2k`, the `n` where it
fails are few, because `C(2n, n)` has many factors `p` for most `n` (Lemma 2 of the paper: few `n ≤ x`
have few carries in base `p`) and few `n ≤ x` have `p^j ∣ n + k` with `j` large.

## Main results

* `MiddleBinomial.tendsto_density_add_dvd_centralBinom`: for k >= 1 the proportion of n < x with n + k dividing C(2n, n) tends to 1 (Theorem 2)

## References

* C. Pomerance, Divisors of the middle binomial coefficient, Amer. Math. Monthly 122 (2015) 636–644,
  doi:10.4169/amer.math.monthly.122.7.636.
-/

@[expose] public section

namespace MiddleBinomial

open Nat Filter Topology

/-- Kummer for the central binomial coefficient (copy of the private lemma of
`MiddleBinomialDivisors`). -/
private lemma central_val' {p : ℕ} [Fact p.Prime] (n b : ℕ) (hb : Nat.log p (2 * n) < b) :
    padicValNat p (centralBinom n) =
      (Finset.filter (fun i => p ^ i ≤ 2 * (n % p ^ i)) (Finset.Ico 1 b)).card := by
  rw [Nat.centralBinom_eq_two_mul_choose, padicValNat_choose (by omega) hb]
  have h : 2 * n - n = n := by omega
  rw [h]
  congr 1
  apply Finset.filter_congr
  intro i _
  omega

/-! ### Counting residues in blocks -/

private lemma count_block (q : ℕ) (P : ℕ → Prop) [DecidablePred P] (M : ℕ) :
    Nat.count (fun n => P (n % q)) (q * M) = M * Nat.count P q := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.mul_succ, Nat.count_add, ih, Nat.succ_mul]
    congr 1
    rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
    congr 1
    apply Finset.filter_congr
    intro k hk
    rw [Finset.mem_range] at hk
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hk]

private lemma block_le {q : ℕ} (hq : 0 < q) (P : ℕ → Prop) [DecidablePred P] (x : ℕ) :
    ((Finset.range x).filter (fun n => P (n % q))).card ≤
      (x / q + 1) * ((Finset.range q).filter P).card := by
  have hcb := count_block q P (x / q + 1)
  simp only [Nat.count_eq_card_filter_range] at hcb
  rw [← hcb]
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  refine ⟨?_, hn.2⟩
  have h1 := Nat.div_add_mod x q
  have h2 := Nat.mod_lt x hq
  nlinarith [hn.1]

/-! ### Large digits -/

/-- Number of "large" base-`p` digits (those `d` with `p ≤ 2 d`) among the first `D` digits of `r`. -/
private def cntL (p D r : ℕ) : ℕ :=
  ∑ i ∈ Finset.range D, if p ≤ 2 * (r / p ^ i % p) then 1 else 0

private lemma cntL_succ (D r : ℕ) {p : ℕ} :
    cntL p (D + 1) r = (if p ≤ 2 * (r % p) then 1 else 0) + cntL p D (r / p) := by
  unfold cntL
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ', Nat.div_div_eq_div_mul]

/-- Number of `r < p ^ D` with fewer than `J` large digits. -/
private def fS (p D J : ℕ) : ℕ :=
  ((Finset.range (p ^ D)).filter (fun r => cntL p D r < J)).card

private lemma fS_zero (p D : ℕ) : fS p D 0 = 0 := by simp [fS]

private lemma fS_le (p D J : ℕ) : fS p D J ≤ p ^ D := by
  unfold fS
  exact (Finset.card_filter_le _ _).trans (by simp)

private lemma fS_succ {p : ℕ} (hp : 0 < p) (D J : ℕ) :
    fS p (D + 1) (J + 1) ≤ fS p D (J + 1) * ((p + 1) / 2) + fS p D J * p := by
  set A := (Finset.range (p ^ D)).filter (fun r => cntL p D r < J + 1) with hA
  set B := (Finset.range (p ^ D)).filter (fun r => cntL p D r < J) with hB
  have sub : (Finset.range (p ^ (D + 1))).filter (fun r => cntL p (D + 1) r < J + 1) ⊆
      Finset.image (fun q : ℕ × ℕ => q.2 + p * q.1)
        (A ×ˢ Finset.range ((p + 1) / 2) ∪ B ×ˢ Finset.range p) := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨hr1, hr2⟩ := hr
    rw [Finset.mem_image]
    have hm : r / p < p ^ D := by
      rw [Nat.div_lt_iff_lt_mul hp]
      rw [pow_succ] at hr1
      exact hr1
    refine ⟨(r / p, r % p), ?_, ?_⟩
    · rw [cntL_succ] at hr2
      rw [Finset.mem_union, Finset.mem_product, Finset.mem_product]
      by_cases hl : p ≤ 2 * (r % p)
      · right
        simp only [hl, ↓reduceIte] at hr2
        refine ⟨?_, ?_⟩
        · rw [hB]
          simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨hm, by omega⟩
        · simpa using Nat.mod_lt r hp
      · left
        simp only [hl, ↓reduceIte] at hr2
        refine ⟨?_, ?_⟩
        · rw [hA]
          simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨hm, by omega⟩
        · simp only [Finset.mem_range]
          omega
    · exact Nat.mod_add_div r p
  calc fS p (D + 1) (J + 1)
      ≤ (Finset.image (fun q : ℕ × ℕ => q.2 + p * q.1)
        (A ×ˢ Finset.range ((p + 1) / 2) ∪ B ×ˢ Finset.range p)).card := Finset.card_le_card sub
    _ ≤ (A ×ˢ Finset.range ((p + 1) / 2) ∪ B ×ˢ Finset.range p).card := Finset.card_image_le
    _ ≤ (A ×ˢ Finset.range ((p + 1) / 2)).card + (B ×ˢ Finset.range p).card :=
        Finset.card_union_le _ _
    _ = fS p D (J + 1) * ((p + 1) / 2) + fS p D J * p := by
        rw [Finset.card_product, Finset.card_product, Finset.card_range, Finset.card_range]
        rfl

/-! ### Analysis -/

private lemma tendsto_zero_of_rec (a b : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hb : Tendsto b atTop (𝓝 0)) (h : ∀ n, a (n + 1) ≤ 2 / 3 * a n + b n) :
    Tendsto a atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hb (ε / 6) (by positivity)
  set m : ℕ → ℝ := fun n => max (a n - ε / 2) 0 with hm
  have hstep : ∀ n, N ≤ n → m (n + 1) ≤ 2 / 3 * m n := by
    intro n hn
    have := hN n hn
    rw [Real.dist_eq, sub_zero] at this
    have hb' := (abs_lt.1 this).2
    have h1 := h n
    simp only [hm]
    apply max_le
    · have : 0 ≤ max (a n - ε / 2) 0 := le_max_right _ _
      have h3 : a n - ε / 2 ≤ max (a n - ε / 2) 0 := le_max_left _ _
      linarith
    · have : 0 ≤ max (a n - ε / 2) 0 := le_max_right _ _
      linarith
  have hpow : ∀ j, m (N + j) ≤ (2 / 3) ^ j * m N := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have := hstep (N + j) (by omega)
      calc m (N + j + 1) ≤ 2 / 3 * m (N + j) := this
        _ ≤ 2 / 3 * ((2 / 3) ^ j * m N) := by linarith
        _ = (2 / 3) ^ (j + 1) * m N := by ring
  have ht : Tendsto (fun j : ℕ => (2 / 3 : ℝ) ^ j * m N) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 / 3 : ℝ)) (by norm_num)
      (by norm_num)).mul_const (m N)
    simpa using this
  obtain ⟨J0, hJ0⟩ := Metric.tendsto_atTop.1 ht (ε / 2) (by positivity)
  refine ⟨N + J0, fun n hn => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (by omega : N ≤ n)
  have h1 := hJ0 j (by omega)
  rw [Real.dist_eq, sub_zero] at h1 ⊢
  have h2 := hpow j
  have h3 : a (N + j) - ε / 2 ≤ m (N + j) := le_max_left _ _
  have h4 := ha (N + j)
  have h5 := (abs_lt.1 h1).2
  rw [abs_of_nonneg h4]
  linarith

private lemma tendsto_fS {p : ℕ} (hp : 2 ≤ p) (J : ℕ) :
    Tendsto (fun D : ℕ => (fS p D J : ℝ) / (p : ℝ) ^ D) atTop (𝓝 0) := by
  induction J with
  | zero => simp [fS_zero]
  | succ J ih =>
    apply tendsto_zero_of_rec _ _ (fun D => by positivity) ih
    intro D
    have hp0 : (0 : ℝ) < p := by positivity
    have hpD : (0 : ℝ) < (p : ℝ) ^ D := by positivity
    have h1 := fS_succ (by omega : 0 < p) D J
    have h2 : 3 * ((p + 1) / 2) ≤ 2 * p := by omega
    have h1' : (fS p (D + 1) (J + 1) : ℝ) ≤
        (fS p D (J + 1) : ℝ) * (((p + 1) / 2 : ℕ) : ℝ) + (fS p D J : ℝ) * p := by
      exact_mod_cast h1
    have h2' : 3 * (((p + 1) / 2 : ℕ) : ℝ) ≤ 2 * p := by exact_mod_cast h2
    have hF : (0 : ℝ) ≤ fS p D (J + 1) := by positivity
    rw [div_le_iff₀ (by positivity)]
    have e : (2 / 3 * ((fS p D (J + 1) : ℝ) / (p : ℝ) ^ D) + (fS p D J : ℝ) / (p : ℝ) ^ D) *
        (p : ℝ) ^ (D + 1) = (2 / 3 * (fS p D (J + 1) : ℝ) + fS p D J) * p := by
      field_simp
      ring
    rw [e]
    nlinarith

/-! ### Carries -/

private lemma cntL_le_padic {p : ℕ} (hp : p.Prime) (D n : ℕ) :
    cntL p D (n % p ^ D) ≤ padicValNat p (centralBinom n) := by
  have : Fact p.Prime := ⟨hp⟩
  have hb : Nat.log p (2 * n) < max (Nat.log p (2 * n) + 1) (D + 1) :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  rw [central_val' n _ hb]
  unfold cntL
  rw [← Finset.card_filter]
  apply Finset.card_le_card_of_injOn (fun i => i + 1)
  · intro i hi
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico]
    beta_reduce
    refine ⟨⟨by omega, lt_of_lt_of_le (by omega) (le_max_right _ _)⟩, ?_⟩
    have e1 : n % p ^ (i + 1) = (n % p ^ D) % p ^ (i + 1) :=
      (Nat.mod_mod_of_dvd n (pow_dvd_pow p (by omega))).symm
    rw [e1, Nat.mod_pow_succ]
    have hpos : 0 < p ^ i := pow_pos hp.pos i
    have h3 := Nat.mul_le_mul_left (p ^ i) hi.2
    rw [pow_succ]
    nlinarith [Nat.zero_le (n % p ^ D % p ^ i)]
  · intro a _ b _ h
    simpa using h

/-! ### Per-prime bound -/

private lemma card_dvd_le_one (Q k : ℕ) :
    ((Finset.range Q).filter (fun r => (r + k) % Q = 0)).card ≤ 1 := by
  apply Finset.card_le_one.2
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_range] at ha hb
  have h : a + k ≡ b + k [MOD Q] := by
    unfold Nat.ModEq
    rw [ha.2, hb.2]
  have h2 := Nat.ModEq.add_right_cancel' k h
  unfold Nat.ModEq at h2
  rwa [Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt hb.1] at h2

private lemma tendsto_bad {p : ℕ} (hp : p.Prime) (k : ℕ) :
    Tendsto (fun x : ℕ => (((Finset.range x).filter
      (fun n => padicValNat p (centralBinom n) < padicValNat p (n + k))).card : ℝ) / x)
      atTop (𝓝 0) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (4 / ε) hpR
  obtain ⟨D, hD0⟩ := Metric.tendsto_atTop.1 (tendsto_fS hp2 J) (ε / 4) (by positivity)
  have hD := hD0 D le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hD
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * (fS p D J : ℝ) / ε + 4 / ε)
  have hQpos : (0 : ℝ) < (p : ℝ) ^ J := by positivity
  have hqpos : (0 : ℝ) < (p : ℝ) ^ D := by positivity
  have hQ' : 4 < (p : ℝ) ^ J * ε := (div_lt_iff₀ hε).1 hJ
  refine ⟨N, fun x hx => ?_⟩
  have hxN : (N : ℝ) ≤ x := by exact_mod_cast hx
  have h4 : (0 : ℝ) < 4 / ε := by positivity
  have h4F : (0 : ℝ) ≤ 4 * (fS p D J : ℝ) / ε := by positivity
  have hxpos : (0 : ℝ) < x := by linarith
  have hF : 4 * (fS p D J : ℝ) < x * ε := (div_lt_iff₀ hε).1 (by linarith)
  have hx1 : 4 < (x : ℝ) * ε := (div_lt_iff₀ hε).1 (by linarith)
  set bad := (Finset.range x).filter
    (fun n => padicValNat p (centralBinom n) < padicValNat p (n + k)) with hbad
  set A := (Finset.range x).filter (fun n => cntL p D (n % p ^ D) < J) with hA
  set C := (Finset.range x).filter (fun n => (n % p ^ J + k) % p ^ J = 0) with hC
  have hsub : bad ⊆ A ∪ C := by
    intro n hn
    rw [hbad, Finset.mem_filter] at hn
    rw [Finset.mem_union]
    by_cases h : padicValNat p (centralBinom n) < J
    · left
      rw [hA, Finset.mem_filter]
      exact ⟨hn.1, lt_of_le_of_lt (cntL_le_padic hp D n) h⟩
    · right
      rw [hC, Finset.mem_filter]
      refine ⟨hn.1, ?_⟩
      have h1 : p ^ J ∣ n + k :=
        (pow_dvd_pow p (by omega : J ≤ padicValNat p (n + k))).trans pow_padicValNat_dvd
      rw [Nat.mod_add_mod]
      exact Nat.mod_eq_zero_of_dvd h1
  have hAc : A.card ≤ (x / p ^ D + 1) * fS p D J :=
    block_le (pow_pos hp.pos D) (fun r => cntL p D r < J) x
  have hCc : C.card ≤ (x / p ^ J + 1) * 1 :=
    (block_le (pow_pos hp.pos J) (fun r => (r + k) % p ^ J = 0) x).trans
      (Nat.mul_le_mul_left _ (card_dvd_le_one _ _))
  have hcard : bad.card ≤ (x / p ^ D + 1) * fS p D J + (x / p ^ J + 1) * 1 :=
    (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (_root_.add_le_add hAc hCc))
  have hcardR : (bad.card : ℝ) ≤ (((x / p ^ D : ℕ) : ℝ) + 1) * fS p D J +
      (((x / p ^ J : ℕ) : ℝ) + 1) * 1 := by exact_mod_cast hcard
  have e1 : ((x / p ^ D : ℕ) : ℝ) ≤ (x : ℝ) / (p : ℝ) ^ D := by
    have := Nat.cast_div_le (α := ℝ) (m := x) (n := p ^ D)
    simpa using this
  have e2 : ((x / p ^ J : ℕ) : ℝ) ≤ (x : ℝ) / (p : ℝ) ^ J := by
    have := Nat.cast_div_le (α := ℝ) (m := x) (n := p ^ J)
    simpa using this
  have hF0 : (0 : ℝ) ≤ fS p D J := by positivity
  have e3 : (x : ℝ) / (p : ℝ) ^ D * fS p D J = x * ((fS p D J : ℝ) / (p : ℝ) ^ D) := by ring
  have e4 : (x : ℝ) / (p : ℝ) ^ J < x * ε / 4 := by
    rw [div_lt_iff₀ hQpos]
    nlinarith
  have e5 : (x : ℝ) * ((fS p D J : ℝ) / (p : ℝ) ^ D) ≤ x * (ε / 4) :=
    mul_le_mul_of_nonneg_left hD.le hxpos.le
  have e6 : ((x / p ^ D : ℕ) : ℝ) * fS p D J ≤ x * (ε / 4) := by
    calc ((x / p ^ D : ℕ) : ℝ) * fS p D J ≤ (x : ℝ) / (p : ℝ) ^ D * fS p D J :=
          mul_le_mul_of_nonneg_right e1 hF0
      _ = _ := e3
      _ ≤ _ := e5
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hxpos]
  nlinarith

/-- A prime power in `n + k` not dividing `C(2n, n)` happens at a small prime. -/
private lemma exists_small_prime {k : ℕ} (hk : 1 ≤ k) (n : ℕ)
    (h : ¬ (n + k ∣ centralBinom n)) :
    ∃ p, p.Prime ∧ p < 2 * k ∧ padicValNat p (centralBinom n) < padicValNat p (n + k) := by
  by_contra hcon
  push Not at hcon
  apply h
  rw [← Nat.factorization_prime_le_iff_dvd (by omega) (centralBinom_pos n).ne']
  intro p hp
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  by_cases hlt : p < 2 * k
  · exact hcon p hp hlt
  · have : Fact p.Prime := ⟨hp⟩
    exact padicValNat_add_le hk (by omega) n

/-- **Pomerance, Theorem 2.** For every `k ≥ 1`, the proportion of `n < x` with `n + k ∣ C(2n, n)`
tends to `1`. -/
theorem tendsto_density_add_dvd_centralBinom (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun x : ℕ => (((Finset.range x).filter (fun n => n + k ∣ centralBinom n)).card : ℝ) / x)
      atTop (𝓝 1) := by
  set S := (Finset.range (2 * k)).filter Nat.Prime with hS
  set badp : ℕ → ℕ → Finset ℕ := fun p x => (Finset.range x).filter
    (fun n => padicValNat p (centralBinom n) < padicValNat p (n + k)) with hbp
  have hsum : Tendsto (fun x : ℕ => ∑ p ∈ S, ((badp p x).card : ℝ) / x) atTop (𝓝 0) := by
    have := tendsto_finsetSum S (fun p hp => tendsto_bad (Finset.mem_filter.1 hp).2 k)
    simpa using this
  have hlow : Tendsto (fun x : ℕ => 1 - ∑ p ∈ S, ((badp p x).card : ℝ) / x) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with x hx
    have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
    set good := (Finset.range x).filter (fun n => n + k ∣ centralBinom n) with hgood
    have h1 : good.card + ((Finset.range x).filter (fun n => ¬ n + k ∣ centralBinom n)).card = x := by
      rw [hgood, Finset.card_filter_add_card_filter_not, Finset.card_range]
    have hsub : (Finset.range x).filter (fun n => ¬ n + k ∣ centralBinom n) ⊆
        S.biUnion (fun p => badp p x) := by
      intro n hn
      rw [Finset.mem_filter] at hn
      obtain ⟨p, hp, hpk, hv⟩ := exists_small_prime hk n hn.2
      rw [Finset.mem_biUnion]
      refine ⟨p, Finset.mem_filter.2 ⟨Finset.mem_range.2 hpk, hp⟩, ?_⟩
      rw [hbp]
      exact Finset.mem_filter.2 ⟨hn.1, hv⟩
    have h2 : ((Finset.range x).filter (fun n => ¬ n + k ∣ centralBinom n)).card ≤
        ∑ p ∈ S, (badp p x).card :=
      (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have h1R : (good.card : ℝ) + (((Finset.range x).filter
        (fun n => ¬ n + k ∣ centralBinom n)).card : ℝ) = x := by exact_mod_cast h1
    have h2R : (((Finset.range x).filter (fun n => ¬ n + k ∣ centralBinom n)).card : ℝ) ≤
        ∑ p ∈ S, ((badp p x).card : ℝ) := by exact_mod_cast h2
    have hs : ∑ p ∈ S, ((badp p x).card : ℝ) / x = (∑ p ∈ S, ((badp p x).card : ℝ)) / x := by
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]
    rw [hs, le_div_iff₀ hxpos, sub_mul, one_mul, div_mul_cancel₀ _ hxpos.ne']
    linarith
  · filter_upwards [eventually_ge_atTop 1] with x hx
    have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
    rw [div_le_one hxpos]
    have : ((Finset.range x).filter (fun n => n + k ∣ centralBinom n)).card ≤ x := by
      simpa using Finset.card_filter_le (Finset.range x) (fun n => n + k ∣ centralBinom n)
    exact_mod_cast this

end MiddleBinomial
