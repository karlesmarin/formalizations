/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.Wilson
public import Mathlib.NumberTheory.Bertrand

/-!
# Willans' formula for the n-th prime

The `n`-th prime is `1 + Σ_{i=1}^{2^n} ⌊(n / Σ_{j=1}^{i} ⌊cos² (π ((j - 1)! + 1) / j)⌋)^{1/n}⌋`
(Willans, 1964). By Wilson's theorem (Mathlib's `Nat.prime_iff_fac_equiv_neg_one`) the inner floor
is `1` exactly when `j = 1` or `j` is prime, so the inner sum is `π(i) + 1`; the outer floor is `1`
when `π(i) < n` and `0` otherwise (bounding `y^n < 2^n` instead of `n^{1/n}`), and Bertrand's
postulate gives `p_n ≤ 2^n`, so the outer sum counts `1 ≤ i < p_n`.

## Main results

* `Willans.floor_cos_sq_eq`: floor(cos^2(pi((j-1)!+1)/j)) is 1 iff j = 1 or j is prime (Wilson)
* `Willans.nth_prime_eq`: Willans' formula for the n-th prime

## References

* C. P. Willans, *On formulae for the nth prime number*, Math. Gazette 48 (1964), 413–415.
-/

@[expose] public section

open Finset

namespace Willans

/-- **Wilson floor.** For `j ≥ 1`, `⌊cos²(π((j-1)!+1)/j)⌋` is `1` if `j = 1` or `j` is prime,
and `0` otherwise. -/
theorem floor_cos_sq_eq (j : ℕ) (hj : 1 ≤ j) :
    ⌊Real.cos (Real.pi * (((j - 1).factorial : ℝ) + 1) / j) ^ 2⌋ =
      if j = 1 ∨ j.Prime then 1 else 0 := by
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  have key : j ∣ (j - 1).factorial + 1 ↔ (j = 1 ∨ j.Prime) := by
    by_cases h1 : j = 1
    · subst h1; simp
    · rw [Nat.prime_iff_fac_equiv_neg_one h1, ← ZMod.natCast_eq_zero_iff]
      push_cast
      simp [h1, eq_neg_iff_add_eq_zero]
  have hsin : Real.sin (Real.pi * (((j - 1).factorial : ℝ) + 1) / j) = 0 ↔ j ∣ (j - 1).factorial + 1 := by
    rw [Real.sin_eq_zero_iff]
    constructor
    · rintro ⟨n, hn⟩
      have h2 : (n : ℝ) * j = (((j - 1).factorial : ℝ) + 1) := by
        have := Real.pi_pos
        field_simp at hn
        nlinarith [hn]
      have h3 : n * (j : ℤ) = (((j - 1).factorial + 1 : ℕ) : ℤ) := by exact_mod_cast h2
      have : (j : ℤ) ∣ (((j - 1).factorial + 1 : ℕ) : ℤ) := ⟨n, by rw [← h3]; ring⟩
      exact_mod_cast this
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have : (((j - 1).factorial : ℝ) + 1) = j * k := by exact_mod_cast hk
      rw [this]; push_cast; field_simp
  have hc : Real.cos (Real.pi * (((j - 1).factorial : ℝ) + 1) / j) ^ 2 =
      1 - Real.sin (Real.pi * (((j - 1).factorial : ℝ) + 1) / j) ^ 2 := by
    rw [Real.cos_sq']
  split_ifs with h
  · rw [hc, (hsin.mpr (key.mpr h)), Int.floor_eq_iff]; norm_num
  · have hne : Real.sin (Real.pi * (((j - 1).factorial : ℝ) + 1) / j) ≠ 0 := fun h0 =>
      h (key.mp (hsin.mp h0))
    rw [Int.floor_eq_iff]
    refine ⟨by simp; positivity, ?_⟩
    rw [hc]
    have := pow_pos (abs_pos.mpr hne) 2
    rw [sq_abs] at this
    push_cast; linarith

open scoped Nat.Prime

/-- Step 2: the inner sum is `π(i) + 1`. -/
theorem sum_floor_eq (i : ℕ) (hi : 1 ≤ i) :
    ∑ j ∈ Icc (1 : ℕ) i,
      (⌊Real.cos (Real.pi * (((j - 1).factorial : ℝ) + 1) / j) ^ 2⌋ : ℝ) = ((π i + 1 : ℕ) : ℝ) := by
  induction i, hi using Nat.le_induction with
  | base =>
    rw [Finset.Icc_self, Finset.sum_singleton, floor_cos_sq_eq 1 le_rfl]
    simp [Nat.primeCounting_one]
  | succ i hi ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, floor_cos_sq_eq (i + 1) (by omega)]
    have h1 : π (i + 1) = π i + if (i + 1).Prime then 1 else 0 := by
      show Nat.count Nat.Prime (i + 1 + 1) = Nat.count Nat.Prime (i + 1) + _
      rw [Nat.count_succ]
    rw [h1]
    have h3 : i ≠ 0 := by omega
    by_cases hp : (i + 1).Prime <;> simp [hp, h3]

/-- Step 3: the `n`-th root floor is an indicator. -/
theorem floor_root_eq (n k : ℕ) (hn : 1 ≤ n) :
    ⌊((n : ℝ) / ((k + 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / n)⌋ = if k < n then 1 else 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hx0 : 0 ≤ (n : ℝ) / ((k + 1 : ℕ) : ℝ) := by positivity
  split_ifs with h
  · have hx1 : 1 ≤ (n : ℝ) / ((k + 1 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hk0]; simp only [one_mul]; exact_mod_cast h
    have hxn : (n : ℝ) / ((k + 1 : ℕ) : ℝ) ≤ n := by
      rw [div_le_iff₀ hk0]; push_cast; nlinarith [hn0, (by positivity : (0 : ℝ) ≤ k)]
    rw [Int.floor_eq_iff]
    refine ⟨by simpa using Real.one_le_rpow hx1 (by positivity), ?_⟩
    set y := ((n : ℝ) / ((k + 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / n) with hy
    have hyn : y ^ n = (n : ℝ) / ((k + 1 : ℕ) : ℝ) := by
      rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0, one_div_mul_cancel hn0.ne', Real.rpow_one]
    by_contra hcon
    push Not at hcon
    have h2 : (2 : ℝ) ^ n ≤ y ^ n :=
      pow_le_pow_left₀ (by norm_num) (by push_cast at hcon; linarith) n
    have h3 : (n : ℝ) < 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
    linarith
  · push Not at h
    have hx1 : (n : ℝ) / ((k + 1 : ℕ) : ℝ) < 1 := by
      rw [div_lt_one hk0]; exact_mod_cast Nat.lt_succ_of_le h
    rw [Int.floor_eq_iff]
    refine ⟨by simpa using Real.rpow_nonneg hx0 _, ?_⟩
    have := Real.rpow_lt_one hx0 hx1 (by positivity : (0 : ℝ) < 1 / n)
    simpa using this

/-- `p_k ≤ 2^(k+1)` for the `k`-th prime indexed from 0. -/
theorem nth_prime_le (k : ℕ) : Nat.nth Nat.Prime k ≤ 2 ^ (k + 1) := by
  induction k with
  | zero => simp [Nat.nth_prime_zero_eq_two]
  | succ k ih =>
    have hp := Nat.prime_nth_prime k
    obtain ⟨q, hq, hlt, hle⟩ :=
      Nat.exists_prime_lt_and_le_two_mul (Nat.nth Nat.Prime k) hp.ne_zero
    have : Nat.nth Nat.Prime (k + 1) ≤ q :=
      (Nat.nth_add_one_le_iff Nat.infinite_setOfPred_prime hq).mpr hlt
    calc Nat.nth Nat.Prime (k + 1) ≤ q := this
      _ ≤ 2 * Nat.nth Nat.Prime k := hle
      _ ≤ 2 * 2 ^ (k + 1) := by omega
      _ = 2 ^ (k + 1 + 1) := by ring

/-- **Willans' formula** for the `n`-th prime. -/
theorem nth_prime_eq (n : ℕ) (hn : 1 ≤ n) :
    (Nat.nth Nat.Prime (n - 1) : ℝ) =
      1 + ∑ i ∈ Finset.Icc (1 : ℕ) (2 ^ n),
        (⌊((n : ℝ) / ∑ j ∈ Finset.Icc (1 : ℕ) i,
            (⌊Real.cos (Real.pi * (((j - 1).factorial : ℝ) + 1) / j) ^ 2⌋ : ℝ)) ^ ((1 : ℝ) / n)⌋ : ℝ) := by
  set p := Nat.nth Nat.Prime (n - 1) with hpdef
  have hp2 : 2 ≤ p := (Nat.prime_nth_prime _).two_le
  have hpb : p ≤ 2 ^ n := by
    have := nth_prime_le (n - 1)
    rwa [Nat.sub_add_cancel hn] at this
  have hterm : ∀ i ∈ Icc (1 : ℕ) (2 ^ n),
      (⌊((n : ℝ) / ∑ j ∈ Finset.Icc (1 : ℕ) i,
        (⌊Real.cos (Real.pi * (((j - 1).factorial : ℝ) + 1) / j) ^ 2⌋ : ℝ)) ^ ((1 : ℝ) / n)⌋ : ℝ)
        = if i < p then 1 else 0 := by
    intro i hi
    rw [mem_Icc] at hi
    rw [sum_floor_eq i hi.1, floor_root_eq n (π i) hn]
    have hiff : π i < n ↔ i < p := by
      have := Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime (a := n - 1) (b := i + 1)
      change n - 1 < π i ↔ p < i + 1 at this
      omega
    by_cases h : i < p
    · simp [h, hiff.mpr h]
    · simp [h, (not_congr hiff).mpr h]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have : (Icc (1 : ℕ) (2 ^ n)).filter (· < p) = Icc 1 (p - 1) := by
    ext i; simp only [mem_filter, mem_Icc]; omega
  rw [this, Nat.card_Icc]
  have : (p - 1 + 1 - 1 : ℕ) = p - 1 := by omega
  rw [this]
  have : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [this]; ring

end Willans
