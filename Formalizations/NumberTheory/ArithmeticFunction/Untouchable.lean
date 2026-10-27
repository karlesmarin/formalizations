/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# 2 and 5 are untouchable

A number `m` is *untouchable* if no `n` has aliquot sum `s(n) = σ(n) - n = m`. Both `2` and `5` are
untouchable: a prime has `s(p) = 1`, and a composite `n` has the proper divisors `1` and
`n / minFac n ≥ √n`, so `s(n) ≥ 1 + √n`; only finitely many `n` remain, and they are checked.

As a consequence, `σ(x) mod x = 5` forces `σ(x) ≥ 2x + 5`: the case `σ(x) = x + 5` of the open
statement `a 5 = 0` of OEIS A076495 (no `x` with `σ(x) mod x = 5`) is impossible, and what remains open
is `σ(x) = k x + 5` with `k ≥ 2`.

## Main results

* `Untouchable.untouchable_two`: no n has sum of proper divisors 2
* `Untouchable.untouchable_five`: no n has sum of proper divisors 5
* `Untouchable.two_mul_add_five_le_sigma`: sigma x mod x = 5 forces sigma x >= 2x + 5

## References

* OEIS A005114 (untouchable numbers); OEIS A076495 (smallest x with sigma(x) mod x = n; a(5) = 0 is
  open, searched beyond 1.5 * 10^14).
-/

@[expose] public section

namespace Untouchable

open scoped ArithmeticFunction.sigma

/-- `m` is untouchable when no natural number has aliquot sum `m`. -/
def IsUntouchable (m : ℕ) : Prop :=
  ∀ n : ℕ, ∑ d ∈ n.properDivisors, d ≠ m

private lemma exists_big_divisor {n : ℕ} (h2 : 2 ≤ n) (hp : ¬ n.Prime) :
    ∃ b, 2 ≤ b ∧ n ≤ b * b ∧ 1 + b ≤ ∑ d ∈ n.properDivisors, d := by
  have hap : n.minFac.Prime := Nat.minFac_prime (by omega)
  have ha2 := hap.two_le
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  obtain ⟨b, hb⟩ := Nat.minFac_dvd n
  set a := n.minFac
  have hab : a ≤ b := by nlinarith
  have hbn : b < n := by nlinarith
  refine ⟨b, by omega, by nlinarith, ?_⟩
  have hsub : ({1, b} : Finset ℕ) ⊆ n.properDivisors := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rw [Nat.mem_properDivisors]
    rcases hd with rfl | rfl
    · exact ⟨one_dvd _, by omega⟩
    · exact ⟨⟨a, by rw [hb]; ring⟩, hbn⟩
  have := Finset.sum_le_sum_of_subset (f := id) hsub
  rwa [Finset.sum_pair (by omega)] at this

theorem untouchable_two : IsUntouchable 2 := by
  intro n h
  by_cases h2 : n < 2
  · interval_cases n <;> simp at h
  by_cases hp : n.Prime
  · have := Nat.sum_properDivisors_eq_one_iff_prime.2 hp
    omega
  · obtain ⟨b, hb, -, hs⟩ := exists_big_divisor (by omega) hp
    omega

theorem untouchable_five : IsUntouchable 5 := by
  intro n h
  by_cases h2 : n < 2
  · interval_cases n <;> simp at h
  by_cases hp : n.Prime
  · have := Nat.sum_properDivisors_eq_one_iff_prime.2 hp
    omega
  · obtain ⟨b, hb, hn, hs⟩ := exists_big_divisor (by omega) hp
    have hn16 : n ≤ 16 := by nlinarith
    interval_cases n <;> revert h <;> decide

/-- If `σ(x) mod x = 5`, then `σ(x) ≥ 2x + 5`: the quotient `⌊σ(x)/x⌋` is at least `2`, since the
quotient `1` would make `x` have aliquot sum `5`. -/
theorem two_mul_add_five_le_sigma {x : ℕ} (h : σ 1 x % x = 5) : 2 * x + 5 ≤ σ 1 x := by
  have hx : 5 < x := by
    by_contra hle
    rcases Nat.eq_zero_or_pos x with rfl | hpos
    · simp at h
    · have := Nat.mod_lt (σ 1 x) hpos
      omega
  have hσ : σ 1 x = ∑ d ∈ x.properDivisors, d + x := by
    rw [ArithmeticFunction.sigma_one_apply]
    exact Nat.sum_divisors_eq_sum_properDivisors_add_self
  have hd := Nat.div_add_mod (σ 1 x) x
  rw [h] at hd
  have h5 := untouchable_five x
  rcases Nat.lt_or_ge (σ 1 x / x) 2 with hq | hq
  · interval_cases hqq : σ 1 x / x <;> omega
  · nlinarith

end Untouchable
