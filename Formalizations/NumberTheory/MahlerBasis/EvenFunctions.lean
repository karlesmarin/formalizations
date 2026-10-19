/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.NumberTheory.MahlerBasis.ParityAndKernel
public import Mathlib.RingTheory.Binomial
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination

/-!
# Mahler coefficients of an even function

If `G = ∑_{i ≤ N} c_i C(x, i)` (`x : ℤ`, values in a commutative ring) is even, then for odd
`k ≤ N`, `2 c_k = ∑_{k < i ≤ N} (−1)^i C(i − 1, i − k) c_i`: compare coefficients in
`G(−x) = G(x)`, using `C(−x, i) = (−1)^i ∑_k C(i − 1, i − k) C(x, k)` (Vandermonde).

## Main results

* `LemaP2.choose_neg_vandermonde`: the expansion of `C(−x, i)`.
* `LemaP2.mahler_unique`: Mahler coefficients are determined by the values on `ℕ`.
* `LemaP2.lemP_two`: the statement above.

## References

* C. Marín, *Reading Iwasawa λ-invariants from Mahler matrices modulo p: programs, data and Lean
  files*, Zenodo (2026), doi:10.5281/zenodo.23085315.
-/

@[expose] public section

open Finset

namespace LemaP2

variable {R : Type*} [CommRing R]

/-! `mahlerZ N c x = ∑_{i ≤ N} c_i C(x, i)` for `x : ℤ` is `ConjeturaC.mahlerZ`. -/
open ConjeturaC (mahlerZ)

/-- **Vandermonde, as in the proof of `lem:P`(2).** For `x ∈ ℕ`:
`C(-x, i) = (-1)^i ∑_{k ≤ i} C(i-1, i-k) C(x, k)`. -/
theorem choose_neg_vandermonde (x i : ℕ) :
    Ring.choose (-(x : ℤ)) i =
      (-1) ^ i * ∑ k ∈ range (i + 1), ((Nat.choose (i - 1) (i - k) * Nat.choose x k : ℕ) : ℤ) := by
  rcases i with _ | j
  · simp
  · rw [Ring.choose_neg, show (x : ℤ) + ((j + 1 : ℕ) : ℤ) - 1 = ((x + j : ℕ) : ℤ) by push_cast; ring,
      Ring.choose_natCast, Nat.add_choose_eq, Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Units.smul_def, Int.coe_negOnePow_natCast, smul_eq_mul]
    push_cast
    congr 1
    apply sum_congr rfl; intro k _; ring

/-- Mahler coefficients are unique: if `∑_{k ≤ N} e_k C(x, k) = 0` for every `x ∈ ℕ`, then
`e_k = 0` for `k ≤ N`. -/
theorem mahler_unique (N : ℕ) (e : ℕ → R)
    (h : ∀ x : ℕ, ∑ k ∈ range (N + 1), e k * (Nat.choose x k : R) = 0) :
    ∀ k ≤ N, e k = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hx := h k
    rw [sum_congr rfl (g := fun j => if j = k then e k else 0)] at hx
    · rwa [sum_ite_eq', ite_eq_left (mem_range.mpr (by omega))] at hx
    · intro j hj
      rcases lt_trichotomy j k with hlt | heq | hgt
      · rw [ih j hlt (by omega), zero_mul, ite_eq_right (by omega)]
      · subst heq; simp
      · rw [Nat.choose_eq_zero_of_lt hgt, Nat.cast_zero, mul_zero, ite_eq_right (by omega)]

/-- `G(-x)` in Mahler form: its `k`-th coefficient is `∑_{k ≤ i ≤ N} (-1)^i C(i-1, i-k) c_i`. -/
theorem mahlerZ_neg (N : ℕ) (c : ℕ → R) (x : ℕ) :
    mahlerZ N c (-(x : ℤ)) = ∑ k ∈ range (N + 1),
      (∑ i ∈ Icc k N, (-1) ^ i * (Nat.choose (i - 1) (i - k) : R) * c i) * (Nat.choose x k : R) := by
  unfold mahlerZ
  simp_rw [choose_neg_vandermonde]
  push_cast
  simp_rw [mul_sum, sum_mul]
  rw [sum_comm' (t' := range (N + 1)) (s' := fun k => Icc k N)]
  · apply sum_congr rfl; intro k _; apply sum_congr rfl; intro i _
    ring
  · intro i k; simp only [mem_range, mem_Icc]; omega

/-- **`lem:P`(2).** If `G = ∑_{i ≤ N} c_i C(x, i)` is even on `ℤ`, then for every odd
`k ≤ N`, `2 c_k = ∑_{k < i ≤ N} (-1)^i C(i-1, i-k) c_i`. Valid over any commutative ring. -/
theorem lemP_two (N : ℕ) (c : ℕ → R) (heven : ∀ x : ℤ, mahlerZ N c (-x) = mahlerZ N c x)
    {k : ℕ} (hk : Odd k) (hkN : k ≤ N) :
    2 * c k = ∑ i ∈ Ioc k N, (-1) ^ i * (Nat.choose (i - 1) (i - k) : R) * c i := by
  have hu := mahler_unique N
    (fun k => (∑ i ∈ Icc k N, (-1) ^ i * (Nat.choose (i - 1) (i - k) : R) * c i) - c k)
    (fun x => by
      have h1 := heven x
      rw [mahlerZ_neg] at h1
      simp only [sub_mul, sum_sub_distrib]
      rw [h1]; unfold mahlerZ
      rw [sub_eq_zero]; apply sum_congr rfl; intro i _
      rw [Ring.choose_natCast]; push_cast; ring) k hkN
  rw [Icc_eq_cons_Ioc hkN, sum_cons, Odd.neg_one_pow hk, Nat.sub_self, Nat.choose_zero_right,
    Nat.cast_one] at hu
  linear_combination -hu

/-! ## Controls -/

/-- `x² = C(x,1) + 2 C(x,2)` is even, `c = (0, 1, 2)`; at `k = 1` the identity reads
`2 · 1 = (-1)² C(1,1) · 2`. -/
example : (2 : ℤ) * 1 =
    ∑ i ∈ Ioc 1 2, (-1) ^ i * (Nat.choose (i - 1) (i - 1) : ℤ) * (if i = 2 then 2 else 0) := by
  decide

/-- `C(-2, 3) = -4`, computed both ways. -/
example : Ring.choose (-((2 : ℕ) : ℤ)) 3 = -4 := by
  rw [choose_neg_vandermonde]; decide

end LemaP2
