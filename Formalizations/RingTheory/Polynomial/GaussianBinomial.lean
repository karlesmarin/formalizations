/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Tactic.Ring

/-!
# The elementary symmetric functions of a geometric progression

The Gaussian binomial coefficient `[n k]_X` (by the `q`-Pascal rule) and the identity
`e_k(1, X, …, X^{n−1}) = X^{k(k−1)/2} [n k]_X` (Lemma 2.1 of «A segment of the character ring»): induction on `n`,
splitting `{1, X, …, X^n} = {1} ∪ X·{1, …, X^{n−1}}` and using `e_{k+1}(a, s) = e_{k+1}(s) + a e_k(s)` and
`e_k(c·s) = c^k e_k(s)`.

## Main definitions

* `GaussBinom.gaussBinom`: the Gaussian binomial coefficient in `ℤ[X]`.

## Main results

* `GaussBinom.esymm_geometric`: the identity above.
* `GaussBinom.esymm_cons_succ`, `GaussBinom.esymm_map_mul`: the two rules for `Multiset.esymm`.
-/

@[expose] public section

open Polynomial

namespace GaussBinom

/-- The Gaussian binomial coefficient `[n k]_X`, by the `q`-Pascal rule
`[n+1, k+1] = [n, k] + X^{k+1} [n, k+1]`. -/
noncomputable def gaussBinom : ℕ → ℕ → ℤ[X]
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => gaussBinom n k + X ^ (k + 1) * gaussBinom n (k + 1)

theorem range_succ_map_pow (n : ℕ) :
    (Multiset.range (n + 1)).map (fun i => (X : ℤ[X]) ^ i)
      = 1 ::ₘ ((Multiset.range n).map fun i => X * (X : ℤ[X]) ^ i) := by
  rw [← Multiset.coe_range, List.range_succ_eq_map]
  simp only [Multiset.map_coe, List.map_cons, pow_zero, List.map_map]
  rw [← Multiset.cons_coe, ← Multiset.map_coe, Multiset.coe_range]
  congr 1
  exact Multiset.map_congr rfl fun i _ => by simp [Function.comp_apply, pow_succ']

theorem esymm_cons_succ (a : ℤ[X]) (s : Multiset ℤ[X]) (k : ℕ) :
    (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.prod_cons,
    Multiset.sum_map_mul_left]

theorem esymm_map_mul (c : ℤ[X]) (s : Multiset ℤ[X]) (k : ℕ) :
    (s.map fun x => c * x).esymm k = c ^ k * s.esymm k := by
  rw [Multiset.esymm, Multiset.esymm, Multiset.powersetCard_map, Multiset.map_map, ← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun t ht => ?_)
  rw [Function.comp_apply, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, Multiset.map_id',
    (Multiset.mem_powersetCard.mp ht).2]

theorem tri_succ (k : ℕ) : k + k * (k - 1) / 2 = (k + 1) * k / 2 := by
  cases k with
  | zero => rfl
  | succ m =>
    rw [Nat.add_sub_cancel, show (m + 1 + 1) * (m + 1) = (m + 1) * m + 2 * (m + 1) by ring,
      Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
    omega

theorem esymm_range_zero (k : ℕ) :
    ((Multiset.range 0).map fun i => (X : ℤ[X]) ^ i).esymm k = X ^ (k * (k - 1) / 2) * gaussBinom 0 k := by
  cases k <;> simp [Multiset.esymm, gaussBinom, Multiset.powersetCard_zero_right]

/-- Lemma 2.1 of character-ring-segment: the `k`-th elementary symmetric function of `1, X, …, X^{n−1}` is
`X^{k(k−1)/2} [n k]_X`. -/
theorem esymm_geometric (n k : ℕ) :
    ((Multiset.range n).map fun i => (X : ℤ[X]) ^ i).esymm k = X ^ (k * (k - 1) / 2) * gaussBinom n k := by
  induction n generalizing k with
  | zero => exact esymm_range_zero k
  | succ n ih =>
    cases k with
    | zero => simp [gaussBinom]
    | succ k =>
      have hmap : ((Multiset.range n).map fun i => X * (X : ℤ[X]) ^ i)
          = ((Multiset.range n).map fun i => (X : ℤ[X]) ^ i).map fun x => X * x := by
        rw [Multiset.map_map]; rfl
      rw [range_succ_map_pow, esymm_cons_succ, hmap, esymm_map_mul, esymm_map_mul, ih, ih, gaussBinom, one_mul]
      rw [show (k + 1) * (k + 1 - 1) / 2 = (k + 1) * k / 2 by simp]
      rw [← tri_succ k]
      ring

end GaussBinom
