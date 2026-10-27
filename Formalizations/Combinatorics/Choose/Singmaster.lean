/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Singmaster's bound on binomial multiplicities

For `a ≥ 2`, the set of positions `(n, k)` with `k ≤ n` and `C(n, k) = a` is finite with at most
`2 + 2 ⌊log₂ a⌋` elements (Singmaster, 1971). Positions with `2k ≤ n` satisfy
`2^k ≤ C(2k, k) ≤ C(n, k) = a`, so `1 ≤ k ≤ log₂ a`, and for fixed `k ≥ 1` the map `n ↦ C(n, k)` is
strictly increasing, so each such `k` gives at most one position; the positions with `2k > n` inject
into these by `(n, k) ↦ (n, n - k)`. The proof gives `2 ⌊log₂ a⌋`.

## Main results

* `Singmaster.ncard_choose_eq_le`: positions of a >= 2 in Pascal triangle: finite, at most 2 + 2 log2 a

## References

* D. Singmaster, *How often does an integer occur as a binomial coefficient?*, Amer. Math. Monthly 78 (1971), 385–386.
-/

@[expose] public section

namespace Singmaster

private lemma two_pow_le_centralBinom (k : ℕ) : 2 ^ k ≤ Nat.centralBinom k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := Nat.succ_mul_centralBinom_succ k
    have : (k + 1) * (2 * Nat.centralBinom k) ≤ (k + 1) * Nat.centralBinom (k + 1) := by
      rw [h]; nlinarith [Nat.centralBinom_pos k]
    have h2 := Nat.le_of_mul_le_mul_left this (Nat.succ_pos k)
    rw [pow_succ]; omega

private lemma two_pow_le_choose {n k : ℕ} (h : 2 * k ≤ n) : 2 ^ k ≤ n.choose k :=
  (two_pow_le_centralBinom k).trans
    (by rw [Nat.centralBinom_eq_two_mul_choose]; exact Nat.choose_le_choose k h)

private lemma choose_strict {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    n.choose k < (n + 1).choose k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.choose_succ_succ']
  have := Nat.choose_pos (show j ≤ n by omega)
  omega

private lemma choose_inj {n m k : ℕ} (hk : 1 ≤ k) (hn : k ≤ n) (hm : k ≤ m)
    (h : n.choose k = m.choose k) : n = m := by
  have key : ∀ n m : ℕ, k ≤ n → n < m → n.choose k < m.choose k := by
    intro n m hn hnm
    induction m, hnm using Nat.le_induction with
    | base => exact choose_strict hk hn
    | succ m hm ih => exact ih.trans (choose_strict hk (by omega))
  rcases lt_trichotomy n m with h1 | h1 | h1
  · exact absurd h (key n m hn h1).ne
  · exact h1
  · exact absurd h (key m n hm h1).ne'

/-- **Singmaster's bound (1971).** An integer `a ≥ 2` occurs at most `2 + 2 ⌊log₂ a⌋` times in
Pascal's triangle: the positions `(n, k)` with `k ≤ n` and `C(n, k) = a` form a finite set with at
most that many elements. -/
theorem ncard_choose_eq_le (a : ℕ) (ha : 2 ≤ a) :
    {p : ℕ × ℕ | p.2 ≤ p.1 ∧ Nat.choose p.1 p.2 = a}.Finite ∧
    {p : ℕ × ℕ | p.2 ≤ p.1 ∧ Nat.choose p.1 p.2 = a}.ncard ≤ 2 + 2 * Nat.log 2 a := by
  set P : Set (ℕ × ℕ) := {p : ℕ × ℕ | p.2 ≤ p.1 ∧ Nat.choose p.1 p.2 = a} with hP
  set A : Set (ℕ × ℕ) := {p | p ∈ P ∧ 2 * p.2 ≤ p.1} with hA
  set B : Set (ℕ × ℕ) := {p | p ∈ P ∧ ¬ 2 * p.2 ≤ p.1} with hB
  have hPAB : P = A ∪ B := by
    ext p; simp only [hA, hB, Set.mem_union, Set.mem_ofPred_eq]; tauto
  have hmaps : Set.MapsTo Prod.snd A (Set.Icc 1 (Nat.log 2 a)) := by
    rintro ⟨n, k⟩ ⟨⟨hkn, hc⟩, h2⟩
    simp only at hkn hc h2
    refine ⟨?_, Nat.le_log_of_pow_le (by norm_num) (hc ▸ two_pow_le_choose h2)⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at hc; omega
    · exact hk
  have hinj : Set.InjOn Prod.snd A := by
    rintro ⟨n, k⟩ ⟨⟨hkn, hc⟩, h2⟩ ⟨m, k'⟩ ⟨⟨hkm, hc'⟩, h2'⟩ (hk : k = k')
    subst hk
    simp only at hkn hc h2 hkm hc' h2'
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at hc; omega
      · exact hk
    rw [choose_inj hk1 hkn hkm (hc.trans hc'.symm)]
  have hAfin : A.Finite := Set.Finite.of_injOn hmaps hinj (Set.toFinite _)
  have hAc : A.ncard ≤ Nat.log 2 a := by
    have := Set.ncard_le_ncard_of_injOn Prod.snd hmaps hinj (Set.toFinite (Set.Icc 1 (Nat.log 2 a)))
    simpa [Set.ncard_eq_toFinset_card'] using this
  let g : ℕ × ℕ → ℕ × ℕ := fun p => (p.1, p.1 - p.2)
  have hgm : Set.MapsTo g B A := by
    rintro ⟨n, k⟩ ⟨⟨hkn, hc⟩, h2⟩
    simp only at hkn hc h2
    refine ⟨⟨by simp [g], ?_⟩, by simp [g]; omega⟩
    simp only [g]
    rw [Nat.choose_symm hkn]; exact hc
  have hgi : Set.InjOn g B := by
    rintro ⟨n, k⟩ ⟨⟨hkn, hc⟩, h2⟩ ⟨m, k'⟩ ⟨⟨hkm, hc'⟩, h2'⟩ hg
    simp only [g, Prod.mk.injEq] at hg hkn hkm
    obtain ⟨rfl, h⟩ := hg
    simp only [Prod.mk.injEq, true_and]; omega
  have hBfin : B.Finite := Set.Finite.of_injOn hgm hgi hAfin
  have hBc : B.ncard ≤ A.ncard := Set.ncard_le_ncard_of_injOn g hgm hgi hAfin
  refine ⟨hPAB ▸ hAfin.union hBfin, ?_⟩
  rw [hPAB]
  have := Set.ncard_union_le A B
  omega

end Singmaster
