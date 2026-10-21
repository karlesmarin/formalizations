/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Data.Nat.Count
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Finset.Prod

/-!
# The number of monomials `e₂^a e₃^b` of weight `k`

The power sum `s_k` at `e₁ = 0` is, by Newton–Waring, a combination with no vanishing coefficient
of the monomials `e₂^a e₃^b` with `2a + 3b = k`; dividing out the common monomial leaves a
polynomial `Q_k` in `u = e₂³/e₃²` with `deg Q_k = #{(a, b) ∈ ℕ² | 2a + 3b = k} − 1`. This file
proves the combinatorial half of that statement: the count of pairs in closed form,
`#{(a, b) | 2a + 3b = k} = ⌊k/6⌋ + 1 − [k ≡ 1 (mod 6)]`, and that for `k ≥ 3` it equals `1`
(i.e. `deg Q_k = 0`) exactly for `k ∈ {3, 4, 5, 7}`.

The identification of `deg Q_k + 1` with this count (Newton–Waring with nonvanishing
coefficients) is not formalized here.

## Main results

* `P3d.card_degreePairs`: `#{(a, b) | 2a + 3b = k} = k / 6 + 1 − [k % 6 = 1]`, for every `k`.
* `P3d.card_degreePairs_eq_one_iff`: for `k ≥ 3`, the count is `1` iff `k ∈ {3, 4, 5, 7}`.

## References

* C. Marín, *Subsets of F_p with two prescribed moments, Part II: every exponent*, Zenodo (2026),
  doi:10.5281/zenodo.22886543, Proposition `prop:grado`.
-/

@[expose] public section

open Finset

namespace P3d

/-- The pairs `(a, b) ∈ ℕ²` with `2a + 3b = k` (both coordinates are at most `k`). -/
def degreePairs (k : ℕ) : Finset (ℕ × ℕ) :=
  {p ∈ range (k + 1) ×ˢ range (k + 1) | 2 * p.1 + 3 * p.2 = k}

lemma mem_degreePairs {k : ℕ} {p : ℕ × ℕ} : p ∈ degreePairs k ↔ 2 * p.1 + 3 * p.2 = k := by
  simp only [degreePairs, mem_filter, mem_product, mem_range]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨⟨by omega, by omega⟩, h⟩

/-- Projecting to `b`: the pairs are in bijection with `b < k / 3 + 1`, `b ≡ k (mod 2)`. -/
lemma card_degreePairs_eq_count (k : ℕ) :
    (degreePairs k).card = (k / 3 + 1).count (· ≡ k [MOD 2]) := by
  rw [Nat.count_eq_card_filter_range]
  refine card_bij (fun p _ => p.2) ?_ ?_ ?_
  · intro p hp
    rw [mem_degreePairs] at hp
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), by simp only [Nat.ModEq]; omega⟩
  · intro p hp q hq h
    rw [mem_degreePairs] at hp hq
    ext
    · omega
    · exact h
  · intro b hb
    obtain ⟨hb1, hb2⟩ := mem_filter.mp hb
    rw [mem_range] at hb1
    simp only [Nat.ModEq] at hb2
    exact ⟨((k - 3 * b) / 2, b), mem_degreePairs.mpr (by omega), rfl⟩

/-- **Proposition `prop:grado`** (combinatorial half):
`#{(a, b) ∈ ℕ² | 2a + 3b = k} = ⌊k/6⌋ + 1 − [k ≡ 1 (mod 6)]`. -/
theorem card_degreePairs (k : ℕ) :
    (degreePairs k).card = k / 6 + 1 - if k % 6 = 1 then 1 else 0 := by
  rw [card_degreePairs_eq_count, Nat.count_modEq_card _ (by norm_num)]
  split_ifs <;> omega

/-- For `k ≥ 3` the count is `1` (`deg Q_k = 0`) exactly for `k ∈ {3, 4, 5, 7}`. -/
theorem card_degreePairs_eq_one_iff {k : ℕ} (hk : 3 ≤ k) :
    (degreePairs k).card = 1 ↔ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 7 := by
  rw [card_degreePairs]
  split_ifs <;> omega

end P3d
