/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Hlawka's inequality and its generalisation by Djoković

Hlawka's inequality `‖x+y‖ + ‖y+z‖ + ‖z+x‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ + ‖x+y+z‖` in a real inner product
space, and its generalisation (Djoković 1963; Smiley–Smiley 1964): for `n ≥ 3` vectors, with `d_k`
the sum of the norms of all `k`-element subsums, `d_2 + ⋯ + d_{n-1} ≤ (2^(n-2) - 1) (d_1 + d_n)`.
The general case is equivalent to `4F ≤ 2^n (d_1 + d_n)`, where `F` sums the norms of the subsums
over all subsets; it is proved by strong induction on the number of vectors, merging two of them,
`x a` and `x b`, into `x a + x b`: the subsets containing both or neither form the merged family,
and each subset `T` containing exactly one of them is handled by Hlawka's inequality for
`(Σ_T, x a, x b)`.

## Main results

* `Hlawka.norm_add_add_le`: Hlawka's inequality for three vectors
* `Hlawka.generalised`: d_2 + ... + d_(n-1) <= (2^(n-2) - 1)(d_1 + d_n) for n >= 3 vectors

## References

* D. Ž. Djoković, *Generalizations of Hlawka's inequality*, Glasnik Mat.-Fiz. Astronom. 18 (1963), 169–175.
* D. M. Smiley and M. F. Smiley, *The polygonal inequalities*, Amer. Math. Monthly 71 (1964), 755–760.
-/

@[expose] public section

open Finset

namespace Hlawka

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Hlawka's inequality** (`n = 3`). -/
theorem norm_add_add_le (x y z : E) :
    ‖x + y‖ + ‖y + z‖ + ‖z + x‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ + ‖x + y + z‖ := by
  have e1 := norm_add_sq_real x y
  have e2 := norm_add_sq_real y z
  have e3 := norm_add_sq_real z x
  have e4 := norm_add_sq_real (x + y) z
  rw [inner_add_left] at e4
  have c1 := real_inner_comm x z
  have h : ‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2 + ‖x + y + z‖ ^ 2
      = ‖x + y‖ ^ 2 + ‖y + z‖ ^ 2 + ‖z + x‖ ^ 2 := by
    linarith
  have t1 : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
  have t2 : ‖y + z‖ ≤ ‖y‖ + ‖z‖ := norm_add_le y z
  have t3 : ‖z + x‖ ≤ ‖z‖ + ‖x‖ := norm_add_le z x
  have u1 : ‖x + y‖ ≤ ‖x + y + z‖ + ‖z‖ := by
    calc ‖x + y‖ = ‖(x + y + z) - z‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖x + y + z‖ + ‖z‖ := norm_sub_le _ _
  have u2 : ‖y + z‖ ≤ ‖x + y + z‖ + ‖x‖ := by
    calc ‖y + z‖ = ‖(x + y + z) - x‖ := by congr 1; abel
      _ ≤ ‖x + y + z‖ + ‖x‖ := norm_sub_le _ _
  have u3 : ‖z + x‖ ≤ ‖x + y + z‖ + ‖y‖ := by
    calc ‖z + x‖ = ‖(x + y + z) - y‖ := by congr 1; abel
      _ ≤ ‖x + y + z‖ + ‖y‖ := norm_sub_le _ _
  have key : (‖x‖ + ‖y‖ + ‖z‖ + ‖x + y + z‖) *
      (‖x‖ + ‖y‖ + ‖z‖ + ‖x + y + z‖ - ‖x + y‖ - ‖y + z‖ - ‖z + x‖) =
      (‖x‖ + ‖y‖ - ‖x + y‖) * (‖z‖ - ‖x + y‖ + ‖x + y + z‖) +
      (‖y‖ + ‖z‖ - ‖y + z‖) * (‖x‖ - ‖y + z‖ + ‖x + y + z‖) +
      (‖z‖ + ‖x‖ - ‖z + x‖) * (‖y‖ - ‖z + x‖ + ‖x + y + z‖) := by
    linear_combination h
  have p1 : 0 ≤ (‖x‖ + ‖y‖ - ‖x + y‖) * (‖z‖ - ‖x + y‖ + ‖x + y + z‖) :=
    mul_nonneg (by linarith) (by linarith)
  have p2 : 0 ≤ (‖y‖ + ‖z‖ - ‖y + z‖) * (‖x‖ - ‖y + z‖ + ‖x + y + z‖) :=
    mul_nonneg (by linarith) (by linarith)
  have p3 : 0 ≤ (‖z‖ + ‖x‖ - ‖z + x‖) * (‖y‖ - ‖z + x‖ + ‖x + y + z‖) :=
    mul_nonneg (by linarith) (by linarith)
  have n1 := norm_nonneg x
  have n2 := norm_nonneg y
  have n3 := norm_nonneg z
  have n4 := norm_nonneg (x + y + z)
  rcases (add_nonneg (add_nonneg (add_nonneg n1 n2) n3) n4).eq_or_lt with hs | hs
  · linarith
  · by_contra hc
    have hneg : (‖x‖ + ‖y‖ + ‖z‖ + ‖x + y + z‖ - ‖x + y‖ - ‖y + z‖ - ‖z + x‖) < 0 := by
      linarith
    have := mul_neg_of_pos_of_neg hs hneg
    linarith

/-- Pointwise step: Hlawka rewritten for merging two summands. -/
private lemma pt (u v w : E) :
    ‖u‖ + ‖w + u‖ + ‖v + u‖ + ‖v + (w + u)‖ ≤
      2 * (‖u‖ + ‖v + w + u‖) + (‖v‖ + ‖w‖ - ‖v + w‖) := by
  have h := norm_add_add_le u v w
  have e1 : ‖v + u‖ = ‖u + v‖ := by rw [add_comm]
  have e2 : ‖v + (w + u)‖ = ‖u + v + w‖ := by congr 1; abel
  have e3 : ‖v + w + u‖ = ‖u + v + w‖ := by congr 1; abel
  linarith

private lemma sum_powerset_four {ι : Type*} [DecidableEq ι] {a b : ι} {R : Finset ι}
    (ha : a ∉ insert b R) (hb : b ∉ R) (f : Finset ι → ℝ) :
    ∑ S ∈ (insert a (insert b R)).powerset, f S =
      ∑ T ∈ R.powerset, (f T + f (insert b T) + f (insert a T) + f (insert a (insert b T))) := by
  rw [Finset.sum_powerset_insert ha, Finset.sum_powerset_insert hb f,
    Finset.sum_powerset_insert hb (fun t => f (insert a t))]
  simp only [Finset.sum_add_distrib]
  ring

/-- Key induction: `4 · F ≤ 2^m (d₁ + dₘ)` where `F` sums the norms of all subsums. -/
private lemma key {ι : Type*} [DecidableEq ι] (m : ℕ) : ∀ (s : Finset ι) (x : ι → E),
    s.card = m →
    4 * ∑ S ∈ s.powerset, ‖∑ i ∈ S, x i‖ ≤
      2 ^ m * (∑ i ∈ s, ‖x i‖ + ‖∑ i ∈ s, x i‖) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro s x hs
  rcases m with _ | _ | k
  · have h0 : s = ∅ := Finset.card_eq_zero.mp hs
    subst h0
    simp
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hs
    rw [show ({a} : Finset ι) = insert a ∅ from rfl,
      Finset.sum_powerset_insert (Finset.notMem_empty a)]
    simp
    linarith
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
    have hb' : b ∈ s.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
    have hsR : insert a (insert b ((s.erase a).erase b)) = s := by
      rw [Finset.insert_erase hb', Finset.insert_erase ha]
    have haR : a ∉ insert b ((s.erase a).erase b) := by simp [hab]
    have hbR : b ∉ (s.erase a).erase b := by simp
    obtain ⟨R, hsR', haR', hbR'⟩ : ∃ R : Finset ι, insert a (insert b R) = s ∧
        a ∉ insert b R ∧ b ∉ R := ⟨_, hsR, haR, hbR⟩
    subst hsR'
    have haR2 : a ∉ R := fun h => haR' (Finset.mem_insert_of_mem h)
    have hRc : R.card = k := by
      rw [Finset.card_insert_of_notMem haR', Finset.card_insert_of_notMem hbR'] at hs
      omega
    -- merged family
    let x' : ι → E := fun i => if i = a then x a + x b else x i
    have hx' : ∀ T ⊆ R, ∑ i ∈ T, x' i = ∑ i ∈ T, x i := by
      intro T hT
      refine Finset.sum_congr rfl fun i hi => ?_
      have hia : i ≠ a := fun h => haR2 (h ▸ hT hi)
      simp [x', hia]
    have hnx' : ∑ i ∈ R, ‖x' i‖ = ∑ i ∈ R, ‖x i‖ := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hia : i ≠ a := fun h => haR2 (h ▸ hi)
      simp [x', hia]
    have IH := ih (k + 1) (by omega) (insert a R) x' (by rw [Finset.card_insert_of_notMem haR2, hRc])
    have hF' : ∑ S ∈ (insert a R).powerset, ‖∑ i ∈ S, x' i‖ =
        ∑ T ∈ R.powerset, (‖∑ i ∈ T, x i‖ + ‖x a + x b + ∑ i ∈ T, x i‖) := by
      rw [Finset.sum_powerset_insert haR2, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun T hT => ?_
      have hTR := Finset.mem_powerset.mp hT
      have haT : a ∉ T := fun h => haR2 (hTR h)
      rw [Finset.sum_insert haT, hx' T hTR]
      simp [x']
    have hF : ∑ S ∈ (insert a (insert b R)).powerset, ‖∑ i ∈ S, x i‖ ≤
        ∑ T ∈ R.powerset, (2 * (‖∑ i ∈ T, x i‖ + ‖x a + x b + ∑ i ∈ T, x i‖) +
          (‖x a‖ + ‖x b‖ - ‖x a + x b‖)) := by
      rw [sum_powerset_four haR' hbR']
      refine Finset.sum_le_sum fun T hT => ?_
      have hTR := Finset.mem_powerset.mp hT
      have haT : a ∉ T := fun h => haR2 (hTR h)
      have hbT : b ∉ T := fun h => hbR' (hTR h)
      have haT' : a ∉ insert b T := fun h => haR' (by
        rcases Finset.mem_insert.mp h with h | h
        · exact Finset.mem_insert.mpr (Or.inl h)
        · exact Finset.mem_insert_of_mem (hTR h))
      rw [Finset.sum_insert hbT, Finset.sum_insert haT, Finset.sum_insert haT',
        Finset.sum_insert hbT]
      exact pt (∑ i ∈ T, x i) (x a) (x b)
    have hsum : ∑ T ∈ R.powerset, (2 * (‖∑ i ∈ T, x i‖ + ‖x a + x b + ∑ i ∈ T, x i‖) +
          (‖x a‖ + ‖x b‖ - ‖x a + x b‖)) =
        2 * ∑ S ∈ (insert a R).powerset, ‖∑ i ∈ S, x' i‖ +
          2 ^ k * (‖x a‖ + ‖x b‖ - ‖x a + x b‖) := by
      rw [hF', Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_powerset,
        hRc, nsmul_eq_mul]
      push_cast
      ring
    rw [Finset.sum_insert haR2, Finset.sum_insert haR2, hnx', hx' R (subset_refl R)] at IH
    have e1 : x' a = x a + x b := by simp [x']
    rw [e1] at IH
    rw [Finset.sum_insert haR', Finset.sum_insert hbR', Finset.sum_insert haR',
      Finset.sum_insert hbR', ← add_assoc (x a) (x b)]
    have p1 : (2 : ℝ) ^ (k + 1 + 1) = 4 * 2 ^ k := by ring
    have p2 : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [p2] at IH
    rw [p1]
    have := hF.trans_eq hsum
    nlinarith [this, IH]

private lemma sum_range_split (h : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ range (m + 4), h k = h 0 + h 1 + ∑ k ∈ Icc 2 (m + 2), h k + h (m + 3) := by
  induction m with
  | zero => simp [Finset.sum_range_succ]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, show m + 1 + 2 = (m + 2) + 1 from rfl,
      Finset.sum_Icc_succ_top (a := 2) (b := m + 2) (by omega)]
    ring

/-- **Generalised Hlawka inequality (Djoković 1963; Smiley–Smiley 1964).** For `n ≥ 3` vectors of a real
inner product space, write `d_k` for the sum of the norms of all `k`-element subsums. Then
`d_2 + ⋯ + d_{n-1} ≤ (2^(n-2) - 1) (d_1 + d_n)`. For `n = 3` this is Hlawka's inequality
`‖x+y‖ + ‖y+z‖ + ‖z+x‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ + ‖x+y+z‖`. -/
theorem generalised {n : ℕ} (hn : 3 ≤ n) (x : Fin n → E) :
    ∑ k ∈ Finset.Icc 2 (n - 1), ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ‖∑ i ∈ S, x i‖
      ≤ (2 ^ (n - 2) - 1 : ℝ) * (∑ i, ‖x i‖ + ‖∑ i, x i‖) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hK := key (m + 3) (Finset.univ : Finset (Fin (m + 3))) x (by simp)
  have hF : ∑ S ∈ (Finset.univ : Finset (Fin (m + 3))).powerset, ‖∑ i ∈ S, x i‖ =
      ∑ k ∈ range (m + 4), ∑ S ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard k,
        ‖∑ i ∈ S, x i‖ := by
    rw [Finset.powerset_card_biUnion,
      Finset.sum_biUnion ((Finset.pairwise_disjoint_powersetCard _).set_pairwise _)]
    simp
  rw [hF, sum_range_split (fun k => ∑ S ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard k,
    ‖∑ i ∈ S, x i‖)] at hK
  have h0 : ∑ S ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard 0, ‖∑ i ∈ S, x i‖ = 0 := by
    simp
  have h1 : ∑ S ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard 1, ‖∑ i ∈ S, x i‖ =
      ∑ i, ‖x i‖ := by
    rw [Finset.powersetCard_one, Finset.sum_map]
    simp
  have hn : ∑ S ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard (m + 3), ‖∑ i ∈ S, x i‖ =
      ‖∑ i, x i‖ := by
    have := Finset.powersetCard_self (Finset.univ : Finset (Fin (m + 3)))
    rw [Finset.card_univ, Fintype.card_fin] at this
    rw [this]
    simp
  simp only [h0, h1, hn] at hK
  have e1 : m + 3 - 1 = m + 2 := rfl
  have e2 : m + 3 - 2 = m + 1 := rfl
  rw [e1, e2]
  have p : (2 : ℝ) ^ (m + 3) = 4 * 2 ^ (m + 1) := by ring
  rw [p] at hK
  nlinarith [hK]

end Hlawka
