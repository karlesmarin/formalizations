/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fin.SuccPred

/-!
# The Johnson bound for the independence number of the Johnson graph (Erdős Problem 835)

An independent set of the Johnson graph `J(n, k)` is a family of `k`-subsets of `Fin n` pairwise
meeting in at most `k - 2` points, that is, a constant-weight binary code of distance 4. Johnson's
bound `α(J(n, k)) ≤ johnsonBound n 4 k` is proved by recursion on `(n, k)`: double counting the
pairs (point, member) and shortening the members through a point. Definitions and statement are
copied verbatim from formal-conjectures.

## Main results

* `Erdos835.indepNum_johnson_le_johnsonBound`: α(J(n, k)) ≤ johnsonBound n 4 k (Johnson 1962; formal-conjectures, Erdős Problem 835)
* `Erdos835.card_le_johnsonBound`: a family of w-subsets of Fin n pairwise meeting in ≤ w - 2 points has at most johnsonBound n 4 w members

## References

* S. M. Johnson, «A new upper bound for error-correcting codes», IRE Trans. Inform. Theory 8 (1962) 203–207.
* erdosproblems.com/835; definitions and statement copied verbatim from google-deepmind/formal-conjectures (ErdosProblems/835.lean and FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Johnson.lean).
-/

@[expose] public section

namespace Finset
variable {α : Type*} {s t : Finset α}

lemma card_lt_card_iff_of_subset (hst : s ⊆ t) : #s < #t ↔ s ≠ t := by
  rw [← not_le, eq_iff_card_le_of_subset hst]

end Finset

open Finset

namespace SimpleGraph
variable {n k : ℕ}

/--
The Johnson graph $J(n, k)$ has as vertices the $k$-subsets of an $n$-set.
Two vertices are adjacent if their intersection has size $k - 1$.
-/
@[simps -isSimp]
def johnson (n k : ℕ) : SimpleGraph {s : Finset (Fin n) // #s = k} where
  Adj s t := #(s.val ∩ t.val) + 1 = k
  symm.symm s t h := by simpa [inter_comm]
  loopless.irrefl := by simp +contextual

scoped notation "J(" n ", " k ")" => johnson n k

@[inherit_doc] scoped notation "α(" G ")" => indepNum G

lemma johnson_adj_iff_ge {s t : {s : Finset (Fin n) // #s = k}} :
    J(n, k).Adj s t ↔ s ≠ t ∧ k ≤ #(s.val ∩ t.val) + 1 := by
  obtain ⟨s, hs⟩ := s
  obtain ⟨t, ht⟩ := t
  simp only [johnson_adj, le_antisymm_iff (α := ℕ), ne_eq, Subtype.mk.injEq, and_congr_left_iff]
  rintro h
  constructor
  · rintro hst rfl
    simp at hst
    omega
  · rintro hst
    rw [Nat.add_one_le_iff, ← hs, card_lt_card_iff_of_subset inter_subset_left]
    simp only [ne_eq, inter_eq_left]
    contrapose! hst
    exact eq_of_subset_of_card_le hst (by simp [*])

lemma not_johnson_adj_iff_lt {s t : {s : Finset (Fin n) // #s = k}} :
    ¬ J(n, k).Adj s t ↔ s = t ∨ #(s.val ∩ t.val) + 1 < k := by simp [johnson_adj_iff_ge]; tauto

end SimpleGraph

open SimpleGraph
open scoped Nat
namespace Erdos835

variable {n k : ℕ}

/-- Johnson's upper bound on the maximum size `A(n, d, w)` of a `n`-dimensional binary code of
distance `d` and weight `w` is as follows:
* If `d > 2 * w`, then `A(n, d, w) = 1`.
* If `d ≤ 2 * w`, then `A(n, d, w) ≤ ⌊n / w * A(n - 1, d, w - 1)⌋`. -/
def johnsonBound : ℕ → ℕ → ℕ → ℕ
  | 0, _d, _w => 1
  | _n, _d, 0 => 1
  | n + 1, d, w + 1 => if 2 * (w + 1) < d then 1 else (n + 1) * johnsonBound n d w / (w + 1)

/-! ### Proof -/

/-- A family with no two distinct members is a subsingleton. -/
private lemma card_le_one_of_forall_ne {β : Type*} {C : Finset β}
    (h : ∀ s ∈ C, ∀ t ∈ C, s ≠ t → False) : #C ≤ 1 :=
  Finset.card_le_one.2 fun s hs t ht => by_contra fun hst => h s hs t ht hst

/-- Removing the point `x` and relabelling `Fin (n + 1) \ {x}` as `Fin n`. -/
private def shrink (x : Fin (n + 1)) (s : Finset (Fin (n + 1))) : Finset (Fin n) :=
  univ.filter fun i => x.succAbove i ∈ s

private lemma map_shrink (x : Fin (n + 1)) (s : Finset (Fin (n + 1))) :
    (shrink x s).map x.succAboveEmb = s.erase x := by
  ext y
  simp only [shrink, mem_map, mem_filter, mem_univ, true_and, Fin.coe_succAboveEmb, mem_erase]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨Fin.succAbove_ne x i, hi⟩
  · rintro ⟨hy, hys⟩
    obtain ⟨z, rfl⟩ := Fin.exists_succAbove_eq hy
    exact ⟨z, hys, rfl⟩

private lemma card_shrink (x : Fin (n + 1)) (s : Finset (Fin (n + 1))) :
    #(shrink x s) = #(s.erase x) := by
  rw [← map_shrink, card_map]

private lemma card_shrink_inter (x : Fin (n + 1)) (s t : Finset (Fin (n + 1))) :
    #(shrink x s ∩ shrink x t) = #((s ∩ t).erase x) := by
  rw [← card_map x.succAboveEmb, map_inter, map_shrink, map_shrink]
  congr 1
  ext y
  simp only [mem_inter, mem_erase]
  tauto

/-- Johnson's bound for constant-weight families with pairwise intersections `≤ w - 2`. -/
theorem card_le_johnsonBound :
    ∀ (n w : ℕ) (C : Finset (Finset (Fin n))), (∀ s ∈ C, #s = w) →
      (∀ s ∈ C, ∀ t ∈ C, s ≠ t → #(s ∩ t) + 2 ≤ w) → #C ≤ johnsonBound n 4 w
  | 0, w, C, _, _ => by
    rw [johnsonBound]
    refine Finset.card_le_one.2 fun s _ t _ => ?_
    rw [Finset.eq_empty_of_isEmpty s, Finset.eq_empty_of_isEmpty t]
  | n + 1, 0, C, _, hC => by
    show #C ≤ 1
    exact card_le_one_of_forall_ne fun s hs t ht hst => by have := hC s hs t ht hst; omega
  | n + 1, w + 1, C, hw, hC => by
    rw [johnsonBound]
    split_ifs with hlt
    · exact card_le_one_of_forall_ne fun s hs t ht hst => by have := hC s hs t ht hst; omega
    rw [Nat.le_div_iff_mul_le (Nat.succ_pos w)]
    -- each fibre `Cₓ` is bounded by the induction hypothesis
    have hfib : ∀ x : Fin (n + 1), #(C.filter fun s => x ∈ s) ≤ johnsonBound n 4 w := by
      intro x
      set Cx := C.filter fun s => x ∈ s
      have hinj : Set.InjOn (shrink x) Cx := by
        intro s hs t ht hst
        simp only [Cx, coe_filter, Set.mem_ofPred_eq] at hs ht
        have h := congrArg (Finset.map x.succAboveEmb) hst
        simp only [map_shrink] at h
        rw [← insert_erase hs.2, ← insert_erase ht.2, h]
      rw [← card_image_of_injOn hinj]
      apply card_le_johnsonBound n w
      · intro u hu
        obtain ⟨s, hs, rfl⟩ := mem_image.1 hu
        rw [mem_filter] at hs
        rw [card_shrink, card_erase_of_mem hs.2, hw s hs.1]
        rfl
      · intro u hu v hv huv
        obtain ⟨s, hs, rfl⟩ := mem_image.1 hu
        obtain ⟨t, ht, rfl⟩ := mem_image.1 hv
        rw [mem_filter] at hs ht
        have hst : s ≠ t := fun h => huv (h ▸ rfl)
        have h1 := hC s hs.1 t ht.1 hst
        have hx : x ∈ s ∩ t := mem_inter.2 ⟨hs.2, ht.2⟩
        have h2 := card_erase_of_mem hx
        have h3 : 1 ≤ #(s ∩ t) := card_pos.2 ⟨x, hx⟩
        rw [card_shrink_inter, h2]
        omega
    -- double counting of the incidences `x ∈ s ∈ C`
    have hdc : ∑ s ∈ C, #((univ : Finset (Fin (n + 1))).bipartiteAbove (fun s x => x ∈ s) s) =
        ∑ x ∈ (univ : Finset (Fin (n + 1))), #(C.bipartiteBelow (fun s x => x ∈ s) x) :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
    have hleft : ∑ s ∈ C, #((univ : Finset (Fin (n + 1))).bipartiteAbove (fun s x => x ∈ s) s) =
        #C * (w + 1) := by
      rw [sum_const_nat]
      intro s hs
      simp only [bipartiteAbove, filter_mem_eq_inter, univ_inter]
      exact hw s hs
    rw [← hleft, hdc]
    calc ∑ x ∈ (univ : Finset (Fin (n + 1))), #(C.bipartiteBelow (fun s x => x ∈ s) x)
        ≤ ∑ _x ∈ (univ : Finset (Fin (n + 1))), johnsonBound n 4 w :=
          sum_le_sum fun x _ => hfib x
      _ = (n + 1) * johnsonBound n 4 w := by simp

/-- Johnson's bound for the independence number of the Johnson graph. -/
lemma indepNum_johnson_le_johnsonBound : α(J(n, k)) ≤ johnsonBound n 4 k := by
  obtain ⟨S, hS⟩ := (J(n, k)).exists_isNIndepSet_indepNum
  rw [← hS.card_eq, ← card_map (Function.Embedding.subtype _)]
  apply card_le_johnsonBound n k
  · intro u hu
    obtain ⟨s, -, rfl⟩ := mem_map.1 hu
    exact s.2
  · intro u hu v hv huv
    obtain ⟨s, hs, rfl⟩ := mem_map.1 hu
    obtain ⟨t, ht, rfl⟩ := mem_map.1 hv
    have hst : s ≠ t := fun h => huv (h ▸ rfl)
    rcases (not_johnson_adj_iff_lt (n := n) (k := k)).1 (hS.isIndepSet hs ht hst) with h | h
    · exact absurd h hst
    · simp only [Function.Embedding.subtype_apply]
      omega

end Erdos835
