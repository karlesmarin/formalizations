/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Combinatorics.Additive.Dissociation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Dissociated subsets of real sets: the greedy bound (Erdős Problem 963)

`f n` is the largest `k` such that every set of `n` reals has a dissociated subset with at least `k`
elements (definition copied verbatim from formal-conjectures). The greedy algorithm gives
`Nat.log 3 n ≤ f n`: the elements that spoil a dissociated set `B` lie in its `{-1, 0, 1}`-span, of
size at most `3 ^ #B`.

## Main results

* `Erdos963.erdos_963.variants.greedy`: Nat.log 3 n ≤ f n (Erdős 1965; formal-conjectures erdos_963.variants.greedy)
* `Erdos963.card_span_le`: the {-1,0,1}-span of B has at most 3^#B elements
* `Erdos963.addDissociated_insert`: B dissociated and x ∉ span B ⇒ insert x B dissociated
* `Erdos963.exists_dissociated`: 3^j ≤ #A ⇒ A has a dissociated subset with j elements

## References

* P. Erdős, «Extremal problems in number theory», Proc. Sympos. Pure Math. VIII (1965) 181–189, p. 188.
* erdosproblems.com/963; statement and definition copied verbatim from google-deepmind/formal-conjectures, FormalConjectures/ErdosProblems/963.lean.
-/

@[expose] public section

namespace Erdos963

/-- $f(n)$ is the largest $k$ such that every set $A\subset\mathbb{R}$ with $n$ elements has a
dissociated subset with at least $k$ elements. The set of such $k$ contains $0$ (take the empty
subset) and is bounded by $n$, so `sSup` is a true maximum. The set $A$ may contain $0$, which
can never belong to a dissociated set. For $n = 0$ the value is $0$. -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, k ≤ B.card ∧ AddDissociated (B : Set ℝ)}

/-- If every set of `n` reals has a dissociated subset with at least `k` elements, then
$k \leq f(n)$. -/
theorem le_f {n k : ℕ}
    (h : ∀ A : Finset ℝ, A.card = n → ∃ B ⊆ A, k ≤ B.card ∧ AddDissociated (B : Set ℝ)) :
    k ≤ f n := by
  refine le_csSup ⟨n, fun m hm ↦ ?_⟩ h
  obtain ⟨A, hA⟩ := Infinite.exists_subset_card_eq ℝ n
  obtain ⟨B, hBA, hmB, -⟩ := hm A hA
  exact hmB.trans ((Finset.card_le_card hBA).trans hA.le)

/-- The `{-1, 0, 1}`-span of a finset of reals. -/
noncomputable def span (B : Finset ℝ) : Finset ℝ :=
  (Fintype.piFinset fun _ : B ↦ ({-1, 0, 1} : Finset ℤ)).image
    fun ε ↦ ∑ b : B, (ε b : ℝ) * b

lemma card_span_le (B : Finset ℝ) : (span B).card ≤ 3 ^ B.card := by
  refine (Finset.card_image_le).trans ?_
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  have : ({-1, 0, 1} : Finset ℤ).card = 3 := by decide
  rw [this]

lemma mem_span_of {B : Finset ℝ} (ε : ℝ → ℤ) (hε : ∀ b, ε b = -1 ∨ ε b = 0 ∨ ε b = 1) :
    ∑ b ∈ B, (ε b : ℝ) * b ∈ span B := by
  refine Finset.mem_image.2 ⟨fun b ↦ ε b, Fintype.mem_piFinset.2 fun b ↦ ?_, ?_⟩
  · rcases hε b with h | h | h <;> simp [h]
  · exact Finset.sum_coe_sort B (fun b ↦ (ε b : ℝ) * b)

lemma subset_span (B : Finset ℝ) : B ⊆ span B := by
  classical
  intro a ha
  have := mem_span_of (B := B) (fun b ↦ if b = a then 1 else 0)
    (fun b ↦ by by_cases h : b = a <;> simp [h])
  simpa [ha] using this

/-- Difference of two subset sums lies in the span. -/
lemma sub_mem_span {B t u : Finset ℝ} (ht : t ⊆ B) (hu : u ⊆ B) :
    ∑ a ∈ u, a - ∑ a ∈ t, a ∈ span B := by
  classical
  have h := mem_span_of (B := B)
    (fun b ↦ (if b ∈ u then 1 else 0) - (if b ∈ t then 1 else 0))
    (fun b ↦ by by_cases h1 : b ∈ u <;> by_cases h2 : b ∈ t <;> simp [h1, h2])
  have e : ∑ b ∈ B, (((if b ∈ u then 1 else 0) - (if b ∈ t then 1 else 0) : ℤ) : ℝ) * b
      = ∑ a ∈ u, a - ∑ a ∈ t, a := by
    simp only [Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero, sub_mul, ite_mul,
      one_mul, zero_mul, Finset.sum_sub_distrib]
    rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hu, Finset.inter_eq_right.2 ht]
  rwa [e] at h

/-- Key step: adding an element outside the span keeps a set dissociated. -/
lemma addDissociated_insert {B : Finset ℝ} {x : ℝ} (hB : AddDissociated (B : Set ℝ))
    (hx : x ∉ span B) : AddDissociated ((insert x B : Finset ℝ) : Set ℝ) := by
  classical
  have hxB : x ∉ B := fun h ↦ hx (subset_span B h)
  -- one-sided case: `x ∈ t`, `x ∉ u`
  have key : ∀ t u : Finset ℝ, t ⊆ insert x B → u ⊆ insert x B → x ∈ t → x ∉ u →
      ∑ a ∈ t, a = ∑ a ∈ u, a → False := by
    intro t u ht hu hxt hxu hs
    have hu' : u ⊆ B := fun a ha ↦ by
      rcases Finset.mem_insert.1 (hu ha) with rfl | h
      · exact absurd ha hxu
      · exact h
    have ht' : t.erase x ⊆ B := fun a ha ↦ by
      rcases Finset.mem_insert.1 (ht (Finset.mem_of_mem_erase ha)) with rfl | h
      · exact absurd rfl (Finset.ne_of_mem_erase ha)
      · exact h
    have hsum : ∑ a ∈ t, a = x + ∑ a ∈ t.erase x, a := (Finset.add_sum_erase t id hxt).symm
    apply hx
    have : x = ∑ a ∈ u, a - ∑ a ∈ t.erase x, a := by linarith
    rw [this]
    exact sub_mem_span ht' hu'
  by_contra hnd
  obtain ⟨t, u, ht, hu, -, htu, hs⟩ := not_addDissociated_iff_exists_disjoint.1 hnd
  have ht0 : t ⊆ insert x B := by exact_mod_cast ht
  have hu0 : u ⊆ insert x B := by exact_mod_cast hu
  by_cases hxt : x ∈ t <;> by_cases hxu : x ∈ u
  · -- both contain `x`: erase it and use dissociation of `B`
    have ht' : t.erase x ⊆ B := fun a ha ↦ by
      rcases Finset.mem_insert.1 (ht0 (Finset.mem_of_mem_erase ha)) with rfl | h
      · exact absurd rfl (Finset.ne_of_mem_erase ha)
      · exact h
    have hu' : u.erase x ⊆ B := fun a ha ↦ by
      rcases Finset.mem_insert.1 (hu0 (Finset.mem_of_mem_erase ha)) with rfl | h
      · exact absurd rfl (Finset.ne_of_mem_erase ha)
      · exact h
    have h1 := Finset.add_sum_erase t id hxt
    have h2 := Finset.add_sum_erase u id hxu
    have heq : t.erase x = u.erase x := by
      refine hB (by exact_mod_cast ht') (by exact_mod_cast hu') ?_
      simp only [id] at h1 h2
      show ∑ a ∈ t.erase x, a = ∑ a ∈ u.erase x, a
      linarith
    apply htu
    rw [← Finset.insert_erase hxt, ← Finset.insert_erase hxu, heq]
  · exact key t u ht0 hu0 hxt hxu hs
  · exact key u t hu0 ht0 hxu hxt hs.symm
  · have ht' : t ⊆ B := fun a ha ↦ by
      rcases Finset.mem_insert.1 (ht0 ha) with rfl | h
      · exact absurd ha hxt
      · exact h
    have hu' : u ⊆ B := fun a ha ↦ by
      rcases Finset.mem_insert.1 (hu0 ha) with rfl | h
      · exact absurd ha hxu
      · exact h
    exact htu (hB (by exact_mod_cast ht') (by exact_mod_cast hu') hs)

/-- Greedy construction: if `3 ^ j ≤ #A` there is a dissociated `B ⊆ A` with `#B = j`. -/
lemma exists_dissociated (A : Finset ℝ) :
    ∀ j : ℕ, 3 ^ j ≤ A.card → ∃ B ⊆ A, B.card = j ∧ AddDissociated (B : Set ℝ) := by
  classical
  intro j
  induction j with
  | zero => intro _; exact ⟨∅, Finset.empty_subset _, rfl, by simp⟩
  | succ j ih =>
    intro hj
    obtain ⟨B, hBA, hBc, hB⟩ := ih (le_trans (Nat.pow_le_pow_right (by norm_num) j.le_succ) hj)
    have hlt : (span B).card < A.card := by
      have := card_span_le B
      rw [hBc] at this
      have : 3 ^ j < 3 ^ (j + 1) := Nat.pow_lt_pow_right (by norm_num) j.lt_succ_self
      omega
    obtain ⟨x, hxA, hxs⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have hxB : x ∉ B := fun h ↦ hxs (subset_span B h)
    refine ⟨insert x B, Finset.insert_subset hxA hBA, ?_, addDissociated_insert hB hxs⟩
    rw [Finset.card_insert_of_notMem hxB, hBc]

/--
Erdős noted that the greedy algorithm showed $f(n)\geq \lfloor \log_3 n\rfloor$
[Er65, p. 188].
-/
theorem erdos_963.variants.greedy (n : ℕ) : Nat.log 3 n ≤ f n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  apply le_f
  intro A hA
  obtain ⟨B, hBA, hBc, hB⟩ :=
    exists_dissociated A (Nat.log 3 n) (hA.symm ▸ Nat.pow_log_le_self 3 hn.ne')
  exact ⟨B, hBA, hBc.ge, hB⟩

end Erdos963

end
