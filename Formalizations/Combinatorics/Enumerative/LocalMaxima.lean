/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# The mean number of k-local maxima of a random permutation

The `k`-local maxima of a permutation are the distinct values among the maxima of its windows of
length `k`. Summed over the `n!` permutations, `(k + 1) · Σ_σ #maxima = n! (2n − k + 1)`: the mean
is `(2n − k + 1)/(k + 1)` (Theorem of the Day, after Austin–Fagen–Lehrer–Penney 1957). Proof: the
window maximum changes between windows `i − 1` and `i` exactly when the maximum of the block of
`k + 1` positions `[i − 1, i + k − 1]` sits at one of its ends, which by symmetry happens for
`2 n!/(k + 1)` permutations.

## Main results

* `LocalMaxima.card_image_windowMax`: number of distinct window maxima = 1 + number of blocks whose maximum is at an end
* `LocalMaxima.card_argmax_end`: the maximum of a block of k + 1 positions is at an end for 2 n!/(k+1) permutations
* `LocalMaxima.sum_card_windowMax`: (k + 1) Σ_σ #k-local maxima = n! (2n − k + 1)

## References

* R. Whitty, Theorem of the Day, «Distribution of local maxima in random samples» (Statistics/PermLocalMax).
* T. L. Austin, R. E. Fagen, T. A. Lehrer, W. F. Penney, The distribution of the number of locally maximal elements in a random sample, Ann. Math. Statist. 28 (1957).
-/

@[expose] public section

open Finset

namespace LocalMaxima

/-- The maximum of the window `[i, i + k)` of `σ` (values as natural numbers). -/
def windowMax {n : ℕ} (σ : Equiv.Perm (Fin n)) (k i : ℕ) : ℕ :=
  ((univ.filter fun j : Fin n => i ≤ j.val ∧ j.val < i + k).image fun j => (σ j : ℕ)).sup id

/-- `p` is a position of the block `[a, a + k]` carrying the largest value of `σ` on the block. -/
def IsBlockMax {n : ℕ} (σ : Equiv.Perm (Fin n)) (a k : ℕ) (p : Fin n) : Prop :=
  a ≤ p.val ∧ p.val ≤ a + k ∧
    ∀ j : Fin n, a ≤ j.val → j.val ≤ a + k → (σ j : ℕ) ≤ σ p

/-- The maximum of the block `[a, a + k]` of `σ` sits at one of its two ends. -/
def EndMax {n : ℕ} (σ : Equiv.Perm (Fin n)) (a k : ℕ) : Prop :=
  ∃ p : Fin n, (p.val = a ∨ p.val = a + k) ∧ IsBlockMax σ a k p

lemma le_windowMax {n : ℕ} (σ : Equiv.Perm (Fin n)) (k i : ℕ) (j : Fin n) (h1 : i ≤ j.val)
    (h2 : j.val < i + k) : (σ j : ℕ) ≤ windowMax σ k i := by
  unfold windowMax
  exact Finset.le_sup (f := id)
    (mem_image.mpr ⟨j, mem_filter.mpr ⟨mem_univ _, h1, h2⟩, rfl⟩)

lemma exists_windowMax {n : ℕ} (σ : Equiv.Perm (Fin n)) (k i : ℕ) (hk : 1 ≤ k) (hi : i + k ≤ n) :
    ∃ j : Fin n, i ≤ j.val ∧ j.val < i + k ∧ (σ j : ℕ) = windowMax σ k i := by
  have hne : ((univ.filter fun j : Fin n => i ≤ j.val ∧ j.val < i + k).image
      fun j => (σ j : ℕ)).Nonempty :=
    ⟨σ ⟨i, by omega⟩, mem_image.mpr ⟨⟨i, by omega⟩,
      mem_filter.mpr ⟨mem_univ _, by simp, by simp; omega⟩, rfl⟩⟩
  obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_sup _ hne id
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
  obtain ⟨_, h1, h2⟩ := mem_filter.mp hj
  exact ⟨j, h1, h2, hxe.symm⟩

section Cl

open scoped Classical

lemma exists_blockMax {n : ℕ} (σ : Equiv.Perm (Fin n)) (a k : ℕ) (h : a + k < n) :
    ∃ p : Fin n, IsBlockMax σ a k p := by
  have hne : (univ.filter fun j : Fin n => a ≤ j.val ∧ j.val ≤ a + k).Nonempty :=
    ⟨⟨a, by omega⟩, mem_filter.mpr ⟨mem_univ _, by simp, by simp⟩⟩
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image _ (fun j : Fin n => (σ j : ℕ)) hne
  obtain ⟨_, h1, h2⟩ := mem_filter.mp hp
  exact ⟨p, h1, h2, fun j hj1 hj2 => hmax j (mem_filter.mpr ⟨mem_univ _, hj1, hj2⟩)⟩

lemma windowMax_eq {n : ℕ} (σ : Equiv.Perm (Fin n)) (k i a : ℕ) (hk : 1 ≤ k) (hi : i + k ≤ n)
    (q : Fin n) (hq : IsBlockMax σ a k q) (h1 : a ≤ i) (h2 : i + k ≤ a + k + 1)
    (hq1 : i ≤ q.val) (hq2 : q.val < i + k) : windowMax σ k i = σ q := by
  apply le_antisymm
  · obtain ⟨s, hs1, hs2, hs⟩ := exists_windowMax σ k i hk hi
    rw [← hs]
    exact hq.2.2 s (by omega) (by omega)
  · exact le_windowMax σ k i q hq1 hq2

lemma mem_image_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) (k m : ℕ) (hk : 1 ≤ k) (hm : m + 1 + k ≤ n) :
    windowMax σ k (m + 1) ∈ (range (m + 1)).image (windowMax σ k) ↔ ¬ EndMax σ m k := by
  have hinj : ∀ x y : Fin n, (σ x : ℕ) = σ y → x = y := fun x y h => σ.injective (Fin.ext h)
  constructor
  · intro hmem hend
    obtain ⟨l, hl, hle⟩ := mem_image.mp hmem
    have hl' : l ≤ m := by simpa [Nat.lt_succ_iff] using hl
    obtain ⟨p, hp, hpmax⟩ := hend
    obtain ⟨r, hr1, hr2, hreq⟩ := exists_windowMax σ k (m + 1) hk hm
    obtain ⟨s, hs1, hs2, hseq⟩ := exists_windowMax σ k l hk (by omega)
    have hsr : s = r := hinj _ _ (by rw [hseq, hreq, hle])
    subst hsr
    rcases hp with hp | hp
    · have h1 : (σ p : ℕ) ≤ windowMax σ k l := le_windowMax σ k l p (by omega) (by omega)
      have h2 : (σ s : ℕ) ≤ σ p := hpmax.2.2 s (by omega) (by omega)
      have : p = s := hinj _ _ (le_antisymm (by rw [hseq]; exact h1) h2)
      omega
    · have h1 : (σ p : ℕ) ≤ windowMax σ k (m + 1) := le_windowMax σ k (m + 1) p (by omega) (by omega)
      have h2 : (σ s : ℕ) ≤ σ p := hpmax.2.2 s (by omega) (by omega)
      have : p = s := hinj _ _ (le_antisymm (by rw [hreq]; exact h1) h2)
      omega
  · intro hnot
    obtain ⟨q, hq⟩ := exists_blockMax σ m k (by omega)
    have hq1 : q.val ≠ m := fun h => hnot ⟨q, Or.inl h, hq⟩
    have hq2 : q.val ≠ m + k := fun h => hnot ⟨q, Or.inr h, hq⟩
    have e1 := windowMax_eq σ k m m hk (by omega) q hq le_rfl (by omega) (by have := hq.1; omega)
      (by have := hq.2.1; omega)
    have e2 := windowMax_eq σ k (m + 1) m hk hm q hq (by omega) (by omega)
      (by have := hq.1; omega) (by have := hq.2.1; omega)
    exact mem_image.mpr ⟨m, mem_range.mpr (by omega), by rw [e1, e2]⟩

lemma card_image_range {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) (hk : 1 ≤ k) :
    ∀ m : ℕ, m + k ≤ n →
      ((range (m + 1)).image (windowMax σ k)).card =
        1 + ((range m).filter fun a => EndMax σ a k).card := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have ih' := ih (by omega)
    have key := mem_image_iff σ k m hk hm
    rw [range_add_one (n := m + 1), image_insert]
    conv_rhs => rw [range_add_one, filter_insert]
    by_cases hE : EndMax σ m k
    · have hn : windowMax σ k (m + 1) ∉ (range (m + 1)).image (windowMax σ k) := by
        rw [key]; exact not_not.mpr hE
      rw [card_insert_of_notMem hn]
      simp only [hE, ↓reduceIte]
      rw [card_insert_of_notMem (by simp), ih']
      omega
    · have hn : windowMax σ k (m + 1) ∈ (range (m + 1)).image (windowMax σ k) := key.mpr hE
      rw [card_insert_of_mem hn]
      simp only [hE, ↓reduceIte]
      rw [ih']

/-- The number of distinct window maxima of `σ` is `1 +` the number of blocks `[a, a + k]`
(`0 ≤ a < n - k`) whose maximum sits at an end. -/
lemma card_image_windowMax {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ((range (n - k + 1)).image (windowMax σ k)).card =
      1 + ((range (n - k)).filter fun a => EndMax σ a k).card :=
  card_image_range σ k hk (n - k) (by omega)

lemma isBlockMax_swap {n : ℕ} (σ : Equiv.Perm (Fin n)) (a k : ℕ) (p q : Fin n)
    (hp1 : a ≤ p.val) (hp2 : p.val ≤ a + k) (hq1 : a ≤ q.val) (hq2 : q.val ≤ a + k)
    (h : IsBlockMax σ a k p) : IsBlockMax (σ * Equiv.swap p q) a k q := by
  refine ⟨hq1, hq2, fun j hj1 hj2 => ?_⟩
  have hs : a ≤ (Equiv.swap p q j).val ∧ (Equiv.swap p q j).val ≤ a + k := by
    rw [Equiv.swap_apply_def]
    split_ifs
    · exact ⟨hq1, hq2⟩
    · exact ⟨hp1, hp2⟩
    · exact ⟨hj1, hj2⟩
  have := h.2.2 _ hs.1 hs.2
  simpa [Equiv.Perm.mul_apply] using this

lemma card_blockMax_eq {n : ℕ} (a k : ℕ) (p q : Fin n)
    (hp1 : a ≤ p.val) (hp2 : p.val ≤ a + k) (hq1 : a ≤ q.val) (hq2 : q.val ≤ a + k) :
    ((univ : Finset (Equiv.Perm (Fin n))).filter fun σ => IsBlockMax σ a k p).card =
      ((univ : Finset (Equiv.Perm (Fin n))).filter fun σ => IsBlockMax σ a k q).card := by
  refine Finset.card_nbij' (fun σ => σ * Equiv.swap p q) (fun σ => σ * Equiv.swap p q)
    ?_ ?_ ?_ ?_
  · intro σ hσ
    exact mem_filter.mpr ⟨mem_univ _,
      isBlockMax_swap σ a k p q hp1 hp2 hq1 hq2 (mem_filter.mp hσ).2⟩
  · intro σ hσ
    have := isBlockMax_swap σ a k q p hq1 hq2 hp1 hp2 (mem_filter.mp hσ).2
    rw [Equiv.swap_comm] at this
    exact mem_filter.mpr ⟨mem_univ _, this⟩
  · intro σ _
    simp [mul_assoc]
  · intro σ _
    simp [mul_assoc]

lemma card_block {n : ℕ} (a k : ℕ) (h : a + k < n) :
    ((univ : Finset (Fin n)).filter fun j => a ≤ j.val ∧ j.val ≤ a + k).card = k + 1 := by
  have : ((univ : Finset (Fin n)).filter fun j => a ≤ j.val ∧ j.val ≤ a + k).map
      ⟨Fin.val, Fin.val_injective⟩ = Icc a (a + k) := by
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coeFn_mk, mem_Icc]
    constructor
    · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, by omega⟩, ⟨h1, h2⟩, rfl⟩
  rw [← card_map ⟨Fin.val, Fin.val_injective⟩, this, Nat.card_Icc]
  omega

/-- The block maximum is uniformly distributed on the `k + 1` positions of the block. -/
lemma card_blockMax_mul {n : ℕ} (a k : ℕ) (h : a + k < n) (p : Fin n)
    (hp1 : a ≤ p.val) (hp2 : p.val ≤ a + k) :
    ((univ : Finset (Equiv.Perm (Fin n))).filter fun σ => IsBlockMax σ a k p).card * (k + 1) =
      n.factorial := by
  set B := (univ : Finset (Fin n)).filter fun j => a ≤ j.val ∧ j.val ≤ a + k with hB
  have hconst : ∀ q ∈ B,
      ((univ : Finset (Equiv.Perm (Fin n))).filter fun σ => IsBlockMax σ a k q).card =
      ((univ : Finset (Equiv.Perm (Fin n))).filter fun σ => IsBlockMax σ a k p).card := by
    intro q hq
    obtain ⟨_, hq1, hq2⟩ := mem_filter.mp hq
    exact card_blockMax_eq a k q p hq1 hq2 hp1 hp2
  have htot : ∑ q ∈ B,
      ((univ : Finset (Equiv.Perm (Fin n))).filter fun σ => IsBlockMax σ a k q).card =
      n.factorial := by
    calc _ = ∑ q ∈ B, ∑ σ : Equiv.Perm (Fin n), if IsBlockMax σ a k q then 1 else 0 := by
          refine sum_congr rfl fun q _ => ?_
          rw [card_filter]
      _ = ∑ σ : Equiv.Perm (Fin n), ∑ q ∈ B, if IsBlockMax σ a k q then 1 else 0 := sum_comm
      _ = ∑ _σ : Equiv.Perm (Fin n), 1 := by
          refine sum_congr rfl fun σ _ => ?_
          rw [← card_filter]
          rw [Finset.card_eq_one]
          obtain ⟨p0, hp0⟩ := exists_blockMax σ a k h
          refine ⟨p0, ?_⟩
          ext x
          simp only [mem_filter, mem_singleton, hB, mem_univ, true_and]
          constructor
          · rintro ⟨_, hx⟩
            have e1 := hx.2.2 p0 hp0.1 hp0.2.1
            have e2 := hp0.2.2 x hx.1 hx.2.1
            exact σ.injective (Fin.ext (le_antisymm e2 e1))
          · rintro rfl
            exact ⟨⟨hp0.1, hp0.2.1⟩, hp0⟩
      _ = n.factorial := by simp [Fintype.card_perm]
  rw [sum_congr rfl hconst, sum_const, card_block a k h, smul_eq_mul] at htot
  rw [← htot]
  ring

/-- For a block `[a, a + k]` inside `Fin n`, the maximum is at an end for exactly `2 n! / (k + 1)`
permutations. -/
lemma card_argmax_end {n : ℕ} (a k : ℕ) (hk : 1 ≤ k) (h : a + k < n) :
    ((univ : Finset (Equiv.Perm (Fin n))).filter fun σ => EndMax σ a k).card * (k + 1) =
      2 * n.factorial := by
  set pa : Fin n := ⟨a, by omega⟩
  set pb : Fin n := ⟨a + k, h⟩
  have hU : ((univ : Finset (Equiv.Perm (Fin n))).filter fun σ => EndMax σ a k) =
      ((univ : Finset (Equiv.Perm (Fin n))).filter fun σ => IsBlockMax σ a k pa) ∪
      ((univ : Finset (Equiv.Perm (Fin n))).filter fun σ => IsBlockMax σ a k pb) := by
    ext σ
    simp only [mem_filter, mem_union, mem_univ, true_and]
    constructor
    · rintro ⟨p, hp | hp, hmax⟩
      · left; have : p = pa := Fin.ext hp
        exact this ▸ hmax
      · right; have : p = pb := Fin.ext hp
        exact this ▸ hmax
    · rintro (hm | hm)
      · exact ⟨pa, Or.inl rfl, hm⟩
      · exact ⟨pb, Or.inr rfl, hm⟩
  have hD : Disjoint
      ((univ : Finset (Equiv.Perm (Fin n))).filter fun σ => IsBlockMax σ a k pa)
      ((univ : Finset (Equiv.Perm (Fin n))).filter fun σ => IsBlockMax σ a k pb) := by
    rw [Finset.disjoint_left]
    intro σ h1 h2
    have m1 := (mem_filter.mp h1).2
    have m2 := (mem_filter.mp h2).2
    have e1 := m1.2.2 pb (by simp [pb]) (by simp [pb])
    have e2 := m2.2.2 pa (by simp [pa]) (by simp [pa])
    have : pa = pb := σ.injective (Fin.ext (le_antisymm e2 e1))
    have := congrArg Fin.val this
    simp [pa, pb] at this
    omega
  have ha := card_blockMax_mul a k h pa (by simp [pa]) (by simp [pa])
  have hb := card_blockMax_mul a k h pb (by simp [pb]) (by simp [pb])
  rw [hU, card_union_of_disjoint hD]
  nlinarith

end Cl

open scoped Classical in
/-- **Sum over permutations of the number of distinct window maxima.** -/
theorem sum_card_windowMax (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (k + 1) * ∑ σ : Equiv.Perm (Fin n), ((range (n - k + 1)).image (windowMax σ k)).card =
      n.factorial * (2 * n - k + 1) := by
  have h1 : ∑ σ : Equiv.Perm (Fin n), ((range (n - k + 1)).image (windowMax σ k)).card =
      n.factorial + ∑ a ∈ range (n - k),
        ((univ : Finset (Equiv.Perm (Fin n))).filter fun σ => EndMax σ a k).card := by
    calc _ = ∑ σ : Equiv.Perm (Fin n),
          (1 + ((range (n - k)).filter fun a => EndMax σ a k).card) :=
          sum_congr rfl fun σ _ => card_image_windowMax σ k hk hkn
      _ = ∑ σ : Equiv.Perm (Fin n), 1 + ∑ σ : Equiv.Perm (Fin n),
            ((range (n - k)).filter fun a => EndMax σ a k).card := sum_add_distrib
      _ = _ := by
          congr 1
          · simp [Fintype.card_perm]
          · calc _ = ∑ σ : Equiv.Perm (Fin n), ∑ a ∈ range (n - k),
                  if EndMax σ a k then 1 else 0 := by
                  refine sum_congr rfl fun σ _ => ?_
                  rw [card_filter]
              _ = ∑ a ∈ range (n - k), ∑ σ : Equiv.Perm (Fin n),
                  if EndMax σ a k then 1 else 0 := sum_comm
              _ = _ := by
                  refine sum_congr rfl fun a _ => ?_
                  rw [← card_filter]
  have h2 : (k + 1) * ∑ a ∈ range (n - k),
      ((univ : Finset (Equiv.Perm (Fin n))).filter fun σ => EndMax σ a k).card =
      (n - k) * (2 * n.factorial) := by
    rw [mul_sum]
    calc _ = ∑ _a ∈ range (n - k), 2 * n.factorial := by
          refine sum_congr rfl fun a ha => ?_
          have := card_argmax_end (n := n) a k hk (by have := mem_range.mp ha; omega)
          linarith
      _ = _ := by simp
  rw [h1, mul_add, h2]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
  have e1 : k + d - k = d := by omega
  have e2 : 2 * (k + d) - k + 1 = 2 * d + k + 1 := by omega
  rw [e1, e2]
  ring

end LocalMaxima

open Finset LocalMaxima
