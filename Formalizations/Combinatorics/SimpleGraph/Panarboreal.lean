/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# The panarboreal lower bound

If a graph on `n` vertices contains a copy of every tree on `n` vertices, it has at least
`½ Σ_{k=1}^{n} ⌈(n − 1)/k⌉ ≥ ½ (n − 1) Hₙ` edges (Chung–Graham; the easy half of Theorem of the
Day's panarboreal formula `s(n) ~ c n log n`). For each `k` a caterpillar with a spine of `k`
vertices has `k` vertices of degree `≥ ⌈(n − 1)/k⌉`, so `G` has `k` such vertices too, and summing
the sorted degrees gives the bound. Whether `c = 1/2` is open.

## Main results

* `Panarboreal.exists_caterpillar`: for 1 ≤ k ≤ n there is a tree on n vertices with k vertices of degree ≥ ⌈(n−1)/k⌉
* `Panarboreal.sum_le_sum_degrees`: if for each k at least k vertices have degree ≥ d_k, Σ_v deg v ≥ Σ_k d_k (no monotonicity needed)
* `Panarboreal.sum_ceil_le_two_mul_card_edges`: tree-universal graphs: Σ_k ⌈(n−1)/k⌉ ≤ 2|E|

## References

* R. Whitty, Theorem of the Day, «The Panarboreal Formula» (CombinatorialTheory/Panarboreal).
* F. R. K. Chung, R. L. Graham, Universal graphs for trees, 1979 (cota inferior ½ n log n; superior (5/log 4) n log n).
-/

@[expose] public section

open Finset

namespace Panarboreal

open Finset

/-- Graph on `Fin n` in which every vertex `v ≠ 0` is joined to its parent `q v`. -/
def pg {n : ℕ} (q : Fin n → Fin n) (hq : ∀ v, 0 < v.val → (q v).val < v.val) :
    SimpleGraph (Fin n) where
  Adj u v := (0 < v.val ∧ u = q v) ∨ (0 < u.val ∧ v = q u)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun v h => by
    rcases h with ⟨h0, h⟩ | ⟨h0, h⟩
    · have := hq v h0; rw [← h] at this; omega
    · have := hq v h0; rw [← h] at this; omega⟩

theorem pg_connected {n : ℕ} (hn : 0 < n) (q : Fin n → Fin n)
    (hq : ∀ v, 0 < v.val → (q v).val < v.val) : (pg q hq).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨0, hn⟩, fun w => ?_⟩
  suffices h : ∀ m, ∀ w : Fin n, w.val = m → (pg q hq).Reachable ⟨0, hn⟩ w from h _ w rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro w hw
    by_cases h0 : 0 < w.val
    · have h1 := ih (q w).val (by have := hq w h0; omega) (q w) rfl
      exact h1.trans (SimpleGraph.Adj.reachable (Or.inl ⟨h0, rfl⟩))
    · have : w = ⟨0, hn⟩ := Fin.ext (by show w.val = 0; omega)
      rw [this]

theorem pg_edgeFinset {n : ℕ} (hn : 0 < n) (q : Fin n → Fin n)
    (hq : ∀ v, 0 < v.val → (q v).val < v.val) [DecidableRel (pg q hq).Adj] :
    (pg q hq).edgeFinset = (univ.erase (⟨0, hn⟩ : Fin n)).image (fun v => s(q v, v)) := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, mem_image, mem_erase,
      mem_univ, and_true]
    constructor
    · rintro (⟨h0, h⟩ | ⟨h0, h⟩)
      · refine ⟨b, fun hb => ?_, ?_⟩
        · rw [hb] at h0; simp at h0
        · rw [← h]
      · refine ⟨a, fun hb => ?_, ?_⟩
        · rw [hb] at h0; simp at h0
        · rw [← h]; exact Sym2.eq_swap
    · rintro ⟨v, hv, hv2⟩
      have hv0 : 0 < v.val := by
        rcases Nat.eq_zero_or_pos v.val with h | h
        · exact absurd (Fin.ext h) hv
        · exact h
      rcases Sym2.eq_iff.1 hv2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1; subst h2; exact Or.inl ⟨hv0, rfl⟩
      · subst h1; subst h2; exact Or.inr ⟨hv0, rfl⟩

theorem pg_isTree {n : ℕ} (hn : 0 < n) (q : Fin n → Fin n)
    (hq : ∀ v, 0 < v.val → (q v).val < v.val) : (pg q hq).IsTree := by
  classical
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨pg_connected hn q hq, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, pg_edgeFinset hn q hq,
    card_image_of_injOn, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  · omega
  · intro v hv w hw hvw
    simp only [coe_erase, coe_univ, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff,
      true_and] at hv hw
    have hv0 : 0 < v.val := Nat.pos_of_ne_zero (fun h => hv (Fin.ext h))
    have hw0 : 0 < w.val := Nat.pos_of_ne_zero (fun h => hw (Fin.ext h))
    have h1 := hq v hv0
    have h2 := hq w hw0
    rcases Sym2.eq_iff.1 hvw with ⟨_, h⟩ | ⟨h3, h4⟩
    · exact h
    · have h5 : v.val = (q w).val := by rw [h4]
      rw [h3] at h1; omega

/-- Spine vertex that receives the leaves of residue `r` (residues `0`, `1` go to the two ends). -/
def lp (k r : ℕ) : ℕ := if r = 0 then 0 else if r = 1 then k - 1 else r - 1

/-- Parent of `j` in the caterpillar with spine `0 – 1 – ⋯ – (k-1)`. -/
def par (k j : ℕ) : ℕ := if j < k then j - 1 else lp k ((j - k) % k)

theorem par_lt {k : ℕ} (hk : 1 ≤ k) {j : ℕ} (hj : 0 < j) : par k j < j := by
  have h := Nat.mod_lt (j - k) hk
  unfold par lp
  generalize (j - k) % k = r at *
  split_ifs <;> omega

theorem par_le {k : ℕ} (hk : 1 ≤ k) (j : ℕ) : par k j ≤ j := by
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h; unfold par; simp; omega
  · exact (par_lt hk h).le

/-- The caterpillar on `Fin n` with a spine of `k` vertices. -/
def catGraph (n k : ℕ) (hk : 1 ≤ k) : SimpleGraph (Fin n) :=
  pg (fun v => ⟨par k v.val, lt_of_le_of_lt (par_le hk _) v.2⟩) (fun _ h => par_lt hk h)

theorem catGraph_isTree {n k : ℕ} (hk : 1 ≤ k) (hn : 0 < n) : (catGraph n k hk).IsTree :=
  pg_isTree hn _ _

theorem card_filter_mod_ge {k : ℕ} (hk : 0 < k) (L r : ℕ) (hr : r < k) :
    L ≤ k * ((range L).filter (fun t => t % k = r)).card + r := by
  have h := Nat.count_modEq_card hk (b := L) r
  rw [Nat.count_eq_card_filter_range] at h
  have e : (range L).filter (fun t => t ≡ r [MOD k]) = (range L).filter (fun t => t % k = r) := by
    apply filter_congr
    intro t _
    simp [Nat.ModEq, Nat.mod_eq_of_lt hr]
  rw [e, Nat.mod_eq_of_lt hr] at h
  rw [h]
  have h2 := Nat.div_add_mod L k
  split_ifs with hh
  · nlinarith [Nat.mod_lt L hk]
  · nlinarith

theorem catGraph_adj {n k : ℕ} (hk : 1 ≤ k) (u v : Fin n) :
    (catGraph n k hk).Adj u v ↔
      ((0 < v.val ∧ u.val = par k v.val) ∨ (0 < u.val ∧ v.val = par k u.val)) := by
  unfold catGraph pg
  simp only [Fin.ext_iff]

theorem cat_deg {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) [DecidableRel (catGraph n k hk).Adj]
    (w : Fin n) (hw : w.val < k) (r : ℕ) (hr : r < k) (hrw : lp k r = w.val) :
    ((range (n - k)).filter (fun t => t % k = r)).card +
      ((range k).filter (fun u => u + 1 = w.val ∨ w.val + 1 = u)).card
      ≤ (catGraph n k hk).degree w := by
  classical
  set A := ((range (n - k)).filter (fun t => t % k = r)).image (· + k) with hA
  set SP := (range k).filter (fun u => u + 1 = w.val ∨ w.val + 1 = u) with hSP
  have hdisj : Disjoint A SP := by
    rw [Finset.disjoint_left]
    intro u hu hu2
    simp only [hA, mem_image] at hu
    obtain ⟨t, _, rfl⟩ := hu
    simp only [hSP, mem_filter, mem_range] at hu2
    omega
  have hcard : A.card = ((range (n - k)).filter (fun t => t % k = r)).card :=
    card_image_of_injective _ (add_left_injective k)
  have hlt : ∀ u ∈ A ∪ SP, u < n := by
    intro u hu
    rcases mem_union.1 hu with hu | hu
    · simp only [hA, mem_image, mem_filter, mem_range] at hu
      obtain ⟨t, ⟨ht, _⟩, rfl⟩ := hu
      omega
    · simp only [hSP, mem_filter, mem_range] at hu
      omega
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← hcard, ← card_union_of_disjoint hdisj]
  refine card_le_card_of_injOn (fun u => if h : u < n then (⟨u, h⟩ : Fin n) else w) ?_ ?_
  · intro u hu
    have hun := hlt u hu
    simp only [coe_union, Set.mem_union, mem_coe] at hu
    simp only [hun, ↓reduceDIte, mem_coe, SimpleGraph.mem_neighborFinset]
    rw [catGraph_adj]
    rcases hu with hu | hu
    · simp only [hA, mem_image, mem_filter, mem_range] at hu
      obtain ⟨t, ⟨ht, htr⟩, rfl⟩ := hu
      left
      refine ⟨by show 0 < t + k; omega, ?_⟩
      have : ¬ (t + k < k) := by omega
      simp only [par, this, ↓reduceIte, Nat.add_sub_cancel, htr, ← hrw]
    · simp only [hSP, mem_filter, mem_range] at hu
      obtain ⟨huk, h | h⟩ := hu
      · right
        refine ⟨by omega, ?_⟩
        simp only [par, hw, ↓reduceIte]; omega
      · left
        refine ⟨by show 0 < u; omega, ?_⟩
        simp only [par, huk, ↓reduceIte]; omega
  · intro u hu u' hu' h
    have h1 := hlt u hu
    have h2 := hlt u' hu'
    simp only [h1, h2, ↓reduceDIte, Fin.mk.injEq] at h
    exact h

theorem spine_card_ge_one {k : ℕ} (hk2 : 2 ≤ k) {w : ℕ} (hw : w < k) :
    1 ≤ ((range k).filter (fun u => u + 1 = w ∨ w + 1 = u)).card := by
  rw [Nat.one_le_iff_ne_zero, Ne, card_eq_zero, ← Ne, ← nonempty_iff_ne_empty]
  by_cases h0 : w = 0
  · exact ⟨1, by simp only [mem_filter, mem_range]; omega⟩
  · exact ⟨w - 1, by simp only [mem_filter, mem_range]; omega⟩

theorem spine_card_ge_two {k : ℕ} {w : ℕ} (hw0 : 0 < w) (hw : w + 1 < k) :
    2 ≤ ((range k).filter (fun u => u + 1 = w ∨ w + 1 = u)).card := by
  have hsub : ({w - 1, w + 1} : Finset ℕ) ⊆ (range k).filter (fun u => u + 1 = w ∨ w + 1 = u) := by
    intro u hu
    simp only [mem_insert, mem_singleton] at hu
    simp only [mem_filter, mem_range]
    omega
  have := card_le_card hsub
  rwa [card_pair (by omega)] at this

theorem exists_caterpillar {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∃ T : SimpleGraph (Fin n), T.IsTree ∧ ∃ S : Finset (Fin n), S.card = k ∧
      ∀ v ∈ S, (n - 1 + k - 1) / k ≤ Nat.card (T.neighborSet v) := by
  classical
  refine ⟨catGraph n k hk, catGraph_isTree hk (by omega),
    univ.map (Fin.castLEEmb hkn), by simp, ?_⟩
  intro w hw
  simp only [mem_map, mem_univ, true_and] at hw
  obtain ⟨a, rfl⟩ := hw
  have hwk : (Fin.castLEEmb hkn a).val < k := a.2
  set w := Fin.castLEEmb hkn a with hwdef
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]
  suffices h : n - 1 ≤ k * (catGraph n k hk).degree w by
    have hk0 : 0 < k := hk
    have : (n - 1 + k - 1) / k < (catGraph n k hk).degree w + 1 := by
      rw [Nat.div_lt_iff_lt_mul hk0]
      rw [add_mul, one_mul, mul_comm]
      generalize k * (catGraph n k hk).degree w = Z at *
      omega
    omega
  have gen : ∀ (r s : ℕ), r < k → lp k r = w.val →
      s ≤ ((range k).filter (fun u => u + 1 = w.val ∨ w.val + 1 = u)).card →
      r + k ≤ k * s + 1 → n - 1 ≤ k * (catGraph n k hk).degree w := by
    intro r s hr hrw hs hneed
    have h1 := cat_deg hk hkn w hwk r hr hrw
    have h2 := card_filter_mod_ge hk (n - k) r hr
    have h3 := Nat.mul_le_mul_left k h1
    have h4 := Nat.mul_le_mul_left k hs
    rw [mul_add] at h3
    generalize k * ((range (n - k)).filter (fun t => t % k = r)).card = X at *
    generalize k * ((range k).filter (fun u => u + 1 = w.val ∨ w.val + 1 = u)).card = Y at *
    generalize k * (catGraph n k hk).degree w = Z at *
    omega
  by_cases hk1 : k = 1
  · subst hk1
    exact gen 0 0 (by omega) (by simp [lp]; omega) (Nat.zero_le _) (by omega)
  · have hk2 : 2 ≤ k := by omega
    by_cases hw0 : w.val = 0
    · exact gen 0 1 (by omega) (by simp [lp, hw0]) (spine_card_ge_one hk2 hwk) (by omega)
    · by_cases hwl : w.val + 1 = k
      · exact gen 1 1 (by omega) (by simp [lp]; omega) (spine_card_ge_one hk2 hwk) (by omega)
      · exact gen (w.val + 1) 2 (by omega) (by simp [lp]; omega)
          (spine_card_ge_two (by omega) (by omega)) (by omega)

theorem eq_sum_ite (a B : ℕ) (h : a ≤ B) :
    a = ∑ t ∈ range B, (if t < a then 1 else 0) := by
  rw [Finset.sum_boole]
  have : (range B).filter (fun t => t < a) = range a := by
    ext t; simp only [mem_filter, mem_range]; omega
  rw [this]; simp

/-- Layer-cake ordering lemma. If for every `k ∈ [1, n]` at least `k` vertices have `f v ≥ d k`,
then `∑ d k ≤ ∑ f v` (the monotonicity of `d` is not needed). -/
theorem sum_le_sum_degrees {V : Type*} [Fintype V] (n : ℕ)
    (f : V → ℕ) (d : ℕ → ℕ)
    (h : ∀ k ∈ Icc 1 n, ∃ S : Finset V, k ≤ S.card ∧ ∀ v ∈ S, d k ≤ f v) :
    ∑ k ∈ Icc 1 n, d k ≤ ∑ v, f v := by
  classical
  obtain ⟨B, hB⟩ : ∃ B, B = ∑ v, f v := ⟨_, rfl⟩
  have hfB : ∀ v, f v ≤ B := fun v =>
    hB ▸ single_le_sum (f := f) (fun _ _ => Nat.zero_le _) (mem_univ v)
  have hdB : ∀ k ∈ Icc 1 n, d k ≤ B := by
    intro k hk
    obtain ⟨S, hS, hS2⟩ := h k hk
    have hk1 := (mem_Icc.1 hk).1
    obtain ⟨v, hv⟩ : S.Nonempty := card_pos.1 (by omega)
    exact (hS2 v hv).trans (hfB v)
  have hL : ∑ v, f v = ∑ t ∈ range B, (univ.filter (fun v => t < f v)).card := by
    calc ∑ v, f v = ∑ v, ∑ t ∈ range B, (if t < f v then 1 else 0) :=
          sum_congr rfl (fun v _ => eq_sum_ite _ _ (hfB v))
      _ = ∑ t ∈ range B, ∑ v, (if t < f v then 1 else 0) := sum_comm
      _ = _ := by simp only [Finset.sum_boole, Nat.cast_id]
  have hR : ∑ k ∈ Icc 1 n, d k = ∑ t ∈ range B, ((Icc 1 n).filter (fun k => t < d k)).card := by
    calc ∑ k ∈ Icc 1 n, d k = ∑ k ∈ Icc 1 n, ∑ t ∈ range B, (if t < d k then 1 else 0) :=
          sum_congr rfl (fun k hk => eq_sum_ite _ _ (hdB k hk))
      _ = ∑ t ∈ range B, ∑ k ∈ Icc 1 n, (if t < d k then 1 else 0) := sum_comm
      _ = _ := by simp only [Finset.sum_boole, Nat.cast_id]
  rw [hL, hR]
  refine sum_le_sum (fun t _ => ?_)
  by_cases hK : ((Icc 1 n).filter (fun k => t < d k)).Nonempty
  · set K := (Icc 1 n).filter (fun k => t < d k) with hKdef
    have hm := K.max'_mem hK
    set m := K.max' hK
    rw [hKdef, mem_filter] at hm
    obtain ⟨S, hS, hS2⟩ := h m hm.1
    have h1 : K.card ≤ m := by
      have : K ⊆ Icc 1 m := by
        intro k hk
        have hk' := hk
        rw [hKdef, mem_filter, mem_Icc] at hk'
        rw [mem_Icc]
        exact ⟨hk'.1.1, K.le_max' k hk⟩
      simpa using card_le_card this
    have h2 : S.card ≤ (univ.filter (fun v => t < f v)).card := by
      refine card_le_card (fun v hv => ?_)
      rw [mem_filter]
      exact ⟨mem_univ _, lt_of_lt_of_le hm.2 (hS2 v hv)⟩
    omega
  · rw [not_nonempty_iff_eq_empty] at hK
    rw [hK]; simp

/-- **The panarboreal lower bound** (Chung–Graham 1979; the easy half of Theorem of the Day's «panarboreal formula»).
If a graph `G` on `n` vertices contains a copy of every tree on `n` vertices (an injective, adjacency-preserving map),
then `2 |E(G)| ≥ Σ_{k=1}^{n} ⌈(n − 1)/k⌉` (`⌈a/k⌉ = (a + k − 1)/k` in `ℕ`). Hence `s(n) ≥ ½ (n − 1) Hₙ ~ ½ n log n`.
Whether `s(n) ~ ½ n log n` (the constant `c ∈ [1/2, 5/log 4]`) is OPEN. -/
theorem sum_ceil_le_two_mul_card_edges (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : ∀ T : SimpleGraph (Fin n), T.IsTree →
      ∃ e : Fin n ↪ Fin n, ∀ u v, T.Adj u v → G.Adj (e u) (e v)) :
    ∑ k ∈ Icc 1 n, (n - 1 + k - 1) / k ≤ 2 * G.edgeFinset.card := by
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  refine sum_le_sum_degrees n (fun v => G.degree v) (fun k => (n - 1 + k - 1) / k) ?_
  intro k hk
  rw [mem_Icc] at hk
  obtain ⟨T, hT, S, hS, hSd⟩ := exists_caterpillar hk.1 hk.2
  obtain ⟨e, he⟩ := hG T hT
  refine ⟨S.map e, by simp [hS], ?_⟩
  intro v hv
  rw [mem_map] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  refine (hSd u hu).trans ?_
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_injective
    (fun x : T.neighborSet u => (⟨e x.1, he _ _ x.2⟩ : G.neighborSet (e u)))
    (fun x y h => Subtype.ext (e.injective (congrArg Subtype.val h)))


end Panarboreal
