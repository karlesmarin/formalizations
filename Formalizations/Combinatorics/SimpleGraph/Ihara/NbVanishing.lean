/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.Combinatorics.SimpleGraph.Ihara.NbWalkCount
public import Formalizations.Combinatorics.SimpleGraph.Ihara.TreeLikeWalks

/-!
# Non-backtracking traces below the girth

A closed non-backtracking dart sequence of positive length contains a cycle of the graph of at most
its length. Hence `tr(Bᵏ) = 0` for `0 < k < g`, where `g` is the girth; below the girth both sides
of the trace-formula gap law `tr(Aᵏ) - #(tree-like closed walks) = tr(Bᵏ)` vanish.

## Main results

* `SimpleGraph.Walk.exists_isCycle_of_nbChain_of_not_nodup`: a non-backtracking walk that repeats a
  vertex contains a cycle no longer than itself.
* `SimpleGraph.relWalks_nbRel_closed_eq_empty`: there are no closed non-backtracking dart sequences
  of length `0 < k < g`.
* `SimpleGraph.trace_hashimoto_pow_eq_zero_of_lt_egirth`: `tr(Bᵏ) = 0` for `0 < k < g`.
* `SimpleGraph.treeLikeGap_eq_trace_hashimoto_of_lt_egirth`: the gap law below the girth.
-/

@[expose] public section

open Finset Matrix

/-! ## Anatomy of `relWalks` members (generic relation) -/

section RelWalks

variable {V : Type*} [Fintype V] [DecidableEq V] {r : V → V → Prop} [DecidableRel r]

/-- Every walk in `relWalks r k i j` is an `r`-chain. -/
theorem isChain_of_mem_relWalks {k : ℕ} {i j : V} {w : List V} (hw : w ∈ relWalks r k i j) :
    w.IsChain r := by
  induction k generalizing i w with
  | zero =>
    rw [relWalks] at hw
    split_ifs at hw with h
    · simp only [Finset.mem_singleton] at hw; subst hw; simp
    · simp at hw
  | succ k ih =>
    rw [relWalks, Finset.mem_biUnion] at hw
    obtain ⟨l, -, hl⟩ := hw
    split_ifs at hl with h
    · rw [Finset.mem_map] at hl
      obtain ⟨p, hp, rfl⟩ := hl
      have hhead := head?_of_mem_relWalks hp
      cases p with
      | nil => simp at hhead
      | cons a as =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst hhead
        exact List.isChain_cons_cons.mpr ⟨h, ih hp⟩
    · simp at hl

/-- Every walk in `relWalks r k i j` ends at `j`. -/
theorem getLast?_of_mem_relWalks {k : ℕ} {i j : V} {w : List V} (hw : w ∈ relWalks r k i j) :
    w.getLast? = some j := by
  induction k generalizing i w with
  | zero =>
    rw [relWalks] at hw
    split_ifs at hw with h
    · simp only [Finset.mem_singleton] at hw; subst hw; simp [h]
    · simp at hw
  | succ k ih =>
    rw [relWalks, Finset.mem_biUnion] at hw
    obtain ⟨l, -, hl⟩ := hw
    split_ifs at hl with h
    · rw [Finset.mem_map] at hl
      obtain ⟨p, hp, rfl⟩ := hl
      have hlast := ih hp
      cases p with
      | nil => simp at hlast
      | cons a as => simpa using hlast
    · simp at hl

/-- Every walk in `relWalks r k i j` visits `k + 1` vertices. -/
theorem length_of_mem_relWalks {k : ℕ} {i j : V} {w : List V} (hw : w ∈ relWalks r k i j) :
    w.length = k + 1 := by
  induction k generalizing i w with
  | zero =>
    rw [relWalks] at hw
    split_ifs at hw with h
    · simp only [Finset.mem_singleton] at hw; subst hw; rfl
    · simp at hw
  | succ k ih =>
    rw [relWalks, Finset.mem_biUnion] at hw
    obtain ⟨l, -, hl⟩ := hw
    split_ifs at hl with h
    · rw [Finset.mem_map] at hl
      obtain ⟨p, hp, rfl⟩ := hl
      simp [ih hp]
    · simp at hl

end RelWalks

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ## Dart-list anatomy of short walks -/

/-- A walk of length one consists of a single dart joining its endpoints. -/
theorem Walk.darts_eq_singleton_of_length_eq_one {x y : V} {q : G.Walk x y}
    (hq : q.length = 1) : ∃ hadj : G.Adj x y, q.darts = [⟨(x, y), hadj⟩] := by
  cases q with
  | nil => simp at hq
  | cons h q' =>
    cases q' with
    | nil => exact ⟨h, rfl⟩
    | cons h' q'' => simp only [Walk.length_cons] at hq; omega

/-! ## The key step: a non-backtracking chain with a repeated vertex contains a cycle -/

/-- **The cycle-extraction key step.** A walk whose darts form a non-backtracking chain
(`Chain' G.nbRel`) and whose support repeats a vertex contains a cycle of length at most the
walk's length, supported on the walk's own edges. Structural induction; the `takeUntil`
prefix of a nodup support is a path, so the only obstruction to closing the cycle — the
closing edge already lying on the path — forces an immediate backtrack, contradicting the
chain. -/
theorem Walk.exists_isCycle_of_nbChain_of_not_nodup [DecidableEq V] {u v : V} (w : G.Walk u v)
    (hnb : w.darts.IsChain G.nbRel) (hdup : ¬ w.support.Nodup) :
    ∃ (a : V) (c : G.Walk a a), c.IsCycle ∧ c.length ≤ w.length ∧ c.edges ⊆ w.edges := by
  induction w with
  | nil => simp at hdup
  | @cons u u₁ v h p ih =>
    rw [Walk.support_cons, List.nodup_cons] at hdup
    rw [Walk.darts_cons] at hnb
    by_cases hp : p.support.Nodup
    · -- the repeat must be `u` re-entering `p`
      have hu : u ∈ p.support := by tauto
      have hcPath : (p.takeUntil u hu).IsPath := (p.isPath_def.mpr hp).takeUntil hu
      by_cases hedge : s(u, u₁) ∈ (p.takeUntil u hu).edges
      · -- the closing edge lies on the path: forces a backtrack, contradicting the chain
        exfalso
        set c := p.takeUntil u hu with hc
        have hpen : u₁ = c.penultimate := hcPath.eq_penultimate_of_mem_edges hedge
        -- the path starts at its own penultimate vertex, so it has length exactly one
        have hlc0 : c.length ≠ 0 := by
          intro h0
          have hver := c.getVert_length
          rw [h0, Walk.getVert_zero] at hver
          exact h.ne hver.symm
        have hl1 : c.length = 1 := by
          by_contra hne
          have hgg : c.support[0]'(by simp) =
              c.support[c.length - 1]'(by rw [Walk.length_support]; omega) := by
            rw [Walk.support_getElem_eq_getVert, Walk.support_getElem_eq_getVert,
              Walk.getVert_zero]
            exact hpen
          have hfin := c.isPath_iff_injective_get_support.mp hcPath hgg
          have hval : (0 : ℕ) = c.length - 1 := congrArg Fin.val hfin
          omega
        obtain ⟨hadj, hcd⟩ := Walk.darts_eq_singleton_of_length_eq_one hl1
        -- the first dart of `p` is the reverse of the entering dart
        have hpd : p.darts = ⟨(u₁, u), hadj⟩ :: (p.dropUntil u hu).darts := by
          conv_lhs => rw [← p.take_spec hu]
          rw [Walk.darts_append, ← hc, hcd]
          rfl
        rw [hpd] at hnb
        exact (List.isChain_cons_cons.mp hnb).1.2 (Dart.ext _ _ rfl)
      · -- the closing edge is fresh: `cons h (takeUntil)` is a genuine cycle
        refine ⟨u, Walk.cons h (p.takeUntil u hu),
          ((p.takeUntil u hu).cons_isCycle_iff h).mpr ⟨hcPath, hedge⟩, ?_, ?_⟩
        · rw [Walk.length_cons, Walk.length_cons]
          exact Nat.succ_le_succ (p.length_takeUntil_le_length hu)
        · rw [Walk.edges_cons, Walk.edges_cons]
          exact List.cons_subset_cons _ (p.edges_takeUntil_subset_edges hu)
    · -- the repeat is inside `p`: recurse
      obtain ⟨a, c, hc, hlen, hsub⟩ := ih (List.isChain_of_isChain_cons hnb) hp
      refine ⟨a, c, hc, hlen.trans (by rw [Walk.length_cons]; exact Nat.le_succ _), ?_⟩
      rw [Walk.edges_cons]
      exact List.Subset.trans hsub (List.subset_cons_self _ _)

/-! ## Assembly: emptiness, vanishing trace, and the below-girth gap law

The dart-list → walk assembly is Mathlib's `Walk.ofDarts` on the FULL member list: the last
dart repeats the first, so the walk's support repeats a vertex (key step applies) and its edge
list has at most `k` distinct entries (pigeonhole bounds the extracted cycle below `g`). -/

variable [Fintype V] [DecidableEq V] (G) [DecidableRel G.Adj]

/-- **No closed non-backtracking walk below the girth.** -/
theorem relWalks_nbRel_closed_eq_empty {k : ℕ} (hk : 0 < k) (hg : (k : ℕ∞) < G.egirth)
    (e : G.Dart) : relWalks G.nbRel k e e = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro L hL
  have hch := isChain_of_mem_relWalks hL
  have hlen := length_of_mem_relWalks hL
  have hhead := head?_of_mem_relWalks hL
  have hlast := getLast?_of_mem_relWalks hL
  cases L with
  | nil => simp at hhead
  | cons d l =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    have hlf : (d :: l).length = k + 1 := hlen
    have hgl : (d :: l).getLast (by simp) = d := by
      rw [List.getLast?_eq_getLast_of_ne_nil (by simp), Option.some.injEq] at hlast
      exact hlast
    -- the dart at the closing position repeats the basepoint dart
    have hdk : (d :: l)[k]'(by omega) = d := by
      have := List.getLast_eq_getElem (l := d :: l) (by simp)
      rw [this] at hgl
      simpa [hlf] using hgl
    -- assemble the walk on ALL the darts
    have hchD : ((d :: l)).IsChain G.DartAdj :=
      hch.imp fun _ _ hab => hab.1
    set W := Walk.ofDarts (d :: l) (by simp) hchD with hW
    have hWd : W.darts = d :: l := by rw [hW, Walk.darts_ofDarts]
    have hWlen : W.length = k + 1 := by rw [hW, Walk.length_ofDarts, hlf]
    -- support repeats: positions 0 and k both carry `d.fst`
    have hdartk : W.darts[k]'(by rw [hWd, hlf]; omega) = d := by
      simp only [hWd]
      exact hdk
    have hdup : ¬ W.support.Nodup := by
      intro hnod
      have h0 : W.support[0]'(by rw [Walk.length_support, hWlen]; omega) = d.fst := by
        rw [Walk.support_getElem_eq_getVert, Walk.getVert_zero]
        simp
      have hk2 : W.support[k]'(by rw [Walk.length_support, hWlen]; omega) = d.fst := by
        have h2 := Walk.fst_darts_getElem (p := W) (i := k)
          (hi := by rw [Walk.length_darts, hWlen]; omega)
        rw [hdartk, List.getElem_dropLast] at h2
        exact h2.symm
      have hinj := List.nodup_iff_injective_get.mp hnod
      have := hinj (a₁ := ⟨0, by rw [Walk.length_support, hWlen]; omega⟩)
        (a₂ := ⟨k, by rw [Walk.length_support, hWlen]; omega⟩)
        (by simp only [List.get_eq_getElem, h0, hk2])
      simp only [Fin.mk.injEq] at this
      omega
    -- extract a cycle on at most k distinct edges: contradiction with the girth
    obtain ⟨a, c, hcyc, -, hsub⟩ := W.exists_isCycle_of_nbChain_of_not_nodup
      (by rw [hWd]; exact hch) hdup
    have hced : c.edges ⊆ W.edges.dedup := fun x hx =>
      List.mem_dedup.mpr (hsub hx)
    have hWed : ¬ W.edges.Nodup := by
      intro hnod
      have hinj := List.nodup_iff_injective_get.mp hnod
      have hWe : W.edges = (d :: l).map Dart.edge := by
        rw [hW, Walk.edges_ofDarts]
      have h0e : W.edges[0]'(by rw [hWe]; simp) = d.edge := by
        simp only [hWe, List.getElem_map, List.getElem_cons_zero]
      have hke : W.edges[k]'(by rw [hWe, List.length_map, hlf]; omega) = d.edge := by
        simp only [hWe, List.getElem_map, hdk]
      have := hinj (a₁ := ⟨0, by rw [hWe]; simp⟩)
        (a₂ := ⟨k, by rw [hWe, List.length_map, hlf]; omega⟩)
        (by simp only [List.get_eq_getElem, h0e, hke])
      simp only [Fin.mk.injEq] at this
      omega
    have hdlt : W.edges.dedup.length < W.edges.length := by
      have hsl := W.edges.dedup_sublist
      rcases hsl.length_le.lt_or_eq with hlt | heq
      · exact hlt
      · exact absurd (hsl.eq_of_length heq ▸ W.edges.nodup_dedup) hWed
    have hclen : c.length ≤ k := by
      have hnd : c.edges.Nodup := hcyc.isCircuit.isTrail.edges_nodup
      have h1 : c.edges.length ≤ W.edges.dedup.length := (hnd.subperm hced).length_le
      have h2 : W.edges.length = k + 1 := by rw [Walk.length_edges, hWlen]
      rw [Walk.length_edges] at h1
      omega
    have h1 : G.egirth ≤ (c.length : ℕ∞) := hcyc.egirth_le_length
    have h2 : (c.length : ℕ∞) ≤ (k : ℕ∞) := by exact_mod_cast hclen
    exact absurd ((h1.trans h2).trans_lt hg) (lt_irrefl _)

/-- **Lemma A, non-backtracking side.** Below the girth the Hashimoto traces vanish:
`tr(Bᵏ) = 0` for `1 ≤ k < g`. -/
theorem trace_hashimoto_pow_eq_zero_of_lt_egirth (R : Type*) [CommRing R] {k : ℕ}
    (hk : 0 < k) (hg : (k : ℕ∞) < G.egirth) :
    ((G.hashimoto R) ^ k).trace = 0 := by
  rw [trace_hashimoto_pow]
  simp [relWalks_nbRel_closed_eq_empty G hk hg]

/-- **Lemma A: the gap law below the girth.** For `1 ≤ k < g` both sides of the trace-formula
gap law vanish, so `gap_k = tr(Bᵏ)` holds (trivially) on the whole below-girth range. The
remaining window `k ∈ {g, g+1}` (where both sides equal `2k·c_k`) is Lemma B. -/
theorem treeLikeGap_eq_trace_hashimoto_of_lt_egirth {k : ℕ} (hk : 0 < k)
    (hg : (k : ℕ∞) < G.egirth) :
    G.treeLikeGap k = ((G.hashimoto ℤ) ^ k).trace := by
  rw [G.treeLikeGap_eq_zero_of_lt_egirth k hg,
    G.trace_hashimoto_pow_eq_zero_of_lt_egirth ℤ hk hg]

end SimpleGraph
