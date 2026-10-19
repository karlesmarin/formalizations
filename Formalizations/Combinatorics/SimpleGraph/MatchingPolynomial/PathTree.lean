/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Godsil's path tree

The path tree `T(G, u)` of a graph `G` at a vertex `u` has as vertices the paths of `G` starting at
`u`; two paths are adjacent when one extends the other by one edge. It is a forest (indeed a tree)
rooted at the trivial path.

## Main definitions

* `SimpleGraph.PathFrom G u`: the paths of `G` starting at `u`, as `Σ v, G.Path u v`.
* `SimpleGraph.Grows a b`: `b` extends `a` by one edge.
* `SimpleGraph.pathTree G u`: the path tree.
* `SimpleGraph.pathTreeRoot G u`: its root, the trivial path.
* `SimpleGraph.prependRoot G hub`: prepending the edge `u b` to a path of `G - u` from `b`.

## Main results

* `SimpleGraph.pathTree_isAcyclic`: the path tree is acyclic.
* `SimpleGraph.Grows.parent_unique`: every path has at most one parent.
* `SimpleGraph.prependRoot_injective`, `SimpleGraph.prependRoot_grows`: prepending the root edge is
  injective and preserves the tree structure.

## References

* C. D. Godsil, *Matchings and walks in graphs*, J. Graph Theory 5 (1981) 285–297.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- A **path of `G` starting at `u`** (with its endpoint), the vertex type of the path
tree. `PathFrom G u := Σ v, G.Path u v`. -/
abbrev PathFrom (u : V) := Σ v, G.Path u v

variable {G}

/-- The length (number of edges) of a path-tree vertex. -/
abbrev PathFrom.length {u : V} (a : G.PathFrom u) : ℕ := a.2.1.length

/-- **`b` grows from `a`**: `b` is `a` with one further edge appended at the end. This is
the (directed) covering relation of the path tree. -/
def Grows {u : V} (a b : G.PathFrom u) : Prop :=
  ∃ he : G.Adj a.1 b.1, b.2.1 = a.2.1.concat he

variable (G)

/-- **Godsil's path tree `T(G, u)`.** Vertices are paths of `G` starting at `u`; two are
adjacent when one extends the other by a single edge. -/
def pathTree (u : V) : SimpleGraph (G.PathFrom u) where
  Adj a b := Grows a b ∨ Grows b a
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun a h => by
    rcases h with ⟨he, _⟩ | ⟨he, _⟩ <;> exact G.loopless.irrefl a.1 he⟩

variable {G}

@[simp] theorem pathTree_adj {u : V} (a b : G.PathFrom u) :
    (G.pathTree u).Adj a b ↔ Grows a b ∨ Grows b a := Iff.rfl

/-- The **root** of the path tree: the trivial path at `u`. -/
def pathTreeRoot (G : SimpleGraph V) (u : V) : G.PathFrom u := ⟨u, Path.nil⟩

/-! ## Structural lemmas: length, parent -/

/-- Growing adds exactly one edge: `length b = length a + 1`. -/
theorem Grows.length_eq {u : V} {a b : G.PathFrom u} (h : Grows a b) :
    b.length = a.length + 1 := by
  obtain ⟨he, hb⟩ := h
  simp only [PathFrom.length, hb, Walk.length_concat]

/-- Adjacent path-tree vertices differ in length by exactly one. -/
theorem pathTree_adj_length {u : V} {a b : G.PathFrom u} (h : (G.pathTree u).Adj a b) :
    b.length = a.length + 1 ∨ a.length = b.length + 1 :=
  h.imp Grows.length_eq Grows.length_eq

/-- **Uniqueness of the down-neighbour (parent).** If `b` grows from both `a` and `a'`
then `a = a'`: the parent of a path is unique (it is `dropLast`). The key reason the
path tree branches only upward — the heart of acyclicity. -/
theorem Grows.parent_unique {u : V} {a a' b : G.PathFrom u}
    (h : Grows a b) (h' : Grows a' b) : a = a' := by
  obtain ⟨av, ap, hap⟩ := a
  obtain ⟨a'v, a'p, ha'p⟩ := a'
  obtain ⟨he, hb⟩ := h
  obtain ⟨he', hb'⟩ := h'
  -- both express `b`'s walk as a concat; `concat_inj` forces equal endpoints and walks
  have hcat : ap.concat he = a'p.concat he' := by rw [← hb, ← hb']
  obtain ⟨hv, hw⟩ := Walk.concat_inj hcat
  subst hv
  rw [Walk.copy_rfl_rfl] at hw
  subst hw
  rfl

/-! ## The path tree is a forest -/

/-- **`T(G, u)` is acyclic — a forest.** Suppose a cycle existed. Rotate it to start
at a vertex `m` of **maximal** path-length in the cycle. Both cycle-neighbours of `m`
(its `snd` and `penultimate`) then have length `≤ m`, so — adjacency changing length by
exactly one — each has length `m − 1`, i.e. each *grows into* `m`. Hence each is a
**parent** of `m`; by `Grows.parent_unique` they coincide. But a cycle's second and
penultimate vertices are distinct (`IsCycle.snd_ne_penultimate`). Contradiction. So no
cycle exists, and the path tree is a forest — exactly what makes `μ(T(G,u))` the
characteristic polynomial of a symmetric matrix, hence real-rooted. -/
theorem pathTree_isAcyclic (G : SimpleGraph V) (u : V) : (G.pathTree u).IsAcyclic := by
  classical
  intro x c hc
  -- a vertex `m` of maximal length in the cycle's support
  obtain ⟨m, hm_eq⟩ : ∃ m, c.support.argmax PathFrom.length = some m := by
    rcases h : c.support.argmax PathFrom.length with _ | m
    · exact absurd (List.argmax_eq_none.mp h) c.support_ne_nil
    · exact ⟨m, rfl⟩
  have hm_mem : m ∈ c.support := List.argmax_mem hm_eq
  have hm_max : ∀ a ∈ c.support, a.length ≤ m.length :=
    fun a ha => List.le_of_mem_argmax ha hm_eq
  -- rotate the cycle so it starts at `m`
  have hc' : (c.rotate m hm_mem).IsCycle := (Walk.isCycle_rotate hm_mem).mpr hc
  have hnnil : ¬ (c.rotate m hm_mem).Nil := hc'.not_nil
  have hmax' : ∀ a ∈ (c.rotate m hm_mem).support, a.length ≤ m.length :=
    fun a ha => hm_max a ((Walk.mem_support_rotate_iff c m hm_mem).mp ha)
  -- the two cycle-neighbours of `m`
  have hsnd_mem : (c.rotate m hm_mem).snd ∈ (c.rotate m hm_mem).support :=
    Walk.getVert_mem_support _ 1
  have hpen_mem : (c.rotate m hm_mem).penultimate ∈ (c.rotate m hm_mem).support :=
    Walk.getVert_mem_support _ _
  have hsnd_adj : (G.pathTree u).Adj m (c.rotate m hm_mem).snd :=
    (c.rotate m hm_mem).adj_snd hnnil
  have hpen_adj : (G.pathTree u).Adj (c.rotate m hm_mem).penultimate m :=
    (c.rotate m hm_mem).adj_penultimate hnnil
  rw [pathTree_adj] at hsnd_adj hpen_adj
  -- both neighbours are shorter than `m`, hence both grow into `m` (parents of `m`)
  have hsnd_par : Grows (c.rotate m hm_mem).snd m := by
    rcases hsnd_adj with hg | hg
    · exact absurd hg.length_eq (by have := hmax' _ hsnd_mem; omega)
    · exact hg
  have hpen_par : Grows (c.rotate m hm_mem).penultimate m := by
    rcases hpen_adj with hg | hg
    · exact hg
    · exact absurd hg.length_eq (by have := hmax' _ hpen_mem; omega)
  -- unique parent ⟹ the two neighbours coincide, impossible in a cycle
  exact hc'.snd_ne_penultimate (hsnd_par.parent_unique hpen_par)

/-! ## Root decomposition `T(G,u) − r ≅ ⊔_{b∼u} T(G−u, b)` — the child embedding

Removing the root `r = (u)` from `T(G,u)` leaves, hanging from each child `(u,b)` (`b ∼ u`),
the subtree of paths through that edge. That subtree is `T(G−u, b)`: a path of `G` from `u`
with second vertex `b` is exactly `u` prepended to a path of `G−u` from `b` (`u` is never
revisited, so the tail lives in `G−u`). `prependRoot` is this injection; assembling it over
all `b ∼ u` (plus the isolated `r`) gives the decomposition, hence — via `matchingPoly_sum`
— `μ(T−r) = X·∏_{b∼u} μ(T(G−u,b))`, the product step of Godsil's divisibility. -/

/-- A walk starting at `a ≠ x` never visits an **isolated** vertex `x`. -/
theorem isolated_not_mem_support {W : Type*} {H : SimpleGraph W} {x : W}
    (hx : H.IsIsolated x) : ∀ {a c : W} (p : H.Walk a c), a ≠ x → x ∉ p.support := by
  intro a c p
  induction p with
  | nil => intro ha; simpa using ha.symm
  | @cons a b c h q ih =>
    intro ha
    simp only [Walk.support_cons, List.mem_cons, not_or]
    exact ⟨ha.symm, ih (fun hb => hx a (hb ▸ h.symm))⟩

/-- **Child embedding.** Prepend the root edge `u–b` to a path of `G−u` starting at `b`,
giving a path of `G` from `u` with second vertex `b` — the branch of `T(G,u)` hanging from
the root's child `(u,b)`, identified with `T(G−u, b)`. -/
def prependRoot (G : SimpleGraph V) {u b : V} (hub : G.Adj u b)
    (p : (G.deleteIncidenceSet u).PathFrom b) : G.PathFrom u :=
  ⟨p.1, Walk.cons hub (p.2.1.mapLe (G.deleteIncidenceSet_le u)), by
    rw [Walk.cons_isPath_iff]
    refine ⟨(Walk.isPath_mapLe (G.deleteIncidenceSet_le u)).mpr p.2.2, ?_⟩
    rw [Walk.support_mapLe_eq_support]
    exact isolated_not_mem_support
      (fun w hw => (deleteIncidenceSet_adj.mp hw).2.1 rfl) p.2.1 hub.ne.symm⟩

/-- The child embedding is **injective**: distinct subtree paths give distinct paths of `G`. -/
theorem prependRoot_injective (G : SimpleGraph V) {u b : V} (hub : G.Adj u b) :
    Function.Injective (prependRoot G hub) := by
  rintro ⟨v, p, hp⟩ ⟨v', q, hq⟩ h
  simp only [prependRoot, Sigma.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  rw [heq_eq_eq, Subtype.mk.injEq, Walk.cons.injEq] at h2
  obtain ⟨_, h3⟩ := h2
  have hinj : Function.Injective (Hom.ofLE (G.deleteIncidenceSet_le u)) := by
    rw [Hom.coe_ofLE]; exact Function.injective_id
  have : p = q := Walk.map_injective_of_injective hinj b v (eq_of_heq h3)
  subst this
  rfl

/-- `mapLe` distributes over `concat` (all `rfl`-glued except `map_append`); the target
edge `hc'` is supplied at the same endpoints, so no `ofLE`-coercion leaks into the type. -/
theorem mapLe_concat {W : Type*} {H H' : SimpleGraph W} (hle : H ≤ H') {a c d : W}
    (w : H.Walk a c) (hc : H.Adj c d) (hc' : H'.Adj c d) :
    (w.concat hc).mapLe hle = (w.mapLe hle).concat hc' := by
  show (w.concat hc).map (Hom.ofLE hle) = (w.map (Hom.ofLE hle)).concat hc'
  rw [Walk.concat_eq_append, Walk.map_append]
  rfl

/-- An endpoint of a path of `G−u` from `b ∼ u` is never `u`: it lies in the walk's support,
and `u` is isolated in `G−u`. -/
theorem pathFrom_fst_ne (G : SimpleGraph V) {u b : V} (hub : G.Adj u b)
    (p : (G.deleteIncidenceSet u).PathFrom b) : p.1 ≠ u :=
  ne_of_mem_of_not_mem p.2.1.end_mem_support
    (isolated_not_mem_support (fun _ hw => (deleteIncidenceSet_adj.mp hw).2.1 rfl)
      p.2.1 hub.ne.symm)

/-- **`Grows`-compatibility of the child embedding.** `prependRoot` both preserves and
reflects the covering relation `Grows`, so it is an isomorphism of the subtree `T(G−u, b)`
onto the branch of `T(G,u)` hanging from the root's child `(u,b)`. The forward direction
reconciles adjacency (`G.Adj p.1 q.1 ⟹ (G−u).Adj p.1 q.1`, valid since neither endpoint is
`u`) and cancels the prepended root edge; both use that `mapLe` commutes with `concat`. -/
theorem prependRoot_grows (G : SimpleGraph V) {u b : V} (hub : G.Adj u b)
    (p q : (G.deleteIncidenceSet u).PathFrom b) :
    Grows (prependRoot G hub p) (prependRoot G hub q) ↔ Grows p q := by
  have hle := G.deleteIncidenceSet_le u
  have hinj : Function.Injective (Hom.ofLE hle) := by
    rw [Hom.coe_ofLE]; exact Function.injective_id
  constructor
  · rintro ⟨he, heq⟩
    have he' : (G.deleteIncidenceSet u).Adj p.1 q.1 :=
      deleteIncidenceSet_adj.mpr ⟨he, pathFrom_fst_ne G hub p, pathFrom_fst_ne G hub q⟩
    refine ⟨he', ?_⟩
    replace heq : Walk.cons hub (q.2.1.mapLe hle)
        = Walk.cons hub ((p.2.1.mapLe hle).concat he) := heq
    injection heq with _ _ _ htail
    exact Walk.map_injective_of_injective hinj b q.1
      (htail.trans (mapLe_concat hle p.2.1 he' he).symm)
  · rintro ⟨he', heq⟩
    have heG : G.Adj p.1 q.1 := (deleteIncidenceSet_adj.mp he').1
    refine ⟨heG, ?_⟩
    show Walk.cons hub (q.2.1.mapLe hle) = (Walk.cons hub (p.2.1.mapLe hle)).concat heG
    rw [Walk.concat_cons, heq, mapLe_concat hle p.2.1 he' heG]

end SimpleGraph
