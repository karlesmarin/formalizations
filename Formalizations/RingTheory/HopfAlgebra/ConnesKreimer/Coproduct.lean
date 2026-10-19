/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Data.List.Perm.Basic

/-!
# The admissible-cut coproduct on planar rooted trees

Planar rooted trees (`RTree.node : List RTree → RTree`, so `B₊ = node`), forests (`List RTree`),
and the Connes–Kreimer / Foissy coproduct by admissible cuts, defined through the `B₊` cocycle
`Δ(B₊ F) = B₊ F ⊗ 𝟙 + (id ⊗ B₊)(Δ F)` on formal sums `List (Forest × Forest)`. Coassociativity
holds up to `List.Perm` (equality of formal sums).

## Main results

* `ConnesKreimer.coprodTree`, `ConnesKreimer.coprodForest`: the coproduct on trees and forests.
* `ConnesKreimer.tmul_assoc`: the leg-wise forest product on formal tensors is associative.
* `ConnesKreimer.coprodForest_append`: `Δ` is multiplicative (combinatorially).
* `ConnesKreimer.coprod_coassoc`: `(Δ ⊗ id) Δ t` and `(id ⊗ Δ) Δ t` agree up to permutation.

## Implementation notes

Mathlib's `RootedTree` (`Mathlib.Order.SuccPred.Tree`) is a rooted tree given by its ancestorship
order on a carrier type. It is not used here: the Hopf algebra needs a type whose elements are the
(isomorphism classes of) finite planar trees, to serve as a basis, and an inductive type gives that
with decidable, computable cuts. Trees are planar (ordered children); the commutative algebra is
the quotient of `Formalizations.RingTheory.HopfAlgebra.ConnesKreimer.Abelianization`.

## References

* A. Connes, D. Kreimer, *Hopf algebras, renormalization and noncommutative geometry*,
  Comm. Math. Phys. 199 (1998) 203–242.
* L. Foissy, *Les algèbres de Hopf des arbres enracinés décorés, I*, Bull. Sci. Math. 126 (2002)
  193–239.
* C. Marín, *How a Tree Remembers Its Cuts: the Connes–Kreimer–Foissy Hopf Algebra of Rooted Trees,
  Machine-Checked in Lean 4* (2026), doi:10.5281/zenodo.20762280. Ported from `ConnesKreimer.lean`
  of [karlesmarin/connes-kreimer-lean](https://github.com/karlesmarin/connes-kreimer-lean)
  (Lean v4.30.0-rc2).
-/

@[expose] public section

namespace ConnesKreimer

/-- Planar rooted trees, represented by the forest of children below the root. -/
inductive RTree where
  | node : List RTree → RTree
deriving Repr, Inhabited

/-- A planar rooted forest is a list of planar rooted trees. -/
abbrev Forest := List RTree

/-- Formal sums of coproduct tensor monomials, represented by their forest pairs. -/
abbrev Tens := List (Forest × Forest)

/-- Product on formal tensor monomials, multiplying the two tensor legs by forest concatenation. -/
def tmul (x y : Tens) : Tens :=
  x.flatMap (fun (p, r) => y.map (fun (p', r') => (p ++ p', r ++ r')))

mutual
  /-- The Connes-Kreimer coproduct on one rooted tree, as a formal list of tensor terms. -/
  def coprodTree : RTree → Tens
    | .node F => ([RTree.node F], []) :: (coprodForest F).map (fun (p, r) => (p, [RTree.node r]))
  /-- The multiplicative extension of the coproduct from trees to forests. -/
  def coprodForest : Forest → Tens
    | []      => [([], [])]
    | t :: ts => tmul (coprodTree t) (coprodForest ts)
end

@[simp] theorem tmul_unit_left (y : Tens) : tmul [([], [])] y = y := by simp [tmul]

@[simp] theorem tmul_unit_right (x : Tens) : tmul x [([], [])] = x := by
  induction x with
  | nil => rfl
  | cons a xs ih => obtain ⟨p, r⟩ := a; simp [tmul, List.append_nil]

theorem tmul_append_left (x₁ x₂ y : Tens) :
    tmul (x₁ ++ x₂) y = tmul x₁ y ++ tmul x₂ y := by simp [tmul, List.flatMap_append]

theorem tmul_cons (p r : Forest) (xs y : Tens) :
    tmul ((p, r) :: xs) y =
      y.map (fun (p', r') => (p ++ p', r ++ r')) ++ tmul xs y := by
  simp [tmul]

theorem tmul_assoc (x y z : Tens) : tmul (tmul x y) z = tmul x (tmul y z) := by
  induction x with
  | nil => rfl
  | cons a xs ih =>
    obtain ⟨p, r⟩ := a
    rw [tmul_cons, tmul_append_left, ih, tmul_cons]
    congr 1
    simp [tmul, List.flatMap_map, List.map_flatMap, List.append_assoc, Function.comp_def]

theorem coprodForest_append (F G : Forest) :
    coprodForest (F ++ G) = tmul (coprodForest F) (coprodForest G) := by
  induction F with
  | nil => simp [coprodForest, tmul_unit_left]
  | cons t ts ih =>
    change coprodForest (t :: (ts ++ G)) = _
    rw [show coprodForest (t :: (ts ++ G)) = tmul (coprodTree t) (coprodForest (ts ++ G)) from rfl,
        ih, ← tmul_assoc,
        show tmul (coprodTree t) (coprodForest ts) = coprodForest (t :: ts) from rfl]

open List in
theorem perm_middle_swap {α} (A B C D : List α) :
    ((A ++ B) ++ (C ++ D)).Perm ((A ++ C) ++ (B ++ D)) := by
  calc (A ++ B) ++ (C ++ D)
      = A ++ ((B ++ C) ++ D) := by simp [List.append_assoc]
    _ ~ A ++ ((C ++ B) ++ D) := (List.perm_append_comm).append_right D |>.append_left A
    _ = (A ++ C) ++ (B ++ D) := by simp [List.append_assoc]

open List in
theorem flatMap_append_distrib {α β} (l : List α) (X Y : α → List β) :
    (l.flatMap (fun a => X a ++ Y a)).Perm (l.flatMap X ++ l.flatMap Y) := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.flatMap_cons]
    refine (List.Perm.append_left (X a ++ Y a) ih).trans ?_
    exact perm_middle_swap (X a) (Y a) (as.flatMap X) (as.flatMap Y)

open List in
theorem flatMap_const_nil {α β} (l : List α) :
    l.flatMap (fun _ => ([] : List β)) = [] := by
  simp_all

theorem flatMap_singleton_eq_map {α β} (g : α → β) (l : List α) :
    l.flatMap (fun a => [g a]) = l.map g := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [List.flatMap_cons, ih]

open List in
theorem flatMap_comm {α β γ} (l1 : List α) (l2 : List β)
    (f : α → β → List γ) :
    (l1.flatMap (fun a => l2.flatMap (fun b => f a b))).Perm
    (l2.flatMap (fun b => l1.flatMap (fun a => f a b))) := by
  induction l1 with
  | nil => simp [flatMap_const_nil]
  | cons a as ih =>
    simp only [List.flatMap_cons]
    refine (List.Perm.append_right _ (List.Perm.refl _)).trans ?_
    refine (List.Perm.append_left (l2.flatMap (fun b => f a b)) ih).trans ?_
    exact (flatMap_append_distrib l2 (fun b => f a b) (fun b => as.flatMap (fun a => f a b))).symm

theorem Perm.flatMap_congr_right {α β} (l : List α) {f g : α → List β}
    (h : ∀ a, (f a).Perm (g a)) : (l.flatMap f).Perm (l.flatMap g) := by
  induction l with
  | nil => simp
  | cons a as ih => simp only [List.flatMap_cons]; exact (h a).append ih

/-- Formal sums of triple tensor monomials, represented by forest triples. -/
abbrev Tens3 := List (Forest × Forest × Forest)

/-- Expand the left tensor leg of every coproduct term. -/
def coLeft (x : Tens) : Tens3 :=
  x.flatMap (fun (p, r) => (coprodForest p).map (fun (a, b) => (a, b, r)))

/-- Expand the right tensor leg of every coproduct term. -/
def coRight (x : Tens) : Tens3 :=
  x.flatMap (fun (p, r) => (coprodForest r).map (fun (b, c) => (p, b, c)))

/-- Product on formal triple tensor monomials, multiplying all three tensor legs. -/
def tmul3 (x y : Tens3) : Tens3 :=
  x.flatMap (fun (a, b, c) => y.map (fun (a', b', c') => (a ++ a', b ++ b', c ++ c')))

theorem coLeft_tmul (x y : Tens) :
    (coLeft (tmul x y)).Perm (tmul3 (coLeft x) (coLeft y)) := by
  simp only [coLeft, tmul, tmul3, List.flatMap_map, List.map_flatMap, List.map_map,
    List.flatMap_assoc, Function.comp_def, coprodForest_append]
  exact Perm.flatMap_congr_right x (fun pr => flatMap_comm _ _ _)

theorem coRight_tmul (x y : Tens) :
    (coRight (tmul x y)).Perm (tmul3 (coRight x) (coRight y)) := by
  simp only [coRight, tmul, tmul3, List.flatMap_map, List.map_flatMap, List.map_map,
    List.flatMap_assoc, Function.comp_def, coprodForest_append]
  exact Perm.flatMap_congr_right x (fun pr => flatMap_comm _ _ _)

theorem coprodTree_node (F : Forest) :
    coprodTree (RTree.node F)
      = ([RTree.node F], []) :: (coprodForest F).map (fun pr => (pr.1, [RTree.node pr.2])) := rfl

theorem coprodForest_single (t : RTree) : coprodForest [t] = coprodTree t := by
  change tmul (coprodTree t) (coprodForest []) = coprodTree t
  rw [show coprodForest ([] : Forest) = [([], [])] from rfl, tmul_unit_right]

theorem tmul3_perm {a a' b b' : Tens3} (ha : a.Perm a') (hb : b.Perm b') :
    (tmul3 a b).Perm (tmul3 a' b') := by
  refine (ha.flatMap_right _).trans ?_
  exact Perm.flatMap_congr_right a' (fun _ => hb.map _)

mutual
  theorem coassocTree (t : RTree) :
      (coLeft (coprodTree t)).Perm (coRight (coprodTree t)) := by
    cases t with
    | node F =>
      simp only [coLeft, coRight, coprodTree_node, coprodForest_single, List.map_cons,
        List.flatMap_cons, List.map_map, List.flatMap_map, Function.comp_def,
        show coprodForest ([] : Forest) = [([], [])] from rfl]
      refine List.Perm.cons _ ?_
      have hR2 :
          (List.flatMap (fun a => (a.fst, [RTree.node a.snd], []) ::
              List.map (fun x => (a.fst, x.fst, [RTree.node x.snd])) (coprodForest a.snd))
              (coprodForest F)).Perm
          (List.map (fun x => (x.fst, [RTree.node x.snd], [])) (coprodForest F)
            ++ List.flatMap (fun a => List.map (fun x => (a.fst, x.fst, [RTree.node x.snd]))
                (coprodForest a.snd)) (coprodForest F)) := by
        have h := flatMap_append_distrib (coprodForest F)
          (fun a => [(a.fst, [RTree.node a.snd], [])])
          (fun a => List.map (fun x => (a.fst, x.fst, [RTree.node x.snd])) (coprodForest a.snd))
        rwa [flatMap_singleton_eq_map] at h
      have hkey :
          (List.flatMap (fun a => List.map (fun x => (x.fst, x.snd, [RTree.node a.snd]))
              (coprodForest a.fst)) (coprodForest F)).Perm
          (List.flatMap (fun a => List.map (fun x => (a.fst, x.fst, [RTree.node x.snd]))
              (coprodForest a.snd)) (coprodForest F)) := by
        have e1 :
            (List.flatMap (fun a => List.map (fun x => (x.fst, x.snd, [RTree.node a.snd]))
              (coprodForest a.fst)) (coprodForest F))
            = (coLeft (coprodForest F)).map (fun t => (t.1, t.2.1, [RTree.node t.2.2])) := by
          simp [coLeft, List.map_flatMap, List.map_map, Function.comp_def]
        have e2 :
            (List.flatMap (fun a => List.map (fun x => (a.fst, x.fst, [RTree.node x.snd]))
              (coprodForest a.snd)) (coprodForest F))
            = (coRight (coprodForest F)).map (fun t => (t.1, t.2.1, [RTree.node t.2.2])) := by
          simp [coRight, List.map_flatMap, List.map_map, Function.comp_def]
        rw [e1, e2]
        exact (coassocForest F).map _
      exact (List.Perm.append_left _ hkey).trans hR2.symm
  theorem coassocForest (F : Forest) :
      (coLeft (coprodForest F)).Perm (coRight (coprodForest F)) := by
    cases F with
    | nil => exact .refl _
    | cons t ts =>
      rw [show coprodForest (t :: ts) = tmul (coprodTree t) (coprodForest ts) from rfl]
      refine (coLeft_tmul _ _).trans ?_
      refine (tmul3_perm (coassocTree t) (coassocForest ts)).trans ?_
      exact (coRight_tmul _ _).symm
end

/-- **Coassociativity** of the Connes–Kreimer / Foissy (planar) coproduct on rooted trees:
    `(Δ⊗id)∘Δ` and `(id⊗Δ)∘Δ` agree as formal sums (multiset equality / `List.Perm`).
    Proved by mutual induction tree ↔ forest via the `B₊` Hochschild 1-cocycle,
    on top of multiplicativity and a Fubini swap. -/
theorem coprod_coassoc (t : RTree) :
    (coLeft (coprodTree t)).Perm (coRight (coprodTree t)) := coassocTree t

/-! ### Examples: `Δ(•) = •⊗1 + 1⊗•`, `Δ(ℓ₂)` has three terms, and
    `Δ(cherry) = cherry⊗1 + 2 •⊗ℓ₂ + ••⊗• + 1⊗cherry` five. -/

example : (coprodTree (.node [])).length = 2 := by decide
example : (coprodTree (.node [.node []])).length = 3 := by decide
example : (coprodTree (.node [.node [], .node []])).length = 5 := by decide

end ConnesKreimer
