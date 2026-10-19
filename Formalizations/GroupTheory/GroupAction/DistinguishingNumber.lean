/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Group.Submonoid.MulAction
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fin.VecNotation

/-!
# Distinguishing numbers of group actions

A coloring `c : X → Fin k` of a `G`-set `X` is distinguishing if the identity is the only element of
`G` preserving it, and the distinguishing number is the least such `k`. This file develops the basic
API and computes the distinguishing number of the collineation group of the Fano plane acting on its
seven points: it is `4`. The values are those of Klavžar, Wong and Zhu; the lower bound checks all
`3⁷` colorings against a list of 21 involutions with `decide`, and the upper bound is a structural
argument from the lines.

## Main definitions

* `TotD.IsDistinguishing`, `TotD.distinguishingNumber`.
* `TotD.fanoGroup`: the stabilizer of the seven lines of the Fano plane in `Equiv.Perm (Fin 7)`.

## Main results

* `TotD.IsDistinguishing.mono`, `TotD.distinguishingNumber_le_card`,
  `TotD.distinguishingNumber_le_card_base_add_one`: monotonicity, `D ≤ #X` for faithful actions,
  `D ≤ b + 1` for a base of size `b`.
* `TotD.fano_not_isDistinguishing_two`, `TotD.fano_not_isDistinguishing_three`,
  `TotD.fanoColoring_isDistinguishing`.
* `TotD.fano_distinguishingNumber`: `distinguishingNumber fanoGroup (Fin 7) = 4`.

## References

* M. O. Albertson, K. L. Collins, *Symmetry breaking in graphs*, Electron. J. Combin. 3 (1996) R18.
* S. Klavžar, T.-L. Wong, X. Zhu, *Distinguishing labellings of group action on vector spaces and
  graphs*, J. Algebra 303 (2006) 626–641.
-/

@[expose] public section

open MulAction Pointwise

-- The Fano decide lemmas (`fanoWitnesses_spec`, `fanoWitnesses_cover`) exhaust
-- thousands of colorings / nested-`Finset` membership checks in the kernel; raise the
-- elaboration recursion limit so `decide` can unfold them.
set_option maxRecDepth 10000

namespace TotD

/-! ### Distinguishing colorings and the distinguishing number, in general -/

/-- A coloring `c : X → Fin k` is *distinguishing* for the action of `G` on `X` if the
only `g : G` preserving the coloring is the identity (Albertson–Collins 1996;
Tymoczko 2004 for arbitrary group actions). -/
def IsDistinguishing (G : Type*) {X : Type*} [Group G] [MulAction G X] {k : ℕ}
    (c : X → Fin k) : Prop :=
  ∀ g : G, (∀ x : X, c (g • x) = c x) → g = 1

/-- The *distinguishing number* `D(G ↷ X)`: the least number of colors admitting a
distinguishing coloring (`sInf`, so `0` if no coloring distinguishes — e.g. an
unfaithful action of a nontrivial group on a finite set). -/
noncomputable def distinguishingNumber (G X : Type*) [Group G] [MulAction G X] : ℕ :=
  sInf {k : ℕ | ∃ c : X → Fin k, IsDistinguishing G c}

variable {G X : Type*} [Group G] [MulAction G X]

/-- Monotonicity: a distinguishing `k`-coloring yields a distinguishing `m`-coloring
for any `m ≥ k` (recolor through the inclusion `Fin k ↪ Fin m`). -/
theorem IsDistinguishing.mono {k m : ℕ} (hkm : k ≤ m) {c : X → Fin k}
    (hc : IsDistinguishing G c) :
    IsDistinguishing G fun x : X => (⟨(c x).1, (c x).2.trans_le hkm⟩ : Fin m) :=
  fun g hg => hc g fun x => by
    have h := congrArg Fin.val (hg x)
    exact Fin.ext h

/-- Existence form of monotonicity: the set of color counts admitting a distinguishing
coloring is upward closed. -/
theorem exists_isDistinguishing_mono {k m : ℕ} (hkm : k ≤ m)
    (h : ∃ c : X → Fin k, IsDistinguishing G c) :
    ∃ c : X → Fin m, IsDistinguishing G c :=
  let ⟨_, hc⟩ := h
  ⟨_, hc.mono hkm⟩

/-- A distinguishing `k`-coloring bounds the distinguishing number: `D ≤ k`. -/
theorem distinguishingNumber_le {k : ℕ} {c : X → Fin k} (hc : IsDistinguishing G c) :
    distinguishingNumber G X ≤ k :=
  Nat.sInf_le ⟨c, hc⟩

/-- Lower bound: if some coloring distinguishes (so the defining set is nonempty) but
no `k`-coloring does, then `k < D`. -/
theorem lt_distinguishingNumber {k m : ℕ} {c : X → Fin m} (hc : IsDistinguishing G c)
    (hnone : ∀ c' : X → Fin k, ¬IsDistinguishing G c') :
    k < distinguishingNumber G X := by
  rcases Nat.lt_or_ge k (distinguishingNumber G X) with hlt | hge
  · exact hlt
  · have hmem := Nat.sInf_mem
      (s := {n : ℕ | ∃ c' : X → Fin n, IsDistinguishing G c'}) ⟨m, c, hc⟩
    obtain ⟨c₁, hc₁⟩ := exists_isDistinguishing_mono hge hmem
    exact absurd hc₁ (hnone c₁)

/-- A faithful action on a finite set is distinguished by the all-distinct coloring:
`D ≤ |X|`. -/
theorem distinguishingNumber_le_card [Fintype X] [FaithfulSMul G X] :
    distinguishingNumber G X ≤ Fintype.card X :=
  distinguishingNumber_le (c := fun x => Fintype.equivFin X x) fun g hg =>
    eq_of_smul_eq_smul (α := X) fun x => by
      rw [one_smul]
      exact (Fintype.equivFin X).injective (hg x)

/-- **Bases and distinguishing colorings**: a base of size `b` — a finite set whose
pointwise stabilizer is trivial — gives `D ≤ b + 1`: color the base points with `b`
distinct nonzero colors and everything else with `0`. -/
theorem distinguishingNumber_le_card_base_add_one [DecidableEq X] (S : Finset X)
    (hS : ∀ g : G, (∀ x ∈ S, g • x = x) → g = 1) :
    distinguishingNumber G X ≤ S.card + 1 := by
  have key : IsDistinguishing G fun x : X =>
      if h : x ∈ S then (S.equivFin ⟨x, h⟩).succ else (0 : Fin (S.card + 1)) := by
    intro g hg
    refine hS g fun x hx => ?_
    have hgx : (if h : g • x ∈ S then (S.equivFin ⟨g • x, h⟩).succ
        else (0 : Fin (S.card + 1))) =
        (if h : x ∈ S then (S.equivFin ⟨x, h⟩).succ else (0 : Fin (S.card + 1))) := hg x
    rw [dite_eq_left hx] at hgx
    by_cases hmem : g • x ∈ S
    · rw [dite_eq_left hmem] at hgx
      have : (⟨g • x, hmem⟩ : S) = ⟨x, hx⟩ :=
        S.equivFin.injective (Fin.ext (Nat.succ.inj (congrArg Fin.val hgx)))
      exact congrArg Subtype.val this
    · rw [dite_eq_right hmem] at hgx
      exact absurd hgx.symm (Fin.succ_ne_zero _)
  exact distinguishingNumber_le key

/-! ### The Fano exception: `D(GL(3,2) ↷ F₂³ \ {0}) = 4`

Points `0, …, 6 : Fin 7` stand for the nonzero vectors of `F₂³`: point `i` is the
vector whose binary digits are those of `i + 1` (so `0 ↔ (1,0,0)`, `1 ↔ (0,1,0)`,
`2 ↔ (1,1,0)`, `3 ↔ (0,0,1)`, `4 ↔ (1,0,1)`, `5 ↔ (0,1,1)`, `6 ↔ (1,1,1)`).
A triple is a line of the Fano plane iff the corresponding vectors sum to zero, and a
permutation of the points is induced by a (unique) element of `GL(3,2)` iff it maps
lines to lines. -/

/-- The 7 lines of the Fano plane on `Fin 7` (triples whose vectors XOR to zero). -/
def fanoLines : Finset (Finset (Fin 7)) :=
  {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}}

/-- The collineation group of the Fano plane: the stabilizer in `Equiv.Perm (Fin 7)`
of the line set. Abstractly `GL(3,2) ≅ PSL(2,7)`, of order 168, in its natural action
on the nonzero vectors of `F₂³`. -/
def fanoGroup : Subgroup (Equiv.Perm (Fin 7)) :=
  MulAction.stabilizer (Equiv.Perm (Fin 7)) fanoLines

instance : DecidablePred (· ∈ fanoGroup) := fun g =>
  decidable_of_iff (g • fanoLines = fanoLines) MulAction.mem_stabilizer_iff.symm

-- The collineation group of the Fano plane has order 168 (`= |GL(3,2)| = |PSL(2,7)|`),
-- the classical count of Fano structures on 7 points. The cardinality is not proved here: `decide`
-- on the subtype
-- fintype of `Equiv.Perm (Fin 7)` (5040 elements, each a nested-`Finset` membership test)
-- blows up the kernel (>19 GB), and the `D = 4` result below does not depend on it.

/-- Build an involutive permutation of `Fin 7` from its vector of images. -/
def involPerm (v : Fin 7 → Fin 7) (h : ∀ x, v (v x) = x) : Equiv.Perm (Fin 7) :=
  ⟨v, v, h, h⟩

/-- 21 involutions of `fanoGroup` (the transvections of `GL(3,2)`), listed in greedy
cover order: every 3-coloring of the 7 points is preserved by at least one of them
(`fanoWitnesses_cover`). -/
def fanoWitnesses : List (Equiv.Perm (Fin 7)) :=
  [involPerm ![0, 1, 2, 4, 3, 6, 5] (by decide),
   involPerm ![0, 3, 4, 1, 2, 5, 6] (by decide),
   involPerm ![0, 5, 6, 3, 4, 1, 2] (by decide),
   involPerm ![2, 1, 0, 3, 6, 5, 4] (by decide),
   involPerm ![1, 0, 2, 3, 5, 4, 6] (by decide),
   involPerm ![3, 1, 5, 0, 4, 2, 6] (by decide),
   involPerm ![0, 4, 3, 2, 1, 5, 6] (by decide),
   involPerm ![3, 6, 2, 0, 4, 5, 1] (by decide),
   involPerm ![0, 2, 1, 3, 4, 6, 5] (by decide),
   involPerm ![0, 1, 2, 5, 6, 3, 4] (by decide),
   involPerm ![0, 1, 2, 6, 5, 4, 3] (by decide),
   involPerm ![0, 2, 1, 4, 3, 5, 6] (by decide),
   involPerm ![0, 6, 5, 3, 4, 2, 1] (by decide),
   involPerm ![1, 0, 2, 6, 4, 5, 3] (by decide),
   involPerm ![2, 1, 0, 5, 4, 3, 6] (by decide),
   involPerm ![4, 1, 6, 3, 0, 5, 2] (by decide),
   involPerm ![4, 5, 2, 3, 0, 1, 6] (by decide),
   involPerm ![5, 1, 3, 2, 4, 0, 6] (by decide),
   involPerm ![5, 4, 2, 3, 1, 0, 6] (by decide),
   involPerm ![6, 1, 4, 3, 2, 5, 0] (by decide),
   involPerm ![6, 3, 2, 1, 4, 5, 0] (by decide)]

/-- Every witness is a nontrivial element of the collineation group. Kernel `decide`
(the `p ∈ fanoGroup` checks are nested-`Finset` line-set equalities, too heavy for the
heartbeat-bounded elaborator; only 21 items, so the kernel handles them quickly). -/
theorem fanoWitnesses_spec :
    ∀ p ∈ fanoWitnesses, p ∈ fanoGroup ∧ ∃ x : Fin 7, p x ≠ x := by decide +kernel

private theorem dec7 (y : Fin 7) :
    y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 := by
  revert y; decide

private theorem vec_apply {α : Type*} (c : Fin 7 → α) (x : Fin 7) :
    ![c 0, c 1, c 2, c 3, c 4, c 5, c 6] x = c x := by
  rcases dec7 x with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **Kernel-checked cover**: each of the `3^7 = 2187` colorings of the Fano points is
preserved by at least one of the 21 witnesses. This is the entire exhaustive content
of "no 3-coloring distinguishes", packed into one plain `decide`. -/
theorem fanoWitnesses_cover : ∀ a b c d e f g : Fin 3,
    ∃ p ∈ fanoWitnesses, ∀ x : Fin 7,
      ![a, b, c, d, e, f, g] (p x) = ![a, b, c, d, e, f, g] x := by decide +kernel

/-- No 3-coloring of the Fano points is distinguishing (Klavžar–Wong–Zhu 2006 for `GL(3,2)`). -/
theorem fano_not_isDistinguishing_three (c : Fin 7 → Fin 3) :
    ¬IsDistinguishing ↥fanoGroup c := by
  intro hc
  obtain ⟨p, hp, hpres⟩ := fanoWitnesses_cover (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6)
  obtain ⟨hmem, x, hx⟩ := fanoWitnesses_spec p hp
  have h1 : (⟨p, hmem⟩ : ↥fanoGroup) = 1 :=
    hc ⟨p, hmem⟩ fun y => (vec_apply c (p y)).symm.trans ((hpres y).trans (vec_apply c y))
  exact hx (congrArg (fun q : Equiv.Perm (Fin 7) => q x) (congrArg Subtype.val h1))

/-- No 2-coloring of the Fano points is distinguishing (so `D ≥ 3`; in fact `D = 4`). -/
theorem fano_not_isDistinguishing_two (c : Fin 7 → Fin 2) :
    ¬IsDistinguishing ↥fanoGroup c := fun hc =>
  fano_not_isDistinguishing_three _ (hc.mono (by decide))

/-- A distinguishing 4-coloring: points `0,1,2,3` share color `0`,
points `4,5,6` get the unique colors `1,2,3`. In vector terms the color classes are
`{(1,0,0), (0,1,0), (1,1,0), (0,0,1)}`, `{(1,0,1)}`, `{(0,1,1)}`, `{(1,1,1)}`. -/
def fanoColoring : Fin 7 → Fin 4 := ![0, 0, 0, 0, 1, 2, 3]

/-- The coloring `(0,0,0,0,1,2,3)` is distinguishing. Structural proof from the line
geometry: the unique colors pin `4, 5, 6`; the lines `{2,4,5}`, `{0,5,6}`, `{1,4,6}`
are the unique lines through their two pinned points, so `2, 0, 1` are pinned;
injectivity pins `3`. -/
theorem fanoColoring_isDistinguishing : IsDistinguishing ↥fanoGroup fanoColoring := by
  rintro ⟨g, hg⟩ hfix
  have hfix' : ∀ x : Fin 7, fanoColoring (g x) = fanoColoring x := hfix
  -- the unique colors 1, 2, 3 pin the points 4, 5, 6
  have h4 : g 4 = 4 :=
    (by decide : ∀ y : Fin 7, fanoColoring y = 1 → y = 4) _ ((hfix' 4).trans (by decide))
  have h5 : g 5 = 5 :=
    (by decide : ∀ y : Fin 7, fanoColoring y = 2 → y = 5) _ ((hfix' 5).trans (by decide))
  have h6 : g 6 = 6 :=
    (by decide : ∀ y : Fin 7, fanoColoring y = 3 → y = 6) _ ((hfix' 6).trans (by decide))
  -- g maps lines to lines
  have hstab : g • fanoLines = fanoLines := MulAction.mem_stabilizer_iff.mp hg
  have hline : ∀ L ∈ fanoLines, g • L ∈ fanoLines := fun L hL => by
    rw [← hstab]; exact Finset.smul_mem_smul_finset hL
  have happ : ∀ (L : Finset (Fin 7)) (y : Fin 7), y ∈ L → g y ∈ g • L := fun L y hy => by
    have := Finset.smul_mem_smul_finset (a := g) hy
    rwa [Equiv.Perm.smul_def] at this
  -- the line {2,4,5} is the unique line through 4 and 5, so 2 is pinned
  have h2 : g 2 = 2 := by
    have hM : g • ({2, 4, 5} : Finset (Fin 7)) ∈ fanoLines := hline _ (by decide)
    have m4 : (4 : Fin 7) ∈ g • ({2, 4, 5} : Finset (Fin 7)) := by
      have h := happ ({2, 4, 5} : Finset (Fin 7)) 4 (by decide); rwa [h4] at h
    have m5 : (5 : Fin 7) ∈ g • ({2, 4, 5} : Finset (Fin 7)) := by
      have h := happ ({2, 4, 5} : Finset (Fin 7)) 5 (by decide); rwa [h5] at h
    have hM245 : g • ({2, 4, 5} : Finset (Fin 7)) = {2, 4, 5} :=
      (by decide : ∀ M ∈ fanoLines, (4 : Fin 7) ∈ M → (5 : Fin 7) ∈ M → M = {2, 4, 5})
        _ hM m4 m5
    have m2 : g 2 ∈ ({2, 4, 5} : Finset (Fin 7)) := by
      have h := happ ({2, 4, 5} : Finset (Fin 7)) 2 (by decide); rwa [hM245] at h
    rcases (by decide : ∀ y : Fin 7, y ∈ ({2, 4, 5} : Finset (Fin 7)) →
        y = 2 ∨ y = 4 ∨ y = 5) _ m2 with h | h | h
    · exact h
    · exact absurd (g.injective (h.trans h4.symm)) (by decide)
    · exact absurd (g.injective (h.trans h5.symm)) (by decide)
  -- the line {0,5,6} is the unique line through 5 and 6, so 0 is pinned
  have h0 : g 0 = 0 := by
    have hM : g • ({0, 5, 6} : Finset (Fin 7)) ∈ fanoLines := hline _ (by decide)
    have m5 : (5 : Fin 7) ∈ g • ({0, 5, 6} : Finset (Fin 7)) := by
      have h := happ ({0, 5, 6} : Finset (Fin 7)) 5 (by decide); rwa [h5] at h
    have m6 : (6 : Fin 7) ∈ g • ({0, 5, 6} : Finset (Fin 7)) := by
      have h := happ ({0, 5, 6} : Finset (Fin 7)) 6 (by decide); rwa [h6] at h
    have hM056 : g • ({0, 5, 6} : Finset (Fin 7)) = {0, 5, 6} :=
      (by decide : ∀ M ∈ fanoLines, (5 : Fin 7) ∈ M → (6 : Fin 7) ∈ M → M = {0, 5, 6})
        _ hM m5 m6
    have m0 : g 0 ∈ ({0, 5, 6} : Finset (Fin 7)) := by
      have h := happ ({0, 5, 6} : Finset (Fin 7)) 0 (by decide); rwa [hM056] at h
    rcases (by decide : ∀ y : Fin 7, y ∈ ({0, 5, 6} : Finset (Fin 7)) →
        y = 0 ∨ y = 5 ∨ y = 6) _ m0 with h | h | h
    · exact h
    · exact absurd (g.injective (h.trans h5.symm)) (by decide)
    · exact absurd (g.injective (h.trans h6.symm)) (by decide)
  -- the line {1,4,6} is the unique line through 4 and 6, so 1 is pinned
  have h1 : g 1 = 1 := by
    have hM : g • ({1, 4, 6} : Finset (Fin 7)) ∈ fanoLines := hline _ (by decide)
    have m4 : (4 : Fin 7) ∈ g • ({1, 4, 6} : Finset (Fin 7)) := by
      have h := happ ({1, 4, 6} : Finset (Fin 7)) 4 (by decide); rwa [h4] at h
    have m6 : (6 : Fin 7) ∈ g • ({1, 4, 6} : Finset (Fin 7)) := by
      have h := happ ({1, 4, 6} : Finset (Fin 7)) 6 (by decide); rwa [h6] at h
    have hM146 : g • ({1, 4, 6} : Finset (Fin 7)) = {1, 4, 6} :=
      (by decide : ∀ M ∈ fanoLines, (4 : Fin 7) ∈ M → (6 : Fin 7) ∈ M → M = {1, 4, 6})
        _ hM m4 m6
    have m1 : g 1 ∈ ({1, 4, 6} : Finset (Fin 7)) := by
      have h := happ ({1, 4, 6} : Finset (Fin 7)) 1 (by decide); rwa [hM146] at h
    rcases (by decide : ∀ y : Fin 7, y ∈ ({1, 4, 6} : Finset (Fin 7)) →
        y = 1 ∨ y = 4 ∨ y = 6) _ m1 with h | h | h
    · exact h
    · exact absurd (g.injective (h.trans h4.symm)) (by decide)
    · exact absurd (g.injective (h.trans h6.symm)) (by decide)
  -- injectivity pins the last point 3
  have h3 : g 3 = 3 := by
    rcases dec7 (g 3) with h | h | h | h | h | h | h
    · exact absurd (g.injective (h.trans h0.symm)) (by decide)
    · exact absurd (g.injective (h.trans h1.symm)) (by decide)
    · exact absurd (g.injective (h.trans h2.symm)) (by decide)
    · exact h
    · exact absurd (g.injective (h.trans h4.symm)) (by decide)
    · exact absurd (g.injective (h.trans h5.symm)) (by decide)
    · exact absurd (g.injective (h.trans h6.symm)) (by decide)
  refine Subtype.ext (Equiv.ext fun x => ?_)
  rcases dec7 x with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4, h5, h6]

/-- **The Fano exception, machine-checked** (Klavžar–Wong–Zhu, J. Algebra 303 (2006),
Thm 3.1, the unique `D = 4` case; answers part of Chan's Question 4):
the distinguishing number of `GL(3,2) ≅ PSL(2,7)` acting on the 7 nonzero vectors of
`F₂³` — equivalently, of the collineation group of the Fano plane acting on its
points — is exactly 4. -/
theorem fano_distinguishingNumber : distinguishingNumber ↥fanoGroup (Fin 7) = 4 :=
  le_antisymm (distinguishingNumber_le fanoColoring_isDistinguishing)
    (lt_distinguishingNumber fanoColoring_isDistinguishing fano_not_isDistinguishing_three)

end TotD
