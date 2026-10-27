/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.Function
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Bondy's theorem on induced subsets

If `F` is a family of at most `|X|` distinct finite sets and `X` is nonempty, some `x ∈ X` can be
deleted from all of them and they stay distinct (Bondy, 1972; Bondy states it for subsets of an
`n`-set, the inclusion is not needed). Proof by rank over `ZMod 2`: if every `x ∈ X` is bad, choose
`A_x ≠ B_x` in `F` with the same erasure; their indicator vectors differ by the unit vector at `x`.
These `|X|` unit vectors are linearly independent but lie in the span of the differences
`ind C - ind A₀`, `C ∈ F`, of dimension at most `|F| - 1 < |X|`.

## Main results

* `Bondy.exists_erase_injOn`: at most |X| distinct sets stay distinct after deleting some x in X

## References

* J. A. Bondy, *Induced subsets*, J. Combin. Theory Ser. B 12 (1972), 201–202.
-/

@[expose] public section

namespace Bondy

open Module

/-- Indicator vector of a finset, over `ZMod 2`. -/
private def ind {α : Type*} [DecidableEq α] (A : Finset α) : α → ZMod 2 :=
  fun y => if y ∈ A then 1 else 0

private lemma ind_sub_single {α : Type*} [DecidableEq α] (x : α) (A B : Finset α)
    (hAB : A.erase x = B.erase x) (hne : A ≠ B) :
    ind A - ind B = Pi.single x 1 := by
  have hx : (x ∈ A) ≠ (x ∈ B) := by
    intro h
    apply hne
    ext y
    by_cases hy : y = x
    · subst hy; exact h.to_iff
    · have := congrArg (fun S => y ∈ S) hAB
      simpa [Finset.mem_erase, hy] using this
  funext y
  by_cases hy : y = x
  · subst hy
    by_cases ha : y ∈ A
    · have hb : y ∉ B := fun hb => hx (by simp [ha, hb])
      simp [ind, ha, hb]
    · have hb : y ∈ B := by_contra fun hb => hx (by simp [ha, hb])
      simp [ind, ha, hb]
  · have := congrArg (fun S => y ∈ S) hAB
    have h2 : (y ∈ A) ↔ (y ∈ B) := by simpa [Finset.mem_erase, hy] using this
    by_cases ha : y ∈ A
    · simp [ind, ha, h2.1 ha, hy]
    · simp [ind, ha, mt h2.2 ha, hy]

/-- **Bondy's theorem (1972).** A family of at most `|X|` distinct finite sets, `X` nonempty, has an
element `x ∈ X` such that deleting `x` keeps the sets distinct. The sets need not be subsets of `X`
(Bondy's statement takes subsets of an `n`-set). -/
theorem exists_erase_injOn {α : Type*} [DecidableEq α] (X : Finset α) (hX : X.Nonempty)
    (F : Finset (Finset α)) (hcard : F.card ≤ X.card) :
    ∃ x ∈ X, Set.InjOn (fun A : Finset α => A.erase x) (F : Set (Finset α)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  have hbad : ∀ x : X, ∃ A ∈ F, ∃ B ∈ F, A.erase x.1 = B.erase x.1 ∧ A ≠ B := by
    intro x
    have := hcon x.1 x.2
    simp only [Set.InjOn, not_forall] at this
    obtain ⟨A, hA, B, hB, h, hne⟩ := this
    exact ⟨A, hA, B, hB, h, hne⟩
  obtain ⟨x0⟩ : Nonempty X := ⟨⟨hX.choose, hX.choose_spec⟩⟩
  obtain ⟨A0, hA0, -⟩ := hbad x0
  choose A hA B hB hAB hne using hbad
  let S : Finset (α → ZMod 2) := (F.erase A0).image (fun C => ind C - ind A0)
  let W : Submodule (ZMod 2) (α → ZMod 2) := Submodule.span (ZMod 2) (S : Set (α → ZMod 2))
  have hmem : ∀ C ∈ F, ind C - ind A0 ∈ W := by
    intro C hC
    by_cases h : C = A0
    · subst h; simp
    · exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image.2 ⟨C, Finset.mem_erase.2 ⟨h, hC⟩, rfl⟩))
  let g : X → W := fun x => ⟨Pi.single x.1 1, by
    have := ind_sub_single x.1 _ _ (hAB x) (hne x)
    rw [← this]
    have e : ind (A x) - ind (B x) = (ind (A x) - ind A0) - (ind (B x) - ind A0) := by abel
    rw [e]
    exact W.sub_mem (hmem _ (hA x)) (hmem _ (hB x))⟩
  have hli : LinearIndependent (ZMod 2) g := by
    apply LinearIndependent.of_comp W.subtype
    exact (Pi.linearIndependent_single_one α (ZMod 2)).comp (fun x : X => x.1) Subtype.val_injective
  have : FiniteDimensional (ZMod 2) W := FiniteDimensional.span_finset (ZMod 2) S
  have h1 := LinearIndependent.fintype_card_le_finrank hli
  have h2 : finrank (ZMod 2) W ≤ S.card := finrank_span_finset_le_card S
  have h3 : S.card ≤ (F.erase A0).card := Finset.card_image_le
  have h4 : (F.erase A0).card = F.card - 1 := Finset.card_erase_of_mem hA0
  have h5 : Fintype.card X = X.card := Fintype.card_coe X
  have h6 : 0 < F.card := Finset.card_pos.2 ⟨A0, hA0⟩
  omega

end Bondy
