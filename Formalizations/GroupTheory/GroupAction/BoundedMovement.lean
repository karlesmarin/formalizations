/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Set.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Praeger's theorem on bounded movement

Let a group act on a set `Ω` without fixed points, and let every finite subset that some element
moves off itself have at most `m ≥ 1` points. Then `Ω` is finite, there are at most `2m − 1` orbits,
each orbit has at most `3m` points, and `|Ω| ≤ 3m + t − 1` (Theorem of the Day; Praeger 1991).
Proof: every element has support of size at most `3m` (it lies in `A ∪ gA ∪ g⁻¹A` for a maximal set
`A` moved off itself), and the orbit-counting identity `Σ_g |supp g| = |G| (|Ω| − t)` gives the
bounds.

## Main results

* `Praeger.card_support_le`: every element has at most 3m moved points
* `Praeger.bounded_movement`: Praeger's bounds: Ω finite, t ≤ 2m − 1, orbits ≤ 3m, |Ω| ≤ 3m + t − 1

## References

* R. Whitty, Theorem of the Day, «Praeger's Theorem on Bounded Movement» (GroupTheory/Movement).
* C. E. Praeger, On permutation groups with bounded movement, J. Algebra 144 (1991) 436–442.
-/

@[expose] public section

open MulAction

namespace Praeger

theorem exists_max (P : ℕ → Prop) (b : ℕ) (hb : ∀ k, P k → k ≤ b) (h0 : ∃ k, P k) :
    ∃ k, P k ∧ ∀ j, P j → j ≤ k := by
  classical
  obtain ⟨k0, hk0⟩ := h0
  exact ⟨Nat.findGreatest P b, Nat.findGreatest_spec (hb k0 hk0) hk0,
    fun j hj => Nat.le_findGreatest (hb j hj) hj⟩

section Support

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem card_support_le (m : ℕ)
    (hmove : ∀ (Γ : Finset Ω) (g : G), (∀ x ∈ Γ, g • x ∉ Γ) → Γ.card ≤ m) (g : G) :
    {x : Ω | g • x ≠ x}.Finite ∧ {x : Ω | g • x ≠ x}.ncard ≤ 3 * m := by
  classical
  obtain ⟨k, ⟨A, hA, hAk⟩, hmax⟩ := exists_max
    (fun k => ∃ A : Finset Ω, (∀ x ∈ A, g • x ∉ A) ∧ A.card = k) m
    (fun k ⟨A, hA, hk⟩ => hk ▸ hmove A g hA) ⟨0, ∅, by simp, rfl⟩
  have hkm : k ≤ m := hAk ▸ hmove A g hA
  have hsub : {x : Ω | g • x ≠ x} ⊆
      ↑(A ∪ A.image (fun y => g • y) ∪ A.image (fun y => g⁻¹ • y)) := by
    intro x hx
    by_contra hnot
    simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, not_or, Set.mem_image,
      Finset.mem_coe, not_exists, not_and] at hnot
    obtain ⟨⟨hxA, hxg⟩, hxg'⟩ := hnot
    have hx' : g • x ≠ x := hx
    have hcard : (insert x A).card ≤ k := hmax _ ⟨insert x A, ?_, rfl⟩
    · rw [Finset.card_insert_of_notMem hxA] at hcard
      omega
    · intro y hy
      rw [Finset.mem_insert] at hy ⊢
      rcases hy with rfl | hy
      · rintro (h | h)
        · exact hx' h
        · exact hxg' _ h (by simp)
      · rintro (h | h)
        · exact hxg _ hy h
        · exact hA y hy h
  have hfin : {x : Ω | g • x ≠ x}.Finite := (Finset.finite_toSet _).subset hsub
  refine ⟨hfin, ?_⟩
  calc {x : Ω | g • x ≠ x}.ncard
      ≤ (↑(A ∪ A.image (fun y => g • y) ∪ A.image (fun y => g⁻¹ • y)) : Set Ω).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (A ∪ A.image (fun y => g • y) ∪ A.image (fun y => g⁻¹ • y)).card :=
        Set.ncard_coe_finset _
    _ ≤ 3 * m := by
        have h1 := Finset.card_union_le (A ∪ A.image (fun y => g • y)) (A.image (fun y => g⁻¹ • y))
        have h2 := Finset.card_union_le A (A.image (fun y => g • y))
        have h3 : (A.image (fun y => g • y)).card ≤ A.card := Finset.card_image_le
        have h4 : (A.image (fun y => g⁻¹ • y)).card ≤ A.card := Finset.card_image_le
        omega

end Support

section Finite

variable (H X : Type*) [Group H] [MulAction H X] [Fintype H] [Finite X]

/-- Burnside for supports: `Σ_h |supp h| + s·|H| = |H|·|X|`. -/
theorem burnside_supp :
    (∑ h : H, {x : X | h • x ≠ x}.ncard) + Nat.card (orbitRel.Quotient H X) * Nat.card H =
      Nat.card H * Nat.card X := by
  classical
  have := Fintype.ofFinite X
  have := Fintype.ofFinite (orbitRel.Quotient H X)
  have hb := sum_card_fixedBy_eq_card_orbits_mul_card_group H X
  have key : ∀ h : H, {x : X | h • x ≠ x}.ncard + Fintype.card (fixedBy X h) = Nat.card X := by
    intro h
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    have := Set.ncard_add_ncard_compl (fixedBy X h)
    have e : {x : X | h • x ≠ x} = (fixedBy X h)ᶜ := by
      ext x
      simp [mem_fixedBy]
    rw [e, add_comm]
    exact this
  have hs : ∑ h : H, ({x : X | h • x ≠ x}.ncard + Fintype.card (fixedBy X h)) =
      ∑ _h : H, Nat.card X := Finset.sum_congr rfl (fun h _ => key h)
  rw [Finset.sum_add_distrib, hb, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hs
  rw [Nat.card_eq_fintype_card (α := orbitRel.Quotient H X),
    Nat.card_eq_fintype_card (α := H)]
  exact hs

omit [Fintype H] in
theorem two_le_card_orbit (hfree : ∀ x : X, ∃ h : H, h • x ≠ x) (x : X) :
    2 ≤ Nat.card (orbit H x) := by
  obtain ⟨h, hh⟩ := hfree x
  have hsub : ({x, h • x} : Set X) ⊆ orbit H x := by
    intro y hy
    rcases hy with rfl | rfl
    · exact mem_orbit_self _
    · exact mem_orbit _ _
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair (Ne.symm hh)] at this
  rwa [Nat.card_coe_set_eq]

omit [Fintype H] in
theorem card_eq_sum_orbits [Fintype (orbitRel.Quotient H X)] :
    Nat.card X = ∑ ω : orbitRel.Quotient H X, Nat.card (orbit H ω.out) := by
  rw [Nat.card_congr (selfEquivSigmaOrbits H X), Nat.card_sigma]

theorem finite_bounds (c : ℕ) (hc : 1 ≤ c) (hsupp : ∀ h : H, {x : X | h • x ≠ x}.ncard ≤ c)
    (hfree : ∀ x : X, ∃ h : H, h • x ≠ x) :
    Nat.card X + 1 ≤ Nat.card (orbitRel.Quotient H X) + c ∧
    2 * Nat.card (orbitRel.Quotient H X) ≤ Nat.card X ∧
    ∀ x : X, Nat.card (orbit H x) + Nat.card (orbitRel.Quotient H X) ≤ Nat.card X + 1 := by
  classical
  have := Fintype.ofFinite (orbitRel.Quotient H X)
  have h2 := two_le_card_orbit H X hfree
  have hsum := card_eq_sum_orbits H X
  have hB := burnside_supp H X
  have hQpos : 0 < Nat.card H := Nat.card_pos
  -- the sum of supports
  have hS : ∑ h : H, {x : X | h • x ≠ x}.ncard ≤ (Nat.card H - 1) * c := by
    have h1 := Finset.add_sum_erase Finset.univ (fun h : H => {x : X | h • x ≠ x}.ncard)
      (Finset.mem_univ (1 : H))
    have h0 : {x : X | (1 : H) • x ≠ x}.ncard = 0 := by simp
    have h3 : ∑ h ∈ Finset.univ.erase (1 : H), {x : X | h • x ≠ x}.ncard ≤
        (Finset.univ.erase (1 : H)).card • c :=
      Finset.sum_le_card_nsmul _ _ _ (fun h _ => hsupp h)
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card, smul_eq_mul] at h3
    omega
  -- number of orbits
  have hs2 : 2 * Nat.card (orbitRel.Quotient H X) ≤ Nat.card X := by
    have := Finset.card_nsmul_le_sum (Finset.univ : Finset (orbitRel.Quotient H X))
      (fun ω => Nat.card (orbit H ω.out)) 2 (fun ω _ => h2 _)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, smul_eq_mul] at this
    omega
  refine ⟨?_, hs2, ?_⟩
  · obtain ⟨q, hq⟩ : ∃ q, Nat.card H = q + 1 := ⟨Nat.card H - 1, by omega⟩
    rw [hq] at hB hS
    simp only [Nat.add_sub_cancel] at hS
    by_contra hcon
    have hN : Nat.card (orbitRel.Quotient H X) + c ≤ Nat.card X := by omega
    have := Nat.mul_le_mul_left (q + 1) hN
    nlinarith
  · intro x
    have hx : Nat.card (orbit H x) =
        Nat.card (orbit H (Quotient.mk (orbitRel H X) x).out) := by
      congr 2
      exact (orbit_eq_iff.mpr ((orbitRel_apply).mp (Quotient.mk_out x))).symm
    have hne : Nonempty (orbitRel.Quotient H X) := ⟨Quotient.mk _ x⟩
    obtain ⟨ω0, hω0⟩ : ∃ ω0 : orbitRel.Quotient H X, ω0 = Quotient.mk (orbitRel H X) x :=
      ⟨_, rfl⟩
    rw [← hω0] at hx
    let f : orbitRel.Quotient H X → ℕ := fun ω => Nat.card (orbit H ω.out)
    have hsum' : Nat.card X = ∑ ω, f ω := hsum
    have h1 := Finset.add_sum_erase (Finset.univ : Finset (orbitRel.Quotient H X)) f
      (Finset.mem_univ ω0)
    have h3 : (Nat.card (orbitRel.Quotient H X) - 1) * 2 ≤
        ∑ ω ∈ (Finset.univ : Finset (orbitRel.Quotient H X)).erase ω0, f ω := by
      have := Finset.card_nsmul_le_sum
        ((Finset.univ : Finset (orbitRel.Quotient H X)).erase ω0) f 2 (fun ω _ => h2 _)
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        ← Nat.card_eq_fintype_card, smul_eq_mul] at this
      exact this
    have hpos : 0 < Nat.card (orbitRel.Quotient H X) := Nat.card_pos
    have hf : f ω0 = Nat.card (orbit H x) := hx.symm
    omega

theorem orbits_le (m : ℕ) (hm : 1 ≤ m) (hfree : ∀ x : X, ∃ h : H, h • x ≠ x)
    (hmove : ∀ (Γ : Finset X) (h : H), (∀ x ∈ Γ, h • x ∉ Γ) → Γ.card ≤ m) :
    Nat.card (orbitRel.Quotient H X) ≤ 2 * m - 1 := by
  classical
  have := Fintype.ofFinite X
  have := Fintype.ofFinite (orbitRel.Quotient H X)
  have h2 := two_le_card_orbit H X hfree
  -- the displaced sets of representatives
  let a : H → ℕ := fun h =>
    (Finset.univ.filter (fun ω : orbitRel.Quotient H X => h • ω.out ≠ ω.out)).card
  have ha : ∀ h : H, a h ≤ m := by
    intro h
    have hc := hmove
      ((Finset.univ.filter (fun ω : orbitRel.Quotient H X => h • ω.out ≠ ω.out)).image
        Quotient.out) h ?_
    · rwa [Finset.card_image_of_injective _ Quotient.out_injective] at hc
    · intro x hx hhx
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx hhx
      obtain ⟨ω, hω, rfl⟩ := hx
      obtain ⟨ω', hω', hω'e⟩ := hhx
      have e1 : (Quotient.mk (orbitRel H X) (h • ω.out)) = ω :=
        (Quotient.sound (orbitRel_apply.mpr (mem_orbit ω.out h)) :
          Quotient.mk (orbitRel H X) (h • ω.out) = Quotient.mk (orbitRel H X) ω.out).trans
          (Quotient.out_eq ω)
      have e2 : (Quotient.mk (orbitRel H X) (h • ω.out)) = ω' := by
        rw [← hω'e, Quotient.out_eq]
      have : ω' = ω := e2.symm.trans e1
      subst this
      exact hω hω'e.symm
  have h1 : a 1 = 0 := by simp [a]
  have hsa : ∑ h : H, a h ≤ (Nat.card H - 1) * m := by
    have e := Finset.add_sum_erase Finset.univ a (Finset.mem_univ (1 : H))
    have h3 : ∑ h ∈ Finset.univ.erase (1 : H), a h ≤ (Finset.univ.erase (1 : H)).card • m :=
      Finset.sum_le_card_nsmul _ _ _ (fun h _ => ha h)
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card, smul_eq_mul] at h3
    omega
  -- double counting
  have hdc : ∑ h : H, a h = ∑ ω : orbitRel.Quotient H X,
      (Finset.univ.filter (fun h : H => h • ω.out ≠ ω.out)).card := by
    simp only [a, Finset.card_filter]
    exact Finset.sum_comm
  have hper : ∀ ω : orbitRel.Quotient H X,
      Nat.card H ≤ 2 * (Finset.univ.filter (fun h : H => h • ω.out ≠ ω.out)).card := by
    intro ω
    set y := ω.out
    have hos := card_orbit_mul_card_stabilizer_eq_card_group H y
    have hst : Fintype.card (stabilizer H y) =
        (Finset.univ.filter (fun h : H => ¬ (h • y ≠ y))).card := by
      rw [Fintype.card_subtype]
      congr 1
      ext h
      simp [mem_stabilizer_iff]
    have hsplit := (Finset.univ : Finset H).card_filter_add_card_filter_not
      (fun h : H => h • y ≠ y)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hsplit
    rw [← Nat.card_eq_fintype_card (α := H), ← Nat.card_eq_fintype_card (α := orbit H y),
      ← Nat.card_eq_fintype_card (α := stabilizer H y)] at hos
    have ho2 := h2 y
    rw [← Nat.card_eq_fintype_card (α := stabilizer H y)] at hst
    have : 2 * Nat.card (stabilizer H y) ≤ Nat.card H := by
      rw [← hos]
      exact Nat.mul_le_mul_right _ ho2
    omega
  have hsum : Nat.card (orbitRel.Quotient H X) * Nat.card H ≤ 2 * ((Nat.card H - 1) * m) := by
    calc Nat.card (orbitRel.Quotient H X) * Nat.card H
        = ∑ _ω : orbitRel.Quotient H X, Nat.card H := by
          rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, smul_eq_mul]
      _ ≤ ∑ ω : orbitRel.Quotient H X,
          2 * (Finset.univ.filter (fun h : H => h • ω.out ≠ ω.out)).card :=
          Finset.sum_le_sum (fun ω _ => hper ω)
      _ = 2 * ∑ h : H, a h := by rw [hdc, Finset.mul_sum]
      _ ≤ 2 * ((Nat.card H - 1) * m) := Nat.mul_le_mul_left _ hsa
  obtain ⟨q, hq⟩ : ∃ q, Nat.card H = q + 1 := ⟨Nat.card H - 1, by
    have : 0 < Nat.card H := Nat.card_pos
    omega⟩
  rw [hq] at hsum
  simp only [Nat.add_sub_cancel] at hsum
  by_contra hcon
  have : 2 * m ≤ Nat.card (orbitRel.Quotient H X) := by omega
  nlinarith

end Finite

section Infinite

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-- The elements of `Perm U` induced by elements of `G`. -/
def inducedSubgroup (G : Type*) [Group G] {Ω : Type*} [MulAction G Ω] (U : Set Ω) :
    Subgroup (Equiv.Perm U) where
  carrier := {σ | ∃ g : G, ∀ x : U, (σ x : Ω) = g • (x : Ω)}
  mul_mem' := by
    rintro σ τ ⟨g, hg⟩ ⟨g', hg'⟩
    refine ⟨g * g', fun x => ?_⟩
    rw [Equiv.Perm.mul_apply, hg, hg', mul_smul]
  one_mem' := ⟨1, fun x => by simp⟩
  inv_mem' := by
    rintro σ ⟨g, hg⟩
    refine ⟨g⁻¹, fun x => ?_⟩
    rw [eq_inv_smul_iff]
    have := hg (σ⁻¹ x)
    simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at this
    exact this.symm

/-- A finite set covered by supports contained in itself has at most `6m` points. -/
theorem card_union_le (m : ℕ) (hm : 1 ≤ m)
    (hmove : ∀ (Γ : Finset Ω) (g : G), (∀ x ∈ Γ, g • x ∉ Γ) → Γ.card ≤ m)
    (U : Set Ω) (hU : U.Finite)
    (hcov : ∀ x ∈ U, ∃ g : G, g • x ≠ x ∧ {y : Ω | g • y ≠ y} ⊆ U) :
    U.ncard ≤ 6 * m := by
  classical
  have : Finite U := hU.to_subtype
  have : Finite (inducedSubgroup G U) := inferInstance
  have : Fintype (inducedSubgroup G U) := Fintype.ofFinite _
  have key := finite_bounds (inducedSubgroup G U) U (3 * m) (by omega) ?_ ?_
  · obtain ⟨k1, k2, -⟩ := key
    rw [Nat.card_coe_set_eq] at k1 k2
    omega
  · rintro ⟨σ, g, hg⟩
    have hfin := (card_support_le (G := G) m hmove g)
    have hsub : Subtype.val '' {x : U | (⟨σ, g, hg⟩ : inducedSubgroup G U) • x ≠ x} ⊆
        {y : Ω | g • y ≠ y} := by
      rintro _ ⟨x, hx, rfl⟩
      intro h
      apply hx
      apply Subtype.ext
      show (σ x : Ω) = x
      rw [hg x]
      exact h
    calc {x : U | (⟨σ, g, hg⟩ : inducedSubgroup G U) • x ≠ x}.ncard
        = (Subtype.val '' {x : U | (⟨σ, g, hg⟩ : inducedSubgroup G U) • x ≠ x}).ncard :=
          (Set.ncard_image_of_injective _ Subtype.val_injective).symm
      _ ≤ {y : Ω | g • y ≠ y}.ncard := Set.ncard_le_ncard hsub hfin.1
      _ ≤ 3 * m := hfin.2
  · rintro ⟨x, hxU⟩
    obtain ⟨g, hgx, hsub⟩ := hcov x hxU
    have hiff : ∀ y : Ω, (g • y ∈ U) ↔ (y ∈ U) := by
      intro y
      by_cases hy : g • y = y
      · rw [hy]
      · exact iff_of_true (hsub (fun h => hy (smul_left_cancel g h))) (hsub hy)
    refine ⟨⟨Equiv.Perm.subtypePerm (MulAction.toPerm g) hiff, g, fun z => rfl⟩, ?_⟩
    intro h
    apply hgx
    have := congrArg Subtype.val h
    exact this

/-- Finiteness of `Ω` (B.4): a maximal finite union of supports contains all supports. -/
theorem finite_of_hmove (m : ℕ) (hm : 1 ≤ m)
    (hfix : ∀ x : Ω, ∃ g : G, g • x ≠ x)
    (hmove : ∀ (Γ : Finset Ω) (g : G), (∀ x ∈ Γ, g • x ∉ Γ) → Γ.card ≤ m) : Finite Ω := by
  classical
  have hfinS : ∀ S : Finset G, (⋃ g ∈ S, {y : Ω | g • y ≠ y}).Finite := fun S =>
    Set.Finite.biUnion S.finite_toSet (fun g _ => (card_support_le m hmove g).1)
  have hbound : ∀ S : Finset G, (⋃ g ∈ S, {y : Ω | g • y ≠ y}).ncard ≤ 6 * m := by
    intro S
    refine card_union_le m hm hmove _ (hfinS S) ?_
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨g, hgS, hgx⟩ := hx
    exact ⟨g, hgx, Set.subset_biUnion_of_mem (u := fun g => {y : Ω | g • y ≠ y}) hgS⟩
  obtain ⟨k, ⟨S₀, hS₀⟩, hmax⟩ := exists_max
    (fun k => ∃ S : Finset G, (⋃ g ∈ S, {y : Ω | g • y ≠ y}).ncard = k) (6 * m)
    (fun k ⟨S, hS⟩ => hS ▸ hbound S) ⟨_, ∅, rfl⟩
  have hall : ∀ g : G, {y : Ω | g • y ≠ y} ⊆ ⋃ g ∈ S₀, {y : Ω | g • y ≠ y} := by
    intro g
    have hsub : (⋃ g ∈ S₀, {y : Ω | g • y ≠ y}) ⊆ ⋃ g' ∈ insert g S₀, {y : Ω | g' • y ≠ y} :=
      Set.iUnion₂_mono' (fun g' hg' => ⟨g', Finset.mem_insert_of_mem hg', subset_rfl⟩)
    have hle : (⋃ g' ∈ insert g S₀, {y : Ω | g' • y ≠ y}).ncard ≤
        (⋃ g ∈ S₀, {y : Ω | g • y ≠ y}).ncard := hS₀ ▸ hmax _ ⟨insert g S₀, rfl⟩
    have heq := Set.eq_of_subset_of_ncard_le hsub hle (hfinS _)
    rw [heq]
    exact Set.subset_biUnion_of_mem (u := fun g => {y : Ω | g • y ≠ y}) (Finset.mem_insert_self g S₀)
  refine Set.finite_univ_iff.mp ((hfinS S₀).subset ?_)
  intro x _
  obtain ⟨g, hg⟩ := hfix x
  exact hall g hg

end Infinite

section Main

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-- **Praeger's theorem on bounded movement.** -/
theorem bounded_movement (m : ℕ) (hm : 1 ≤ m)
    (hfix : ∀ x : Ω, ∃ g : G, g • x ≠ x)
    (hmove : ∀ (Γ : Finset Ω) (g : G), (∀ x ∈ Γ, g • x ∉ Γ) → Γ.card ≤ m) :
    Finite Ω ∧ Nat.card (MulAction.orbitRel.Quotient G Ω) ≤ 2 * m - 1 ∧
      (∀ x : Ω, Nat.card (MulAction.orbit G x) ≤ 3 * m) ∧
      Nat.card Ω ≤ 3 * m + Nat.card (MulAction.orbitRel.Quotient G Ω) - 1 := by
  classical
  have hfin : Finite Ω := finite_of_hmove m hm hfix hmove
  let K : Subgroup (Equiv.Perm Ω) := (MulAction.toPermHom G Ω).range
  have : Fintype K := Fintype.ofFinite K
  have hKact : ∀ (k : K) (x : Ω), k • x = (k : Equiv.Perm Ω) x := fun _ _ => rfl
  have hKG : ∀ (k : K), ∃ g : G, ∀ x : Ω, k • x = g • x := by
    rintro ⟨k, g, rfl⟩
    exact ⟨g, fun x => rfl⟩
  have hmoveK : ∀ (Γ : Finset Ω) (k : K), (∀ x ∈ Γ, k • x ∉ Γ) → Γ.card ≤ m := by
    intro Γ k hΓ
    obtain ⟨g, hg⟩ := hKG k
    exact hmove Γ g (fun x hx => by rw [← hg]; exact hΓ x hx)
  have hfreeK : ∀ x : Ω, ∃ k : K, k • x ≠ x := by
    intro x
    obtain ⟨g, hg⟩ := hfix x
    exact ⟨⟨MulAction.toPermHom G Ω g, g, rfl⟩, hg⟩
  have hsuppK : ∀ k : K, {x : Ω | k • x ≠ x}.ncard ≤ 3 * m :=
    fun k => (card_support_le (G := K) m hmoveK k).2
  obtain ⟨b1, b2, b3⟩ := finite_bounds K Ω (3 * m) (by omega) hsuppK hfreeK
  have b4 := orbits_le K Ω m hm hfreeK hmoveK
  have horb : ∀ x : Ω, MulAction.orbit K x = MulAction.orbit G x := by
    intro x
    ext y
    simp only [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨k, rfl⟩
      obtain ⟨g, hg⟩ := hKG k
      exact ⟨g, (hg x).symm⟩
    · rintro ⟨g, rfl⟩
      exact ⟨⟨MulAction.toPermHom G Ω g, g, rfl⟩, rfl⟩
  have hQ : Nat.card (MulAction.orbitRel.Quotient K Ω) =
      Nat.card (MulAction.orbitRel.Quotient G Ω) := by
    refine Nat.card_congr (Quotient.congr (Equiv.refl Ω) (fun a b => ?_))
    simp only [Equiv.refl_apply]
    rw [MulAction.orbitRel_apply, MulAction.orbitRel_apply, horb]
  refine ⟨hfin, ?_, ?_, ?_⟩
  · rw [← hQ]; exact b4
  · intro x
    have := b3 x
    rw [horb x] at this
    omega
  · rw [← hQ]; omega

end Main

end Praeger
