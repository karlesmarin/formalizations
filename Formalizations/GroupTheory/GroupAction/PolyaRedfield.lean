/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.Cycle.Factors
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The Pólya–Redfield enumeration theorem

A finite group `G` acting on a finite set `α` acts on colourings `α → C` by
`(g • F) a = F (g⁻¹ • a)`. With colour weights `w c` in a commutative ring and colouring weight
`W F = ∏ₐ w (F a)`, `|G| · Σ_{orbits} W = Σ_g ∏_{cycles of g} p_{length}`, `p_k = Σ_c (w c)^k`: the
cycle index evaluated at the power sums (Theorem of the Day's `Z(G, Ω; x, x⁽²⁾, …)`). Proof: a
weighted Burnside lemma, and a colouring fixed by `g` is constant on each cycle of `g`, so the fixed
colourings factor over the cycles. With `w = 1` it counts colourings up to symmetry:
`|G| · #orbits = Σ_g |C|^{c(g)}`.

## Main results

* `PolyaRedfield.sum_fixed_weight`: the weight of the colourings fixed by g is the product over the cycles of g of the power sums
* `PolyaRedfield.card_mul_sum_orbit_weight`: Pólya–Redfield: |G| · Σ_orbits W = cycle index at the power sums
* `PolyaRedfield.card_mul_card_orbits`: unweighted: |G| · #orbits = Σ_g |C|^(number of cycles of g)

## References

* R. Whitty, Theorem of the Day, «The Pólya–Redfield Enumeration Theorem» (CombinatorialTheory/PRET).
* J. H. Redfield, The theory of group-reduced distributions, Amer. J. Math. 49 (1927); G. Pólya, Acta Math. 68 (1937).
-/

@[expose] public section

namespace PolyaRedfield

open Finset Equiv


theorem burnside_weighted {G X R : Type*} [Group G] [Fintype G] [MulAction G X] [Fintype X]
    [Fintype (MulAction.orbitRel.Quotient G X)] [∀ g : G, DecidablePred (fun x : X => g • x = x)]
    [CommRing R] (W : X → R) (hW : ∀ (g : G) x, W (g • x) = W x) :
    (Fintype.card G : R) * ∑ O : MulAction.orbitRel.Quotient G X, W O.out =
      ∑ g : G, ∑ x ∈ univ.filter (fun x : X => g • x = x), W x := by
  classical
  have hs : ∀ x : X, (univ.filter fun g : G => g • x = x).card *
      Fintype.card (MulAction.orbit G x) = Fintype.card G := by
    intro x
    have h1 := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G x
    have h2 : (univ.filter fun g : G => g • x = x).card = Fintype.card (MulAction.stabilizer G x) := by
      rw [← Fintype.card_subtype]
      exact Fintype.card_congr (Equiv.subtypeEquivRight fun g => MulAction.mem_stabilizer_iff.symm)
    rw [h2, mul_comm]; exact h1
  -- swap the sums
  have hswap : ∑ g : G, ∑ x ∈ univ.filter (fun x : X => g • x = x), W x =
      ∑ x : X, W x * ((univ.filter fun g : G => g • x = x).card : R) := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hswap, ← Finset.sum_fiberwise univ (fun x : X => (Quotient.mk _ x : MulAction.orbitRel.Quotient G X)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun O _ => ?_
  have hfib : ∀ x ∈ univ.filter (fun x : X => (Quotient.mk _ x : MulAction.orbitRel.Quotient G X) = O),
      W x * ((univ.filter fun g : G => g • x = x).card : R) =
        W O.out * ((univ.filter fun g : G => g • O.out = O.out).card : R) := by
    intro x hx
    rw [mem_filter] at hx
    have hxo : x ∈ MulAction.orbit G O.out := by
      have : (Quotient.mk _ x : MulAction.orbitRel.Quotient G X) = Quotient.mk _ O.out := by
        rw [hx.2]; exact (Quotient.out_eq O).symm
      have := Quotient.exact this
      exact MulAction.orbitRel_apply.mp this
    obtain ⟨h, rfl⟩ := MulAction.mem_orbit_iff.mp hxo
    have hor : MulAction.orbit G (h • O.out) = MulAction.orbit G O.out := MulAction.orbit_smul h _
    have hc : Fintype.card (MulAction.orbit G (h • O.out)) = Fintype.card (MulAction.orbit G O.out) :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun x => by rw [hor])
    have hpos : 0 < Fintype.card (MulAction.orbit G O.out) :=
      Fintype.card_pos_iff.mpr ⟨⟨O.out, MulAction.mem_orbit_self _⟩⟩
    have hseq : (univ.filter fun g : G => g • (h • O.out) = h • O.out).card =
        (univ.filter fun g : G => g • O.out = O.out).card := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      have h3 := hs (h • O.out)
      rw [hc] at h3
      rw [h3, hs]
    rw [hW, hseq]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul]
  have hcard : (univ.filter (fun x : X => (Quotient.mk _ x : MulAction.orbitRel.Quotient G X) = O)).card =
      Fintype.card (MulAction.orbit G O.out) := by
    rw [← Fintype.card_subtype]
    refine Fintype.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    constructor
    · intro hx
      have : (Quotient.mk _ x : MulAction.orbitRel.Quotient G X) = Quotient.mk _ O.out := by
        rw [hx]; exact (Quotient.out_eq O).symm
      exact MulAction.orbitRel_apply.mp (Quotient.exact this)
    · intro hx
      rw [← Quotient.out_eq O]
      exact Quotient.sound (MulAction.orbitRel_apply.mpr hx)
  rw [hcard]
  have := hs O.out
  have h' : ((univ.filter fun g : G => g • O.out = O.out).card : R) * (Fintype.card (MulAction.orbit G O.out) : R)
      = (Fintype.card G : R) := by rw [← Nat.cast_mul, this]
  calc (Fintype.card G : R) * W O.out
      = W O.out * (((univ.filter fun g : G => g • O.out = O.out).card : R) * (Fintype.card (MulAction.orbit G O.out) : R)) := by rw [h']; ring
    _ = _ := by ring


theorem fixed_iff_sameCycle {α C : Type*} (σ : Perm α) (F : α → C) :
    (∀ a, F (σ a) = F a) ↔ ∀ a b, σ.SameCycle a b → F a = F b := by
  constructor
  · intro h a b ⟨i, hi⟩
    subst hi
    have hz : ∀ (i : ℤ) (a : α), F ((σ ^ i) a) = F a := by
      intro i
      induction i using Int.induction_on with
      | zero => simp
      | succ n ih =>
        intro a
        rw [zpow_add_one, Perm.mul_apply, ih, h]
      | pred n ih =>
        intro a
        rw [zpow_sub_one, Perm.mul_apply, ih]
        exact (by simpa using h (σ⁻¹ a) : F a = F (σ.symm a)).symm
    exact (hz i a).symm
  · intro h a
    exact (h a (σ a) ⟨1, by simp⟩).symm

open Classical in
theorem sum_fixed_perm {α C R : Type*} [Fintype α] [Fintype C] [CommRing R] (σ : Perm α) (w : C → R) :
    ∑ F ∈ univ.filter (fun F : α → C => ∀ a, F (σ a) = F a), ∏ a, w (F a) =
      ∏ q : Quotient (Perm.SameCycle.setoid σ),
        ∑ c, w c ^ (univ.filter (fun a : α => (Quotient.mk _ a : Quotient (Perm.SameCycle.setoid σ)) = q)).card := by
  classical
  have step1 : ∑ F ∈ univ.filter (fun F : α → C => ∀ a, F (σ a) = F a), ∏ a, w (F a) =
      ∑ H : Quotient (Perm.SameCycle.setoid σ) → C, ∏ a, w (H (Quotient.mk _ a)) := by
    symm
    refine Finset.sum_nbij' (fun H a => H (Quotient.mk _ a)) (fun F q => F q.out) ?_ ?_ ?_ ?_ ?_
    · intro H _
      rw [mem_filter]
      refine ⟨mem_univ _, fun a => ?_⟩
      have : (Quotient.mk (Perm.SameCycle.setoid σ) (σ a)) = Quotient.mk _ a :=
        Quotient.sound (Perm.sameCycle_apply_left.mpr (Perm.SameCycle.refl σ a))
      simp only [this]
    · intro F _; exact mem_univ _
    · intro H _
      funext q
      simp only [Quotient.out_eq]
    · intro F hF
      rw [mem_filter] at hF
      funext a
      have hr : (Perm.SameCycle.setoid σ).r (Quotient.mk (Perm.SameCycle.setoid σ) a).out a :=
        Quotient.mk_out a
      exact (fixed_iff_sameCycle σ F).mp hF.2 _ _ hr
    · intro H _; rfl
  rw [step1]
  have step2 : ∀ H : Quotient (Perm.SameCycle.setoid σ) → C, ∏ a, w (H (Quotient.mk _ a)) =
      ∏ q : Quotient (Perm.SameCycle.setoid σ),
        w (H q) ^ (univ.filter (fun a : α => (Quotient.mk _ a : Quotient (Perm.SameCycle.setoid σ)) = q)).card := by
    intro H
    rw [← Finset.prod_fiberwise univ (fun a : α => (Quotient.mk _ a : Quotient (Perm.SameCycle.setoid σ)))]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [Finset.prod_congr rfl (g := fun _ => w (H q)) (fun a ha => by rw [(mem_filter.mp ha).2]),
      Finset.prod_const]
  simp_rw [step2]
  rw [Finset.prod_univ_sum]
  simp


open Classical in
theorem prod_classes {α M : Type*} [Fintype α] [CommMonoid M] (σ : Perm α) (h : ℕ → M) :
    ∏ q : Quotient (Perm.SameCycle.setoid σ),
        h (univ.filter (fun a : α => (Quotient.mk _ a : Quotient (Perm.SameCycle.setoid σ)) = q)).card =
      h 1 ^ Fintype.card (Function.fixedPoints σ) * (σ.cycleType.map h).prod := by
  classical
  set Q := Quotient (Perm.SameCycle.setoid σ) with hQ
  have hrel : ∀ q : Q, σ.SameCycle q.out (q.out) := fun q => Perm.SameCycle.refl σ _
  have hout : ∀ a : α, σ.SameCycle (Quotient.mk (Perm.SameCycle.setoid σ) a).out a := fun a =>
    Quotient.mk_out (s := Perm.SameCycle.setoid σ) a
  rw [← Finset.prod_filter_mul_prod_filter_not univ (fun q : Q => σ q.out = q.out)]
  congr 1
  · -- fixed classes
    have hn : ∀ q ∈ univ.filter (fun q : Q => σ q.out = q.out),
        h (univ.filter (fun a : α => (Quotient.mk _ a : Q) = q)).card = h 1 := by
      intro q hq
      rw [mem_filter] at hq
      congr 1
      rw [Finset.card_eq_one]
      refine ⟨q.out, ?_⟩
      ext a
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · intro ha
        have : σ.SameCycle q.out a := by
          have h2 : σ.SameCycle (Quotient.mk (Perm.SameCycle.setoid σ) a).out a := hout a
          rw [ha] at h2
          exact h2
        exact (this.eq_of_left hq.2).symm
      · intro ha
        rw [ha]; exact Quotient.out_eq q
    rw [Finset.prod_congr rfl hn, Finset.prod_const]
    congr 1
    have hc : (univ.filter (fun q : Q => σ q.out = q.out)).card =
        (univ.filter (fun x : α => σ x = x)).card := by
      refine Finset.card_bij (fun q _ => q.out) ?_ ?_ ?_
      · intro q hq; simpa using hq
      · intro q1 h1 q2 h2 he
        simpa [Quotient.out_eq] using congrArg (fun x => (Quotient.mk (Perm.SameCycle.setoid σ) x)) he
      · intro x hx
        refine ⟨Quotient.mk _ x, ?_, ?_⟩
        · simp only [mem_filter, mem_univ, true_and] at hx ⊢
          have h2 := hout x
          have := (h2.apply_eq_self_iff).mpr hx
          exact this
        · have h2 := hout x
          simp only [mem_filter, mem_univ, true_and] at hx
          exact h2.eq_of_right hx
    rw [hc, ← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)
  · -- non-fixed classes
    have hcy : (σ.cycleType.map h).prod = ∏ c ∈ σ.cycleFactorsFinset, h c.support.card := by
      rw [Perm.cycleType_def, Multiset.map_map, Finset.prod_eq_multiset_prod]
      rfl
    rw [hcy]
    refine Finset.prod_bij (fun q _ => σ.cycleOf q.out) ?_ ?_ ?_ ?_
    · intro q hq
      rw [mem_filter] at hq
      exact Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Perm.mem_support.mpr hq.2)
    · intro q1 h1 q2 h2 he
      rw [mem_filter] at h1 h2
      have hm : q2.out ∈ (σ.cycleOf q1.out).support := by
        rw [he, Perm.mem_support_cycleOf_iff]
        exact ⟨Perm.SameCycle.refl σ _, Perm.mem_support.mpr h2.2⟩
      rw [Perm.mem_support_cycleOf_iff] at hm
      rw [← Quotient.out_eq q1, ← Quotient.out_eq q2]
      exact Quotient.sound hm.1
    · intro c hc
      have hc' := Perm.mem_cycleFactorsFinset_iff.mp hc
      obtain ⟨x, hx⟩ := hc'.1.nonempty_support
      have hcx : c = σ.cycleOf x := Perm.cycle_is_cycleOf hx hc
      have hxs : σ x ≠ x := by
        have := hc'.2 x hx
        rw [← this]; exact Perm.mem_support.mp hx
      refine ⟨Quotient.mk _ x, ?_, ?_⟩
      · rw [mem_filter]
        refine ⟨mem_univ _, ?_⟩
        intro hf
        have h2 := hout x
        have := h2.eq_of_left hf
        exact hxs (by rw [← this]; exact hf)
      · have h2 := hout x
        rw [hcx]
        exact h2.cycleOf_eq
    · intro q hq
      rw [mem_filter] at hq
      congr 1
      have hxs : σ q.out ≠ q.out := hq.2
      have : (σ.cycleOf q.out).support = univ.filter (fun a : α => (Quotient.mk _ a : Q) = q) := by
        ext a
        rw [Perm.mem_support_cycleOf_iff]
        simp only [mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨ha, _⟩
          rw [← Quotient.out_eq q]
          exact Quotient.sound ha.symm
        · intro ha
          refine ⟨?_, Perm.mem_support.mpr hxs⟩
          have h2 := hout a
          rw [ha] at h2
          exact h2
      rw [this]

open Classical in
/-- The weight of the colourings fixed by `g` is the product over the cycles of `g` of the power sums. -/
theorem sum_fixed_weight {G α C R : Type*} [Group G] [MulAction G α] [Fintype α] [Fintype C]
    [CommRing R] (w : C → R) (g : G) :
    letI := arrowAction (G := G) (A := α) (B := C)
    ∑ F ∈ univ.filter (fun F : α → C => g • F = F), ∏ a, w (F a) =
      (∑ c, w c) ^ (Fintype.card (Function.fixedPoints (MulAction.toPerm g : Equiv.Perm α))) *
        ((MulAction.toPerm g : Equiv.Perm α).cycleType.map (fun k => ∑ c, w c ^ k)).prod := by
  let _ := arrowAction (G := G) (A := α) (B := C)
  have hfil : (univ.filter (fun F : α → C => g • F = F)) =
      univ.filter (fun F : α → C => ∀ a, F ((MulAction.toPerm g : Equiv.Perm α) a) = F a) := by
    ext F
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro hF a
      have h1 : F (g⁻¹ • g • a) = F (g • a) := congrFun hF (g • a)
      rw [inv_smul_smul] at h1
      exact h1.symm
    · intro hF
      funext a
      have h1 := hF (g⁻¹ • a)
      simp only [MulAction.toPerm_apply, smul_inv_smul] at h1
      exact h1.symm
  rw [hfil, sum_fixed_perm, prod_classes (MulAction.toPerm g : Equiv.Perm α) (fun k => ∑ c, w c ^ k)]
  simp

open Classical in
/-- **Pólya–Redfield** (weighted form), as stated in the queue. -/
theorem card_mul_sum_orbit_weight {G α C R : Type*} [Group G] [Fintype G] [MulAction G α] [Fintype α]
    [Fintype C] [CommRing R] (w : C → R) :
    letI := arrowAction (G := G) (A := α) (B := C)
    (Fintype.card G : R) * ∑ O : MulAction.orbitRel.Quotient G (α → C), ∏ a, w (O.out a) =
      ∑ g : G, (∑ c, w c) ^ (Fintype.card (Function.fixedPoints (MulAction.toPerm g : Equiv.Perm α))) *
        ((MulAction.toPerm g : Equiv.Perm α).cycleType.map (fun k => ∑ c, w c ^ k)).prod := by
  let _ := arrowAction (G := G) (A := α) (B := C)
  have hW : ∀ (g : G) (F : α → C), (fun F : α → C => ∏ a, w (F a)) (g • F) =
      (fun F : α → C => ∏ a, w (F a)) F := by
    intro g F
    show ∏ a, w (F (g⁻¹ • a)) = ∏ a, w (F a)
    exact Fintype.prod_equiv (MulAction.toPerm g⁻¹) _ _ (fun a => rfl)
  refine (burnside_weighted (G := G) (X := α → C) (R := R) (fun F : α → C => ∏ a, w (F a)) hW).trans ?_
  exact Finset.sum_congr rfl fun g _ => sum_fixed_weight w g

open Classical in
/-- Unweighted corollary: `|G| · #orbits = ∑_g |C|^(number of cycles of g, fixed points included)`. -/
theorem card_mul_card_orbits {G α C : Type*} [Group G] [Fintype G] [MulAction G α] [Fintype α]
    [Fintype C] :
    letI := arrowAction (G := G) (A := α) (B := C)
    Fintype.card G * Fintype.card (MulAction.orbitRel.Quotient G (α → C)) =
      ∑ g : G, (Fintype.card C) ^
        (Fintype.card (Function.fixedPoints (MulAction.toPerm g : Equiv.Perm α)) +
          (MulAction.toPerm g : Equiv.Perm α).cycleType.card) := by
  let _ := arrowAction (G := G) (A := α) (B := C)
  have h := card_mul_sum_orbit_weight (G := G) (α := α) (C := C) (R := ℤ) (fun _ => 1)
  simp only [Finset.prod_const_one, Finset.sum_const, Finset.card_univ, one_pow, nsmul_eq_mul,
    mul_one, Multiset.map_const', Multiset.prod_replicate] at h
  rw [← Nat.cast_inj (R := ℤ)]
  push_cast
  rw [h]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [pow_add]


end PolyaRedfield
