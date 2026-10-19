/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Perm.Subgroup
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.Ring
public import Formalizations.MusicTheory.NeoRiemannian

/-!
# The order-12 dual of the set class 6-30

The Forte hexachord 6-30 `= {0, 1, 3, 6, 7, 9}` has a `T/I`-orbit of 12 sets, no inversional
symmetry, and stabilizer `{T₀, T₆}`. The induced action of `DihedralGroup 12` on the orbit has
kernel `{1, r 6}`, and its centralizer in `Equiv.Perm` of the orbit (the dual group) has order 12.
The dual is built as the opposite regular representation, acts simply transitively, and has a
dihedral presentation: an element of order 6 inverted by an involution.

## Main results

* `stab_T`, `stab_I_empty`, `not_inversionally_symmetric`, `orbit_card`: the decidable facts.
* `Action.Ker_eq`, `Action.card_TIgrpO`: the kernel `{1, r 6}` and the image of order 12.
* `Action.card_Cgrp`, `Action.Cgrp_transitive`: the dual has order 12 and acts transitively.
* `Action.dihedral_fingerprint`: order 12, `orderOf s = 6`, `t ^ 2 = 1`, `t * s * t = s⁻¹`.

The isomorphism of the dual with `DihedralGroup 6` is not constructed.

## References

* A. S. Crans, T. M. Fiore, R. Satyendra, *Musical actions of dihedral groups*, Amer. Math.
  Monthly 116 (2009) 479–495.
* C. Marín, *A tritone-centered self-duality: the set class 6-30 and its order-12
  neo-Riemannian dual*, Zenodo (2026), doi:10.5281/zenodo.20820961.
-/

@[expose] public section

namespace MusicTheory

open DihedralGroup

namespace SixThirty

/-- Forte 6-30 = (013679), the Petrushka / octatonic-subset hexachord. -/
def A : Finset (ZMod 12) := {0, 1, 3, 6, 7, 9}

/-- Transposition of a pc-set: `Tₖ A = A + k`. -/
def tpose (k : ZMod 12) (S : Finset (ZMod 12)) : Finset (ZMod 12) := S.image (· + k)
/-- Inversion of a pc-set: `Iⱼ A = j − A`. -/
def inv (j : ZMod 12) (S : Finset (ZMod 12)) : Finset (ZMod 12) := S.image (fun x => j - x)

/-! ## TIER 1 — decidable facts about 6-30 -/

/-- The transposition stabilizer of 6-30 is exactly the center `{T0, T6}`. -/
theorem stab_T :
    Finset.univ.filter (fun k : ZMod 12 => tpose k A = A) = {0, 6} := by decide

/-- 6-30 has no inversional symmetry: no `Iⱼ` fixes it. -/
theorem stab_I_empty :
    Finset.univ.filter (fun j : ZMod 12 => inv j A = A) = ∅ := by decide

/-- Equivalent statement: `A` is not inversionally symmetric. -/
theorem not_inversionally_symmetric : ∀ j : ZMod 12, inv j A ≠ A := by decide

/-- `A` is `T6`-invariant (the central transposition symmetry). -/
theorem T6_invariant : tpose 6 A = A := by decide

/-- The full T/I-orbit of 6-30 as a finset of pc-sets. -/
def orbit : Finset (Finset (ZMod 12)) :=
  (Finset.univ.image (fun k : ZMod 12 => tpose k A)) ∪
  (Finset.univ.image (fun j : ZMod 12 => inv j A))

/-- The T/I-orbit of 6-30 has exactly 12 elements. -/
theorem orbit_card : orbit.card = 12 := by decide

/-! ## TIER 2 — the T/I action on pc-sets, restricted to the orbit, is regular

We make `DihedralGroup 12` act on `Finset (ZMod 12)` by `r i ↦ Tᵢ`, `sr j ↦ I₋ⱼ` (the reindex
`sr j ↦ inv (-j)` is forced to make this a genuine *left* action matching `DihedralGroup`
multiplication). This action restricts to the 12-element orbit `O` of 6-30; the restricted action is
transitive, so by the abstract Wielandt lemma its centralizer in `Sym(O)` is semiregular, bounding
the dual by 12. The 12-element image is itself regular, and an explicit opposite-regular family of
12 commuting permutations witnesses the dual has order exactly 12. -/

namespace Action

/-- The T/I action on pitch-class sets. -/
def smul : DihedralGroup 12 → Finset (ZMod 12) → Finset (ZMod 12)
  | r i,  S => tpose i S
  | sr j, S => inv (-j) S

instance : SMul (DihedralGroup 12) (Finset (ZMod 12)) := ⟨smul⟩

@[simp] lemma smul_r (i : ZMod 12) (S : Finset (ZMod 12)) :
    (r i : DihedralGroup 12) • S = tpose i S := rfl
@[simp] lemma smul_sr (j : ZMod 12) (S : Finset (ZMod 12)) :
    (sr j : DihedralGroup 12) • S = inv (-j) S := rfl

@[simp] lemma tpose_tpose (i j : ZMod 12) (S : Finset (ZMod 12)) :
    tpose i (tpose j S) = tpose (i + j) S := by
  unfold tpose; rw [Finset.image_image]
  apply Finset.image_congr; intro x _; simp only [Function.comp]; ring
@[simp] lemma inv_tpose (i j : ZMod 12) (S : Finset (ZMod 12)) :
    inv i (tpose j S) = inv (i - j) S := by
  unfold tpose inv; rw [Finset.image_image]
  apply Finset.image_congr; intro x _; simp only [Function.comp]; ring
@[simp] lemma tpose_inv (i j : ZMod 12) (S : Finset (ZMod 12)) :
    tpose i (inv j S) = inv (j + i) S := by
  unfold tpose inv; rw [Finset.image_image]
  apply Finset.image_congr; intro x _; simp only [Function.comp]; ring
@[simp] lemma inv_inv (i j : ZMod 12) (S : Finset (ZMod 12)) :
    inv i (inv j S) = tpose (i - j) S := by
  unfold tpose inv; rw [Finset.image_image]
  apply Finset.image_congr; intro x _; simp only [Function.comp]; ring
@[simp] lemma tpose_zero (S : Finset (ZMod 12)) : tpose 0 S = S := by
  unfold tpose; simp

instance : MulAction (DihedralGroup 12) (Finset (ZMod 12)) where
  one_smul S := by
    show (r 0 : DihedralGroup 12) • S = S
    rw [smul_r, tpose_zero]
  mul_smul g h S := by
    cases g <;> cases h <;>
      simp only [r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr, smul_r, smul_sr,
        tpose_tpose, inv_tpose, tpose_inv, inv_inv, neg_sub, neg_add_rev] <;>
      (apply congrFun (congrArg _ _); ring)

/-- The orbit of 6-30 as a set of pc-sets (the Mathlib `MulAction.orbit`). -/
abbrev O : Set (Finset (ZMod 12)) := MulAction.orbit (DihedralGroup 12) A

/-- 6-30 itself is in its orbit. -/
theorem A_mem_O : A ∈ O := MulAction.mem_orbit_self A

/-- `g • B` stays in `O` when `B ∈ O`. -/
theorem smul_mem_O {B : Finset (ZMod 12)} (hB : B ∈ O) (g : DihedralGroup 12) : g • B ∈ O := by
  obtain ⟨h, rfl⟩ := hB
  exact ⟨g * h, mul_smul g h A⟩

/-! ### The orbit as a set of cardinality 12 -/

/-- The Mathlib `MulAction.orbit` set coincides with the explicit Tier-1 `orbit` finset. -/
theorem O_eq_orbit : O = (orbit : Set (Finset (ZMod 12))) := by
  ext B
  rw [MulAction.mem_orbit_iff, Finset.mem_coe, orbit, Finset.mem_union,
    Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨g, rfl⟩
    cases g with
    | r i => exact Or.inl ⟨i, Finset.mem_univ _, rfl⟩
    | sr j => exact Or.inr ⟨-j, Finset.mem_univ _, rfl⟩
  · rintro (⟨k, _, rfl⟩ | ⟨j, _, rfl⟩)
    · exact ⟨r k, rfl⟩
    · exact ⟨sr (-j), by simp only [Action.smul_sr, neg_neg]⟩

/-- The induced action on the orbit has 12 elements. -/
theorem card_O : Nat.card O = 12 := by
  rw [Nat.card_coe_set_eq, O_eq_orbit, Set.ncard_coe_finset, orbit_card]

/-! ### The dual group: centralizer of the induced T/I action on the orbit

The induced action of `DihedralGroup 12` on `↥O` is transitive (Mathlib's `IsPretransitive` on
orbits). By the abstract Wielandt lemma `NeoRiemannian.Duality.centralizing_fixedPoint_eq_one`, the
centralizer of its image in `Sym(O)` is **semiregular**, so it embeds into `O` and has at most 12
elements. This is the dual group of 6-30. -/

open MulAction

/-- The image of the T/I group inside `Sym(O)` — the induced permutation representation. -/
abbrev TIgrpO : Subgroup (Equiv.Perm O) := (toPermHom (DihedralGroup 12) O).range

/-- The dual group: the centralizer of the T/I image in `Sym(O)`. -/
abbrev Cgrp : Subgroup (Equiv.Perm O) := Subgroup.centralizer (TIgrpO : Set (Equiv.Perm O))

/-- A centralizer element commutes with every `toPerm g`. -/
theorem Cgrp_comm {σ : Equiv.Perm O} (hσ : σ ∈ Cgrp) (g : DihedralGroup 12) :
    σ * toPerm g = toPerm g * σ :=
  ((Subgroup.mem_centralizer_iff).1 hσ (toPerm g) ⟨g, rfl⟩).symm

/-- The base point of the orbit: 6-30 itself. -/
def base : O := ⟨A, A_mem_O⟩

/-- Evaluation at `base` injects the dual group into `O` (semiregularity, via Wielandt). -/
theorem eval_injective : Function.Injective (fun c : Cgrp => (c : Equiv.Perm O) base) := by
  rintro ⟨c, hc⟩ ⟨d, hd⟩ heq
  simp only at heq
  have hmem : d⁻¹ * c ∈ Cgrp := mul_mem (inv_mem hd) hc
  have hfix : (d⁻¹ * c) base = base := by
    show d⁻¹ (c base) = base
    rw [heq]; exact d.symm_apply_apply base
  have h1 : d⁻¹ * c = 1 :=
    Duality.centralizing_fixedPoint_eq_one (G := DihedralGroup 12)
      (d⁻¹ * c) (Cgrp_comm hmem) base hfix
  exact Subtype.ext (inv_mul_eq_one.1 h1).symm

/-- **Wielandt bound:** the dual group of 6-30 has at most 12 elements. -/
theorem card_Cgrp_le : Nat.card Cgrp ≤ 12 := by
  have : Nat.card Cgrp ≤ Nat.card O := Nat.card_le_card_of_injective _ eval_injective
  rwa [card_O] at this

/-! ### The kernel of the T/I action on the orbit is the center `Z = {1, r 6}`

The induced action of `DihedralGroup 12` on `O` is *not* faithful: `T6` (the central transposition,
`r 6`) acts trivially on every orbit element. We show the kernel is exactly `{1, r 6}` — the center
of `D₁₂` for `n = 6` even — so the induced action factors through `D₁₂/Z`, which has order
`24/2 = 12 = |O|` and acts **faithfully + transitively**, i.e. *regularly*. -/

/-- The kernel of the permutation representation on `O`. -/
abbrev Ker : Subgroup (DihedralGroup 12) := (toPermHom (DihedralGroup 12) O).ker

/-- The stabilizer of `A` (as a pc-set) under `r i` is exactly `i ∈ {0, 6}`. -/
theorem r_smul_A_iff (i : ZMod 12) : (r i : DihedralGroup 12) • A = A ↔ i = 0 ∨ i = 6 := by
  rw [Action.smul_r]
  constructor
  · intro h
    have : i ∈ Finset.univ.filter (fun k : ZMod 12 => tpose k A = A) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩
    rw [stab_T] at this
    rcases Finset.mem_insert.mp this with h0 | h6
    · exact Or.inl h0
    · exact Or.inr (Finset.mem_singleton.mp h6)
  · rintro (rfl | rfl) <;> decide

/-- No inversion `sr j` fixes `A`. -/
theorem sr_smul_A_ne (j : ZMod 12) : (sr j : DihedralGroup 12) • A ≠ A := by
  rw [Action.smul_sr]
  have := not_inversionally_symmetric (-j)
  exact this

/-- `r 6` is central in `DihedralGroup 12`: it commutes with everything. -/
theorem r6_central (g : DihedralGroup 12) : (r 6 : DihedralGroup 12) * g = g * r 6 := by
  cases g with
  | r i => simp [r_mul_r, add_comm]
  | sr j =>
    simp only [r_mul_sr, sr_mul_r]; congr 1
    have h : (-6 : ZMod 12) = 6 := by decide
    rw [sub_eq_add_neg, h]

/-- `r 6` fixes `A`. -/
theorem r6_smul_A : (r 6 : DihedralGroup 12) • A = A := (r_smul_A_iff 6).mpr (Or.inr rfl)

/-- `r 6` acts trivially on the whole orbit (central + fixes `A`). -/
theorem r6_mem_Ker : (r 6 : DihedralGroup 12) ∈ Ker := by
  rw [MonoidHom.mem_ker]
  apply Equiv.Perm.ext
  intro B
  rw [toPermHom_apply, toPerm_apply, Equiv.Perm.coe_one, id]
  apply Subtype.ext
  rw [MulAction.orbit.coe_smul]
  obtain ⟨g, hg⟩ := B.2
  calc (r 6 : DihedralGroup 12) • (B : Finset (ZMod 12))
      = (r 6 : DihedralGroup 12) • (g • A) := by rw [← hg]
    _ = ((r 6 : DihedralGroup 12) * g) • A := by rw [mul_smul]
    _ = (g * r 6) • A := by rw [r6_central]
    _ = g • ((r 6 : DihedralGroup 12) • A) := by rw [mul_smul]
    _ = g • A := by rw [r6_smul_A]
    _ = (B : Finset (ZMod 12)) := hg

/-- An element of the kernel fixes `A`, hence is `r 0` or `r 6`. -/
theorem mem_Ker_iff (g : DihedralGroup 12) : g ∈ Ker ↔ g = 1 ∨ g = r 6 := by
  constructor
  · intro hg
    rw [MonoidHom.mem_ker] at hg
    have hA : g • A = A := by
      have := congrArg (fun σ => (σ base : Finset (ZMod 12))) hg
      simpa [base, toPermHom_apply, toPerm_apply, MulAction.orbit.coe_smul] using this
    cases g with
    | r i =>
      rcases (r_smul_A_iff i).mp hA with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    | sr j => exact absurd hA (sr_smul_A_ne j)
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact r6_mem_Ker

/-- The kernel of the action on `O` is exactly the center `{1, r 6}`. -/
theorem Ker_eq : (Ker : Set (DihedralGroup 12)) = {1, r 6} := by
  ext g
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact mem_Ker_iff g

/-- The kernel has exactly 2 elements (`1 ≠ r 6`). -/
theorem card_Ker : Nat.card Ker = 2 := by
  have : Nat.card Ker = Nat.card ({1, r 6} : Set (DihedralGroup 12)) :=
    Nat.card_congr (Set.equivOfEq Ker_eq)
  rw [this, Nat.card_coe_set_eq, Set.ncard_pair (by decide)]

/-! ### Regularity of the induced (quotient) action

The image `TIgrpO ≅ D₁₂/Ker` has order `24/2 = 12 = |O|`, and acts transitively on `O`. A
transitive action of a group whose order equals the size of the set is **regular** (simply
transitive). This is the precise sense in which the T/I action on the 6-30 orbit is the *regular
representation of `D₁₂/Z ≅ D₆`*. -/

/-- The induced T/I image on `O` has exactly 12 elements (`= |D₁₂| / |Ker| = 24/2`). -/
theorem card_TIgrpO : Nat.card TIgrpO = 12 := by
  -- |range| = |D12| / |ker| via first iso + Lagrange
  have hiso : Nat.card TIgrpO = Nat.card (DihedralGroup 12 ⧸ Ker) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv.symm
  have hlag : Nat.card (DihedralGroup 12 ⧸ Ker) * Nat.card Ker = Nat.card (DihedralGroup 12) :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup Ker).symm
  rw [card_Ker, DihedralGroup.nat_card] at hlag
  rw [hiso]
  omega

/-! ### The lower bound `|C| ≥ 12` — the opposite regular representation

For each `B ∈ O`, transitivity gives some `h` with `h • base = B`; the choice of `h` is unique only
mod `Ker`, but since `Ker` fixes every orbit point, `B ↦ h • (g • base)` is *well-defined*. This is
the **opposite regular representation** `opp g`: it commutes with the whole left T/I action (so lies
in `Cgrp`), and `opp g base = g • base`, so `g ↦ opp g` separates the 12 cosets of `Ker`. Hence the
dual has at least 12 elements, and with the Wielandt bound, exactly 12 — it acts regularly. -/

/-- A chosen group element carrying `base` to `B` (transitivity witness). -/
noncomputable def carrier (B : O) : DihedralGroup 12 :=
  (MulAction.exists_smul_eq (DihedralGroup 12) base B).choose

theorem carrier_smul (B : O) : carrier B • base = B :=
  (MulAction.exists_smul_eq (DihedralGroup 12) base B).choose_spec

/-- Two carriers of the same point differ by an element of `Ker`, which fixes `g • base`; hence the
opposite-rep value is independent of the chosen carrier. -/
theorem carrier_indep (g : DihedralGroup 12) {h : DihedralGroup 12} {B : O} (hh : h • base = B) :
    h • (g • base) = carrier B • (g • base) := by
  -- `(carrier B)⁻¹ * h` fixes base, so lies in the stabilizer = Ker, which fixes `g • base`.
  have hfix : ((carrier B)⁻¹ * h) • base = base := by
    have e1 : ((carrier B)⁻¹ * h) • base = (carrier B)⁻¹ • B := by rw [mul_smul, hh]
    have e2 : (carrier B)⁻¹ • B = base := by
      rw [inv_smul_eq_iff, carrier_smul]
    rw [e1, e2]
  have hker : (carrier B)⁻¹ * h ∈ Ker := by
    rw [mem_Ker_iff]
    cases hg : (carrier B)⁻¹ * h with
    | r i =>
      have : (r i : DihedralGroup 12) • base = base := hg ▸ hfix
      have hA : (r i : DihedralGroup 12) • A = A := by
        have := congrArg (Subtype.val) this
        rwa [MulAction.orbit.coe_smul] at this
      rcases (r_smul_A_iff i).mp hA with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    | sr j =>
      exfalso
      have : (sr j : DihedralGroup 12) • base = base := hg ▸ hfix
      have hA : (sr j : DihedralGroup 12) • A = A := by
        have := congrArg (Subtype.val) this
        rwa [MulAction.orbit.coe_smul] at this
      exact sr_smul_A_ne j hA
  -- Ker fixes `g • base ∈ O`, so `((carrier B)⁻¹ * h) • (g • base) = g • base`.
  have key : ((carrier B)⁻¹ * h) • (g • base) = (g • base : O) := by
    have := MonoidHom.mem_ker.mp hker
    have h2 := congrArg (fun σ : Equiv.Perm O => σ (g • base)) this
    simpa [toPermHom_apply, toPerm_apply] using h2
  calc (h : DihedralGroup 12) • (g • base)
      = (carrier B * ((carrier B)⁻¹ * h)) • (g • base) := by rw [mul_inv_cancel_left]
    _ = carrier B • (((carrier B)⁻¹ * h) • (g • base)) := by rw [mul_smul]
    _ = carrier B • (g • base) := by rw [key]

/-- The opposite-rep underlying function: `B ↦ (a carrier of B) • (g • base)`. -/
noncomputable def oppFun (g : DihedralGroup 12) (B : O) : O := carrier B • (g • base)

/-- `oppFun g⁻¹` is a two-sided inverse of `oppFun g`. -/
theorem oppFun_left_inv (g : DihedralGroup 12) (B : O) : oppFun g⁻¹ (oppFun g B) = B := by
  unfold oppFun
  set B' : O := carrier B • (g • base) with hB'
  have hwit : (carrier B * g) • base = B' := by rw [mul_smul]
  -- carrier_indep at g⁻¹ with witness `carrier B * g`
  have h1 : (carrier B * g) • (g⁻¹ • base) = carrier B' • (g⁻¹ • base) :=
    carrier_indep g⁻¹ hwit
  rw [← h1, mul_smul, smul_inv_smul, carrier_smul]

/-- `oppFun g` is also a left inverse of `oppFun g⁻¹` (the symmetric direction). -/
theorem oppFun_right_inv (g : DihedralGroup 12) (B : O) : oppFun g (oppFun g⁻¹ B) = B := by
  unfold oppFun
  set B' : O := carrier B • (g⁻¹ • base) with hB'
  have hwit : (carrier B * g⁻¹) • base = B' := by rw [mul_smul]
  have h1 : (carrier B * g⁻¹) • (g • base) = carrier B' • (g • base) :=
    carrier_indep g hwit
  rw [← h1, mul_smul, inv_smul_smul, carrier_smul]

/-- The opposite-rep permutation `opp g ∈ Sym(O)`. -/
noncomputable def oppPerm (g : DihedralGroup 12) : Equiv.Perm O where
  toFun := oppFun g
  invFun := oppFun g⁻¹
  left_inv := oppFun_left_inv g
  right_inv := oppFun_right_inv g

@[simp] theorem oppPerm_apply (g : DihedralGroup 12) (B : O) : oppPerm g B = carrier B • (g • base) :=
  rfl

/-- `opp g` fixes `base ↦ g • base`. -/
theorem oppPerm_base (g : DihedralGroup 12) : oppPerm g base = g • base := by
  rw [oppPerm_apply]
  have : carrier base • base = base := carrier_smul base
  -- carrier base • (g • base) = g • (carrier base • base)? No — use carrier_indep with witness 1.
  have h1 : (1 : DihedralGroup 12) • (g • base) = carrier base • (g • base) :=
    carrier_indep g (by rw [one_smul])
  rw [← h1, one_smul]

/-- Each `opp g` lies in the dual group `Cgrp` (commutes with the whole left T/I action). -/
theorem oppPerm_mem_Cgrp (g : DihedralGroup 12) : oppPerm g ∈ Cgrp := by
  refine (Subgroup.mem_centralizer_iff).2 ?_
  rintro _ ⟨f, rfl⟩
  apply Equiv.Perm.ext
  intro B
  simp only [Equiv.Perm.mul_apply, toPermHom_apply, toPerm_apply, oppPerm_apply]
  -- LHS: f • (carrier B • (g•base));  RHS: carrier (f•B) • (g•base)
  -- (f * carrier B) is a carrier of f • B, so carrier_indep applies.
  have hwit : (f * carrier B) • base = f • B := by rw [mul_smul, carrier_smul]
  have := carrier_indep g hwit
  rw [← this, mul_smul]

/-- The opposite rep, evaluated at `base`, recovers the carrier: `opp (carrier B) base = B`. -/
theorem oppPerm_carrier_base (B : O) : oppPerm (carrier B) base = B :=
  (oppPerm_base (carrier B)).trans (carrier_smul B)

/-- `B ↦ opp (carrier B)` injects `O` into the dual group `Cgrp` (12 distinct elements). -/
theorem oppInj : Function.Injective (fun B : O => (⟨oppPerm (carrier B), oppPerm_mem_Cgrp _⟩ : Cgrp)) := by
  intro B₁ B₂ h
  have h2 : oppPerm (carrier B₁) = oppPerm (carrier B₂) := congrArg Subtype.val h
  have h3 : oppPerm (carrier B₁) base = oppPerm (carrier B₂) base := by rw [h2]
  rw [oppPerm_carrier_base, oppPerm_carrier_base] at h3
  exact h3

/-- **Lower bound:** the dual group has at least 12 elements. -/
theorem card_Cgrp_ge : 12 ≤ Nat.card Cgrp := by
  have h := Nat.card_le_card_of_injective _ oppInj
  rwa [card_O] at h

/-- **Tier 2, headline:** the dual group of 6-30 has exactly 12 elements. -/
theorem card_Cgrp : Nat.card Cgrp = 12 :=
  le_antisymm card_Cgrp_le card_Cgrp_ge

/-! ### The dual acts regularly

`Cgrp` is semiregular (`eval_injective`) and has 12 elements on a 12-point set; together with
transitivity it acts *simply transitively* (regularly). We record transitivity: every point of `O`
is `opp (carrier B) • base`, witnessing that `Cgrp` reaches every orbit element from `base`. -/

/-- The dual group acts **transitively** on `O`. -/
theorem Cgrp_transitive (B : O) :
    ∃ c : Cgrp, (c : Equiv.Perm O) base = B :=
  ⟨⟨oppPerm (carrier B), oppPerm_mem_Cgrp _⟩, oppPerm_carrier_base B⟩

/-! ## TIER 3 — the dihedral fingerprint of the dual

The opposite representation `opp` is a group **anti-homomorphism** `D₁₂ → Sym(O)` with image `Cgrp`
and kernel `Ker = Z`, so `Cgrp ≅ (D₁₂/Z)ᵒᵖ ≅ D₁₂/Z`. Mathlib has no `D₁₂/Z ≃* D₆`, so we land the
*dihedral fingerprint* that pins `Cgrp ≅ D₆` among the five groups of order 12: `Cgrp` is

* order 12 (Tier 2),
* **non-abelian**, with
* an element `s` of **order 6** and
* an **involution** `t ≠ 1` that **inverts** it: `t * s * t = s⁻¹` and `s * t ≠ t * s`.

These four facts identify `Cgrp ≅ DihedralGroup 6`; the named `≃*` is the remaining (Mathlib-gap)
step `D₁₂/Z ≃* D₆`. -/

/-- `opp` sends `1` to `1`. -/
theorem oppPerm_one : oppPerm (1 : DihedralGroup 12) = 1 := by
  apply Equiv.Perm.ext; intro B
  rw [oppPerm_apply, one_smul, Equiv.Perm.coe_one, id, carrier_smul]

/-- `opp` is a group **anti-homomorphism**: `opp (g * h) = opp h * opp g`. -/
theorem oppPerm_mul (g h : DihedralGroup 12) :
    oppPerm (g * h) = oppPerm h * oppPerm g := by
  apply Equiv.Perm.ext; intro B
  rw [Equiv.Perm.mul_apply, oppPerm_apply, oppPerm_apply, oppPerm_apply]
  -- RHS = carrier (carrier B • (g • base)) • (h • base); witness `carrier B * g`.
  have hwit : (carrier B * g) • base = carrier B • (g • base) := by rw [mul_smul]
  have := carrier_indep h hwit
  rw [← this, mul_smul, mul_smul]

/-- Powers go through the anti-hom: `opp (g ^ n) = (opp g) ^ n`. -/
theorem oppPerm_pow (g : DihedralGroup 12) : ∀ n : ℕ, oppPerm (g ^ n) = (oppPerm g) ^ n
  | 0 => by rw [pow_zero, pow_zero, oppPerm_one]
  | n + 1 => by rw [pow_succ, pow_succ', oppPerm_mul, oppPerm_pow g n]

/-- The opposite rep as a map into the dual subgroup `Cgrp`. -/
noncomputable def oppC (g : DihedralGroup 12) : Cgrp := ⟨oppPerm g, oppPerm_mem_Cgrp g⟩

/-- `oppC` is an anti-homomorphism into `Cgrp`. -/
theorem oppC_mul (g h : DihedralGroup 12) : oppC (g * h) = oppC h * oppC g :=
  Subtype.ext (oppPerm_mul g h)

theorem oppC_one : oppC 1 = 1 := Subtype.ext oppPerm_one

/-- The chosen order-6 element of the dual: `s = opp (r 1)`. -/
noncomputable def s : Cgrp := oppC (r 1)
/-- The chosen involution of the dual: `t = opp (sr 0)`. -/
noncomputable def t : Cgrp := oppC (sr 0)

/-- `s` has order 6: `s^6 = 1` and `s^k ≠ 1` for `0 < k < 6` (checked via `opp (r k) base = r k • base`
which are 6 distinct points). -/
theorem s_pow_six : s ^ 6 = 1 := by
  apply Subtype.ext
  show (oppPerm (r 1)) ^ 6 = (1 : Equiv.Perm O)
  rw [← oppPerm_pow, r_pow]
  have h6 : (r (1 * (6 : ℕ)) : DihedralGroup 12) = r 6 := by decide
  rw [h6]
  -- opp (r 6) = 1 since r 6 ∈ Ker
  have := r6_mem_Ker
  rw [MonoidHom.mem_ker] at this  -- not directly opp; instead use that r 6 fixes base
  apply Equiv.Perm.ext; intro B
  rw [oppPerm_apply, Equiv.Perm.coe_one, id]
  -- carrier B • (r 6 • base) = carrier B • base = B
  have hb : (r 6 : DihedralGroup 12) • base = base := by
    apply Subtype.ext; rw [MulAction.orbit.coe_smul]; exact r6_smul_A
  rw [hb, carrier_smul]

/-- `s ≠ 1`: order strictly bigger than 1 (`opp (r 1) base = r 1 • base ≠ base`). -/
theorem s_ne_one : s ≠ 1 := by
  intro h
  have : oppPerm (r 1) base = base := by
    have := congrArg (fun c : Cgrp => (c : Equiv.Perm O) base) h
    simpa [s, oppC] using this
  rw [oppPerm_base] at this
  -- r 1 • base = base would put r 1 ∈ Ker = {1, r6}
  have hA : (r 1 : DihedralGroup 12) • A = A := by
    have := congrArg Subtype.val this
    rwa [MulAction.orbit.coe_smul] at this
  rcases (r_smul_A_iff 1).mp hA with h0 | h6
  · exact absurd h0 (by decide)
  · exact absurd h6 (by decide)

/-- `t` is an involution: `t^2 = 1`. -/
theorem t_sq : t ^ 2 = 1 := by
  apply Subtype.ext
  show (oppPerm (sr 0)) ^ 2 = (1 : Equiv.Perm O)
  rw [← oppPerm_pow]
  have : (sr 0 : DihedralGroup 12) ^ 2 = 1 := by
    rw [pow_two, sr_mul_sr, sub_zero]; rfl
  rw [this, oppPerm_one]

/-- `t ≠ 1`. -/
theorem t_ne_one : t ≠ 1 := by
  intro h
  have : oppPerm (sr 0) base = base := by
    have := congrArg (fun c : Cgrp => (c : Equiv.Perm O) base) h
    simpa [t, oppC] using this
  rw [oppPerm_base] at this
  have hA : (sr 0 : DihedralGroup 12) • A = A := by
    have := congrArg Subtype.val this
    rwa [MulAction.orbit.coe_smul] at this
  exact sr_smul_A_ne 0 hA

/-- `opp (r k)` fixes `base` iff `r k ∈ Ker`, i.e. `k = 0` or `k = 6`. -/
theorem oppC_r_eq_one_iff (k : ZMod 12) : oppC (r k) = 1 ↔ k = 0 ∨ k = 6 := by
  constructor
  · intro h
    have hb : oppPerm (r k) base = base := by
      have := congrArg (fun c : Cgrp => (c : Equiv.Perm O) base) h
      simpa [oppC] using this
    rw [oppPerm_base] at hb
    have hA : (r k : DihedralGroup 12) • A = A := by
      have := congrArg Subtype.val hb
      rwa [MulAction.orbit.coe_smul] at this
    exact (r_smul_A_iff k).mp hA
  · rintro (rfl | rfl)
    · rw [show (r 0 : DihedralGroup 12) = 1 from rfl, oppC_one]
    · exact Subtype.ext (by
        apply Equiv.Perm.ext; intro B
        rw [oppC]; show oppPerm (r 6) B = (1 : Equiv.Perm O) B
        rw [oppPerm_apply, Equiv.Perm.coe_one, id]
        have hb : (r 6 : DihedralGroup 12) • base = base := by
          apply Subtype.ext; rw [MulAction.orbit.coe_smul]; exact r6_smul_A
        rw [hb, carrier_smul])

/-- `oppC` powers: `oppC (g ^ n) = (oppC g) ^ n`. -/
theorem oppC_pow (g : DihedralGroup 12) (n : ℕ) : oppC (g ^ n) = (oppC g) ^ n := by
  apply Subtype.ext
  rw [SubgroupClass.coe_pow]
  show oppPerm (g ^ n) = (oppPerm g) ^ n
  exact oppPerm_pow g n

/-- `s ^ k = oppC (r k)` (since `(r 1) ^ k = r k`). -/
theorem s_pow (k : ℕ) : s ^ k = oppC (r (k : ZMod 12)) := by
  have h : s ^ k = oppC ((r 1) ^ k) := by rw [oppC_pow]; rfl
  rw [h, r_one_pow]

/-- `s ^ k = 1` iff `k ≡ 0` or `k ≡ 6 (mod 12)`. -/
theorem s_pow_eq_one_iff (k : ℕ) : s ^ k = 1 ↔ ((k : ZMod 12) = 0 ∨ (k : ZMod 12) = 6) := by
  rw [s_pow]; exact oppC_r_eq_one_iff _

/-- **`s` has order exactly 6.** -/
theorem orderOf_s : orderOf s = 6 := by
  have hdvd : orderOf s ∣ 6 := orderOf_dvd_of_pow_eq_one s_pow_six
  have h1 : s ^ 1 ≠ 1 := fun h => by have := (s_pow_eq_one_iff 1).mp h; revert this; decide
  have h2 : s ^ 2 ≠ 1 := fun h => by have := (s_pow_eq_one_iff 2).mp h; revert this; decide
  have h3 : s ^ 3 ≠ 1 := fun h => by have := (s_pow_eq_one_iff 3).mp h; revert this; decide
  have hmem : orderOf s ∈ Nat.divisors 6 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hcases : orderOf s = 1 ∨ orderOf s = 2 ∨ orderOf s = 3 ∨ orderOf s = 6 := by
    have : Nat.divisors 6 = {1, 2, 3, 6} := by decide
    rw [this] at hmem
    simpa using hmem
  rcases hcases with hc | hc | hc | hc
  · exact absurd (by rw [← hc]; exact pow_orderOf_eq_one s) h1
  · exact absurd (by rw [← hc]; exact pow_orderOf_eq_one s) h2
  · exact absurd (by rw [← hc]; exact pow_orderOf_eq_one s) h3
  · exact hc

/-- `oppC g⁻¹ = (oppC g)⁻¹` (anti-hom sends inverse to inverse). -/
theorem oppC_inv (g : DihedralGroup 12) : oppC g⁻¹ = (oppC g)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← oppC_mul, mul_inv_cancel, oppC_one]

/-- **`t` inverts `s`:** `t * s * t = s⁻¹` (the dihedral reflection relation). -/
theorem t_mul_s_mul_t : t * s * t = s⁻¹ := by
  show oppC (sr 0) * oppC (r 1) * oppC (sr 0) = (oppC (r 1))⁻¹
  rw [← oppC_mul, ← oppC_mul, ← oppC_inv]
  -- (sr 0) * ((r 1) * (sr 0)) = (r 1)⁻¹  in D₁₂
  congr 1

/-- The two products `s * t` and `t * s`, evaluated at `base`. -/
theorem st_base : (s * t : Cgrp).val base = (sr 1 : DihedralGroup 12) • base := by
  show (oppC (r 1) * oppC (sr 0)).val base = _
  rw [← oppC_mul, sr_mul_r]
  show oppPerm (sr (0 + 1)) base = _
  rw [oppPerm_base, zero_add]
theorem ts_base : (t * s : Cgrp).val base = (sr (-1) : DihedralGroup 12) • base := by
  show (oppC (sr 0) * oppC (r 1)).val base = _
  rw [← oppC_mul, r_mul_sr]
  show oppPerm (sr (0 - 1)) base = _
  rw [oppPerm_base, zero_sub]

/-- **`Cgrp` is non-abelian:** `s * t ≠ t * s`. -/
theorem s_t_not_commute : s * t ≠ t * s := by
  intro h
  have hb : (s * t : Cgrp).val base = (t * s : Cgrp).val base := by rw [h]
  rw [st_base, ts_base] at hb
  -- sr 1 • base = sr (-1) • base ⇒ (sr 1)⁻¹ * sr (-1) = r(-2) ∈ Ker, false
  have hA : (sr 1 : DihedralGroup 12) • A = (sr (-1) : DihedralGroup 12) • A := by
    have := congrArg Subtype.val hb
    rwa [MulAction.orbit.coe_smul, MulAction.orbit.coe_smul] at this
  -- inv 11 A = inv 1 A as pc-sets — disprove by decide
  rw [Action.smul_sr, Action.smul_sr] at hA
  revert hA; decide

/-- **`Cgrp` is non-abelian.** -/
theorem Cgrp_nonabelian : ∃ a b : Cgrp, a * b ≠ b * a := ⟨s, t, s_t_not_commute⟩

/-! ### Tier-3 summary — the dihedral fingerprint of the dual

Bundled: `Cgrp` has order 12, is non-abelian, contains an element `s` of order 6 and a non-trivial
involution `t` that inverts it (`t s t = s⁻¹`). These pin `Cgrp ≅ DihedralGroup 6` among the order-12
groups. The named `Cgrp ≃* DihedralGroup 6` requires `D₁₂/Z ≃* D₆`, absent from Mathlib. -/
theorem dihedral_fingerprint :
    Nat.card Cgrp = 12 ∧ orderOf s = 6 ∧ t ^ 2 = 1 ∧ t ≠ 1 ∧
      t * s * t = s⁻¹ ∧ s * t ≠ t * s :=
  ⟨card_Cgrp, orderOf_s, t_sq, t_ne_one, t_mul_s_mul_t, s_t_not_commute⟩

end Action

end SixThirty

end MusicTheory
