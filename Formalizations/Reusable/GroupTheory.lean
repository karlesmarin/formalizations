/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.GroupTheory.GroupAction.PolyaRedfield
public import Formalizations.GroupTheory.GroupAction.Separation

/-!
# Reusable layer: group actions

Stable names for counting results on finite group actions. Each theorem is proved by the archive
theorem it re-exposes (no proof is copied). The module imported here is general group theory, not a
paper of the archive, and imports only Mathlib.

## Main results

* `Formalizations.Reusable.separation_lemma_of_pretransitive`: if `G` acts pretransitively on `Ω` and
  `#A · #B < #Ω`, some `g` moves `A` off `B` (archive: `TotD.separation_lemma_of_pretransitive`).
* `Formalizations.Reusable.polya_redfield_card_mul_sum_orbit_weight`: the weighted Pólya–Redfield
  enumeration theorem for colourings `α → C` under Mathlib's `arrowAction` (archive:
  `PolyaRedfield.card_mul_sum_orbit_weight`).
-/

@[expose] public section

namespace Formalizations.Reusable

open Classical in
/-- **The Pólya–Redfield enumeration theorem** (weighted form). A finite group `G` acting on a
finite set `α` acts on colourings `F : α → C` by Mathlib's `arrowAction`, `(g • F) a = F (g⁻¹ • a)`.
Give each colour a weight `w c` in a commutative ring and each colouring the weight
`W F = ∏ₐ w (F a)`. Then
`|G| · Σ_{orbits O} W O = Σ_{g ∈ G} p₁^{fix g} · ∏_{cycles of g of length k ≥ 2} p_k`, where
`p_k = Σ_c (w c)^k`: the cycle index of the action evaluated at the power sums of the weights
(Mathlib's `Equiv.Perm.cycleType` lists the cycles of length at least `2`; the fixed points are the
cycles of length `1`). With `w = 1` it counts colourings up to symmetry.

* Archive: `PolyaRedfield.card_mul_sum_orbit_weight`
  (`Formalizations.GroupTheory.GroupAction.PolyaRedfield`, a weighted Burnside lemma plus the
  factorization of the fixed colourings over the cycles); the module cites no paper DOI of ours.
* Classical reference: J. H. Redfield, *The theory of group-reduced distributions*, Amer. J. Math.
  49 (1927) 433–455; G. Pólya, Acta Math. 68 (1937) 145–254.
* Example: the necklaces of `4` beads in `2` colours up to rotation (`G = ZMod 4` acting on itself)
  are `(2⁴ + 2 + 2² + 2) / 4 = 6`. -/
theorem polya_redfield_card_mul_sum_orbit_weight {G α C R : Type*} [Group G] [Fintype G]
    [MulAction G α] [Fintype α] [Fintype C] [CommRing R] (w : C → R) :
    letI := arrowAction (G := G) (A := α) (B := C)
    (Fintype.card G : R) * ∑ O : MulAction.orbitRel.Quotient G (α → C), ∏ a, w (O.out a) =
      ∑ g : G, (∑ c, w c) ^ (Fintype.card (Function.fixedPoints (MulAction.toPerm g : Equiv.Perm α))) *
        ((MulAction.toPerm g : Equiv.Perm α).cycleType.map (fun k => ∑ c, w c ^ k)).prod :=
  PolyaRedfield.card_mul_sum_orbit_weight w


/-- **Separation lemma (transitive case).** If a group `G` acts pretransitively on `Ω` and `A B : Finset Ω`
satisfy `#A · #B < #Ω`, then some `g : G` maps `A` off `B`: `g • a ∉ B` for all `a ∈ A`. No finiteness of
`G` or `Ω` is assumed; the hypothesis forces `Ω` to be finite (`Nat.card` of an infinite type is `0`).

* Archive: `TotD.separation_lemma_of_pretransitive` (`Formalizations.GroupTheory.GroupAction.Separation`, a
  covering argument by B. H. Neumann's coset-cover lemma, `Subgroup.exists_index_le_card_of_leftCoset_cover`);
  the module cites no paper DOI of ours.
* Classical reference: P. J. Cameron, *Synchronization*, LTCC lecture notes, 2010, Lecture 3 (as cited in the
  archive module).
* Example: in `Perm (Fin 4)` some permutation moves `0` off `{1}`, since `1 · 1 < 4`. -/
theorem separation_lemma_of_pretransitive (G : Type*) {Ω : Type*} [Group G] [MulAction G Ω]
    [MulAction.IsPretransitive G Ω] {A B : Finset Ω} (h : A.card * B.card < Nat.card Ω) :
    ∃ g : G, ∀ a ∈ A, g • a ∉ B :=
  TotD.separation_lemma_of_pretransitive G h

end Formalizations.Reusable
