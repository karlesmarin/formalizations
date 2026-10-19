/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Tactic.Ring

/-!
# Characters that are `−1` at an involution and trivial on a subgroup

For a finite commutative group `G`, an element `s` with `s² = 1` and a subgroup `H`, there is a
character `χ : G →* ℂˣ` with `χ s = −1` and `χ` trivial on `H` iff `s ∉ H`. Applied to
`G = (ZMod N)ˣ`, `s = −1`: an odd character trivial on `⟨u⟩` exists iff `−1 ∉ ⟨u⟩`. The separation
of points by characters is Mathlib's `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`.

## Main results

* `ConjeturaC.exists_char_neg_one_iff`: the general statement.
* `ConjeturaC.exists_oddChar_trivial_on_zpowers_iff`: `G = (ZMod N)ˣ`, `s = −1`, `H = ⟨u⟩`.
* `ConjeturaC.exists_oddChar_trivial_on_two_iff`: the case `u = 2`, `N` odd.

## References

* C. Marín, *Where the character values of Sp(2m) at a torsion element fail to generate the ring
  of integers*, Zenodo (2026), doi:10.5281/zenodo.22813216 (odd characters trivial on `⟨2⟩`).
-/

@[expose] public section

namespace ConjeturaC

/-- A unit of `ℂ` whose square is `1` is `1` or `-1`. -/
theorem units_sq_eq_one {u : ℂˣ} (hu : u ^ 2 = 1) : u = 1 ∨ u = -1 :=
  Units.eq_or_eq_neg_of_sq_eq_sq u 1 (by rw [hu, one_pow])

/-- Characters of a finite commutative group with values in `ℂˣ` separate points. -/
theorem exists_char_ne_one {Q : Type*} [CommGroup Q] [Finite Q] {a : Q} (ha : a ≠ 1) :
    ∃ φ : Q →* ℂˣ, φ a ≠ 1 := by
  have : NeZero ((Monoid.exponent Q : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.2 (Monoid.exponent_ne_zero_of_finite)⟩
  exact CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Q ℂ ha

/-- A character with `χ s = −1` and trivial on `H` exists iff `s ∉ H`. (A hypothesis `s ≠ 1` is
not needed: it follows from `s ∉ H`, and the forward direction never uses it.) -/
theorem exists_char_neg_one_iff {G : Type*} [CommGroup G] [Finite G] {s : G} (hs : s ^ 2 = 1)
    (H : Subgroup G) :
    (∃ χ : G →* ℂˣ, χ s = -1 ∧ ∀ h ∈ H, χ h = 1) ↔ s ∉ H := by
  constructor
  · rintro ⟨χ, hχs, hχH⟩ hsH
    have h1 := hχH s hsH
    rw [hχs] at h1
    have : ((-1 : ℂˣ) : ℂ) = ((1 : ℂˣ) : ℂ) := congrArg Units.val h1
    norm_num at this
  · intro hsH
    have ha : (QuotientGroup.mk' H s) ≠ 1 := by
      rwa [ne_eq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    obtain ⟨φ, hφ⟩ := exists_char_ne_one ha
    refine ⟨φ.comp (QuotientGroup.mk' H), ?_, fun h hh => ?_⟩
    · have hsq : (φ.comp (QuotientGroup.mk' H) s) ^ 2 = 1 := by
        rw [← map_pow, hs, map_one]
      rcases units_sq_eq_one hsq with h | h
      · exact absurd h hφ
      · exact h
    · simp [(QuotientGroup.eq_one_iff h).2 hh]

/-- Application: an odd character of `(ZMod N)ˣ` trivial on `⟨u⟩` exists iff `-1 ∉ ⟨u⟩`. -/
theorem exists_oddChar_trivial_on_zpowers_iff {N : ℕ} [NeZero N] (u : (ZMod N)ˣ) :
    (∃ χ : (ZMod N)ˣ →* ℂˣ, χ (-1) = -1 ∧ ∀ h ∈ Subgroup.zpowers u, χ h = 1) ↔
      (-1 : (ZMod N)ˣ) ∉ Subgroup.zpowers u :=
  exists_char_neg_one_iff (by simp) _

/-- Concrete form for `u = 2`, `N` odd. -/
theorem exists_oddChar_trivial_on_two_iff {N : ℕ} [NeZero N] (hN : Nat.Coprime 2 N) :
    (∃ χ : (ZMod N)ˣ →* ℂˣ, χ (-1) = -1 ∧
        ∀ h ∈ Subgroup.zpowers (ZMod.unitOfCoprime 2 hN), χ h = 1) ↔
      (-1 : (ZMod N)ˣ) ∉ Subgroup.zpowers (ZMod.unitOfCoprime 2 hN) :=
  exists_oddChar_trivial_on_zpowers_iff _

end ConjeturaC
