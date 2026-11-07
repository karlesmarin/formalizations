/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

-- encaje: núcleo de la prueba del Teorema 6 (thm:Q) de la nota qp_bsr: unicidad de la Gram PSD.
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic.Ring

/-!
# Uniqueness of the positive semidefinite Gram matrix

This file formalizes the linear-algebra core of the proof of Theorem 6 (`thm:Q`) of
C. Marín, *Quadratic persistence of Segre varieties and a linear gap between biquadratic SOS rank
and Zarankiewicz bounds* (2026): if the points `p i` make the map `D ↦ (D p_i)_i` injective on a
subspace `𝒟` of matrices, then a positive semidefinite Gram matrix that vanishes on the `p i` is
unique modulo `𝒟`; and the Gram matrix `G = ∑ j, c j • u j u jᵀ` (`c j > 0`, `u j ⬝ p i = 0`) of
`F = ∑ j c j u_j²` (in the note `c = (1, …, 1, 7)`) is positive semidefinite, kills the `p i`,
and has rank `e` (the number of `u j`) when the `u j` are linearly independent.

Everything is over `ℝ` with an arbitrary finite index type `n` (in the note `n = Fin (m * n)`).

## Main results

* `SegrePersistence.GramUnique.mulVec_eq_zero`: `G` PSD and `pᵀ G p = 0` give `G p = 0`
  (this is Mathlib's `Matrix.PosSemidef.dotProduct_mulVec_zero_iff`, specialised to `ℝ`).
* `SegrePersistence.GramUnique.eq_of_posSemidef`: two PSD matrices whose difference lies in `𝒟`
  and whose quadratic forms vanish at every `p i` are equal.
* `SegrePersistence.GramUnique.eq_of_posSemidef_of_form_eq`: the same, assuming only that the two
  quadratic forms agree at the `p i` and that one of them vanishes there.
* `SegrePersistence.GramUnique.gramOf_posSemidef`, `gramOf_mulVec_eq_zero`,
  `dotProduct_gramOf_mulVec`, `gramOf_rank`: the Gram matrix of `∑ j c j u_j²`.
* `SegrePersistence.GramUnique.gramOf_unique`: the combination used in the note.

## What is not covered

That `𝒟` is the space of Gram relations of the Segre variety (`⋀²A* ⊗ ⋀²B*`), the existence of
`qp(X)` rational simple tensors `p i` making the map injective (a Zariski-density argument), the
identification of a Gram matrix of the biquadratic form `F` with a matrix whose difference with
`gramOf c u` lies in `𝒟`, and the rational count `ℓ_ℚ(F) = e + 3` (Witt cancellation and
`7` not a sum of three rational squares, which goes through `seven_embedding` in Isabelle) are
not formalized here.
-/

@[expose] public section

open Matrix Finset

namespace SegrePersistence

namespace GramUnique

variable {n ι κ : Type*} [Fintype n]

/-- A positive semidefinite real matrix whose quadratic form vanishes at `p` kills `p`. -/
theorem mulVec_eq_zero {G : Matrix n n ℝ} (hG : G.PosSemidef) {p : n → ℝ}
    (hp : p ⬝ᵥ G *ᵥ p = 0) : G *ᵥ p = 0 :=
  hG.dotProduct_mulVec_zero_iff.mp (by simpa using hp)

/-- **Uniqueness of the PSD Gram matrix.** If `D ↦ (D *ᵥ p i)_i` is injective on `𝒟`, two
positive semidefinite matrices `G, G'` with `G - G' ∈ 𝒟` whose quadratic forms vanish at every
`p i` are equal. -/
theorem eq_of_posSemidef (𝒟 : Submodule ℝ (Matrix n n ℝ)) (p : ι → n → ℝ)
    (hinj : ∀ D ∈ 𝒟, (∀ i, D *ᵥ p i = 0) → D = 0)
    {G G' : Matrix n n ℝ} (hG : G.PosSemidef) (hG' : G'.PosSemidef) (hD : G - G' ∈ 𝒟)
    (h0 : ∀ i, p i ⬝ᵥ G *ᵥ p i = 0) (h0' : ∀ i, p i ⬝ᵥ G' *ᵥ p i = 0) : G = G' := by
  refine sub_eq_zero.mp (hinj _ hD fun i => ?_)
  rw [sub_mulVec, mulVec_eq_zero hG (h0 i), mulVec_eq_zero hG' (h0' i), sub_zero]

/-- Variant of `eq_of_posSemidef`: it suffices that the two quadratic forms agree at the `p i`
and that one of them vanishes there. -/
theorem eq_of_posSemidef_of_form_eq (𝒟 : Submodule ℝ (Matrix n n ℝ)) (p : ι → n → ℝ)
    (hinj : ∀ D ∈ 𝒟, (∀ i, D *ᵥ p i = 0) → D = 0)
    {G G' : Matrix n n ℝ} (hG : G.PosSemidef) (hG' : G'.PosSemidef) (hD : G - G' ∈ 𝒟)
    (h0 : ∀ i, p i ⬝ᵥ G *ᵥ p i = 0)
    (hform : ∀ i, p i ⬝ᵥ G' *ᵥ p i = p i ⬝ᵥ G *ᵥ p i) : G = G' :=
  eq_of_posSemidef 𝒟 p hinj hG hG' hD h0 fun i => (hform i).trans (h0 i)

variable [Fintype κ]

/-- The Gram matrix `∑ j, c j • u j u jᵀ` of the quadratic form `∑ j, c j (u j ⬝ x)²`. -/
noncomputable def gramOf (c : κ → ℝ) (u : κ → n → ℝ) : Matrix n n ℝ :=
  ∑ j, c j • vecMulVec (u j) (u j)

/-- `gramOf c u` is the Gram matrix of `x ↦ ∑ j, c j (u j ⬝ x)²`. -/
theorem dotProduct_gramOf_mulVec (c : κ → ℝ) (u : κ → n → ℝ) (x : n → ℝ) :
    x ⬝ᵥ gramOf c u *ᵥ x = ∑ j, c j * (u j ⬝ᵥ x) ^ 2 := by
  simp only [gramOf, Matrix.sum_mulVec, smul_mulVec, dotProduct_sum, dotProduct_smul,
    vecMulVec_mulVec, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [op_smul_eq_mul, dotProduct_comm x (u j)]
  ring

theorem gramOf_posSemidef {c : κ → ℝ} (hc : ∀ j, 0 ≤ c j) (u : κ → n → ℝ) :
    (gramOf c u).PosSemidef :=
  posSemidef_sum _ fun j _ => by
    simpa using (posSemidef_vecMulVec_self_star (u j)).smul (hc j)

/-- If every `u j` annihilates `p`, the Gram matrix kills `p`. -/
theorem gramOf_mulVec_eq_zero (c : κ → ℝ) (u : κ → n → ℝ) {p : n → ℝ}
    (hp : ∀ j, u j ⬝ᵥ p = 0) : gramOf c u *ᵥ p = 0 := by
  simp [gramOf, Matrix.sum_mulVec, smul_mulVec, vecMulVec_mulVec, hp]

/-- With `c j > 0` and the `u j` linearly independent, `rank (gramOf c u) = card κ`. -/
theorem gramOf_rank {c : κ → ℝ} (hc : ∀ j, 0 < c j) {u : κ → n → ℝ}
    (hu : LinearIndependent ℝ u) : (gramOf c u).rank = Fintype.card κ := by
  set B : Matrix n κ ℝ := Matrix.of fun a j => Real.sqrt (c j) * u j a with hB
  have hG : gramOf c u = B * Bᵀ := by
    ext a b
    simp only [gramOf, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
      Matrix.mul_apply, transpose_apply, hB, Matrix.of_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := Real.mul_self_sqrt (hc j).le
    calc c j * (u j a * u j b) = (Real.sqrt (c j) * Real.sqrt (c j)) * (u j a * u j b) := by
          rw [this]
      _ = _ := by ring
  have hcols : Bᵀ = fun j => (Units.mk0 (Real.sqrt (c j))
      (Real.sqrt_ne_zero'.mpr (hc j))) • u j := by
    ext j a
    simp [hB, Units.smul_def]
  have hli : LinearIndependent ℝ Bᵀ := by
    rw [hcols]
    exact hu.units_smul _
  rw [hG, rank_self_mul_transpose, rank_eq_finrank_span_cols]
  exact finrank_span_eq_card hli

/-- **The combination used in the note.** For `G = gramOf c u` with `c j > 0` and `u j ⬝ p i = 0`:
`G` is PSD, kills every `p i`, every PSD `G'` with `G - G' ∈ 𝒟` and the same quadratic form at the
`p i` equals `G` (when `D ↦ (D p_i)_i` is injective on `𝒟`), and `rank G = card κ` when the `u j`
are linearly independent. -/
theorem gramOf_unique (𝒟 : Submodule ℝ (Matrix n n ℝ)) (p : ι → n → ℝ)
    (hinj : ∀ D ∈ 𝒟, (∀ i, D *ᵥ p i = 0) → D = 0)
    {c : κ → ℝ} (hc : ∀ j, 0 < c j) {u : κ → n → ℝ} (hup : ∀ j i, u j ⬝ᵥ p i = 0)
    {G' : Matrix n n ℝ} (hG' : G'.PosSemidef) (hD : gramOf c u - G' ∈ 𝒟)
    (hform : ∀ i, p i ⬝ᵥ G' *ᵥ p i = p i ⬝ᵥ gramOf c u *ᵥ p i) :
    (gramOf c u).PosSemidef ∧ (∀ i, gramOf c u *ᵥ p i = 0) ∧ gramOf c u = G' ∧
      (LinearIndependent ℝ u → (gramOf c u).rank = Fintype.card κ) := by
  have hG := gramOf_posSemidef (fun j => (hc j).le) u
  have hk : ∀ i, gramOf c u *ᵥ p i = 0 := fun i => gramOf_mulVec_eq_zero c u (hup · i)
  refine ⟨hG, hk, ?_, fun hu => gramOf_rank hc hu⟩
  exact eq_of_posSemidef_of_form_eq 𝒟 p hinj hG hG' hD (fun i => by rw [hk i, dotProduct_zero])
    hform

end GramUnique

end SegrePersistence
