/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Data.Matrix.Composition
public import Mathlib.Data.ENat.Basic
public import Formalizations.LinearAlgebra.Matrix.Rank

/-!
# Monotone invariants and the non-membership criterion

The abstract skeleton of the criterion used to prove that an inverse `H⁻¹` does not have entries
in a localization `U_Σ` (Part 2, Definition 3.3 and Theorem 3.4).

A *monotone invariant* (`MonotoneInvariant`) is a function `μ` from square matrices over a ring `P`
to `ℕ∞` that is unchanged by relabelling, by padding with an identity block and by multiplication
by invertible matrices, and that does not decrease when passing from `F` to a product `G₁ F G₂`.
(In the paper square matrices are indexed by `1, …, n`, so relabelling is invisible there; here
matrices are indexed by arbitrary finite types and invariance under `reindex` is part of the
definition.) Stable association (`StablyAssociated`, Cohn §0.5) is association after padding with
identity blocks.

## What is a hypothesis

The ring-theoretic input of Theorem 3.4 is **not** formalized here:

* the matrix localization lemma (Part 2, Lemma 3.1), which rests on the theory of firs and
  semifirs (Cohn 2006, §3.2, Thm 3.2.3, Prop. 7.5.9; Schofield 2007, Thm 5.6);
* the existence of a complete factorization `Q = G₁ 𝒜 G₂` with an atom `𝒜` stably associated with
  the given atomic factor, and the transitivity of stable association (Cohn 2006, Cor. 0.5.5).

`not_inverseInU` takes their combined conclusion as the named hypothesis `hloc`: if `H⁻¹` has
entries in `U_Σ` (an opaque proposition `inverseInU`), then some `Q ∈ Σ` factors as `G₁ 𝒜 G₂` with
`𝒜` stably associated with the atomic factor `G` of `H`. Neither atoms nor `U_Σ` appear otherwise:
the argument only uses the two conditions of Definition 3.3.

## Main results

* `MonotoneInvariant.eq_of_stablyAssoc`: a monotone invariant is constant on stable
  association classes.
* `MonotoneInvariant.le_of_factor`: if `Q = G₁ 𝒜 G₂` with `𝒜` stably associated with `G`, then
  `μ G ≤ μ Q`.
* `not_inverseInU` (Theorem 3.4): if every `Q ∈ Σ` has a monotone invariant `μ_Q` with
  `μ_Q Q < μ_Q G`, then `H⁻¹` does not have entries in `U_Σ` (given `hloc`).
* `corankInvariant` (Example (b)): for a ring homomorphism `Θ : P →+* Matrix (Fin m) (Fin m) K`
  into matrices over a field, the corank of the evaluated matrix `F^Θ` is a monotone invariant.
  The monotonicity is Mathlib's `Matrix.rank_mul_le_left` / `Matrix.rank_mul_le_right`; invariance
  under invertible factors is `Matrix.rank_mul_eq_left_of_isUnit_det` /
  `Matrix.rank_mul_eq_right_of_isUnit_det`; padding uses the block bounds of
  `Formalizations.LinearAlgebra.Matrix.Rank`. Here `K` is commutative (Mathlib's `Matrix.rank`
  needs a commutative ring); the paper allows a skew field.

## References

* P. M. Cohn, *Free ideal rings and localization in general rings*, Cambridge Univ. Press, 2006,
  §0.5 (stable association), Cor. 0.5.5, §3.2.
* A. H. Schofield, *Representations of rings over skew fields*, and the 2007 preprint cited in the
  paper, Thm 5.6.
-/

@[expose] public section

namespace ThreeAxes.Criterion

open Matrix

variable {P : Type*} [Ring P]

/-- `F` and `G` are *stably associated*: `F ⊕ I_p` and `G ⊕ I_q` are associated (after a
relabelling `e` of the index sets), i.e. `F ⊕ I_p = M (G ⊕ I_q) N` with `M, N` invertible. -/
def StablyAssociated {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (F : Matrix ι ι P) (G : Matrix ι' ι' P) : Prop :=
  ∃ (p q : ℕ) (e : ι' ⊕ Fin q ≃ ι ⊕ Fin p) (M N : Matrix (ι ⊕ Fin p) (ι ⊕ Fin p) P),
    IsUnit M ∧ IsUnit N ∧
      fromBlocks F 0 0 (1 : Matrix (Fin p) (Fin p) P) =
        M * reindex e e (fromBlocks G 0 0 (1 : Matrix (Fin q) (Fin q) P)) * N

variable (P) in
/-- A *monotone invariant* (Definition 3.3): a function from square matrices over `P` to `ℕ∞`,
invariant under relabelling, padding with identity blocks and multiplication by invertible
matrices (condition 1), and satisfying `μ F ≤ μ (G₁ F G₂)` (condition 2). -/
structure MonotoneInvariant where
  /-- The invariant. -/
  μ : ∀ {ι : Type} [Fintype ι] [DecidableEq ι], Matrix ι ι P → ℕ∞
  /-- Relabelling the index set does not change `μ`. -/
  reindex_eq : ∀ {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (e : ι ≃ ι') (F : Matrix ι ι P), μ (reindex e e F) = μ F
  /-- Condition 1: padding with an identity block. -/
  pad_eq : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (p : ℕ) (F : Matrix ι ι P),
    μ (fromBlocks F 0 0 (1 : Matrix (Fin p) (Fin p) P)) = μ F
  /-- Condition 1: invertible factors. -/
  mul_eq : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (M F N : Matrix ι ι P),
    IsUnit M → IsUnit N → μ (M * F * N) = μ F
  /-- Condition 2: `μ F ≤ μ (G₁ F G₂)`. -/
  le_mul : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (G₁ F G₂ : Matrix ι ι P),
    μ F ≤ μ (G₁ * F * G₂)

namespace MonotoneInvariant

variable (I : MonotoneInvariant P)

/-- A monotone invariant is constant on stable association classes. -/
theorem eq_of_stablyAssoc {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] {F : Matrix ι ι P} {G : Matrix ι' ι' P} (h : StablyAssociated F G) :
    I.μ F = I.μ G := by
  obtain ⟨p, q, e, M, N, hM, hN, hFG⟩ := h
  rw [← I.pad_eq p F, hFG, I.mul_eq _ _ _ hM hN, I.reindex_eq, I.pad_eq]

/-- If `Q = G₁ 𝒜 G₂` and `𝒜` is stably associated with `G`, then `μ G ≤ μ Q`. -/
theorem le_of_factor {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    {Q A G₁ G₂ : Matrix ι ι P} {G : Matrix ι' ι' P} (hQ : Q = G₁ * A * G₂)
    (hA : StablyAssociated A G) : I.μ G ≤ I.μ Q := by
  rw [← I.eq_of_stablyAssoc hA, hQ]
  exact I.le_mul G₁ A G₂

end MonotoneInvariant

/-- **Theorem 3.4 (skeleton).** Let `Q : J → (square matrices)` be the family `Σ` and `G` an atomic
factor of `H`. The proposition `inverseInU` stands for "`H⁻¹` has entries in `U_Σ`". The
hypothesis `hloc` is the combined content of the matrix localization lemma (Lemma 3.1), of the
complete factorization of `Q` and of Cohn's Cor. 0.5.5 (not formalized; see the module docstring).
If every `Q j` has a monotone invariant `μ_Q` with `μ_Q (Q j) < μ_Q G`, then `¬ inverseInU`. -/
theorem not_inverseInU {ι : Type} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι P) {J : Type*}
    (Q : J → Σ n : ℕ, Matrix (Fin n) (Fin n) P) (inverseInU : Prop)
    (hloc : inverseInU → ∃ j, ∃ A G₁ G₂ : Matrix (Fin (Q j).1) (Fin (Q j).1) P,
      (Q j).2 = G₁ * A * G₂ ∧ StablyAssociated A G)
    (hμ : ∀ j, ∃ I : MonotoneInvariant P, I.μ (Q j).2 < I.μ G) : ¬ inverseInU := by
  intro hU
  obtain ⟨j, A, G₁, G₂, hQ, hA⟩ := hloc hU
  obtain ⟨I, hI⟩ := hμ j
  exact (I.le_of_factor hQ hA).not_gt hI

/-! ### Example (b): the corank at a representation -/

section Corank

variable {K : Type*} [Field K] {m : ℕ} (Θ : P →+* Matrix (Fin m) (Fin m) K)

/-- The evaluation `F ↦ F^Θ`, an `ι × Fin m` square matrix over `K`. -/
def evalHom (ι : Type) [Fintype ι] [DecidableEq ι] :
    Matrix ι ι P →+* Matrix (ι × Fin m) (ι × Fin m) K :=
  (compRingEquiv ι (Fin m) K).toRingHom.comp Θ.mapMatrix

theorem evalHom_apply {ι : Type} [Fintype ι] [DecidableEq ι] (F : Matrix ι ι P)
    (i j : ι) (a b : Fin m) : evalHom Θ ι F (i, a) (j, b) = Θ (F i j) a b := rfl

/-- `corank F^Θ = #rows − rank F^Θ`. -/
noncomputable def corankAt {ι : Type} [Fintype ι] [DecidableEq ι] (F : Matrix ι ι P) : ℕ :=
  Fintype.card (ι × Fin m) - (evalHom Θ ι F).rank

theorem evalHom_reindex {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (e : ι ≃ ι') (F : Matrix ι ι P) :
    evalHom Θ ι' (reindex e e F) =
      reindex (e.prodCongr (Equiv.refl _)) (e.prodCongr (Equiv.refl _)) (evalHom Θ ι F) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  rfl

theorem evalHom_fromBlocks {ι : Type} [Fintype ι] [DecidableEq ι] (p : ℕ) (F : Matrix ι ι P) :
    evalHom Θ (ι ⊕ Fin p) (fromBlocks F 0 0 (1 : Matrix (Fin p) (Fin p) P)) =
      reindex (Equiv.sumProdDistrib _ _ _).symm (Equiv.sumProdDistrib _ _ _).symm
        (fromBlocks (evalHom Θ ι F) 0 0 1) := by
  ext ⟨i | i, a⟩ ⟨j | j, b⟩
  · rfl
  · simp [evalHom_apply]
  · simp [evalHom_apply]
  · by_cases hij : i = j
    · subst hij
      simp [evalHom_apply, one_apply]
    · simp [evalHom_apply, one_apply, hij]

theorem rank_fromBlocks_one {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι K) : (fromBlocks A 0 0 (1 : Matrix κ κ K)).rank = A.rank + Fintype.card κ := by
  apply le_antisymm
  · exact rank_fromBlocks_zero₂₁_le_left A 0 1
  · simpa [rank_one] using rank_add_rank_le_rank_fromBlocks_zero₂₁ A 0 (1 : Matrix κ κ K)

/-- **Example (b).** The corank at a representation `Θ : P → M_m(K)` is a monotone invariant. -/
noncomputable def corankInvariant : MonotoneInvariant P where
  μ F := (corankAt Θ F : ℕ∞)
  reindex_eq e F := by
    simp only [corankAt, evalHom_reindex, rank_reindex]
    congr 2
    exact Fintype.card_congr (e.prodCongr (Equiv.refl _)).symm
  pad_eq p F := by
    simp only [corankAt, evalHom_fromBlocks, rank_reindex, rank_fromBlocks_one]
    congr 1
    simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, add_mul]
    omega
  mul_eq M F N hM hN := by
    simp only [corankAt, map_mul]
    have hM' := (Matrix.isUnit_iff_isUnit_det _).1 (hM.map (evalHom Θ _))
    have hN' := (Matrix.isUnit_iff_isUnit_det _).1 (hN.map (evalHom Θ _))
    rw [rank_mul_eq_left_of_isUnit_det _ _ hN', rank_mul_eq_right_of_isUnit_det _ _ hM']
  le_mul G₁ F G₂ := by
    simp only [corankAt, map_mul]
    have h := (rank_mul_le_left (evalHom Θ _ G₁ * evalHom Θ _ F) (evalHom Θ _ G₂)).trans
      (rank_mul_le_right (evalHom Θ _ G₁) (evalHom Θ _ F))
    exact_mod_cast Nat.sub_le_sub_left h _

theorem corankInvariant_μ {ι : Type} [Fintype ι] [DecidableEq ι] (F : Matrix ι ι P) :
    (corankInvariant Θ).μ F = (corankAt Θ F : ℕ∞) := rfl

end Corank

end ThreeAxes.Criterion
