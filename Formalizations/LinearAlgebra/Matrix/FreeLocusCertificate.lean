/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Soundness of the free-locus certificate

One direction of the free-locus test: a flip-poly pencil has corank `≤ m` at every point of
size `m`, so corank `> m` at some point of size `m` certifies "not flip-poly".
Over a field `K`, `corank A = card ι - rank A` for a square matrix `A : Matrix ι ι K`.

## Main results

* `rank_add_rank_le_fromBlocks`: `rank A + rank D ≤ rank (fromBlocks A B 0 D)`;
  `corank_fromBlocks_le`: `corank (fromBlocks A B 0 D) ≤ corank A + corank D`.
* `rank_kronecker_one`: `rank (A ⊗ₖ 1_m) = m * rank A`; `corank_kronecker_one`.
* `corank_unit_sub_mul_le`: `corank (U - P * Q) ≤ m` for `U` invertible and `P` of width `m`;
  `corank_one_sub_nil_sub_mul_le`: the same with `U = 1 - N`, `N` nilpotent.
* `TriBounded`, `Cert`: block upper-triangular matrices with one free diagonal block `B` and `k`
  further diagonal blocks of corank `≤ m`; `cert_corank`: `corank M - k * m ≤ corank B`.

The file is self-contained: the statements it needs from `FreeLocus` are re-proved here.
-/

namespace FreeLocusCertificate

open Matrix Module
open scoped Kronecker

variable {K : Type*} [Field K]

/-- Corank of a square matrix: `card ι - rank`. -/
noncomputable def corank {ι : Type*} [Fintype ι] (A : Matrix ι ι K) : ℕ :=
  Fintype.card ι - A.rank

section Basic
variable {n m : Type*} [Fintype n] [Fintype m]

omit [Fintype m] in
/-- Subadditivity of matrix rank (as in FreeLocusLinAlg). -/
theorem rank_add_le (A B : Matrix m n K) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

omit [Fintype m] in
/-- Rank–nullity for a matrix. -/
theorem rank_add_finrank_ker (A : Matrix m n K) :
    A.rank + finrank K (LinearMap.ker A.mulVecLin) = Fintype.card n := by
  unfold Matrix.rank
  rw [LinearMap.finrank_range_add_finrank_ker, Module.finrank_fintype_fun_eq_card]

theorem corank_eq_finrank_ker (A : Matrix n n K) :
    corank A = finrank K (LinearMap.ker A.mulVecLin) := by
  have := rank_add_finrank_ker A
  unfold corank; omega

theorem corank_of_isUnit [DecidableEq n] (A : Matrix n n K) (h : IsUnit A) : corank A = 0 := by
  unfold corank; rw [rank_of_isUnit A h]; simp

end Basic

section Blocks
variable {n m : Type*} [Fintype n] [Fintype m]

/-- Kernel of a block upper-triangular matrix: `dim ker M ≤ dim ker A + dim ker D`. -/
theorem finrank_ker_fromBlocks_le (A : Matrix n n K) (B : Matrix n m K) (D : Matrix m m K) :
    finrank K (LinearMap.ker (fromBlocks A B 0 D).mulVecLin) ≤
      finrank K (LinearMap.ker A.mulVecLin) + finrank K (LinearMap.ker D.mulVecLin) := by
  set KM := LinearMap.ker (fromBlocks A B 0 D).mulVecLin with hKM
  have hmem : ∀ v : KM, A *ᵥ ((v : n ⊕ m → K) ∘ Sum.inl) + B *ᵥ ((v : n ⊕ m → K) ∘ Sum.inr) = 0
      ∧ D *ᵥ ((v : n ⊕ m → K) ∘ Sum.inr) = 0 := by
    intro v
    have hv : (fromBlocks A B 0 D) *ᵥ (v : n ⊕ m → K) = 0 := v.2
    rw [fromBlocks_mulVec] at hv
    refine ⟨funext fun i => ?_, funext fun i => ?_⟩
    · simpa using congrFun hv (Sum.inl i)
    · simpa using congrFun hv (Sum.inr i)
  let f : KM →ₗ[K] (m → K) := (LinearMap.funLeft K K Sum.inr).comp KM.subtype
  have hf : ∀ v : KM, f v = (v : n ⊕ m → K) ∘ Sum.inr := fun v => rfl
  have hfr : LinearMap.range f ≤ LinearMap.ker D.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hf]
    exact (hmem v).2
  let g : (LinearMap.ker f) →ₗ[K] (n → K) :=
    (LinearMap.funLeft K K Sum.inl).comp (KM.subtype.comp (LinearMap.ker f).subtype)
  have hg : ∀ u : LinearMap.ker f, g u = ((u : KM) : n ⊕ m → K) ∘ Sum.inl := fun u => rfl
  have hinr : ∀ u : LinearMap.ker f, ((u : KM) : n ⊕ m → K) ∘ Sum.inr = 0 := by
    intro u; rw [← hf]; exact u.2
  have hginj : Function.Injective g := by
    intro u u' hu
    rw [hg, hg] at hu
    apply Subtype.ext; apply Subtype.ext
    funext s
    rcases s with i | i
    · exact congrFun hu i
    · exact (congrFun (hinr u) i).trans (congrFun (hinr u') i).symm
  have hgr : LinearMap.range g ≤ LinearMap.ker A.mulVecLin := by
    rintro _ ⟨u, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hg]
    have h := (hmem (u : KM)).1
    rw [hinr u, Matrix.mulVec_zero, add_zero] at h
    exact h
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : finrank K (LinearMap.range f) ≤ finrank K (LinearMap.ker D.mulVecLin) :=
    Submodule.finrank_mono hfr
  have h3 : finrank K (LinearMap.ker f) ≤ finrank K (LinearMap.ker A.mulVecLin) := by
    rw [← LinearMap.finrank_range_of_inj hginj]; exact Submodule.finrank_mono hgr
  omega

/-- (1) `rank A + rank D ≤ rank (fromBlocks A B 0 D)`. -/
theorem rank_add_rank_le_fromBlocks (A : Matrix n n K) (B : Matrix n m K) (D : Matrix m m K) :
    A.rank + D.rank ≤ (fromBlocks A B 0 D).rank := by
  have h := finrank_ker_fromBlocks_le A B D
  have hA := rank_add_finrank_ker A
  have hD := rank_add_finrank_ker D
  have hM := rank_add_finrank_ker (fromBlocks A B 0 D)
  rw [Fintype.card_sum] at hM
  omega

/-- (1) `corank (fromBlocks A B 0 D) ≤ corank A + corank D`. -/
theorem corank_fromBlocks_le (A : Matrix n n K) (B : Matrix n m K) (D : Matrix m m K) :
    corank (fromBlocks A B 0 D) ≤ corank A + corank D := by
  rw [corank_eq_finrank_ker, corank_eq_finrank_ker, corank_eq_finrank_ker]
  exact finrank_ker_fromBlocks_le A B D

end Blocks

section Kron
variable {n : Type*} [Fintype n] {m : ℕ}

theorem kron_one_mulVec (A : Matrix n n K) (v : n × Fin m → K) (i : n) (k : Fin m) :
    ((A ⊗ₖ (1 : Matrix (Fin m) (Fin m) K)) *ᵥ v) (i, k) = (A *ᵥ fun j => v (j, k)) i := by
  simp [mulVec, dotProduct, kroneckerMap_apply, one_apply, Fintype.sum_prod_type]

/-- `ker (A ⊗ I_m) ≃ (Fin m → ker A)`. -/
noncomputable def kerKronEquiv (A : Matrix n n K) :
    LinearMap.ker (A ⊗ₖ (1 : Matrix (Fin m) (Fin m) K)).mulVecLin ≃ₗ[K]
      (Fin m → LinearMap.ker A.mulVecLin) where
  toFun v k := ⟨fun j => (v : n × Fin m → K) (j, k), by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext i
    have hv : (A ⊗ₖ (1 : Matrix (Fin m) (Fin m) K)) *ᵥ (v : n × Fin m → K) = 0 := v.2
    rw [← kron_one_mulVec, hv]; rfl⟩
  invFun w := ⟨fun p => (w p.2 : n → K) p.1, by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext ⟨i, k⟩
    rw [kron_one_mulVec]
    have hw : A *ᵥ (w k : n → K) = 0 := (w k).2
    exact congrFun hw i⟩
  map_add' v w := by funext k; rfl
  map_smul' c v := by funext k; rfl
  left_inv v := by rfl
  right_inv w := by rfl

/-- (2) `rank (A ⊗ₖ I_m) = m * rank A`. -/
theorem rank_kronecker_one (A : Matrix n n K) :
    (A ⊗ₖ (1 : Matrix (Fin m) (Fin m) K)).rank = m * A.rank := by
  have hk := (kerKronEquiv (K := K) (m := m) A).finrank_eq
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hk
  have h1 := rank_add_finrank_ker (A ⊗ₖ (1 : Matrix (Fin m) (Fin m) K))
  have h2 := rank_add_finrank_ker A
  rw [Fintype.card_prod, Fintype.card_fin] at h1
  have h3 : m * (A.rank + finrank K (LinearMap.ker A.mulVecLin)) = m * Fintype.card n := by
    rw [h2]
  rw [Nat.mul_add] at h3
  rw [hk] at h1
  have : Fintype.card n * m = m * Fintype.card n := Nat.mul_comm _ _
  omega

/-- (2) `corank (A ⊗ₖ I_m) = m * corank A`. -/
theorem corank_kronecker_one (A : Matrix n n K) :
    corank (A ⊗ₖ (1 : Matrix (Fin m) (Fin m) K)) = m * corank A := by
  unfold corank
  rw [rank_kronecker_one, Fintype.card_prod, Fintype.card_fin, Nat.mul_sub, Nat.mul_comm]

end Kron

section Flip
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-- (3) Invertible minus a matrix of rank ≤ k has corank ≤ k (as in FreeLocusLinAlg). -/
theorem corank_unit_sub_le (U E : Matrix ι ι K) (hU : IsUnit U) (k : ℕ) (hE : E.rank ≤ k) :
    corank (U - E) ≤ k := by
  unfold corank
  have h1 : U.rank = Fintype.card ι := rank_of_isUnit U hU
  have h2 : U.rank ≤ (U - E).rank + E.rank := by
    simpa using rank_add_le (U - E) E
  omega

/-- (3) Flip-poly bound: `corank (U - P * Q) ≤ m` for `U` invertible, `P` with `m` columns. -/
theorem corank_unit_sub_mul_le (U : Matrix ι ι K) (hU : IsUnit U)
    (P : Matrix ι (Fin m) K) (Q : Matrix (Fin m) ι K) :
    corank (U - P * Q) ≤ m := by
  apply corank_unit_sub_le U (P * Q) hU m
  calc (P * Q).rank ≤ P.rank := rank_mul_le_left P Q
    _ ≤ Fintype.card (Fin m) := rank_le_card_width P
    _ = m := Fintype.card_fin m

/-- (3) Same with `U = 1 - N`, `N` nilpotent. -/
theorem corank_one_sub_nil_sub_mul_le (N : Matrix ι ι K) (hN : IsNilpotent N)
    (P : Matrix ι (Fin m) K) (Q : Matrix (Fin m) ι K) :
    corank ((1 - N) - P * Q) ≤ m :=
  corank_unit_sub_mul_le (1 - N) hN.isUnit_one_sub P Q

end Flip

section Certificate

/-- Block upper-triangular matrices whose `k` diagonal blocks (`k ≥ 1`) all have corank `≤ c`. -/
inductive TriBounded (c : ℕ) : (ι : Type) → [Fintype ι] → [DecidableEq ι] → Matrix ι ι K → ℕ → Prop
  | single {ι : Type} [Fintype ι] [DecidableEq ι] (D : Matrix ι ι K) (h : corank D ≤ c) :
      TriBounded c ι D 1
  | cons {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      (D₁ : Matrix ι ι K) (Y : Matrix ι κ K) (D₂ : Matrix κ κ K) (k : ℕ)
      (h : corank D₁ ≤ c) (hD : TriBounded c κ D₂ k) :
      TriBounded c (ι ⊕ κ) (fromBlocks D₁ Y 0 D₂) (k + 1)

theorem TriBounded.corank_le {c : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {D : Matrix ι ι K} {k : ℕ} (h : TriBounded c ι D k) : corank D ≤ k * c := by
  induction h with
  | single D h => simpa using h
  | cons D₁ Y D₂ k h _ ih =>
    calc corank (fromBlocks D₁ Y 0 D₂) ≤ corank D₁ + corank D₂ := corank_fromBlocks_le _ _ _
      _ ≤ c + k * c := Nat.add_le_add h ih
      _ = (k + 1) * c := by rw [Nat.succ_mul, Nat.add_comm]

/-- Block upper-triangular matrices with one free diagonal block `B` (anywhere on the diagonal)
and `k` further diagonal blocks of corank `≤ c` each. -/
inductive Cert (c : ℕ) {β : Type} [Fintype β] [DecidableEq β] (B : Matrix β β K) :
    (ι : Type) → [Fintype ι] → [DecidableEq ι] → Matrix ι ι K → ℕ → Prop
  | self : Cert c B β B 0
  | here {κ : Type} [Fintype κ] [DecidableEq κ] (Y : Matrix β κ K) (D : Matrix κ κ K) (k : ℕ)
      (hD : TriBounded c κ D k) : Cert c B (β ⊕ κ) (fromBlocks B Y 0 D) k
  | there {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      (D₁ : Matrix ι ι K) (Y : Matrix ι κ K) (M' : Matrix κ κ K) (k : ℕ)
      (h : corank D₁ ≤ c) (hM : Cert c B κ M' k) :
      Cert c B (ι ⊕ κ) (fromBlocks D₁ Y 0 M') (k + 1)

theorem Cert.corank_le {c : ℕ} {β : Type} [Fintype β] [DecidableEq β] {B : Matrix β β K}
    {ι : Type} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι K} {k : ℕ}
    (h : Cert c B ι M k) : corank M ≤ corank B + k * c := by
  induction h with
  | self => simp
  | here Y D k hD =>
    exact (corank_fromBlocks_le _ _ _).trans (Nat.add_le_add_left hD.corank_le _)
  | there D₁ Y M' k h _ ih =>
    calc corank (fromBlocks D₁ Y 0 M') ≤ corank D₁ + corank M' := corank_fromBlocks_le _ _ _
      _ ≤ c + (corank B + k * c) := Nat.add_le_add h ih
      _ = corank B + (k + 1) * c := by rw [Nat.succ_mul]; omega

/-- (4) The certificate: `corank B ≥ corank M - k * m`. -/
theorem cert_corank {c : ℕ} {β : Type} [Fintype β] [DecidableEq β] {B : Matrix β β K}
    {ι : Type} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι K} {k : ℕ}
    (h : Cert c B ι M k) : corank M - k * c ≤ corank B := by
  have := h.corank_le; omega

end Certificate
end FreeLocusCertificate
