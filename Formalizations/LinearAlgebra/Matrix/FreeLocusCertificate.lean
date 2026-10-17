/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.LinearAlgebra.Matrix.FreeLocus
public import Formalizations.LinearAlgebra.Matrix.Rank
public import Formalizations.LinearAlgebra.Matrix.Rank.Kronecker
public import Mathlib.Algebra.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Nilpotent.Basic

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

The general rank facts (subadditivity, rank–nullity, block-triangular and Kronecker bounds)
are imported from `Formalizations.LinearAlgebra.Matrix.Rank` and
`Formalizations.LinearAlgebra.Matrix.Rank.Kronecker`; this file restates the two it lists
under `Main results` in terms of `corank`.
-/

@[expose] public section

namespace FreeLocusCertificate

open Matrix Module
open scoped Kronecker

variable {K : Type*} [Field K]

/-- Corank of a square matrix: `card ι - rank`. -/
noncomputable def corank {ι : Type*} [Fintype ι] (A : Matrix ι ι K) : ℕ :=
  Fintype.card ι - A.rank

section Basic
variable {n : Type*} [Fintype n]

theorem corank_eq_finrank_ker (A : Matrix n n K) :
    corank A = finrank K (LinearMap.ker A.mulVecLin) := by
  have := rank_add_finrank_ker_mulVecLin A
  unfold corank; omega

theorem corank_of_isUnit [DecidableEq n] (A : Matrix n n K) (h : IsUnit A) : corank A = 0 := by
  unfold corank; rw [rank_of_isUnit A h]; simp

end Basic

section Blocks
variable {n m : Type*} [Fintype n] [Fintype m]

/-- (1) `rank A + rank D ≤ rank (fromBlocks A B 0 D)`; this is
`Matrix.rank_add_rank_le_rank_fromBlocks_zero₂₁`. -/
theorem rank_add_rank_le_fromBlocks (A : Matrix n n K) (B : Matrix n m K) (D : Matrix m m K) :
    A.rank + D.rank ≤ (fromBlocks A B 0 D).rank :=
  rank_add_rank_le_rank_fromBlocks_zero₂₁ A B D

/-- (1) `corank (fromBlocks A B 0 D) ≤ corank A + corank D`. -/
theorem corank_fromBlocks_le (A : Matrix n n K) (B : Matrix n m K) (D : Matrix m m K) :
    corank (fromBlocks A B 0 D) ≤ corank A + corank D := by
  rw [corank_eq_finrank_ker, corank_eq_finrank_ker, corank_eq_finrank_ker]
  exact finrank_ker_mulVecLin_fromBlocks_zero₂₁_le A B D

end Blocks

section Kron
variable {n : Type*} [Fintype n] {m : ℕ}

/-- (2) `rank (A ⊗ₖ I_m) = m * rank A`; this is `Matrix.rank_kronecker_one` with `p = Fin m`. -/
theorem rank_kronecker_one (A : Matrix n n K) :
    (A ⊗ₖ (1 : Matrix (Fin m) (Fin m) K)).rank = m * A.rank := by
  rw [Matrix.rank_kronecker_one, Fintype.card_fin]

/-- (2) `corank (A ⊗ₖ I_m) = m * corank A`. -/
theorem corank_kronecker_one (A : Matrix n n K) :
    corank (A ⊗ₖ (1 : Matrix (Fin m) (Fin m) K)) = m * corank A := by
  unfold corank
  rw [rank_kronecker_one, Fintype.card_prod, Fintype.card_fin, Nat.mul_sub, Nat.mul_comm]

end Kron

section Flip
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-- (3) Invertible minus a matrix of rank ≤ k has corank ≤ k; this is
`FreeLocus.corank_unit_sub_le`. -/
theorem corank_unit_sub_le (U E : Matrix ι ι K) (hU : IsUnit U) (k : ℕ) (hE : E.rank ≤ k) :
    corank (U - E) ≤ k :=
  FreeLocus.corank_unit_sub_le U E hU k hE

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
