/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.ZMod.Defs
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Tactic.FinCases

/-!
# The linear algebra behind the atoms of the size chain

Linear-algebra core of the atom criterion for the `4d × 4d` pencil `𝐋` of the size chain
(Lemma 6.2(c)). The pencil is an atom when the coefficient matrices `𝖢, 𝖣` generate the
full matrix algebra and `𝖣` and `𝖤 = 𝖣 − 1 − 𝖢²` are invertible. This file proves these three
facts for the two families used in the paper:

* `𝖣_d = diag(3, 4, …, d + 2)` and the cyclic permutation matrix `𝖢_d`
  (`(𝖢_d)_{i, i+1} = 1`, indices mod `d`), for every `d ≥ 1`, over any field of characteristic `0`;
* `𝖣 = diag(λ, λ + 1)` and the swap `𝖢 = 𝖢_2` (the matrices of `F^{(λ)}`), over any field.

That a diagonal matrix with distinct eigenvalues and the cyclic permutation matrix generate the
full matrix algebra is a classical fact (Lagrange interpolation gives the diagonal matrix units,
and the cycle moves them around); it is proved here only because we did not find it in Mathlib.
The invertibility of `𝖤_d` uses Mathlib's Gershgorin theorem (`det_ne_zero_of_sum_row_lt_diag`):
`𝖤_d` is strictly diagonally dominant over `ℚ`, and the statement is transferred to any field of
characteristic `0` through `Rat.castHom`.

The step "these conditions imply that the pencil is an atom" is Cohn's Theorem 5.8.8 (in the form
of Helton–Klep–Volčič, Remark 2.6); it is not formalized here.

## Main results

* `ThreeAxes.SizeChain.adjoin_cyc_diagonal_eq_top`: if `v` is injective, then
  `Algebra.adjoin K {cyc K d, diagonal v} = ⊤`.
* `adjoin_cyc_diagD_eq_top`: `𝖢_d` and `𝖣_d` generate `M_d(K)` (characteristic `0`).
* `det_diagD_ne_zero`, `det_matE_ne_zero`: `𝖣_d` and `𝖤_d = 𝖣_d − 1 − 𝖢_d²` are invertible
  (characteristic `0`).
* `adjoin_swap_diagLam_eq_top`: `𝖢_2` and `diag(λ, λ + 1)` generate `M_2(K)`.
* `det_diagLam_ne_zero_and_iff`: `diag(λ, λ+1)` and `diag(λ, λ+1) − 1 − 𝖢_2²` are both invertible
  iff `λ ∉ {−1, 0, 1, 2}`.

## References

* P. M. Cohn, *Free ideal rings and localization in general rings*, Cambridge Univ. Press, 2006,
  Theorem 5.8.8.
* J. W. Helton, I. Klep, J. Volčič, *Factorization of noncommutative polynomials and Nullstellensätze
  for the free algebra*, IMRN 2022, Remark 2.6.
-/

@[expose] public section

namespace ThreeAxes.SizeChain

open Matrix

/-- The cyclic permutation matrix `𝖢_d`: `(𝖢_d)_{i, i+1} = 1`, indices mod `d`. -/
def cyc (K : Type*) [Zero K] [One K] (d : ℕ) [NeZero d] : Matrix (Fin d) (Fin d) K :=
  of fun i j => if j = i + 1 then 1 else 0

/-- `𝖣_d = diag(3, 4, …, d + 2)`. -/
def diagD (K : Type*) [CommRing K] (d : ℕ) : Matrix (Fin d) (Fin d) K :=
  diagonal fun i => ((i : ℕ) : K) + 3

/-- `𝖤_d = 𝖣_d − 1 − 𝖢_d²`. -/
def matE (K : Type*) [CommRing K] (d : ℕ) [NeZero d] : Matrix (Fin d) (Fin d) K :=
  diagD K d - 1 - cyc K d * cyc K d

section Generation

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- A diagonal matrix with distinct eigenvalues generates every diagonal matrix unit
(Lagrange interpolation). -/
theorem single_mem_adjoin_diagonal {v : n → K} (hv : Function.Injective v) (i : n) :
    single i i (1 : K) ∈ Algebra.adjoin K {diagonal v} := by
  set S := Algebra.adjoin K {diagonal v}
  set c : K := ∏ j ∈ Finset.univ.erase i, (v i - v j)
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun j hj =>
    sub_ne_zero.2 fun h => (Finset.ne_of_mem_erase hj) (hv h).symm
  have hfac : ∀ j, diagonal v - algebraMap K (Matrix n n K) (v j) ∈ S := fun j =>
    S.sub_mem (Algebra.subset_adjoin rfl) (S.algebraMap_mem _)
  have h1 : ∀ j, diagonal v - algebraMap K (Matrix n n K) (v j) =
      diagonal fun k => v k - v j := by
    intro j
    ext a b
    by_cases hab : a = b <;> simp [algebraMap_eq_diagonal, hab]
  have key : ∀ s : Finset n, (diagonal fun k => ∏ j ∈ s, (v k - v j)) ∈ S := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [S.one_mem]
    | insert a s ha ih =>
      have e : (diagonal fun k => ∏ j ∈ insert a s, (v k - v j)) =
          (diagonal v - algebraMap K (Matrix n n K) (v a)) *
            diagonal fun k => ∏ j ∈ s, (v k - v j) := by
        rw [h1 a, diagonal_mul_diagonal]
        congr 1
        ext k
        rw [Finset.prod_insert ha]
      rw [e]
      exact S.mul_mem (hfac a) ih
  have hmem := key (Finset.univ.erase i)
  have heq : single i i (1 : K) = c⁻¹ • diagonal fun k => ∏ j ∈ Finset.univ.erase i, (v k - v j) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      by_cases hai : i = a
      · subst hai
        simp [c, hc]
      · have hz : ∏ j ∈ Finset.univ.erase i, (v a - v j) = 0 :=
          Finset.prod_eq_zero (Finset.mem_erase.2 ⟨Ne.symm hai, Finset.mem_univ a⟩) (sub_self _)
        simp [single, hai, hz]
    · have h0 : single i i (1 : K) a b = 0 := by
        simp only [single, of_apply]
        split_ifs with h
        · exact absurd (h.1.symm.trans h.2) hab
        · rfl
      rw [h0, Matrix.smul_apply, diagonal_apply_ne _ hab, smul_zero]
  rw [heq]
  exact S.smul_mem hmem _

variable {d : ℕ} [NeZero d]

open Fin.NatCast in
/-- A diagonal matrix with distinct eigenvalues and the cyclic permutation matrix generate the
full matrix algebra. Classical; see the module docstring. -/
theorem adjoin_cyc_diagonal_eq_top {v : Fin d → K} (hv : Function.Injective v) :
    Algebra.adjoin K {cyc K d, diagonal v} = ⊤ := by
  set S := Algebra.adjoin K {cyc K d, diagonal v}
  have hD : ∀ i, single i i (1 : K) ∈ S := fun i =>
    Algebra.adjoin_mono (Set.subset_insert _ _) (single_mem_adjoin_diagonal hv i)
  have hC : cyc K d ∈ S := Algebra.subset_adjoin (Set.mem_insert _ _)
  have hstep : ∀ i : Fin d, single i (i + 1) (1 : K) ∈ S := by
    intro i
    have h := S.mul_mem (S.mul_mem (hD i) hC) (hD (i + 1))
    simpa [cyc] using h
  have hpow : ∀ (m : ℕ) (i : Fin d), single i (i + (m : Fin d)) (1 : K) ∈ S := by
    intro m
    induction m with
    | zero => intro i; simpa using hD i
    | succ m ih =>
      intro i
      have h := S.mul_mem (ih i) (hstep (i + (m : Fin d)))
      rwa [single_mul_single_same, one_mul, add_assoc, ← Nat.cast_succ] at h
  have hall : ∀ i j : Fin d, single i j (1 : K) ∈ S := by
    intro i j
    have h := hpow (j - i).val i
    rwa [Fin.cast_val_eq_self, add_sub_cancel] at h
  rw [eq_top_iff]
  intro M _
  rw [matrix_eq_sum_single M]
  refine S.sum_mem fun i _ => S.sum_mem fun j _ => ?_
  have h := S.smul_mem (hall i j) (M i j)
  rwa [smul_single, smul_eq_mul, mul_one] at h

end Generation

/-! ### The family `𝖣_d = diag(3, …, d + 2)`, `𝖢_d` -/

section Family

variable (K : Type*) [Field K] [CharZero K] (d : ℕ) [NeZero d]

omit [NeZero d] in
theorem diagD_injective : Function.Injective fun i : Fin d => ((i : ℕ) : K) + 3 := by
  intro i j h
  exact Fin.ext (Nat.cast_injective (add_right_cancel h))

/-- `𝖢_d` and `𝖣_d` generate `M_d(K)`. -/
theorem adjoin_cyc_diagD_eq_top : Algebra.adjoin K {cyc K d, diagD K d} = ⊤ :=
  adjoin_cyc_diagonal_eq_top (diagD_injective K d)

omit [NeZero d] in
/-- `𝖣_d` is invertible. -/
theorem det_diagD_ne_zero : (diagD K d).det ≠ 0 := by
  rw [diagD, det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun i _ => by exact_mod_cast Nat.succ_ne_zero (i + 2)

theorem cyc_mul_cyc_apply {R : Type*} [CommRing R] (i j : Fin d) :
    (cyc R d * cyc R d) i j = if j = i + 1 + 1 then 1 else 0 := by
  rw [mul_apply, Finset.sum_eq_single (i + 1)]
  · simp [cyc]
  · intro b _ hb
    simp [cyc, hb]
  · simp

/-- Strict diagonal dominance of `𝖤_d` over `ℝ`: Mathlib's Gershgorin theorem
`det_ne_zero_of_sum_row_lt_diag`. -/
theorem det_matE_real_ne_zero : (matE ℝ d).det ≠ 0 := by
  refine det_ne_zero_of_sum_row_lt_diag (A := matE ℝ d) fun k => ?_
  have hoff : ∀ j ∈ Finset.univ.erase k, ‖matE ℝ d k j‖ = if k + 1 + 1 = j then 1 else 0 := by
    intro j hj
    have hkj : k ≠ j := (Finset.ne_of_mem_erase hj).symm
    simp only [matE, diagD, Matrix.sub_apply, cyc_mul_cyc_apply, diagonal_apply_ne _ hkj,
      one_apply_ne hkj, zero_sub]
    by_cases h : j = k + 1 + 1
    · simp [h]
    · simp [h, Ne.symm h]
  rw [Finset.sum_congr rfl hoff, Finset.sum_ite_eq]
  simp only [matE, diagD, Matrix.sub_apply, cyc_mul_cyc_apply, diagonal_apply_eq, one_apply_eq,
    Real.norm_eq_abs]
  have h0 : (0 : ℝ) ≤ (k : ℕ) := by positivity
  by_cases h : k = k + 1 + 1
  · have hk : k + 1 + 1 ∉ Finset.univ.erase k := by simp [← h]
    rw [ite_eq_right_of_eq_false _ _ (eq_false hk), ite_eq_left_of_eq_true _ _ (eq_true h),
      abs_of_pos (by linarith)]
    linarith
  · have hk : k + 1 + 1 ∈ Finset.univ.erase k := by simp [Ne.symm h]
    rw [ite_eq_left_of_eq_true _ _ (eq_true hk), ite_eq_right_of_eq_false _ _ (eq_false h),
      abs_of_pos (by linarith)]
    linarith

theorem mapMatrix_matE : (Rat.castHom K).mapMatrix (matE ℚ d) = matE K d := by
  have hc : (Rat.castHom K).mapMatrix (cyc ℚ d) = cyc K d := by
    ext i j
    by_cases h : j = i + 1 <;> simp [cyc, h]
  have hd : (Rat.castHom K).mapMatrix (diagD ℚ d) = diagD K d := by
    ext i j
    by_cases hij : i = j <;> simp [diagD, hij]
  simp only [matE, map_sub, map_mul, map_one, hc, hd]

theorem det_matE_rat_ne_zero : (matE ℚ d).det ≠ 0 := by
  intro h
  apply det_matE_real_ne_zero d
  rw [← mapMatrix_matE ℝ d, ← RingHom.map_det, h, map_zero]

/-- `𝖤_d = 𝖣_d − 1 − 𝖢_d²` is invertible over every field of characteristic `0`. -/
theorem det_matE_ne_zero : (matE K d).det ≠ 0 := by
  rw [← mapMatrix_matE, ← RingHom.map_det]
  exact (map_ne_zero (Rat.castHom K)).2 (det_matE_rat_ne_zero d)

end Family

/-! ### The matrices of `F^{(λ)}` -/

section Lambda

variable {K : Type*} [Field K]

/-- For `d = 2`, `𝖢_2` is the swap. -/
theorem cyc_two : cyc K 2 = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyc]

theorem cyc_two_mul_self : cyc K 2 * cyc K 2 = 1 := by
  rw [cyc_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]

/-- `𝖢_2` (the swap) and `diag(λ, λ + 1)` generate `M_2(K)`, for every `λ`. -/
theorem adjoin_swap_diagLam_eq_top (l : K) :
    Algebra.adjoin K {cyc K 2, diagonal ![l, l + 1]} = ⊤ := by
  refine adjoin_cyc_diagonal_eq_top ?_
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

/-- `diag(λ, λ + 1)` and `𝖤 = diag(λ, λ + 1) − 1 − 𝖢_2² = diag(λ, λ + 1) − 2` are both invertible
iff `λ ∉ {−1, 0, 1, 2}`. -/
theorem det_diagLam_ne_zero_and_iff (l : K) :
    (diagonal ![l, l + 1]).det ≠ 0 ∧
        (diagonal ![l, l + 1] - 1 - cyc K 2 * cyc K 2).det ≠ 0 ↔
      l ≠ -1 ∧ l ≠ 0 ∧ l ≠ 1 ∧ l ≠ 2 := by
  have hE : diagonal ![l, l + 1] - 1 - cyc K 2 * cyc K 2 = diagonal ![l - 2, l - 1] := by
    rw [cyc_two_mul_self]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [one_apply]
    ring
  rw [hE, det_diagonal, det_diagonal, Fin.prod_univ_two, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_ne_zero_iff, sub_ne_zero, ne_eq,
    add_eq_zero_iff_eq_neg]
  tauto

end Lambda

end ThreeAxes.SizeChain
