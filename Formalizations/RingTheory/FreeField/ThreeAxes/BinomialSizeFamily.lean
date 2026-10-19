/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.LinearAlgebra.Matrix.Invertible
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.RowCol
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Basic

/-!
# The binomial size family `e_d = q_d⁻¹`

Corollary 7.10(a): `q_d = w⁻¹ + Σ_{i<d} yⁱ u⁻¹ y⁻ⁱ` and `e_d = q_d⁻¹`. With
`Δ = diag(w, y u y⁻¹, …, y^{d−1} u y^{−(d−1)})` and `J` the all-ones matrix, `H = Δ + u J` and
`L = H · diag(1, y, …, y^{d−1})`. Over a division ring `D` (no commutativity) unless stated.

## Main results

* `rankOne_mul_inv`, `rankOne_inv_mul` (rank one): for `Δ i ≠ 0`, `u ≠ 0` and
  `q = u⁻¹ + Σ_i (Δ i)⁻¹ ≠ 0`, `H = diagonal Δ + u J` has the two-sided inverse
  `Hinv i j = δ_ij (Δ i)⁻¹ − (Δ i)⁻¹ q⁻¹ (Δ j)⁻¹`. Both are the Woodbury identities
  `Matrix.add_mul_mul_invOf_mul_eq_one` and `Matrix.add_mul_mul_invOf_mul_eq_one'` (over a ring)
  with `A = diagonal Δ`, `U` a column of ones, `C = [u]`, `V` a row of ones, so that
  `⅟C + V ⅟A U = q`.
* `rankOne_isUnit`; `inv_q_eq` : `q⁻¹ = u − u (Σ_{i,j} Hinv i j) u`.
* `conj_add_mul_pow` (conjugation): `(yⁱ u y⁻ⁱ + u) yⁱ = yⁱ u + u yⁱ`, so `L` has entries linear
  in `u`, `w`, `y`.
* `det_scalar_point` (scalar point, commutative ring): `det (diag(0, 1, …, 1) + J) = 1`, via the
  Weinstein–Aronszajn identity `Matrix.det_one_add_mul_comm` with a rank-two factorization.

## Related

`PhiCompression.phi_inv_woodbury` is a scalar reading of the same Woodbury identity;
`ParabolicFamily` has `det (1 + J) = n + 1` via `Matrix.det_one_add_replicateCol_mul_replicateRow`.
-/

@[expose] public section

namespace ThreeAxes.BinomialSizeFamily

open Matrix

/-! ### Rank one: explicit inverse of `diagonal Δ + u J` -/

section RankOne

variable {D : Type*} [DivisionRing D] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `q = u⁻¹ + Σ_i (Δ i)⁻¹`. -/
def qSum (Δ : ι → D) (u : D) : D := u⁻¹ + ∑ i, (Δ i)⁻¹

/-- `H = diagonal Δ + u J`. -/
def rankOne (Δ : ι → D) (u : D) : Matrix ι ι D := diagonal Δ + of fun _ _ => u

/-- The explicit inverse `Hinv i j = δ_ij (Δ i)⁻¹ − (Δ i)⁻¹ q⁻¹ (Δ j)⁻¹`. -/
def rankOneInv (Δ : ι → D) (u : D) : Matrix ι ι D :=
  of fun i j => (if i = j then (Δ i)⁻¹ else 0) - (Δ i)⁻¹ * (qSum Δ u)⁻¹ * (Δ j)⁻¹

/-- `diagonal Δ` with its explicit inverse. -/
private abbrev invA (Δ : ι → D) (hΔ : ∀ i, Δ i ≠ 0) : Invertible (diagonal Δ) where
  invOf := diagonal fun i => (Δ i)⁻¹
  invOf_mul_self := by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext i; simp [hΔ i]
  mul_invOf_self := by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext i; simp [hΔ i]

/-- The `1 × 1` matrix `[u]` with its inverse `[u⁻¹]`. -/
private abbrev invC (u : D) (hu : u ≠ 0) : Invertible (of fun _ _ => u : Matrix Unit Unit D) where
  invOf := of fun _ _ => u⁻¹
  invOf_mul_self := by ext; simp [Matrix.mul_apply, hu]
  mul_invOf_self := by ext; simp [Matrix.mul_apply, hu]

/-- The `1 × 1` matrix `[q]` with its inverse `[q⁻¹]`. -/
private abbrev invS (q : D) (hq : q ≠ 0) : Invertible (of fun _ _ => q : Matrix Unit Unit D) where
  invOf := of fun _ _ => q⁻¹
  invOf_mul_self := by ext; simp [Matrix.mul_apply, hq]
  mul_invOf_self := by ext; simp [Matrix.mul_apply, hq]

/-- The Woodbury data: `diagonal Δ + U [u] V = H`, `⅟[u] + V ⅟(diagonal Δ) U = [q]` and
`⅟A − ⅟A U [q⁻¹] V ⅟A = Hinv`. -/
private theorem woodbury_data (Δ : ι → D) (u : D) (hΔ : ∀ i, Δ i ≠ 0) (hu : u ≠ 0) :
    letI := invA Δ hΔ
    letI := invC u hu
    diagonal Δ + replicateCol Unit (fun _ : ι => (1 : D)) * (of fun _ _ => u) *
        replicateRow Unit (fun _ : ι => (1 : D)) = rankOne Δ u ∧
      ⅟(of fun _ _ => u : Matrix Unit Unit D) + replicateRow Unit (fun _ : ι => (1 : D)) *
        ⅟(diagonal Δ) * replicateCol Unit (fun _ : ι => (1 : D)) = (of fun _ _ => qSum Δ u) ∧
      ⅟(diagonal Δ) - ⅟(diagonal Δ) * replicateCol Unit (fun _ : ι => (1 : D)) *
        (of fun _ _ => (qSum Δ u)⁻¹) * replicateRow Unit (fun _ : ι => (1 : D)) * ⅟(diagonal Δ) =
        rankOneInv Δ u := by
  have hA : (invA Δ hΔ).invOf = diagonal fun i => (Δ i)⁻¹ := rfl
  have hC : (invC u hu).invOf = of fun _ _ => u⁻¹ := rfl
  refine ⟨?_, ?_, ?_⟩
  · ext i j; simp [rankOne, Matrix.mul_apply]
  · ext; simp [hA, hC, qSum, Matrix.mul_apply, diagonal_apply]
  · ext i j
    simp [hA, rankOneInv, Matrix.mul_apply, diagonal_apply, mul_assoc]

/-- `H * Hinv = 1`: Mathlib's `Matrix.add_mul_mul_invOf_mul_eq_one` (Woodbury). -/
theorem rankOne_mul_inv (Δ : ι → D) (u : D) (hΔ : ∀ i, Δ i ≠ 0) (hu : u ≠ 0)
    (hq : qSum Δ u ≠ 0) : rankOne Δ u * rankOneInv Δ u = 1 := by
  let _ := invA Δ hΔ
  let _ := invC u hu
  obtain ⟨hH, hS, hX⟩ := woodbury_data Δ u hΔ hu
  let _ := (invS (qSum Δ u) hq).copy _ hS
  have hSi : ⅟(⅟(of fun _ _ => u : Matrix Unit Unit D) + replicateRow Unit (fun _ : ι => (1 : D)) *
      ⅟(diagonal Δ) * replicateCol Unit (fun _ : ι => (1 : D))) =
      of fun _ _ => (qSum Δ u)⁻¹ := rfl
  have key := Matrix.add_mul_mul_invOf_mul_eq_one (diagonal Δ)
    (replicateCol Unit fun _ : ι => (1 : D)) (of fun _ _ => u) (replicateRow Unit fun _ => 1)
  rwa [hH, hSi, hX] at key

/-- `Hinv * H = 1`: Mathlib's `Matrix.add_mul_mul_invOf_mul_eq_one'` (Woodbury). -/
theorem rankOneInv_mul (Δ : ι → D) (u : D) (hΔ : ∀ i, Δ i ≠ 0) (hu : u ≠ 0)
    (hq : qSum Δ u ≠ 0) : rankOneInv Δ u * rankOne Δ u = 1 := by
  let _ := invA Δ hΔ
  let _ := invC u hu
  obtain ⟨hH, hS, hX⟩ := woodbury_data Δ u hΔ hu
  let _ := (invS (qSum Δ u) hq).copy _ hS
  have hSi : ⅟(⅟(of fun _ _ => u : Matrix Unit Unit D) + replicateRow Unit (fun _ : ι => (1 : D)) *
      ⅟(diagonal Δ) * replicateCol Unit (fun _ : ι => (1 : D))) =
      of fun _ _ => (qSum Δ u)⁻¹ := rfl
  have key := Matrix.add_mul_mul_invOf_mul_eq_one' (diagonal Δ)
    (replicateCol Unit fun _ : ι => (1 : D)) (of fun _ _ => u) (replicateRow Unit fun _ => 1)
  rwa [hH, hSi, hX] at key

theorem rankOne_isUnit (Δ : ι → D) (u : D) (hΔ : ∀ i, Δ i ≠ 0) (hu : u ≠ 0)
    (hq : qSum Δ u ≠ 0) : IsUnit (rankOne Δ u) :=
  ⟨⟨_, _, rankOne_mul_inv Δ u hΔ hu hq, rankOneInv_mul Δ u hΔ hu hq⟩, rfl⟩

/-- `q⁻¹ = u − u (Σ_{i,j} Hinv i j) u`: `e_d` is a linear read-out of the inverse of `H`. -/
theorem inv_q_eq (Δ : ι → D) (u : D) (hu : u ≠ 0) (hq : qSum Δ u ≠ 0) :
    (qSum Δ u)⁻¹ = u - u * (∑ i, ∑ j, rankOneInv Δ u i j) * u := by
  set s := ∑ i, (Δ i)⁻¹ with hs
  have hsum : ∑ i, ∑ j, rankOneInv Δ u i j = s - s * (qSum Δ u)⁻¹ * s := by
    simp [rankOneInv, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum, hs, mul_assoc]
    exact Finset.sum_comm
  have hs' : s = qSum Δ u - u⁻¹ := by simp [qSum, hs]
  rw [hsum, hs']
  set q := qSum Δ u
  simp only [mul_sub, sub_mul, mul_assoc, mul_inv_cancel₀ hq, inv_mul_cancel₀ hq,
    mul_inv_cancel₀ hu, inv_mul_cancel₀ hu, mul_one]
  simp only [← mul_assoc, mul_inv_cancel₀ hu, one_mul]
  abel

end RankOne

/-! ### Conjugation -/

/-- `(yⁱ u y⁻ⁱ + u) yⁱ = yⁱ u + u yⁱ`: the columns of `L = H · diag(1, y, …, y^{d−1})`. -/
theorem conj_add_mul_pow {D : Type*} [DivisionRing D] (y u : D) (hy : y ≠ 0) (i : ℕ) :
    (y ^ i * u * y⁻¹ ^ i + u) * y ^ i = y ^ i * u + u * y ^ i := by
  rw [add_mul, mul_assoc (y ^ i * u), inv_pow, inv_mul_cancel₀ (pow_ne_zero i hy), mul_one]

/-! ### Scalar point -/

/-- At the scalar point `det (diag(0, 1, …, 1) + J) = 1`, over any commutative ring. -/
theorem det_scalar_point {R : Type*} [CommRing R] (n : ℕ) :
    det (diagonal (fun i : Fin (n + 1) => if i = 0 then (0 : R) else 1) + of fun _ _ => 1) = 1 := by
  let A : Matrix (Fin (n + 1)) (Fin 2) R := of fun i k => ![-(if i = 0 then 1 else 0), 1] k
  let B : Matrix (Fin 2) (Fin (n + 1)) R := of fun k j => ![if j = 0 then 1 else 0, 1] k
  have hM : diagonal (fun i : Fin (n + 1) => if i = 0 then (0 : R) else 1) + (of fun _ _ => 1) =
      1 + A * B := by
    ext i j
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
      simp [A, B, Matrix.mul_apply, Fin.sum_univ_two, diagonal_apply, one_apply, hi, hj]
    all_goals exact fun h => absurd h.symm hj
  have hBA : 1 + B * A = !![0, 1; -1, (n : R) + 2] := by
    ext k l
    fin_cases k <;> fin_cases l <;>
      simp [A, B, Matrix.mul_apply, Finset.sum_ite_eq', Finset.card_univ]
    all_goals ring
  rw [hM, det_one_add_mul_comm, hBA, det_fin_two_of]
  ring

end ThreeAxes.BinomialSizeFamily
