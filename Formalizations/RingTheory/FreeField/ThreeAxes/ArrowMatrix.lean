/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.RowCol
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Basic

/-!
# Inverse of an arrow matrix over a division ring

For `d : ι → D` with every `d τ ≠ 0` and `α ω : ι → D`, the arrow (bordered diagonal) matrix
`B = [[diag d, ω], [α, 0]]` is invertible when `x = Σ_τ α_τ d_τ⁻¹ ω_τ ≠ 0`, and the border corner
of its inverse is `−x⁻¹`. So `x⁻¹` is minus a corner of the inverse of a linear matrix.
Over a division ring `Matrix.inv` is not available (it needs a commutative ring), so the inverse
is given explicitly and checked on both sides.

## Main results

* `arrow`, `arrowInv`: the matrix and its explicit inverse (Schur complement of `diag d`, `−x`).
* `arrow_mul_arrowInv`, `arrowInv_mul_arrow`: `B * B' = 1` and `B' * B = 1`.
* `arrow_isUnit`; `arrowInv_corner`: `B' (inr, inr) = −x⁻¹`.

## Related

`InverseIdentities.fromBlocks_mul_schur` has the pivot in the lower-right block and gives a
one-sided inverse; here the pivot is the upper-left diagonal block and both products are checked.
Over a commutative ring this is a case of Mathlib's `Matrix.invOf_fromBlocks₁₁_eq`.
-/

@[expose] public section

namespace ThreeAxes.ArrowMatrix

open Matrix

variable {D : Type*} [DivisionRing D] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `x = Σ_τ α_τ d_τ⁻¹ ω_τ`. -/
def arrowSum (d α ω : ι → D) : D := ∑ τ, α τ * (d τ)⁻¹ * ω τ

/-- The arrow matrix `[[diag d, ω], [α, 0]]`, border indexed by `Unit`. -/
def arrow (d α ω : ι → D) : Matrix (ι ⊕ Unit) (ι ⊕ Unit) D :=
  fromBlocks (diagonal d) (replicateCol Unit ω) (replicateRow Unit α) 0

/-- The inverse of `arrow d α ω`. -/
def arrowInv (d α ω : ι → D) : Matrix (ι ⊕ Unit) (ι ⊕ Unit) D :=
  let x := arrowSum d α ω
  fromBlocks (diagonal (fun τ => (d τ)⁻¹) - of fun τ σ => (d τ)⁻¹ * ω τ * x⁻¹ * α σ * (d σ)⁻¹)
    (replicateCol Unit fun τ => (d τ)⁻¹ * ω τ * x⁻¹)
    (replicateRow Unit fun σ => x⁻¹ * α σ * (d σ)⁻¹) (of fun _ _ => -x⁻¹)

theorem arrow_mul_arrowInv (d α ω : ι → D) (hd : ∀ τ, d τ ≠ 0) (hx : arrowSum d α ω ≠ 0) :
    arrow d α ω * arrowInv d α ω = 1 := by
  rw [arrow, arrowInv, fromBlocks_multiply, ← fromBlocks_one]
  congr 1 <;> ext i k
  · by_cases h : i = k
    · subst h; simp [diagonal, Matrix.mul_apply, mul_assoc]
      rw [mul_sub, mul_inv_cancel₀ (hd i), ← mul_assoc, mul_inv_cancel₀ (hd i), one_mul,
        sub_add_cancel]
    · simp [diagonal, Matrix.mul_apply, h, ← mul_assoc, hd]
  · simp [diagonal, Matrix.mul_apply, ← mul_assoc, hd]
  · simp only [Matrix.mul_sub, add_apply, sub_apply, Matrix.mul_apply, replicateRow_apply,
      diagonal_apply, of_apply, Matrix.zero_mul, zero_apply, add_zero]
    simp only [mul_ite, mul_zero]
    have : ∑ τ, α τ * ((d τ)⁻¹ * ω τ * (arrowSum d α ω)⁻¹ * α k * (d k)⁻¹) =
        arrowSum d α ω * (arrowSum d α ω)⁻¹ * α k * (d k)⁻¹ := by
      simp only [arrowSum, Finset.sum_mul, mul_assoc]
    rw [this, mul_inv_cancel₀ hx, one_mul]
    simp
  · simp only [add_apply, Matrix.mul_apply, replicateRow_apply, replicateCol_apply,
      Matrix.zero_mul, zero_apply, add_zero, one_apply_eq]
    have : ∑ τ, α τ * ((d τ)⁻¹ * ω τ * (arrowSum d α ω)⁻¹) =
        arrowSum d α ω * (arrowSum d α ω)⁻¹ := by
      simp only [arrowSum, Finset.sum_mul, mul_assoc]
    rw [this, mul_inv_cancel₀ hx]

theorem arrowInv_mul_arrow (d α ω : ι → D) (hd : ∀ τ, d τ ≠ 0) (hx : arrowSum d α ω ≠ 0) :
    arrowInv d α ω * arrow d α ω = 1 := by
  rw [arrow, arrowInv, fromBlocks_multiply, ← fromBlocks_one]
  congr 1 <;> ext i k
  · by_cases h : i = k
    · subst h; simp [diagonal, Matrix.mul_apply, mul_assoc]
      rw [sub_mul, inv_mul_cancel₀ (hd i)]
      simp only [mul_assoc, inv_mul_cancel₀ (hd i), mul_one, sub_add_cancel]
    · simp [diagonal, Matrix.mul_apply, h, mul_assoc, hd]
  · simp only [Matrix.sub_mul, add_apply, sub_apply, Matrix.mul_apply, replicateCol_apply,
      diagonal_apply, of_apply, Matrix.mul_zero, zero_apply, add_zero]
    simp only [ite_mul, zero_mul]
    have : ∑ σ, (d i)⁻¹ * ω i * (arrowSum d α ω)⁻¹ * α σ * (d σ)⁻¹ * ω σ =
        (d i)⁻¹ * ω i * (arrowSum d α ω)⁻¹ * arrowSum d α ω := by
      simp only [arrowSum, Finset.mul_sum, mul_assoc]
    rw [this, mul_assoc ((d i)⁻¹ * ω i), inv_mul_cancel₀ hx, mul_one]
    simp
  · simp [diagonal, Matrix.mul_apply, mul_assoc, hd]
  · simp only [add_apply, Matrix.mul_apply, replicateRow_apply, replicateCol_apply,
      Matrix.mul_zero, zero_apply, add_zero, one_apply_eq]
    have : ∑ σ, (arrowSum d α ω)⁻¹ * α σ * (d σ)⁻¹ * ω σ =
        (arrowSum d α ω)⁻¹ * arrowSum d α ω := by
      simp only [arrowSum, Finset.mul_sum, mul_assoc]
    rw [this, inv_mul_cancel₀ hx]

theorem arrow_isUnit (d α ω : ι → D) (hd : ∀ τ, d τ ≠ 0) (hx : arrowSum d α ω ≠ 0) :
    IsUnit (arrow d α ω) :=
  ⟨⟨_, _, arrow_mul_arrowInv d α ω hd hx, arrowInv_mul_arrow d α ω hd hx⟩, rfl⟩

/-- The border corner of the inverse is `−x⁻¹`. -/
theorem arrowInv_corner (d α ω : ι → D) :
    arrowInv d α ω (Sum.inr ()) (Sum.inr ()) = -(arrowSum d α ω)⁻¹ := by
  simp [arrowInv]

end ThreeAxes.ArrowMatrix
