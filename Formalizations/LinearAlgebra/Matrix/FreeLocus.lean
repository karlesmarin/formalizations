/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.LinearAlgebra.Matrix.Rank
public import Formalizations.RingTheory.FreeField.ThreeAxes.InverseIdentities
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Tactic.NoncommRing
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Linear algebra for the free-locus obstruction

Elementary linear-algebra and ring-identity ingredients of the free-locus obstruction to
inversion height.

## Main results

* `woodbury_special`, `inv_add_inv_two`, `inv_add_inv_one`: ring identities in a division ring
  (a special case of Woodbury, and two "inverse of `r` plus inverses" identities).
* `corank_left_le`, `corank_right_le`: the corank of each diagonal block of
  `fromBlocks A B 0 D` is at most the corank of the whole matrix.
* `corank_unit_sub_le`: an invertible matrix minus a matrix of rank `≤ k` has corank `≤ k`.

## Related

* `inv_add_inv_two` is `ThreeAxes.InverseIdentities.three_term_inv` with the summands reordered,
  and `inv_add_inv_one` is the mirror image of `ThreeAxes.InverseIdentities.one_term_inv`
  (obtained from it in the opposite ring). `woodbury_special` is a scalar instance of the
  Woodbury identity, which Mathlib has for matrices as `Matrix.invOf_add_mul_mul`.
* The rank bounds come from `Formalizations.LinearAlgebra.Matrix.Rank` (`Matrix.rank_add_le`,
  `Matrix.rank_fromBlocks_zero₂₁_le_left`, `Matrix.rank_fromBlocks_zero₂₁_le_right`,
  `Matrix.finrank_ker_mulVecLin_sub_le`).
-/

@[expose] public section

namespace FreeLocus

section DivRing
variable {R : Type*} [DivisionRing R]

/-- (1c) `(r + a⁻¹)⁻¹ = a (r a + 1)⁻¹`, only `a ≠ 0` needed. Mirror image of
`ThreeAxes.InverseIdentities.one_term_inv`, read in the opposite ring. -/
theorem inv_add_inv_one (r a : R) (ha : a ≠ 0) : (r + a⁻¹)⁻¹ = a * (r * a + 1)⁻¹ := by
  have h := congrArg MulOpposite.unop
    (ThreeAxes.InverseIdentities.one_term_inv (MulOpposite.op a) (MulOpposite.op r)
      (MulOpposite.op_ne_zero_iff a |>.mpr ha))
  simp only [MulOpposite.unop_inv, MulOpposite.unop_add, MulOpposite.unop_mul,
    MulOpposite.unop_op, MulOpposite.unop_one] at h
  rw [add_comm r, add_comm (r * a), h]

/-- (1b) `(r + a⁻¹ + b⁻¹)⁻¹ = a (b r a + a + b)⁻¹ b`, only `a, b ≠ 0` needed. This is
`ThreeAxes.InverseIdentities.three_term_inv` with `p = b`, `q = a`. -/
theorem inv_add_inv_two (r a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    (r + a⁻¹ + b⁻¹)⁻¹ = a * (b * r * a + a + b)⁻¹ * b := by
  rw [show r + a⁻¹ + b⁻¹ = b⁻¹ + a⁻¹ + r by abel,
    ThreeAxes.InverseIdentities.three_term_inv b a r hb ha,
    show b * r * a + b + a = b * r * a + a + b by abel]

/-- (1a) Woodbury special case: `(1 + x y⁻¹ x)⁻¹ = 1 - x (y + x x)⁻¹ x`,
for `y ≠ 0` and `y + x x ≠ 0` (no hypothesis on `1 + x y⁻¹ x` is needed). -/
theorem woodbury_special (x y : R) (hy : y ≠ 0) (hS : y + x * x ≠ 0) :
    (1 + x * y⁻¹ * x)⁻¹ = 1 - x * (y + x * x)⁻¹ * x := by
  set S := y + x * x with hSdef
  have hxx : x * x = S - y := by rw [hSdef]; abel
  apply inv_eq_of_mul_eq_one_right
  calc (1 + x * y⁻¹ * x) * (1 - x * S⁻¹ * x)
      = 1 + x * y⁻¹ * x - x * S⁻¹ * x - x * y⁻¹ * (x * x) * S⁻¹ * x := by noncomm_ring
    _ = 1 + x * y⁻¹ * x - x * S⁻¹ * x
          - (x * y⁻¹ * (S * S⁻¹) * x - x * (y⁻¹ * y) * S⁻¹ * x) := by
          rw [hxx]; noncomm_ring
    _ = 1 := by rw [mul_inv_cancel₀ hS, inv_mul_cancel₀ hy]; noncomm_ring

end DivRing

section Rank
open Matrix
variable {K : Type*} [Field K]
variable {n m : Type*} [Fintype n] [Fintype m]

/-- (2, left block) corank of `A` ≤ corank of `fromBlocks A B 0 D`. -/
theorem corank_left_le (A : Matrix n n K) (B : Matrix n m K) (D : Matrix m m K) :
    Fintype.card n - A.rank ≤
      (Fintype.card n + Fintype.card m) - (fromBlocks A B 0 D).rank := by
  have h := rank_fromBlocks_zero₂₁_le_left A B D
  have hA := A.rank_le_card_width
  omega

/-- (2, right block) corank of `D` ≤ corank of `fromBlocks A B 0 D`. -/
theorem corank_right_le (A : Matrix n n K) (B : Matrix n m K) (D : Matrix m m K) :
    Fintype.card m - D.rank ≤
      (Fintype.card n + Fintype.card m) - (fromBlocks A B 0 D).rank := by
  have h := rank_fromBlocks_zero₂₁_le_right A B D
  have hD := D.rank_le_card_width
  omega

/-- (3) invertible minus rank ≤ k has corank ≤ k. -/
theorem corank_unit_sub_le [DecidableEq n] (U E : Matrix n n K) (hU : IsUnit U) (k : ℕ)
    (hE : E.rank ≤ k) :
    Fintype.card n - (U - E).rank ≤ k := by
  have h1 := rank_add_finrank_ker_mulVecLin (U - E)
  have h2 := finrank_ker_mulVecLin_sub_le hU E
  omega

end Rank
end FreeLocus
