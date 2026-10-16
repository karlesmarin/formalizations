/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Algebra.Field.Basic
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
* `rank_add_le`: subadditivity of `Matrix.rank` over a field.
* `corank_left_le`, `corank_right_le`: the corank of each diagonal block of
  `fromBlocks A B 0 D` is at most the corank of the whole matrix.
* `corank_unit_sub_le`: an invertible matrix minus a matrix of rank `≤ k` has corank `≤ k`.
-/

@[expose] public section

namespace FreeLocus

section DivRing
variable {R : Type*} [DivisionRing R]

/-- (1c) `(r + a⁻¹)⁻¹ = a (r a + 1)⁻¹`, only `a ≠ 0` needed. -/
theorem inv_add_inv_one (r a : R) (ha : a ≠ 0) : (r + a⁻¹)⁻¹ = a * (r * a + 1)⁻¹ := by
  have h : r + a⁻¹ = (r * a + 1) * a⁻¹ := by
    rw [add_mul, mul_assoc, mul_inv_cancel₀ ha, mul_one, one_mul]
  rw [h, mul_inv_rev, inv_inv]

/-- (1b) `(r + a⁻¹ + b⁻¹)⁻¹ = a (b r a + a + b)⁻¹ b`, only `a, b ≠ 0` needed. -/
theorem inv_add_inv_two (r a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    (r + a⁻¹ + b⁻¹)⁻¹ = a * (b * r * a + a + b)⁻¹ * b := by
  have h : r + a⁻¹ + b⁻¹ = b⁻¹ * (b * r * a + a + b) * a⁻¹ := by
    have e1 : b⁻¹ * (b * r * a) * a⁻¹ = r := by
      rw [show b⁻¹ * (b * r * a) * a⁻¹ = (b⁻¹ * b) * r * (a * a⁻¹) by noncomm_ring,
        inv_mul_cancel₀ hb, mul_inv_cancel₀ ha, one_mul, mul_one]
    have e2 : b⁻¹ * a * a⁻¹ = b⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ ha, mul_one]
    have e3 : b⁻¹ * b * a⁻¹ = a⁻¹ := by rw [inv_mul_cancel₀ hb, one_mul]
    rw [mul_add, mul_add, add_mul, add_mul, e1, e2, e3]; abel
  rw [h, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv]; simp only [mul_assoc]

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

/-- Subadditivity of matrix rank. -/
theorem rank_add_le {m n : Type*} [Fintype n] [Fintype m] (A B : Matrix m n K) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- `rank (fromBlocks A B 0 D) ≤ rank A + card m`. -/
theorem rank_fromBlocks_le_left (A : Matrix n n K) (B : Matrix n m K) (D : Matrix m m K) :
    (fromBlocks A B 0 D).rank ≤ A.rank + Fintype.card m := by
  have hsplit : fromBlocks A B 0 D = fromBlocks A 0 0 0 + fromBlocks 0 B 0 D := by
    rw [fromBlocks_add]; simp
  -- left summand: P * A * Q
  let P : Matrix (n ⊕ m) n K := of fun i j => if i = Sum.inl j then 1 else 0
  let Q : Matrix n (n ⊕ m) K := of fun j k => if k = Sum.inl j then 1 else 0
  have hL : fromBlocks A 0 0 0 = P * A * Q := by
    ext (i | i) (k | k) <;> simp [P, Q, Matrix.mul_apply, fromBlocks]
  -- right summand: X * Y with X of width m
  let X : Matrix (n ⊕ m) m K := of fun i j => fromBlocks (0 : Matrix n n K) B 0 D i (Sum.inr j)
  let Y : Matrix m (n ⊕ m) K := of fun j k => if k = Sum.inr j then 1 else 0
  have hR : fromBlocks 0 B 0 D = X * Y := by
    ext (i | i) (k | k) <;> simp [X, Y, Matrix.mul_apply]
  have h1 : (fromBlocks A (0 : Matrix n m K) 0 (0 : Matrix m m K)).rank ≤ A.rank := by
    rw [hL]; exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  have h2 : (fromBlocks (0 : Matrix n n K) B 0 D).rank ≤ Fintype.card m := by
    rw [hR]; exact (rank_mul_le_left _ _).trans (rank_le_card_width _)
  rw [hsplit]; exact (rank_add_le _ _).trans (Nat.add_le_add h1 h2)

/-- `rank (fromBlocks A B 0 D) ≤ card n + rank D`. -/
theorem rank_fromBlocks_le_right (A : Matrix n n K) (B : Matrix n m K) (D : Matrix m m K) :
    (fromBlocks A B 0 D).rank ≤ Fintype.card n + D.rank := by
  have hsplit : fromBlocks A B 0 D = fromBlocks A B 0 0 + fromBlocks 0 0 0 D := by
    rw [fromBlocks_add]; simp
  let X : Matrix (n ⊕ m) n K := of fun i j => if i = Sum.inl j then 1 else 0
  let Y : Matrix n (n ⊕ m) K := of fun j k => fromBlocks A B (0 : Matrix m n K) (0 : Matrix m m K) (Sum.inl j) k
  have hL : fromBlocks A B 0 0 = X * Y := by
    ext (i | i) (k | k) <;> simp [X, Y, Matrix.mul_apply]
  let P : Matrix (n ⊕ m) m K := of fun i j => if i = Sum.inr j then 1 else 0
  let Q : Matrix m (n ⊕ m) K := of fun j k => if k = Sum.inr j then 1 else 0
  have hR : fromBlocks 0 0 0 D = P * D * Q := by
    ext (i | i) (k | k) <;> simp [P, Q, Matrix.mul_apply, fromBlocks]
  have h1 : (fromBlocks A B 0 (0 : Matrix m m K)).rank ≤ Fintype.card n := by
    rw [hL]; exact (rank_mul_le_left _ _).trans (rank_le_card_width _)
  have h2 : (fromBlocks (0 : Matrix n n K) (0 : Matrix n m K) 0 D).rank ≤ D.rank := by
    rw [hR]; exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  rw [hsplit]; exact (rank_add_le _ _).trans (Nat.add_le_add h1 h2)

/-- (2, left block) corank of `A` ≤ corank of `fromBlocks A B 0 D`. -/
theorem corank_left_le (A : Matrix n n K) (B : Matrix n m K) (D : Matrix m m K) :
    Fintype.card n - A.rank ≤
      (Fintype.card n + Fintype.card m) - (fromBlocks A B 0 D).rank := by
  have h := rank_fromBlocks_le_left A B D
  have hA := A.rank_le_card_width
  omega

/-- (2, right block) corank of `D` ≤ corank of `fromBlocks A B 0 D`. -/
theorem corank_right_le (A : Matrix n n K) (B : Matrix n m K) (D : Matrix m m K) :
    Fintype.card m - D.rank ≤
      (Fintype.card n + Fintype.card m) - (fromBlocks A B 0 D).rank := by
  have h := rank_fromBlocks_le_right A B D
  have hD := D.rank_le_card_width
  omega

/-- (3) invertible minus rank ≤ k has corank ≤ k. -/
theorem corank_unit_sub_le (U E : Matrix n n K) (hU : IsUnit U) (k : ℕ) (hE : E.rank ≤ k) :
    Fintype.card n - (U - E).rank ≤ k := by
  have h1 : U.rank = Fintype.card n := rank_of_isUnit U hU
  have h2 : U.rank ≤ (U - E).rank + E.rank := by
    simpa using rank_add_le (U - E) E
  omega

end Rank
end FreeLocus
