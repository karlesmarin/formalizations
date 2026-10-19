/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Data.Matrix.Block

/-!
# The characteristic polynomial of a 2-lift

For square matrices `B`, `C` over a commutative ring in which `2` is invertible, the block matrix
`[[B, C], [C, B]]` is conjugate to `diag(B + C, B - C)`, so its characteristic polynomial is
`charpoly(B + C) * charpoly(B - C)`. With `B` the positive and `C` the negative part of a signed
adjacency matrix this is the decomposition of the spectrum of a 2-lift of Bilu and Linial: the old
eigenvalues and those of the signed matrix.

## Main results

* `SimpleGraph.MSS.charpoly_twoLift`: `charpoly [[B, C], [C, B]] = charpoly (B + C) * charpoly (B - C)`.

## References

* Y. Bilu, N. Linial, *Lifts, discrepancy and nearly optimal spectral gap*, Combinatorica 26 (2006)
  495–519.
-/

@[expose] public section

open Matrix

namespace SimpleGraph.MSS

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] [Invertible (2 : R)]

omit [Invertible (2 : R)] in
/-- The conjugating involution `P = [[1, 1], [1, −1]]` squares to `2 • 1`. -/
theorem twoLiftConj_sq :
    (fromBlocks 1 1 1 (-1) : Matrix (n ⊕ n) (n ⊕ n) R) * fromBlocks 1 1 1 (-1) = (2 : R) • 1 := by
  rw [fromBlocks_multiply,
    show ((2 : R) • (1 : Matrix (n ⊕ n) (n ⊕ n) R)) = fromBlocks ((2 : R) • 1) 0 0 ((2 : R) • 1) by
      rw [← fromBlocks_one (l := n) (m := n), fromBlocks_smul, smul_zero]]
  congr 1 <;> simp [two_smul]

/-- `P` as a unit, with `P⁻¹ = ⅟2 • P` (using `P² = 2 • 1`). -/
noncomputable def twoLiftConj : (Matrix (n ⊕ n) (n ⊕ n) R)ˣ where
  val := fromBlocks 1 1 1 (-1)
  inv := (⅟ (2 : R)) • fromBlocks 1 1 1 (-1)
  val_inv := by rw [Matrix.mul_smul, twoLiftConj_sq, smul_smul, invOf_mul_self, one_smul]
  inv_val := by rw [Matrix.smul_mul, twoLiftConj_sq, smul_smul, invOf_mul_self, one_smul]

/-- **The 2-lift / Bilu–Linial charpoly factorization.**
`charpoly([[B,C],[C,B]]) = charpoly(B+C) · charpoly(B−C)`. -/
theorem charpoly_twoLift (B C : Matrix n n R) :
    (fromBlocks B C C B).charpoly = (B + C).charpoly * (B - C).charpoly := by
  -- P · M · P = 2 • diag(B+C, B−C)
  have hPMP : (fromBlocks 1 1 1 (-1) : Matrix (n ⊕ n) (n ⊕ n) R) * fromBlocks B C C B
      * fromBlocks 1 1 1 (-1) = (2 : R) • fromBlocks (B + C) 0 0 (B - C) := by
    rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_smul, smul_zero]
    congr 1 <;>
      simp only [Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg, two_smul] <;>
      abel
  -- conjugate: P · M · P⁻¹ = diag(B+C, B−C)
  have hconj : twoLiftConj.val * fromBlocks B C C B * (twoLiftConj (R := R) (n := n))⁻¹.val
      = fromBlocks (B + C) 0 0 (B - C) := by
    show (fromBlocks 1 1 1 (-1) : Matrix (n ⊕ n) (n ⊕ n) R) * fromBlocks B C C B
        * ((⅟ (2 : R)) • fromBlocks 1 1 1 (-1)) = _
    rw [Matrix.mul_smul, hPMP, smul_smul, invOf_mul_self, one_smul]
  rw [← charpoly_units_conj twoLiftConj (fromBlocks B C C B), ← Matrix.coe_units_inv, hconj,
    charpoly_fromBlocks_zero₁₂]

end SimpleGraph.MSS
