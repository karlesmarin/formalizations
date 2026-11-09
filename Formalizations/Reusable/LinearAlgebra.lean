/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.LinearAlgebra.Matrix.BlockRank
public import Formalizations.LinearAlgebra.Matrix.CauchyBinet
public import Formalizations.LinearAlgebra.Matrix.Charpoly.Jacobi

/-!
# Reusable layer: linear algebra

Stable names for matrix results of the archive: rank bounds, the Cauchy–Binet formula and
Jacobi's formula. Each theorem is proved by the archive theorem it re-exposes (no proof is
copied). The modules imported here are general linear algebra; none is a paper of the archive.

## Main results

* `Formalizations.Reusable.rank_fromBlocks_zero₂₁_le_card_add_rank`: the rank of
  `fromBlocks A B 0 D` is at most the number of rows of `A` plus the rank of `D` (archive:
  `Matrix.rank_fromBlocks_zero₂₁_le_right`).
* `Formalizations.Reusable.matrix_rank_add_le`: `rank (A + B) ≤ rank A + rank B` over a field
  (archive: `Matrix.rank_add_le`).
* `Formalizations.Reusable.det_mul_eq_sum_det_submatrix_mul_det_submatrix`: the Cauchy–Binet
  formula (archive: `Matrix.det_mul_cauchyBinet`).
* `Formalizations.Reusable.derivative_det_eq_trace_adjugate_mul`: Jacobi's formula for a matrix
  of polynomials (archive: `Matrix.derivative_det`).
-/

@[expose] public section

open Matrix

namespace Formalizations.Reusable

/-- **Rank of a block upper-triangular matrix.** Over a field `K`, for blocks `A : l × n`,
`B : l × o` and `D : p × o`, `rank !![A, B; 0, D] ≤ |l| + rank D`. The proof splits the block matrix
as `fromBlocks A B 0 0 + fromBlocks 0 0 0 D` and uses subadditivity of the rank (also in the
archive, `Matrix.rank_add_le`, which Mathlib states only for linear maps).

* Archive: `Matrix.rank_fromBlocks_zero₂₁_le_right` (`Formalizations.LinearAlgebra.Matrix.BlockRank`,
  used by the free-locus certificates of the same archive).
* Classical reference: a textbook consequence of the subadditivity of the rank (no single source).
* Example: with `A = 1 : Matrix (Fin 1) (Fin 1) ℚ`, any `B` and `D : Matrix (Fin 2) (Fin 2) ℚ`,
  `rank_fromBlocks_zero₂₁_le_card_add_rank A B D : (fromBlocks A B 0 D).rank ≤ 1 + D.rank`. -/
theorem rank_fromBlocks_zero₂₁_le_card_add_rank {l n o p K : Type*} [Field K]
    [Fintype n] [Fintype o] [Fintype l] [Finite p] (A : Matrix l n K) (B : Matrix l o K)
    (D : Matrix p o K) :
    (fromBlocks A B 0 D).rank ≤ Fintype.card l + D.rank :=
  Matrix.rank_fromBlocks_zero₂₁_le_right A B D

/-- **Subadditivity of the rank.** Over a field `K`, for matrices `A B : Matrix m n K`,
`rank (A + B) ≤ rank A + rank B`. Mathlib states this for linear maps (`LinearMap.rank_add_le`);
this is the `Matrix.rank` form.

* Archive: `Matrix.rank_add_le` (`Formalizations.LinearAlgebra.Matrix.BlockRank`, a shared lemma
  of the free-locus certificates of the same archive).
* Classical reference: textbook (the image of `A + B` lies in the sum of the images).
* Example: with `B = −A`, `matrix_rank_add_le A (-A)` gives `rank 0 ≤ rank A + rank (−A)`. -/
theorem matrix_rank_add_le {m n K : Type*} [Field K] [Fintype n] (A B : Matrix m n K) :
    (A + B).rank ≤ A.rank + B.rank :=
  Matrix.rank_add_le A B

/-- **The Cauchy–Binet formula.** Over a commutative ring `R`, for `A : Matrix m n R` and
`B : Matrix n m R` with `n` linearly ordered, `det (A * B)` is the sum, over the subsets `S` of `n`
with `|S| = |m|`, of `det A[:, S] · det B[S, :]`, the columns of `A` and the rows of `B` taken in
the increasing order of `S` (`S.orderEmbOfFin`) and the rows of `A`, columns of `B` through
`Fintype.equivFin m`. When `|n| < |m|` the sum is empty and `det (A * B) = 0`.

* Archive: `Matrix.det_mul_cauchyBinet` (`Formalizations.LinearAlgebra.Matrix.CauchyBinet`, the
  tool for Kirchhoff's matrix-tree theorem in the same archive); the module cites no paper DOI of
  ours.
* Classical reference: A.-L. Cauchy (1815), J. Binet (1815); F. R. Gantmacher, *The Theory of
  Matrices*, vol. 1.
* Example: for `A : Matrix (Fin 1) (Fin 2) ℚ`, `B : Matrix (Fin 2) (Fin 1) ℚ` it gives
  `det (A * B) = A 0 0 * B 0 0 + A 0 1 * B 1 0`, a sum of two `1 × 1` minors. -/
theorem det_mul_eq_sum_det_submatrix_mul_det_submatrix {R m n : Type*} [CommRing R] [Fintype m]
    [DecidableEq m] [Fintype n] [LinearOrder n] (A : Matrix m n R) (B : Matrix n m R) :
    (A * B).det =
      ∑ S : {s : Finset n // s.card = Fintype.card m},
        (A.submatrix (Fintype.equivFin m).symm (S.1.orderEmbOfFin S.2)).det *
        (B.submatrix (S.1.orderEmbOfFin S.2) (Fintype.equivFin m).symm).det :=
  Matrix.det_mul_cauchyBinet A B

/-- **Jacobi's formula.** For a square matrix `A` with entries in `R[X]` (`R` a commutative ring),
`derivative (det A) = trace (adjugate A * A.map derivative)`. With `A = X • 1 − M` it gives
`charpoly′ = trace (adjugate (X − M))`, the sum of the characteristic polynomials of the principal
submatrices. Mathlib has only the special case `derivative_det_one_add_X_smul` (the first-order
term of `det (1 + X M)`).

* Archive: `Matrix.derivative_det` (`Formalizations.LinearAlgebra.Matrix.Charpoly.Jacobi`, a tool
  for the Ihara trace formula in the same archive); the module cites no paper DOI of ours.
* Classical reference: C. G. J. Jacobi, *De formatione et proprietatibus determinantium*, J. Reine
  Angew. Math. 22 (1841); R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed. (2013).
* Example: for `A = !![X, 1; 0, X]` over `ℚ`, it gives `derivative (X²) = 2 X`. -/
theorem derivative_det_eq_trace_adjugate_mul {n R : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] (A : Matrix n n (Polynomial R)) :
    Polynomial.derivative A.det = (A.adjugate * A.map Polynomial.derivative).trace :=
  Matrix.derivative_det A

end Formalizations.Reusable
