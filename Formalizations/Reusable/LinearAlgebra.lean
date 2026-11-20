/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.LinearAlgebra.Matrix.BlockRank
public import Formalizations.LinearAlgebra.Matrix.CauchyBinet
public import Formalizations.LinearAlgebra.Matrix.Charpoly.Jacobi
public import Formalizations.LinearAlgebra.Matrix.Rank
public import Formalizations.LinearAlgebra.Matrix.Rank.Kronecker
public import Formalizations.LinearAlgebra.Matrix.Adjugate
public import Formalizations.Analysis.Polynomial.RealRoots.AlternatingRoots
public import Formalizations.LinearAlgebra.Matrix.PosSemidefRankSquares
public import Formalizations.LinearAlgebra.Matrix.SchurRank
public import Formalizations.LinearAlgebra.Matrix.BiquadraticOrthogonal
public import Formalizations.LinearAlgebra.Matrix.IntOrthonormal

/-!
# Reusable layer: linear algebra

Stable names for matrix results of the archive: rank bounds, the Cauchy–Binet formula and
Jacobi's formula. Each theorem is proved by the archive theorem it re-exposes (no proof is
copied). The modules imported here are general linear algebra; none is a paper of the archive.

## Main results

* `Formalizations.Reusable.int_columns_of_transpose_mul_self`: the columns of an integer matrix
  with `Aᵀ A = 1` are signed unit vectors in distinct rows (archive: `IntOrthonormal.columns_of_transpose_mul_self`).
* `Formalizations.Reusable.biquadratic_sos_transport`: sums of squares of bilinear forms
  representing `P_H` transport to `P_{Dᵀ H D}` when `Dᵀ D = 1` (archive: `BiquadraticSOS.sos_transport`).
* `Formalizations.Reusable.rank_fromBlocks_zero₂₁_le_card_add_rank`: the rank of
  `fromBlocks A B 0 D` is at most the number of rows of `A` plus the rank of `D` (archive:
  `Matrix.rank_fromBlocks_zero₂₁_le_right`).
* `Formalizations.Reusable.matrix_rank_add_le`: `rank (A + B) ≤ rank A + rank B` over a field
  (archive: `Matrix.rank_add_le`).
* `Formalizations.Reusable.det_mul_eq_sum_det_submatrix_mul_det_submatrix`: the Cauchy–Binet
  formula (archive: `Matrix.det_mul_cauchyBinet`).
* `Formalizations.Reusable.derivative_det_eq_trace_adjugate_mul`: Jacobi's formula for a matrix
  of polynomials (archive: `Matrix.derivative_det`).
* `Formalizations.Reusable.matrix_rank_add_rank_le_rank_fromBlocks`: `rank A + rank D` is at most
  the rank of `fromBlocks A B 0 D` (archive: `Matrix.rank_add_rank_le_rank_fromBlocks_zero₂₁`).
* `Formalizations.Reusable.matrix_rank_kronecker`: `rank (A ⊗ₖ B) = rank A · rank B` over a field
  (archive: `Matrix.rank_kronecker`).
* `Formalizations.Reusable.adjugate_apply_self_eq_det_principal_submatrix`: `adjugate A i i` is the
  principal minor without `i` (archive: `Matrix.adjugate_apply_self_eq_det_submatrix`).
-/

@[expose] public section

open Matrix
open scoped Kronecker

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

/-- **Lower bound for the rank of a block upper-triangular matrix.** Over a field `K`, for blocks
`A : l × n`, `B : l × o` and `D : p × o`, `rank A + rank D ≤ rank !![A, B; 0, D]`. Together with
`rank_fromBlocks_zero₂₁_le_card_add_rank` it pins the rank of a block-triangular certificate
between `rank A + rank D` and `|l| + rank D`; with `A` invertible both bounds agree.

* Archive: `Matrix.rank_add_rank_le_rank_fromBlocks_zero₂₁`
  (`Formalizations.LinearAlgebra.Matrix.Rank`, used by the free-locus certificates of the same
  archive); proved through the nullity bound for block triangular matrices.
* Classical reference: textbook (e.g. G. Marsaglia, G. P. H. Styan, *Equalities and inequalities
  for ranks of matrices*, Linear and Multilinear Algebra 2 (1974) 269–292).
* Example: with `A = D = 1 : Matrix (Fin 2) (Fin 2) ℚ`, any `B` gives
  `4 ≤ rank !![1, B; 0, 1]`, so the `4 × 4` block matrix is invertible. -/
theorem matrix_rank_add_rank_le_rank_fromBlocks {l n o p K : Type*} [Field K] [Fintype n]
    [Fintype o] (A : Matrix l n K) (B : Matrix l o K) (D : Matrix p o K) :
    A.rank + D.rank ≤ (fromBlocks A B 0 D).rank :=
  Matrix.rank_add_rank_le_rank_fromBlocks_zero₂₁ A B D

/-- **The rank of a Kronecker product is the product of the ranks.** Over a field `K`, for
`A : Matrix m n K` and `B : Matrix p q K`, `rank (A ⊗ₖ B) = rank A · rank B`. The proof identifies
`A ⊗ₖ B` with the tensor product of the linear maps of `A` and `B` and uses that vector spaces are
flat.

* Archive: `Matrix.rank_kronecker` (`Formalizations.LinearAlgebra.Matrix.Rank.Kronecker`, used by
  the free-locus certificates and the orbifold products of the same archive); the module cites no
  paper DOI of ours.
* Classical reference: R. A. Horn, C. R. Johnson, *Topics in Matrix Analysis* (1991), ch. 4.
* Example: the adjacency matrix of a tensor product of graphs is a Kronecker product, so its rank
  is the product of the ranks of the factors. -/
theorem matrix_rank_kronecker {m n p q K : Type*} [Field K] [Fintype m] [Fintype n] [Fintype p]
    [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q] (A : Matrix m n K)
    (B : Matrix p q K) : (A ⊗ₖ B).rank = A.rank * B.rank :=
  Matrix.rank_kronecker A B

/-- **Diagonal entries of the adjugate are principal minors.** For a square matrix `A` over a
commutative ring, indexed by any finite type `n`, `adjugate A i i` is the determinant of the
principal submatrix obtained by deleting row and column `i` (indexed by the subtype
`{j // j ≠ i}`). Mathlib has the statement for all entries when `n = Fin k.succ`
(`Matrix.adjugate_fin_succ_eq_det_submatrix`); this form needs no reindexing. With Jacobi's
formula (`derivative_det_eq_trace_adjugate_mul`) it gives
`charpoly′ = Σᵢ charpoly (A with row and column i deleted)`.

* Archive: `Matrix.adjugate_apply_self_eq_det_submatrix`
  (`Formalizations.LinearAlgebra.Matrix.Adjugate`, a tool for the Ihara trace formula in the same
  archive); the module cites no paper DOI of ours.
* Classical reference: textbook (Laplace expansion of the cofactor).
* Example: for `A = !![a, b; c, d]`, `adjugate A 0 0 = d`, the `1 × 1` minor left after deleting
  row and column `0`. -/
theorem adjugate_apply_self_eq_det_principal_submatrix {n R : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] (A : Matrix n n R) (i : n) :
    adjugate A i i = (A.submatrix ((↑) : {j // j ≠ i} → n) ((↑) : {j // j ≠ i} → n)).det :=
  Matrix.adjugate_apply_self_eq_det_submatrix A i

/-- **Alternating characteristic polynomial ⇒ positive semidefinite.** A real symmetric matrix whose
characteristic polynomial has coefficients alternating in sign, `(-1)^(n-k) · c_k ≥ 0`, is positive
semidefinite. The polynomial rule behind it (alternating coefficients ⇒ no negative root) is a corollary
of Descartes' rule of signs in Mathlib (`Polynomial.roots_countP_pos_le_signVariations`).

* Archive: `AlternatingRoots.posSemidef_of_charpoly_alternating`
  (`Formalizations.Analysis.Polynomial.RealRoots.AlternatingRoots`); a piece of the design table
  (artefact P006, SOS certificates); the module cites no paper DOI of ours.
* Classical reference: textbook (spectral theorem; Descartes' rule of signs).
* Example: an exact PSD check of a rational Gram matrix without pivoting: compute its
  characteristic polynomial and read the signs. -/
theorem posSemidef_of_charpoly_alternating {V : Type*} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℝ} (hA : A.IsSymm)
    (halt : ∀ k ≤ A.charpoly.natDegree,
      0 ≤ (-1 : ℝ) ^ (A.charpoly.natDegree - k) * A.charpoly.coeff k) :
    A.PosSemidef :=
  AlternatingRoots.posSemidef_of_charpoly_alternating hA halt

/-- **A positive semidefinite matrix of rank `k` is a sum of `k` squares.** Its quadratic form is a sum
of exactly `k` squares of linear forms: `uᵀ A u = Σ_{i < k} (v_i · u)²`. Mathlib only factors a PSD
matrix as `Bᴴ B` with `B` square; this keeps exactly `rank A` terms. The same statement, as a
factorization `B = Aᴴ A` with `rank B ≤ card m` rows, is in TauCeti
(`Matrix.PosSemidef.exists_eq_conjTranspose_mul_self_of_rank_le`, TauCeti/Analysis/Matrix/
GramFactorization.lean); ours depends on Mathlib only.

* Archive: `PosSemidefRankSquares.quadForm_eq_sum_sq`
  (`Formalizations.LinearAlgebra.Matrix.PosSemidefRankSquares`); a piece of the design table (artefact
  P006: a rational PSD Gram matrix of rank `k` certifies `k` REAL squares, not rational ones).
* Classical reference: textbook (spectral theorem).
* Example: the Gram matrix `!![1, 1; 1, 1]` (rank 1) of `(x + y)²` gives one square. -/
theorem psd_quadForm_eq_sum_rank_sq {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.PosSemidef) {k : ℕ} (hk : A.rank = k) :
    ∃ v : Fin k → (n → ℝ), ∀ u, u ⬝ᵥ (A *ᵥ u) = ∑ i, (v i ⬝ᵥ u) ^ 2 :=
  PosSemidefRankSquares.quadForm_eq_sum_sq hA hk

/-- **Rank through the Schur complement.** Over a field, if the top-left block `A` of a block matrix
is invertible, then `rank (fromBlocks A B C D) = card m + rank (D - C * A⁻¹ * B)`. With `A ≻ 0` and a
zero Schur complement this is the exact certificate "this PSD Gram matrix has rank `card m`"
(`Matrix.posSemidef_rank_of_schur_eq_zero` in the archive). Mathlib has the PSD half
(`Matrix.PosDef.fromBlocks₁₁`) and the LDU factorization, not the rank.

* Archive: `Matrix.rank_fromBlocks_of_isUnit₁₁` (`Formalizations.LinearAlgebra.Matrix.SchurRank`;
  also `Matrix.rank_fromBlocks_diagonal`); a piece of the design table (Schur certificates of sums
  of squares); the module cites no paper DOI of ours.
* Classical reference: textbook (Guttman rank additivity; F. Zhang, *The Schur Complement and Its
  Applications*, Springer 2005, §0.9).
* Example: `!![1, 1; 1, 1]` has `A = 1` and Schur complement `1 - 1 * 1 * 1 = 0`, so rank `1`. -/
theorem rank_fromBlocks_of_isUnit₁₁ {m n K : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] [Field K] (A : Matrix m m K) (B : Matrix m n K) (C : Matrix n m K)
    (D : Matrix n n K) (hA : IsUnit A) :
    (fromBlocks A B C D).rank = Fintype.card m + (D - C * A⁻¹ * B).rank :=
  Matrix.rank_fromBlocks_of_isUnit₁₁ A B C D hA

/-- **Sums of squares of bilinear forms under orthogonal congruence.** For the biquadratic form
`P_H(x, y) = (x₀² + x₁²) (y ⬝ᵥ y) + 2 x₀ x₁ (y ⬝ᵥ H y)` over a commutative ring and `Dᵀ D = 1`,
every representation `P_H = ∑ i (x ⬝ᵥ B i y)²` gives `P_{Dᵀ H D} = ∑ i (x ⬝ᵥ (B i D) y)²` with the same
number of squares; so the sum-of-squares length of `P_H` is invariant under `H ↦ Dᵀ H D` (signed-graph
switching is `D = diagonal s`, `s i² = 1`: `BiquadraticSOS.P_switching`).

* Archive: `BiquadraticSOS.sos_transport` (`Formalizations.LinearAlgebra.Matrix.BiquadraticOrthogonal`;
  also `BiquadraticSOS.P_mulVec_orthogonal`, `BiquadraticSOS.P_switching`); a piece of the design
  table (lengths of `P_H`, signed graphs).
* Classical reference: change of variables `y ↦ D y` (textbook); the form `P_H` is that of
  Blekherman–Plaumann–Sinn–Vinzant and Hanselka–Sinn.
* Example: with `D = diagonal ![1, -1]` the two-square representation of `P_H` transports to one of
  `P_{D H D}`. -/
theorem biquadratic_sos_transport {R n ι : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    [Fintype ι] {H D : Matrix n n R} (hD : Dᵀ * D = 1) (B : ι → Matrix (Fin 2) n R)
    (h : ∀ x y, BiquadraticSOS.P H x y = ∑ i, (x ⬝ᵥ (B i *ᵥ y)) ^ 2) (x : Fin 2 → R) (y : n → R) :
    BiquadraticSOS.P (Dᵀ * H * D) x y = ∑ i, (x ⬝ᵥ ((B i * D) *ᵥ y)) ^ 2 :=
  BiquadraticSOS.sos_transport hD B h x y

/-- **Integer orthonormal columns are signed unit vectors.** If an integer `m × n` matrix satisfies
`Aᵀ A = 1`, then every column `j` is `± Pi.single (f j) 1` for an injective `f : n → m`: the nonzero
entries of distinct columns lie in distinct rows. The one-vector case (an integer vector with
`v ⬝ᵥ v = 1` is `± Pi.single i 1`) is `IntOrthonormal.eq_single_of_dotProduct_self_eq_one`. False over
`ℚ`: `(3/5, 4/5)` has norm one.

* Archive: `IntOrthonormal.columns_of_transpose_mul_self`
  (`Formalizations.LinearAlgebra.Matrix.IntOrthonormal`; also
  `IntOrthonormal.eq_single_of_dotProduct_self_eq_one`); a piece of the design table (first step of the
  integer lengths of `P_H`, signed graphs).
* Classical reference: textbook (sums of integer squares).
* Example: the columns of `!![0, 1; -1, 0]` are `-e₁` and `e₀`. -/
theorem int_columns_of_transpose_mul_self {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] {A : Matrix m n ℤ} (hA : Aᵀ * A = 1) :
    ∃ f : n → m, Function.Injective f ∧
      ∀ j, (fun i => A i j) = Pi.single (f j) 1 ∨ (fun i => A i j) = Pi.single (f j) (-1) :=
  IntOrthonormal.columns_of_transpose_mul_self hA

end Formalizations.Reusable
