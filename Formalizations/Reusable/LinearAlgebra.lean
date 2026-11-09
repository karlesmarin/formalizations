/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.LinearAlgebra.Matrix.Rank

/-!
# Reusable layer: linear algebra

A stable name for a rank bound of block upper-triangular matrices. The theorem is proved by the
archive theorem it re-exposes (no proof is copied).

## Main results

* `Formalizations.Reusable.rank_fromBlocks_zero₂₁_le_card_add_rank`: the rank of
  `fromBlocks A B 0 D` is at most the number of rows of `A` plus the rank of `D` (archive:
  `Matrix.rank_fromBlocks_zero₂₁_le_right`).
-/

@[expose] public section

open Matrix

namespace Formalizations.Reusable

/-- **Rank of a block upper-triangular matrix.** Over a field `K`, for blocks `A : l × n`,
`B : l × o` and `D : p × o`, `rank !![A, B; 0, D] ≤ |l| + rank D`. The proof splits the block matrix
as `fromBlocks A B 0 0 + fromBlocks 0 0 0 D` and uses subadditivity of the rank (also in the
archive, `Matrix.rank_add_le`, which Mathlib states only for linear maps).

* Archive: `Matrix.rank_fromBlocks_zero₂₁_le_right` (`Formalizations.LinearAlgebra.Matrix.Rank`,
  used by the free-locus certificates of the same archive).
* Classical reference: a textbook consequence of the subadditivity of the rank (no single source).
* Example: with `A = 1 : Matrix (Fin 1) (Fin 1) ℚ`, any `B` and `D : Matrix (Fin 2) (Fin 2) ℚ`,
  `rank_fromBlocks_zero₂₁_le_card_add_rank A B D : (fromBlocks A B 0 D).rank ≤ 1 + D.rank`. -/
theorem rank_fromBlocks_zero₂₁_le_card_add_rank {l n o p K : Type*} [Field K]
    [Fintype n] [Fintype o] [Fintype l] [Finite p] (A : Matrix l n K) (B : Matrix l o K)
    (D : Matrix p o K) :
    (fromBlocks A B 0 D).rank ≤ Fintype.card l + D.rank :=
  Matrix.rank_fromBlocks_zero₂₁_le_right A B D

end Formalizations.Reusable
