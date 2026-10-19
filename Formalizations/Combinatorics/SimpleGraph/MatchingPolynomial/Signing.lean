/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Formalizations.Combinatorics.SimpleGraph.MatchingPolynomial.Basic

/-!
# Signed adjacency matrices

A weight function `w : V → V → ℝ` defines the signed adjacency matrix of `G`, equal to `w i j` on
edges and to `0` elsewhere. With `w` taking values `±1` this is the adjacency matrix of a signing of
`G`, whose characteristic polynomials average to the matching polynomial (`GodsilGutman`).

## Main definitions

* `SimpleGraph.signedAdjMatrix G w`: the signed adjacency matrix.

## Main results

* `SimpleGraph.signedAdjMatrix_eq_zero_of_not_adj`, `SimpleGraph.signedAdjMatrix_diag`: it vanishes
  off the edges and on the diagonal.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The **signed adjacency matrix** `A_w`: entry `(i, j)` is the signing `w i j` when `i ~ j`, else `0`.
For the MSS argument the signing is symmetric on edges (`w i j = w j i`) and takes values in `{−1, +1}`;
those constraints enter as hypotheses where needed. -/
noncomputable def signedAdjMatrix (w : V → V → ℝ) : Matrix V V ℝ :=
  fun i j => if G.Adj i j then w i j else 0

/-- Off the edge set, the signed adjacency matrix vanishes. -/
theorem signedAdjMatrix_eq_zero_of_not_adj (w : V → V → ℝ) {i j : V} (h : ¬ G.Adj i j) :
    G.signedAdjMatrix w i j = 0 := by
  simp [signedAdjMatrix, h]

/-- The diagonal of the signed adjacency matrix is zero (no self-loops in a `SimpleGraph`). -/
theorem signedAdjMatrix_diag (w : V → V → ℝ) (i : V) :
    G.signedAdjMatrix w i i = 0 :=
  signedAdjMatrix_eq_zero_of_not_adj G w (G.irrefl)

end SimpleGraph
