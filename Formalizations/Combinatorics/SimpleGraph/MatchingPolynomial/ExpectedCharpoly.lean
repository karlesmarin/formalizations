/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.Combinatorics.SimpleGraph.MatchingPolynomial.Signing
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Data.Sym.Sym2

/-!
# Edge signings and the expected characteristic polynomial

A configuration `cfg : Sym2 V → Bool` signs every edge of `G` with `+1` or `-1`. This file defines
the corresponding signed adjacency matrix and the statement of the Godsil–Gutman identity: the sum
of the characteristic polynomials over all configurations is `#configurations • μ(G)`, i.e. the
expected characteristic polynomial of a uniformly random signing is the matching polynomial. The
identity is proved in `GodsilGutman` (`SimpleGraph.godsil_gutman`).

## Main definitions

* `SimpleGraph.signingMatrix G cfg`: the `±1`-signed adjacency matrix.
* `SimpleGraph.expected_charpoly_eq_matchingPoly_target G`: the Godsil–Gutman identity, as a
  proposition.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The signed adjacency matrix induced by a `Bool`-configuration on edges: `true ↦ +1`, `false ↦ −1`
(off the edge set it is `0`, via `signedAdjMatrix`). Symmetric because `s(i, j) = s(j, i)` in `Sym2`. -/
noncomputable def signingMatrix (cfg : Sym2 V → Bool) : Matrix V V ℝ :=
  G.signedAdjMatrix (fun i j => if cfg s(i, j) then (1 : ℝ) else -1)

/-- **The Godsil–Gutman identity, as a proposition.** The characteristic polynomials of all
`±1` edge-signings sum to `(#configs) • matchingPoly G`. Equivalent to "the *average* charpoly is the
matching polynomial". Proved as `SimpleGraph.godsil_gutman`. -/
def expected_charpoly_eq_matchingPoly_target : Prop :=
  (∑ cfg : Sym2 V → Bool, (G.signingMatrix cfg).charpoly)
    = (Fintype.card (Sym2 V → Bool)) • G.matchingPoly

end SimpleGraph
