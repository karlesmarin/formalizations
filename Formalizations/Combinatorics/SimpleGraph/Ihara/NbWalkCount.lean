/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.Combinatorics.SimpleGraph.Ihara.Bass
public import Formalizations.LinearAlgebra.Matrix.WalkCount

/-!
# Non-backtracking walks and the Hashimoto operator

The Hashimoto operator is the `0-1` adjacency matrix, cast to `R`, of the non-backtracking relation
on darts (`d` is followed by `e` when `e` starts where `d` ends and `e` is not the reversal of `d`).
Hence `tr(Bᵏ)` counts closed non-backtracking dart sequences of length `k`.

## Main definitions

* `SimpleGraph.nbRel`: the non-backtracking relation on darts.

## Main results

* `SimpleGraph.hashimoto_eq_map_relMatrix`: `B` is the cast of `Matrix.relMatrix G.nbRel`.
* `SimpleGraph.trace_hashimoto_pow`: `tr(Bᵏ) = ∑_e #(closed non-backtracking walks of length k at e)`.
-/

@[expose] public section

open Finset Matrix

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The **non-backtracking relation** on darts: `d ⇝ e` iff the head of `d` is the tail of `e` and
`e` is not the reverse of `d`. The Hashimoto operator is its `0-1` adjacency matrix. -/
def nbRel (d e : G.Dart) : Prop := d.snd = e.fst ∧ e ≠ d.symm

instance : DecidableRel G.nbRel :=
  fun d e => inferInstanceAs (Decidable (d.snd = e.fst ∧ e ≠ d.symm))

omit [Fintype V] [DecidableRel G.Adj] in
/-- The Hashimoto operator over a commutative ring `R` is the `Nat.cast` image of the `0-1`
adjacency matrix of the non-backtracking relation. -/
theorem hashimoto_eq_map_relMatrix (R : Type*) [CommRing R] :
    G.hashimoto R = (relMatrix G.nbRel).map (Nat.castRingHom R) := by
  ext d e
  simp only [Matrix.map_apply, hashimoto_apply, relMatrix, nbRel, ne_eq]
  split_ifs with h <;> simp [h]

/-- **The Ihara `N_k` count.** The trace of `Bᵏ` is the natural number of closed non-backtracking
walks of length `k` (summed over the basepoint dart), cast into `R`. This is the combinatorial
identity behind the `N_k = tr(Bᵏ)` generating function of `ihara_Nk_isolated` /
`ihara_Nk_explicit`. -/
theorem trace_hashimoto_pow (R : Type*) [CommRing R] (k : ℕ) :
    ((G.hashimoto R) ^ k).trace
      = ((∑ e : G.Dart, (relWalks G.nbRel k e e).card : ℕ) : R) := by
  have hpow : (G.hashimoto R) ^ k = ((relMatrix G.nbRel) ^ k).map (Nat.castRingHom R) := by
    rw [hashimoto_eq_map_relMatrix G R, ← RingHom.mapMatrix_apply (Nat.castRingHom R), ← map_pow,
      RingHom.mapMatrix_apply]
  have htr : ((relMatrix G.nbRel) ^ k).trace = ∑ e : G.Dart, (relWalks G.nbRel k e e).card := by
    simp only [Matrix.trace, Matrix.diag_apply, relMatrix_pow_apply]
  rw [hpow, ← AddMonoidHom.map_trace, htr]
  simp

end SimpleGraph
