/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.Combinatorics.Choose.MiddleBinomialDensity
public import Formalizations.Combinatorics.SimpleGraph.MatrixTree.Kirchhoff

/-!
# Reusable layer: combinatorics and number theory

Stable names for Pomerance's density theorem on divisors of the middle binomial coefficient and
for Kirchhoff's matrix-tree theorem. Each theorem is proved by the archive theorem it re-exposes
(no proof is copied).

## Main results

* `Formalizations.Reusable.pomerance_density_add_dvd_centralBinom`: for every `k ≥ 1`, the
  proportion of `n < x` with `n + k ∣ C(2n, n)` tends to `1` (archive:
  `MiddleBinomial.tendsto_density_add_dvd_centralBinom`).
* `Formalizations.Reusable.det_lapMatrix_submatrix_eq_card_spanningTrees`: Kirchhoff's
  matrix-tree theorem, with Mathlib's `SimpleGraph.lapMatrix` (archive:
  `SimpleGraph.det_reducedLapMatrix_eq_card_spanningTrees`).
-/

@[expose] public section

open Filter Topology

namespace Formalizations.Reusable

/-- **Pomerance's theorem on the middle binomial coefficient** (Theorem 2 of the paper). For every
integer `k ≥ 1`, the set of `n` with `n + k ∣ C(2n, n)` has asymptotic density `1`:
`#{n < x : n + k ∣ C(2n, n)} / x → 1` as `x → ∞`. (For `k = 1` every `n` qualifies: `C(2n, n)/(n+1)`
is the Catalan number.)

* Archive: `MiddleBinomial.tendsto_density_add_dvd_centralBinom`
  (`Formalizations.Combinatorics.Choose.MiddleBinomialDensity`, with the counting of base-`p`
  digits `≥ p/2` for the primes `p < 2k`).
* Paper formalized: C. Pomerance, *Divisors of the middle binomial coefficient*, Amer. Math. Monthly
  122 (2015) 636–644, Theorem 2, doi:10.4169/amer.math.monthly.122.7.636.
* Example: `pomerance_density_add_dvd_centralBinom 2 (by norm_num)`: almost every `n` has
  `n + 2 ∣ C(2n, n)`. -/
theorem pomerance_density_add_dvd_centralBinom (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun x : ℕ =>
        (((Finset.range x).filter (fun n => n + k ∣ Nat.centralBinom n)).card : ℝ) / x)
      atTop (𝓝 1) :=
  MiddleBinomial.tendsto_density_add_dvd_centralBinom k hk

open scoped Classical in
/-- **Kirchhoff's matrix-tree theorem.** Let `G` be a simple graph on a finite linearly ordered
vertex type `V`, `v₀ : V` and `R` an integral domain. Deleting the row and the column of `v₀` from
Mathlib's Laplacian `G.lapMatrix R` leaves a matrix whose determinant is the number of spanning
trees of `G`, counted as the sets of `|V| − 1` edges of `G` whose spanning subgraph
(`SimpleGraph.fromEdgeSet`) is a tree. The linear order on `V` only fixes the orientation used in
the proof (oriented incidence matrix and Cauchy–Binet); any order gives the same count.

* Archive: `SimpleGraph.det_reducedLapMatrix_eq_card_spanningTrees`
  (`Formalizations.Combinatorics.SimpleGraph.MatrixTree.Kirchhoff`, with the oriented incidence
  matrix and the Cauchy–Binet formula of the same archive); the archive's `reducedLapMatrix` is
  `(G.lapMatrix R).submatrix Subtype.val Subtype.val` by definition. The module cites no paper DOI
  of ours. Mathlib's `SimpleGraph/IncMatrix.lean` lists the oriented incidence matrix and the
  Laplacian as a TODO.
* Classical reference: G. Kirchhoff, Ann. Phys. 148 (1847) 497–508; N. Biggs, *Algebraic
  Graph Theory*, 2nd ed. (1993), ch. 6.
* Example: for the complete graph on `Fin 3` (a triangle) and `v₀ = 0`, the reduced Laplacian is
  `!![2, -1; -1, 2]` with determinant `3`, the three spanning trees of the triangle. -/
theorem det_lapMatrix_submatrix_eq_card_spanningTrees {V : Type*} (R : Type*) [CommRing R]
    [IsDomain R] (G : SimpleGraph V) [Fintype V] [LinearOrder V] [DecidableRel G.Adj] (v₀ : V) :
    ((G.lapMatrix R).submatrix (Subtype.val : {v : V // v ≠ v₀} → V) Subtype.val).det
      = ((Finset.univ.filter
          (fun S : {s : Finset (Sym2 V) // s.card = Fintype.card {v : V // v ≠ v₀}} =>
            ↑S.1 ⊆ G.edgeSet ∧ (SimpleGraph.fromEdgeSet (↑S.1 : Set (Sym2 V))).IsTree)).card : R) :=
  SimpleGraph.det_reducedLapMatrix_eq_card_spanningTrees R G v₀

end Formalizations.Reusable
