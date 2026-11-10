/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.Combinatorics.Choose.MiddleBinomialDensity
public import Formalizations.Combinatorics.SimpleGraph.MatrixTree.Kirchhoff
public import Formalizations.Combinatorics.Hall.Tight
public import Formalizations.Combinatorics.SetFamily.Bondy

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
* `Formalizations.Reusable.card_biUnion_submodular`: the neighbourhood function
  `s ↦ |s.biUnion t|` is submodular (archive: `Finset.card_biUnion_union_add_card_biUnion_inter_le`).
* `Formalizations.Reusable.card_biUnion_union_inter_eq_of_tight`: under Hall's condition, unions and
  intersections of tight sets are tight (archive: `Finset.card_biUnion_union_eq_card_union`,
  `Finset.card_biUnion_inter_eq_card_inter`).
* `Formalizations.Reusable.bondy_exists_erase_injOn`: Bondy's theorem on induced subsets (archive:
  `Bondy.exists_erase_injOn`).
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

/-- **The neighbourhood function of a set family is submodular.** For an indexed family of finite
sets `t : ι → Finset α` and `s u : Finset ι`, with `N(s) = s.biUnion t` (the union of the `t i`,
`i ∈ s`): `|N(s ∪ u)| + |N(s ∩ u)| ≤ |N(s)| + |N(u)|`. It is the inequality behind the deficiency
form of Hall's theorem (Kőnig–Ore) and behind the transversal matroid.

* Archive: `Finset.card_biUnion_union_add_card_biUnion_inter_le`
  (`Formalizations.Combinatorics.Hall.Tight`, which imports only `Mathlib.Combinatorics.Hall.Finite`);
  the module cites no paper DOI of ours. Mathlib proves Hall's theorem by another induction and has
  no tight-set lemmas.
* Classical reference: L. Lovász, M. D. Plummer, *Matching Theory* (1986), ch. 1.
* Example: for `t i = {i, i + 1}` on `ℕ`, `s = {0}`, `u = {1}`, it reads `3 + 0 ≤ 2 + 2`. -/
theorem card_biUnion_submodular {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (t : ι → Finset α) (s u : Finset ι) :
    ((s ∪ u).biUnion t).card + ((s ∩ u).biUnion t).card ≤ (s.biUnion t).card + (u.biUnion t).card :=
  Finset.card_biUnion_union_add_card_biUnion_inter_le t s u

/-- **Tight sets of a Hall family form a lattice.** Let `t : ι → Finset α` satisfy Hall's condition
`|v| ≤ |v.biUnion t|` for every `v : Finset ι`, and call `s` tight when `|s.biUnion t| = |s|`. Then
the union and the intersection of two tight sets are tight. This is the critical-set step of the
Halmos–Vaughan proof of Hall's theorem and the source of the Dulmage–Mendelsohn decomposition.

* Archive: `Finset.card_biUnion_union_eq_card_union` and `Finset.card_biUnion_inter_eq_card_inter`
  (`Formalizations.Combinatorics.Hall.Tight`), paired into one statement here; the module cites no
  paper DOI of ours.
* Classical reference: P. R. Halmos, H. E. Vaughan, Amer. J. Math. 72 (1950) 214–215;
  L. Lovász, M. D. Plummer, *Matching Theory* (1986), ch. 1.
* Example: for the identity family `t i = {i}` every set is tight, and so are unions and
  intersections. -/
theorem card_biUnion_union_inter_eq_of_tight {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    {t : ι → Finset α} {s u : Finset ι} (hall : ∀ v : Finset ι, v.card ≤ (v.biUnion t).card)
    (hs : (s.biUnion t).card = s.card) (hu : (u.biUnion t).card = u.card) :
    ((s ∪ u).biUnion t).card = (s ∪ u).card ∧ ((s ∩ u).biUnion t).card = (s ∩ u).card :=
  ⟨Finset.card_biUnion_union_eq_card_union hall hs hu,
    Finset.card_biUnion_inter_eq_card_inter hall hs hu⟩

/-- **Bondy's theorem on induced subsets.** Let `X` be a nonempty finite set and `F` a family of at
most `|X|` distinct finite sets. Then some `x ∈ X` can be deleted from every member of `F` without
merging two of them: `A ↦ A.erase x` is injective on `F`. The sets need not be subsets of `X`.
Typical uses: test covers and separating systems, and deleting a coordinate of a binary code
without identifying two codewords.

* Archive: `Bondy.exists_erase_injOn` (`Formalizations.Combinatorics.SetFamily.Bondy`, proved by
  the linear-algebra argument over `ZMod 2`); the module cites no paper DOI of ours.
* Classical reference: J. A. Bondy, *Induced subsets*, J. Combin. Theory Ser. B 12 (1972) 201–202.
* Example: for `X = {1, 2}` and `F = {∅, {1}}`, deleting `2` keeps the two sets distinct. -/
theorem bondy_exists_erase_injOn {α : Type*} [DecidableEq α] (X : Finset α) (hX : X.Nonempty)
    (F : Finset (Finset α)) (hcard : F.card ≤ X.card) :
    ∃ x ∈ X, Set.InjOn (fun A : Finset α => A.erase x) (F : Set (Finset α)) :=
  Bondy.exists_erase_injOn X hX F hcard

end Formalizations.Reusable
