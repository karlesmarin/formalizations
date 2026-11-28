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
public import Formalizations.Combinatorics.SimpleGraph.MatchingPolynomial.GodsilGutman
public import Formalizations.Combinatorics.SimpleGraph.Ihara.BassCommRing
public import Formalizations.Combinatorics.Permanent.Bregman
public import Formalizations.Combinatorics.SimpleGraph.Coloring.DeBruijnErdos
public import Formalizations.Combinatorics.Configuration.BruckRyserChowla
public import Formalizations.Combinatorics.Matroid.Transversal
public import Formalizations.Combinatorics.SimpleGraph.OrientedIncMatrix
public import Formalizations.Combinatorics.Choose.Singmaster
public import Formalizations.Combinatorics.SimpleGraph.MatchingPolynomial.HeilmannLiebBound
public import Formalizations.Combinatorics.SimpleGraph.Ihara.MomentAssembly

/-!
# Reusable layer: combinatorics and number theory

Stable names for Pomerance's density theorem on divisors of the middle binomial coefficient and
for Kirchhoff's matrix-tree theorem. Each theorem is proved by the archive theorem it re-exposes
(no proof is copied).

## Main results

* `Formalizations.Reusable.matchingPoly_forest_eq_charpoly`: the matching polynomial of a forest
  is the characteristic polynomial of its adjacency matrix.
* `Formalizations.Reusable.matchingPoly_splits` and `Formalizations.Reusable.matchingPoly_root_bound`:
  the Heilmann–Lieb real-rootedness and maximum-degree bound.
* `Formalizations.Reusable.godsil_pathTree_identity` and
  `Formalizations.Reusable.matchingPoly_root_power_sum_eq_pathTree_walks`: Godsil's
  path-tree identity and moment theorem.
* `Formalizations.Reusable.ncard_choose_eq_le_two_mul_log`: Singmaster's bound, an integer `a ≥ 2` occurs at most
  `2 ⌊log₂ a⌋` times in Pascal's triangle (archive: `Singmaster.ncard_choose_eq_le_two_mul_log`).
* `Formalizations.Reusable.bregman_permanent_le`: Brégman's theorem, `per A ≤ ∏ᵢ (rᵢ!)^(1/rᵢ)` for `(0,1)`-matrices
  (archive: `Bregman.permanent_le`).
* `Formalizations.Reusable.colorable_iff_forall_finite_induce`: the de Bruijn–Erdős colouring theorem (archive:
  `SimpleGraph.colorable_iff_forall_finite_induce`).
* `Formalizations.Reusable.bruck_ryser_chowla`: a projective plane of order `n ≡ 1, 2 (mod 4)` forces `n` to be a
  sum of two squares (archive: `BruckRyserChowla.exists_sq_add_sq`).
* `Formalizations.Reusable.transversalMatroid_indep`: the independent sets of a transversal matroid are the partial
  transversals (archive: `Theorems.TransversalMatroid.transversalMatroid_indep`).
* `Formalizations.Reusable.orientedIncMatrix_mul_transpose`: `N Nᵀ = D - A` for the oriented incidence matrix
  (archive: `SimpleGraph.orientedIncMatrix_mul_transpose`).
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

/-- **Godsil–Gutman identity.** Summed over all `±1` signings of the edges, the characteristic
polynomials of the signed adjacency matrices give `#signings • μ(G)`, the matching polynomial: the
expected characteristic polynomial of a uniformly random signing is `μ(G)`. This is the spectral
bridge of the Marcus–Spielman–Srivastava interlacing-families method.

* Archive: `SimpleGraph.godsil_gutman`
  (`Formalizations.Combinatorics.SimpleGraph.MatchingPolynomial.GodsilGutman`); the module cites no
  paper DOI of ours.
* Classical reference: C. D. Godsil, I. Gutman, *On the matching polynomial of a graph*, Algebraic
  Methods in Graph Theory (1981) 241–249.
* Example: for one edge the two signings give `X² − 1` twice, and `μ(K₂) = X² − 1`. -/
theorem godsil_gutman {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    (∑ cfg : Sym2 V → Bool, (G.signingMatrix cfg).charpoly)
      = (Fintype.card (Sym2 V → Bool)) • G.matchingPoly :=
  G.godsil_gutman

/-- **Bass's determinant formula over any commutative ring.** For a finite simple graph with
Hashimoto (non-backtracking) matrix `B`, adjacency matrix `A` and degree matrix `D`,
`(1 - u²)^|V| · det (1 - u B) = (1 - u²)^|E| · det (1 - u A + u² (D - 1))` for every `u` in any
commutative ring: the Ihara zeta function in determinant form, with no field and no vertex order.

* Archive: `SimpleGraph.bass_determinant_commRing`
  (`Formalizations.Combinatorics.SimpleGraph.Ihara.BassCommRing`, from the field case
  `bass_charpolyRev`); the module cites no paper DOI of ours.
* Classical reference: H. Bass, *The Ihara–Selberg zeta function of a tree lattice*, Internat. J.
  Math. 3 (1992) 717–797.
* Example: `u = 0` gives `1 = 1`. -/
theorem bass_determinant_commRing {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (R : Type*) [CommRing R] (u : R) :
    (1 - u ^ 2) ^ (Fintype.card V) * (1 - u • G.hashimoto R).det
      = (1 - u ^ 2) ^ G.edgeFinset.card
        * (1 - u • G.adjMatrix R + u ^ 2 • (G.degMatrix R - 1)).det :=
  G.bass_determinant_commRing R u


/-- **Brégman's theorem (Minc's conjecture).** For an `n × n` `(0,1)`-matrix `A` with row sums
`rᵢ = Σⱼ A i j`, the permanent satisfies `per A ≤ ∏ᵢ (rᵢ!)^(1/rᵢ)`. A zero row makes `per A = 0`, and with
`1/0 = 0` its factor is `(0!)^0 = 1`, so no non-zero-row hypothesis is needed.

* Archive: `Bregman.permanent_le` (`Formalizations.Combinatorics.Permanent.Bregman`; the logarithmic form is
  `Bregman.log_bound`); the module cites no paper DOI of ours.
* Classical reference: L. M. Brégman, *Some properties of nonnegative matrices and their permanents*, Soviet
  Math. Dokl. 14 (1973) 945–949; A. Schrijver, *A short proof of Minc's conjecture*, J. Combin. Theory Ser. A
  25 (1978) 80–83.
* Example: a `2 × 2` `(0,1)`-matrix. -/
theorem bregman_permanent_le (n : ℕ) (A : Matrix (Fin n) (Fin n) ℕ) (hA : ∀ i j, A i j ≤ 1) :
    (A.permanent : ℝ) ≤ ∏ i, (((∑ j, A i j).factorial : ℕ) : ℝ) ^ ((1 : ℝ) / (∑ j, A i j : ℕ)) :=
  Bregman.permanent_le n A hA

/-- **De Bruijn–Erdős colouring theorem.** A graph `G` is `n`-colourable iff every finite induced subgraph is
`n`-colourable (no finiteness hypothesis on the vertex type).

* Archive: `SimpleGraph.colorable_iff_forall_finite_induce`
  (`Formalizations.Combinatorics.SimpleGraph.Coloring.DeBruijnErdos`, by Rado's selection lemma).
* Classical reference: N. G. de Bruijn, P. Erdős, *A colour problem for infinite graphs and a problem in the
  theory of relations*, Indag. Math. 54 (1951) 371–373.
* Example: a graph on `ℕ` all of whose finite induced subgraphs are 3-colourable is 3-colourable. -/
theorem colorable_iff_forall_finite_induce {V : Type*} (G : SimpleGraph V) (n : ℕ) :
    G.Colorable n ↔ ∀ s : Finset V, (G.induce (↑s : Set V)).Colorable n :=
  SimpleGraph.colorable_iff_forall_finite_induce G n

/-- **Bruck–Ryser–Chowla theorem.** If a finite projective plane of order `n` exists and `n ≡ 1` or `2 (mod 4)`,
then `n` is a sum of two squares (so there is no plane of order `6` or `14`).

* Archive: `BruckRyserChowla.exists_sq_add_sq`
  (`Formalizations.Combinatorics.Configuration.BruckRyserChowla`); the module cites no paper DOI of ours.
* Classical reference: R. H. Bruck, H. J. Ryser, *The nonexistence of certain finite projective planes*,
  Canad. J. Math. 1 (1949) 88–93; S. Chowla, H. J. Ryser, *Combinatorial problems*, Canad. J. Math. 2 (1950)
  93–99.
* Example: no finite projective plane has order `6`. -/
theorem bruck_ryser_chowla (P L : Type*) [Membership P L] [Configuration.ProjectivePlane P L] [Finite P]
    [Finite L]
    (h : Configuration.ProjectivePlane.order P L % 4 = 1 ∨
      Configuration.ProjectivePlane.order P L % 4 = 2) :
    ∃ a b : ℕ, Configuration.ProjectivePlane.order P L = a ^ 2 + b ^ 2 :=
  BruckRyserChowla.exists_sq_add_sq P L h

/-- **Transversal matroids.** For a finite family `A : Fin t → Finset α` of sets, the independent finite sets of
the transversal matroid presented by `A` are exactly the partial transversals of `A` (the sets `I` admitting an
injection `I → Fin t` with `x ∈ A (f x)`). By Hall's theorem (`partialTransversal_iff_hall` in the archive) these
are the `I` with `|S| ≤ |⋃_{x ∈ S} {i | x ∈ A i}|` for all `S ⊆ I`.

* Archive: `Theorems.TransversalMatroid.transversalMatroid_indep`, with the definition
  `Theorems.TransversalMatroid.transversalMatroid` and the Hall characterization
  `Theorems.TransversalMatroid.partialTransversal_iff_hall`
  (`Formalizations.Combinatorics.Matroid.Transversal`); the module cites no paper DOI of ours.
* Classical reference: J. Edmonds, D. R. Fulkerson, *Transversals and matroid partition*, J. Res. Nat. Bur.
  Standards 69B (1965) 147–153; J. Oxley, *Matroid Theory* (2nd ed., 2011), §1.6.
* Example: the empty set is independent in every transversal matroid. -/
theorem transversalMatroid_indep {α : Type*} [DecidableEq α] {t : Nat} (A : Fin t → Finset α)
    (I : Finset α) :
    (Theorems.TransversalMatroid.transversalMatroid A).Indep (I : Set α) ↔
      Theorems.TransversalMatroid.IsPartialTransversal A I :=
  Theorems.TransversalMatroid.transversalMatroid_indep A I

/-- **Laplacian factorization.** The Gram matrix of the oriented incidence matrix of a finite simple graph on a
linearly ordered vertex type is the graph Laplacian: `N * Nᵀ = D - A` (Mathlib's `SimpleGraph.lapMatrix`), over
any ring. The unoriented incidence matrix gives `D + A` instead.

* Archive: `SimpleGraph.orientedIncMatrix_mul_transpose`
  (`Formalizations.Combinatorics.SimpleGraph.OrientedIncMatrix`); the module cites no paper DOI of ours.
* Classical reference: N. Biggs, *Algebraic Graph Theory* (2nd ed., 1993), ch. 4; C. Godsil, G. Royle,
  *Algebraic Graph Theory* (2001), §8.3 (oriented incidence matrix) and §13.1 (the Laplacian).
* Example: a graph on `Fin 3` over `ℤ`. -/
theorem orientedIncMatrix_mul_transpose (R : Type*) [Ring R] {α : Type*} [Fintype α] [LinearOrder α]
    (G : SimpleGraph α) [DecidableRel G.Adj] :
    G.orientedIncMatrix R * (G.orientedIncMatrix R).transpose = G.lapMatrix R :=
  G.orientedIncMatrix_mul_transpose (R := R)


/-- **Singmaster's bound.** An integer `a ≥ 2` occurs at most `2 ⌊log₂ a⌋` times in Pascal's triangle: the set of
positions `(n, k)` with `k ≤ n` and `C(n, k) = a` is finite with at most that many elements. This is a sharpening
of the form stated by Singmaster, `2 + 2 ⌊log₂ a⌋` (archive: `Singmaster.ncard_choose_eq_le`).

* Archive: `Singmaster.ncard_choose_eq_le_two_mul_log` (`Formalizations.Combinatorics.Choose.Singmaster`); the
  module cites no paper DOI of ours.
* Classical reference: D. Singmaster, *How often does an integer occur as a binomial coefficient?*, Amer. Math.
  Monthly 78 (1971) 385–386.
* Example: the integer `2` occurs at most twice in Pascal's triangle. -/
theorem ncard_choose_eq_le_two_mul_log (a : ℕ) (ha : 2 ≤ a) :
    {p : ℕ × ℕ | p.2 ≤ p.1 ∧ Nat.choose p.1 p.2 = a}.Finite ∧
    {p : ℕ × ℕ | p.2 ≤ p.1 ∧ Nat.choose p.1 p.2 = a}.ncard ≤ 2 * Nat.log 2 a :=
  Singmaster.ncard_choose_eq_le_two_mul_log a ha

/-- **Matching polynomial of a forest.** Over `ℝ`, a finite forest's matching polynomial is
the characteristic polynomial of its adjacency matrix.

* Archive: `SimpleGraph.matchingPoly_forest_eq_charpoly`.
* Classical reference: C. D. Godsil, *Matchings and walks in graphs*, J. Graph Theory 5 (1981)
  285–297.
* Example: for an edgeless graph on `n` vertices, both polynomials are `X ^ n`. -/
theorem matchingPoly_forest_eq_charpoly {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic) :
    G.matchingPoly = (G.adjMatrix ℝ).charpoly :=
  G.matchingPoly_forest_eq_charpoly hG

/-- **Heilmann–Lieb real-rootedness.** The matching polynomial of every finite simple graph
splits over `ℝ`.

* Archive: `SimpleGraph.matchingPoly_realRooted`.
* Classical reference: O. J. Heilmann, E. H. Lieb, *Theory of monomer-dimer systems*,
  Comm. Math. Phys. 27 (1972) 190–232.
* Example: the matching polynomial of a triangle splits over `ℝ`. -/
theorem matchingPoly_splits {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.matchingPoly.Splits :=
  G.matchingPoly_realRooted

/-- **Heilmann–Lieb root bound.** For a finite simple graph with all degrees at most `Δ ≥ 2`,
every real root of the matching polynomial has absolute value at most `2√(Δ − 1)`.
The polynomial splits over `ℝ` by `matchingPoly_splits`.

* Archive: `SimpleGraph.matchingPoly_bounded`.
* Classical reference: O. J. Heilmann, E. H. Lieb, *Theory of monomer-dimer systems*,
  Comm. Math. Phys. 27 (1972) 190–232.
* Example: if all degrees are at most two, all roots lie in `[-2, 2]`. -/
theorem matchingPoly_root_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (hΔ : 2 ≤ Δ)
    (hdeg : ∀ v, G.degree v ≤ Δ) {x : ℝ} (hx : G.matchingPoly.IsRoot x) :
    |x| ≤ 2 * Real.sqrt ((Δ : ℝ) - 1) :=
  (G.matchingPoly_bounded Δ hΔ hdeg).2 x hx

open Classical in
/-- **Godsil's path-tree identity.** Write `T` for the tree of simple paths starting at `u`
and `r` for the trivial path. Then `μ(G) μ(T - r) = μ(G - u) μ(T)`, where deleting a vertex
takes the induced graph on the remaining vertices.

* Archive: `SimpleGraph.godsil_identity` and `SimpleGraph.matchingPoly_deleteIncidenceSet_isolate`.
* Classical reference: C. D. Godsil, *Matchings and walks in graphs*, J. Graph Theory 5 (1981)
  285–297.
* Example: the result gives the polynomial identity needed to compare the two deletion ratios. -/
theorem godsil_pathTree_identity {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) :
    G.matchingPoly * ((G.pathTree u).induce {r | r ≠ G.pathTreeRoot u}).matchingPoly =
      (G.induce {v | v ≠ u}).matchingPoly * (G.pathTree u).matchingPoly := by
  have h := G.godsil_identity u
  unfold SimpleGraph.godsil_identity_target at h
  rw [SimpleGraph.matchingPoly_deleteIncidenceSet_isolate,
    SimpleGraph.matchingPoly_deleteIncidenceSet_isolate] at h
  exact mul_right_cancel₀ Polynomial.X_ne_zero (by simpa only [mul_assoc, mul_comm,
    mul_left_comm] using h)

/-- **Godsil's moment theorem.** The sum of the `k`-th powers of the complex roots of a finite
simple graph's matching polynomial, with multiplicity, equals the number of closed tree-like
walks of length `k`. For each starting vertex `v`, count closed walks from the root of the
path tree at `v` using the root–root entry of the `k`-th power of its adjacency matrix.

* Archive: `SimpleGraph.matchingPowerSum_eq_treeLikeWalkCount` and
  `SimpleGraph.treeLikeWalkCount_eq_sum_pathTree_adjMatrix_pow`.
* Classical reference: C. D. Godsil, *Matchings and walks in graphs*, J. Graph Theory 5 (1981)
  285–297.
* Example: at `k = 0` the root power sum equals the number of vertices. -/
theorem matchingPoly_root_power_sum_eq_pathTree_walks {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    ((G.matchingPoly.map (algebraMap ℝ ℂ)).roots.map (· ^ k)).sum =
      ((∑ v : V, ((G.pathTree v).adjMatrix ℕ ^ k) (G.pathTreeRoot v) (G.pathTreeRoot v)) : ℕ) := by
  change G.matchingPowerSum k = _
  rw [G.matchingPowerSum_eq_treeLikeWalkCount, G.treeLikeWalkCount_eq_sum_pathTree_adjMatrix_pow]

end Formalizations.Reusable
