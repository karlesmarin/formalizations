/-
Usage example of the reusable layer, area Combinatorics, with the minimal import of that area: the
same code a user pastes into a file of their own project (README, section "Reusable layer").
-/
import Formalizations.Reusable.Combinatorics

open Formalizations.Reusable Filter Topology Classical

/-- `matchingPoly_derivative_eq_sum_vertex_deletions` evaluated at a real number. -/
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (x : ℝ) :
    G.matchingPoly.derivative.eval x = ∑ v : V, ((G.induce {w | w ≠ v}).matchingPoly).eval x := by
  rw [matchingPoly_derivative_eq_sum_vertex_deletions G, Polynomial.eval_finsetSum]

/-- `treeLikeWalkCount_eq_trace_of_lt_egirth` applies to forests at every length. -/
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (k : ℕ) : G.treeLikeWalkCount k = (G.adjMatrix ℕ ^ k).trace :=
  treeLikeWalkCount_eq_trace_of_lt_egirth G k (by simp [hG.egirth_eq_top])

/-- `trace_hashimoto_pow` at order zero counts the trivial walk at each dart. -/
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ e : G.Dart, (Matrix.relWalks G.nbRel 0 e e).card) = Fintype.card G.Dart := by
  have h := trace_hashimoto_pow G ℤ 0
  simp only [pow_zero, Matrix.trace_one] at h
  exact_mod_cast h.symm

/-- `trace_sub_matchingPoly_root_power_sum_eq_trace_hashimoto` applies at the extended girth
whenever it equals a positive natural number. -/
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 0 < k) (hg : (k : ℕ∞) = G.egirth) :
    ((G.adjMatrix ℕ ^ k).trace : ℂ) - ((G.matchingPoly.map (algebraMap ℝ ℂ)).roots.map (· ^ k)).sum
      = (G.hashimoto ℂ ^ k).trace :=
  trace_sub_matchingPoly_root_power_sum_eq_trace_hashimoto G hk (by rw [hg]; exact le_self_add)

/-- `ihara_Nk_explicit` gives the positive Hashimoto traces by coefficient extraction over `ℚ`. -/
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    let X : Polynomial ℚ := Polynomial.X
    let vertexFactor : PowerSeries ℚ := ((1 - X ^ 2) ^ Fintype.card V : Polynomial ℚ)
    let edgeFactor : PowerSeries ℚ := ((1 - X ^ 2) ^ G.edgeFinset.card : Polynomial ℚ)
    let hashimotoDet : PowerSeries ℚ := (1 - X • (G.hashimoto ℚ).map Polynomial.C).det
    let bassDet : PowerSeries ℚ := (1 - X • (G.adjMatrix ℚ).map Polynomial.C
      + X ^ 2 • ((G.degMatrix ℚ - 1).map Polynomial.C)).det
    (G.hashimoto ℚ ^ (k + 1)).trace = PowerSeries.coeff k
      (PowerSeries.invOfUnit (vertexFactor * hashimotoDet) 1 *
        (hashimotoDet * PowerSeries.derivative vertexFactor - edgeFactor * PowerSeries.derivative bassDet -
          bassDet * PowerSeries.derivative edgeFactor)) := by
  simpa only [PowerSeries.coeff_mk] using congrArg (PowerSeries.coeff k) (ihara_Nk_explicit G ℚ)

/-- `matchingPoly_forest_eq_charpoly` identifies the matching polynomial of a tree with the
characteristic polynomial of its adjacency matrix. -/
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsTree) : G.matchingPoly = (G.adjMatrix ℝ).charpoly :=
  matchingPoly_forest_eq_charpoly G hG.isAcyclic

/-- `matchingPoly_splits` applies to the triangle, which has a cycle. -/
example : (⊤ : SimpleGraph (Fin 3)).matchingPoly.Splits :=
  matchingPoly_splits ⊤

/-- `matchingPoly_root_bound` gives the interval `[-2, 2]` when all degrees are at most two. -/
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 2) {x : ℝ} (hx : G.matchingPoly.IsRoot x) : |x| ≤ 2 := by
  simpa [show (2 : ℝ) - 1 = 1 by norm_num] using matchingPoly_root_bound G 2 (by decide) hdeg hx

/-- `godsil_pathTree_identity` gives a divisibility relation after deleting the starting vertex. -/
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (u : V) :
    G.matchingPoly ∣ (G.induce {v | v ≠ u}).matchingPoly * (G.pathTree u).matchingPoly :=
  ⟨((G.pathTree u).induce {r | r ≠ G.pathTreeRoot u}).matchingPoly,
    (godsil_pathTree_identity G u).symm⟩

/-- `matchingPoly_root_power_sum_eq_pathTree_walks` at order zero counts the trivial walk at each
vertex. Equivalently, the number of complex roots counted with multiplicity is the vertex count. -/
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((G.matchingPoly.map (algebraMap ℝ ℂ)).roots.card : ℂ) = Fintype.card V := by
  simpa [Matrix.one_apply] using matchingPoly_root_power_sum_eq_pathTree_walks G 0

/-- Pomerance: eventually more than half of the `n < x` have `n + 2 ∣ C(2n, n)`. -/
example : ∀ᶠ x : ℕ in atTop,
    (1 / 2 : ℝ) < (((Finset.range x).filter (fun n => n + 2 ∣ Nat.centralBinom n)).card : ℝ) / x :=
  (pomerance_density_add_dvd_centralBinom 2 (by norm_num)).eventually (lt_mem_nhds (by norm_num))

/-- Kirchhoff: the determinant of a reduced Laplacian over `ℤ` is nonnegative (it counts the
spanning trees). -/
example {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj] (v₀ : V) :
    0 ≤ ((G.lapMatrix ℤ).submatrix (Subtype.val : {v : V // v ≠ v₀} → V) Subtype.val).det := by
  rw [det_lapMatrix_submatrix_eq_card_spanningTrees ℤ G v₀]
  exact Int.natCast_nonneg _

/-- The Hall deficiency `δ(s) = |s| − |s.biUnion t|` is supermodular (the inequality behind the
Kőnig–Ore deficiency formula). -/
example (t : ℕ → Finset ℕ) (s u : Finset ℕ) :
    ((s.card : ℤ) - (s.biUnion t).card) + ((u.card : ℤ) - (u.biUnion t).card) ≤
      (((s ∪ u).card : ℤ) - ((s ∪ u).biUnion t).card) +
        (((s ∩ u).card : ℤ) - ((s ∩ u).biUnion t).card) := by
  have h1 := card_biUnion_submodular t s u
  have h2 := Finset.card_union_add_card_inter s u
  omega

/-- Under Hall's condition, the union of three tight sets is tight. -/
example (t : ℕ → Finset ℕ) (hall : ∀ v : Finset ℕ, v.card ≤ (v.biUnion t).card)
    (s u v : Finset ℕ) (hs : (s.biUnion t).card = s.card) (hu : (u.biUnion t).card = u.card)
    (hv : (v.biUnion t).card = v.card) :
    ((s ∪ u ∪ v).biUnion t).card = (s ∪ u ∪ v).card :=
  (card_biUnion_union_inter_eq_of_tight hall
    (card_biUnion_union_inter_eq_of_tight hall hs hu).1 hv).1

/-- Bondy: from a family of at most `|X|` distinct sets one element of `X` can be deleted without
losing any member, so the erased family has the same size. -/
example (X : Finset ℕ) (hX : X.Nonempty) (F : Finset (Finset ℕ)) (hF : F.card ≤ X.card) :
    ∃ x ∈ X, (F.image (fun A => A.erase x)).card = F.card := by
  obtain ⟨x, hx, hinj⟩ := bondy_exists_erase_injOn X hX F hF
  exact ⟨x, hx, Finset.card_image_of_injOn hinj⟩

/-- Godsil–Gutman for any graph: the average signed characteristic polynomial is `μ(G)`. -/
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ cfg : Sym2 V → Bool, (G.signingMatrix cfg).charpoly)
      = (Fintype.card (Sym2 V → Bool)) • G.matchingPoly :=
  godsil_gutman G

/-- Bass's formula over `ℤ` at `u = 2`. -/
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (1 - (2 : ℤ) ^ 2) ^ (Fintype.card V) * (1 - (2 : ℤ) • G.hashimoto ℤ).det
      = (1 - (2 : ℤ) ^ 2) ^ G.edgeFinset.card
        * (1 - (2 : ℤ) • G.adjMatrix ℤ + (2 : ℤ) ^ 2 • (G.degMatrix ℤ - 1)).det :=
  bass_determinant_commRing G ℤ 2

/-- Brégman for a `2 × 2` `(0,1)`-matrix. -/
example (A : Matrix (Fin 2) (Fin 2) ℕ) (hA : ∀ i j, A i j ≤ 1) :
    (A.permanent : ℝ) ≤ ∏ i, (((∑ j, A i j).factorial : ℕ) : ℝ) ^ ((1 : ℝ) / (∑ j, A i j : ℕ)) :=
  bregman_permanent_le 2 A hA

/-- De Bruijn–Erdős: locally 3-colourable graphs on `ℕ` are 3-colourable. -/
example (G : SimpleGraph ℕ) (h : ∀ s : Finset ℕ, (G.induce (↑s : Set ℕ)).Colorable 3) :
    G.Colorable 3 :=
  (colorable_iff_forall_finite_induce G 3).2 h

/-- Bruck–Ryser–Chowla: no finite projective plane has order `6` (`6 ≡ 2 mod 4`, `6` is not a sum of two
squares). -/
example (P L : Type*) [Membership P L] [Configuration.ProjectivePlane P L] [Finite P] [Finite L] :
    Configuration.ProjectivePlane.order P L ≠ 6 := by
  intro h6
  obtain ⟨a, b, hab⟩ := bruck_ryser_chowla P L (Or.inr (by rw [h6]))
  rw [h6] at hab
  have ha : a ≤ 2 := by nlinarith
  have hb : b ≤ 2 := by nlinarith
  interval_cases a <;> interval_cases b <;> omega

/-- The empty set is independent in the transversal matroid of any family. -/
example (A : Fin 2 → Finset ℕ) : (Theorems.TransversalMatroid.transversalMatroid A).Indep
    ((∅ : Finset ℕ) : Set ℕ) :=
  (transversalMatroid_indep A ∅).2 (Theorems.TransversalMatroid.partialTransversal_empty A)

/-- The oriented incidence matrix factors the Laplacian of a graph on `Fin 3` over `ℤ`. -/
example (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj] :
    G.orientedIncMatrix ℤ * (G.orientedIncMatrix ℤ).transpose = G.lapMatrix ℤ :=
  orientedIncMatrix_mul_transpose ℤ G

/-- Singmaster: the integer `2` occurs at most twice in Pascal's triangle. -/
example : {p : ℕ × ℕ | p.2 ≤ p.1 ∧ Nat.choose p.1 p.2 = 2}.ncard ≤ 2 := by
  have h := (ncard_choose_eq_le_two_mul_log 2 le_rfl).2
  have hl : Nat.log 2 2 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  rw [hl] at h
  simpa using h
