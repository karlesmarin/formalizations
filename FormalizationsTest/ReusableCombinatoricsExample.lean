/-
Usage example of the reusable layer, area Combinatorics, with the minimal import of that area: the
same code a user pastes into a file of their own project (README, section "Reusable layer").
-/
import Formalizations.Reusable.Combinatorics

open Formalizations.Reusable Filter Topology

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
