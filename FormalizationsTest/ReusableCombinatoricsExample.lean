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
