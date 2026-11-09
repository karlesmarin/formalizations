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
