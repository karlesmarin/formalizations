/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.Combinatorics.SimpleGraph.Ihara.TraceFormula

/-!
# Bass's determinant formula over a commutative ring

Bass's formula `(1 - u²)^|V| · det(1 - u B) = (1 - u²)^|E| · det(1 - u A + u² (D - 1))` (`B` the
Hashimoto matrix on darts, `A` the adjacency matrix, `D` the degree matrix) for every commutative
ring `R` and every `u : R`. The identity is first obtained in `ℤ[X]`: its image in `ℚ[X]` is the
field case `bass_charpolyRev`, and `ℤ[X] → ℚ[X]` is injective. Evaluating `X ↦ u` through `ℤ → R`
then gives it in `R`.

## Main results

* `SimpleGraph.bass_determinant_commRing`: Bass's determinant formula over any commutative ring

## References

* C. Marín, *Folding Edges into Vertices: A Machine-Checked Proof of Bass's Determinant Formula for
  the Ihara Zeta Function in Lean 4*, Zenodo (2026), doi:10.5281/zenodo.20573120, `thm:bass`.
-/

@[expose] public section

open Matrix Polynomial

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

section BassCommRing

omit [Fintype V] [DecidableRel G.Adj] in
private theorem map_hashimoto' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (G.hashimoto R).map f = G.hashimoto S := by
  ext d e
  by_cases h : d.snd = e.fst ∧ e ≠ d.symm <;> simp [SimpleGraph.hashimoto, h]

omit [Fintype V] [DecidableEq V] in
private theorem map_adjMatrix' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (G.adjMatrix R).map f = G.adjMatrix S := by
  ext i j
  by_cases h : G.Adj i j <;> simp [SimpleGraph.adjMatrix_apply, h]

private theorem map_degMatrix' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (G.degMatrix R).map f = G.degMatrix S := by
  ext i j
  by_cases h : i = j <;> simp [SimpleGraph.degMatrix, h]

/-- **Bass's determinant formula over any commutative ring** (no field, no order on the vertices).
`(1 - u²)^|V| · det(1 - u B) = (1 - u²)^|E| · det(1 - u A + u² (D - 1))`, where `B` is the Hashimoto
(non-backtracking) matrix on darts, `A` the adjacency matrix and `D` the degree matrix. It is
deduced from the field case `bass_charpolyRev` (over `ℚ`) by descending to `ℤ[X]` and evaluating. -/
theorem bass_determinant_commRing (R : Type*) [CommRing R] (u : R) :
    (1 - u ^ 2) ^ (Fintype.card V) * (1 - u • G.hashimoto R).det
      = (1 - u ^ 2) ^ G.edgeFinset.card
        * (1 - u • G.adjMatrix R + u ^ 2 • (G.degMatrix R - 1)).det := by
  -- the identity in ℤ[X]
  have hZ : (1 - (X : ℤ[X]) ^ 2) ^ (Fintype.card V)
        * (1 - (X : ℤ[X]) • (G.hashimoto ℤ).map C).det
      = (1 - (X : ℤ[X]) ^ 2) ^ G.edgeFinset.card
        * (1 - (X : ℤ[X]) • (G.adjMatrix ℤ).map C
            + (X : ℤ[X]) ^ 2 • ((G.degMatrix ℤ - 1).map C)).det := by
    have : LinearOrder V :=
      LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
    have hQ := G.bass_charpolyRev ℚ
    apply Polynomial.map_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
    have e1 : ((1 - (X : ℤ[X]) • (G.hashimoto ℤ).map C : Matrix _ _ ℤ[X]).map
        (Polynomial.mapRingHom (Int.castRingHom ℚ))) = 1 - (X : ℚ[X]) • (G.hashimoto ℚ).map C := by
      refine Matrix.ext fun i j => ?_
      have := congrFun (congrFun (map_hashimoto' G (Int.castRingHom ℚ)) i) j
      simp only [Matrix.map_apply] at this
      by_cases h : i = j <;> simp [h]
      split_ifs <;> simp
    have e2 : ((1 - (X : ℤ[X]) • (G.adjMatrix ℤ).map C
            + (X : ℤ[X]) ^ 2 • ((G.degMatrix ℤ - 1).map C) : Matrix _ _ ℤ[X]).map
        (Polynomial.mapRingHom (Int.castRingHom ℚ)))
        = 1 - (X : ℚ[X]) • (G.adjMatrix ℚ).map C
            + (X : ℚ[X]) ^ 2 • ((G.degMatrix ℚ - 1).map C) := by
      refine Matrix.ext fun i j => ?_
      have h1 := congrFun (congrFun (map_adjMatrix' G (Int.castRingHom ℚ)) i) j
      have h2 := congrFun (congrFun (map_degMatrix' G (Int.castRingHom ℚ)) i) j
      simp only [Matrix.map_apply] at h1 h2
      rcases eq_or_ne i j with rfl | h <;> simp [Matrix.one_apply, ← h2]
      split_ifs <;> simp
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_one,
      Polynomial.map_X]
    have d1 := (Polynomial.mapRingHom (Int.castRingHom ℚ)).map_det
      (1 - (X : ℤ[X]) • (G.hashimoto ℤ).map C : Matrix _ _ ℤ[X])
    have d2 := (Polynomial.mapRingHom (Int.castRingHom ℚ)).map_det
      (1 - (X : ℤ[X]) • (G.adjMatrix ℤ).map C
            + (X : ℤ[X]) ^ 2 • ((G.degMatrix ℤ - 1).map C) : Matrix _ _ ℤ[X])
    rw [RingHom.mapMatrix_apply, e1] at d1
    rw [RingHom.mapMatrix_apply, e2] at d2
    simp only [Polynomial.coe_mapRingHom] at d1 d2
    rw [← d1, ← d2] at hQ
    exact hQ
  -- evaluate at u
  have := congrArg (Polynomial.eval₂RingHom (Int.castRingHom R) u) hZ
  have e1 : ((1 - (X : ℤ[X]) • (G.hashimoto ℤ).map C : Matrix _ _ ℤ[X]).map
      (Polynomial.eval₂RingHom (Int.castRingHom R) u)) = 1 - u • G.hashimoto R := by
    ext i j
    have h := congrFun (congrFun (map_hashimoto' G (Int.castRingHom R)) i) j
    simp only [Matrix.map_apply] at h
    by_cases hij : i = j <;> simp [hij]
    split_ifs <;> simp
  have e2 : ((1 - (X : ℤ[X]) • (G.adjMatrix ℤ).map C
            + (X : ℤ[X]) ^ 2 • ((G.degMatrix ℤ - 1).map C) : Matrix _ _ ℤ[X]).map
      (Polynomial.eval₂RingHom (Int.castRingHom R) u))
      = 1 - u • G.adjMatrix R + u ^ 2 • (G.degMatrix R - 1) := by
    ext i j
    have h1 := congrFun (congrFun (map_adjMatrix' G (Int.castRingHom R)) i) j
    have h2 := congrFun (congrFun (map_degMatrix' G (Int.castRingHom R)) i) j
    simp only [Matrix.map_apply, eq_intCast] at h1 h2
    have hc : ∀ n : ℤ, Polynomial.eval₂ (Int.castRingHom R) u (n : ℤ[X]) = (n : R) := by
      intro n
      exact map_intCast (Polynomial.eval₂RingHom (Int.castRingHom R) u) n
    rcases eq_or_ne i j with rfl | hij <;> simp [Matrix.one_apply, hc, h2]
    split_ifs <;> simp
  have d1 := (Polynomial.eval₂RingHom (Int.castRingHom R) u).map_det
    (1 - (X : ℤ[X]) • (G.hashimoto ℤ).map C : Matrix _ _ ℤ[X])
  have d2 := (Polynomial.eval₂RingHom (Int.castRingHom R) u).map_det
    (1 - (X : ℤ[X]) • (G.adjMatrix ℤ).map C
            + (X : ℤ[X]) ^ 2 • ((G.degMatrix ℤ - 1).map C) : Matrix _ _ ℤ[X])
  rw [RingHom.mapMatrix_apply, e1] at d1
  rw [RingHom.mapMatrix_apply, e2] at d2
  simp only [map_mul, map_pow, map_sub, map_one, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] at this d1 d2
  rw [d1, d2] at this
  simpa using this

end BassCommRing

end SimpleGraph
