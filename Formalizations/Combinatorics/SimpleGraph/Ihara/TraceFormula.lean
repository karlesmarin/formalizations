/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Formalizations.Combinatorics.SimpleGraph.Ihara.Bass
public import Formalizations.LinearAlgebra.Matrix.Charpoly.Jacobi

/-!
# The Ihara trace generating function

Combining Bass's determinant formula with Jacobi's formula and Newton's identity for traces
(`Matrix.derivative_coe_charpolyRev`), the generating function `∑ₖ tr(Bᵏ⁺¹) Xᵏ` of the traces of
the powers of the non-backtracking operator `B` is expressed through the adjacency and degree
matrices. The traces `tr(Bᵏ)` count closed non-backtracking walks of length `k`.

## Main results

* `SimpleGraph.trace_adjMatrix_pow`: `tr(Aᵏ)` is the number of closed walks of length `k`.
* `SimpleGraph.bass_charpolyRev`: Bass's formula as an identity in `R[X]`.
* `SimpleGraph.derivative_bass`: its derivative (Jacobi's formula on both sides).
* `SimpleGraph.ihara_Nk_isolated`, `SimpleGraph.ihara_Nk_explicit`: the generating function of
  `tr(Bᵏ⁺¹)` in terms of `A` and `D`.
* `SimpleGraph.ihara_Nk_genfn`: `d⁄dX (charpolyRev B) = - charpolyRev B · ∑ₖ tr(Bᵏ⁺¹) Xᵏ`.

## References

* H. Bass, *The Ihara–Selberg zeta function of a tree lattice*, Internat. J. Math. 3 (1992)
  717–797.
* A. Terras, *Zeta Functions of Graphs: A Stroll through the Garden*, Cambridge University Press,
  2011.
-/

@[expose] public section

/-! ## The trace generating function

A general-matrix interlude, independent of graphs. The **resolvent series** `∑ₖ Mᵏ Xᵏ`, viewed as a
matrix of formal power series, is the formal inverse of `1 - X•M`, and its trace is the trace
generating function `∑ₖ tr(Mᵏ) Xᵏ`. Everything here is eigenvalue-free and over an arbitrary
`CommRing` — the half of the Newton/trace-generating-function bridge that needs no determinant.
The determinant half is Jacobi's formula `(det F)′ = tr(adj F · F′)`, proved below in `derivative_det`;
together they will tie the trace power sums to `charpolyRev` and so to Bass's identity
(`bass_charpolyRev`). -/
open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Piece 1 of the trace formula.** The trace of the `k`-th power of the adjacency matrix counts
the closed walks of length `k`: `tr(Aᵏ) = Σ_v #{closed walks of length k at v}`. -/
theorem trace_adjMatrix_pow (k : ℕ) :
    (G.adjMatrix ℕ ^ k).trace = ∑ v : V, #(G.finsetWalkLength k v v) := by
  simp only [Matrix.trace, Matrix.diag_apply]
  exact Finset.sum_congr rfl fun v _ => by
    rw [adjMatrix_pow_apply_eq_card_walk, Nat.cast_id, card_set_walk_length_eq]

open Polynomial Matrix

section Spectral
variable (R : Type*) [CommRing R]

/-- Evaluating the determinant of a polynomial-matrix at `u` = determinant of the matrix with
each entry evaluated at `u` (the eval ring-hom commutes with `det`). -/
private theorem eval_det_eq (u : R) (P : Matrix V V R[X]) :
    (P.det).eval u = (P.map (Polynomial.evalRingHom u)).det :=
  (Polynomial.evalRingHom u).map_det P

omit [Fintype V] [DecidableRel G.Adj] in
/-- The Hashimoto polynomial-matrix `1 - X•B`, evaluated at `u`, is `1 - u•B`. -/
private theorem map_eval_hashimoto (u : R) :
    (1 - (X : R[X]) • (G.hashimoto R).map C).map (Polynomial.evalRingHom u)
      = 1 - u • G.hashimoto R := by
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, Polynomial.coe_evalRingHom, apply_ite (eval u),
    eval_sub, eval_mul, eval_X, eval_C, eval_one, eval_zero]

/-- The A/D polynomial-matrix `1 - X•A + X²•(D-1)`, evaluated at `u`, is `1 - u•A + u²•(D-1)`. -/
private theorem map_eval_adj (u : R) :
    (1 - (X : R[X]) • (G.adjMatrix R).map C + (X : R[X]) ^ 2 • ((G.degMatrix R - 1).map C)).map
        (Polynomial.evalRingHom u)
      = 1 - u • G.adjMatrix R + u ^ 2 • (G.degMatrix R - 1) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, Polynomial.coe_evalRingHom, apply_ite (eval u),
    eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_one, eval_zero]

end Spectral

section SpectralField
variable (R : Type*) [Field R] [Infinite R] [LinearOrder V]

/-- **Piece 2 — Bass as a polynomial identity (the charpoly form).** Lifting `bass_determinant`
(pointwise over an infinite field) to an identity in `R[X]`, with the non-backtracking side
expressed through `Matrix.charpolyRev B = det(1 - X•B)`. This is the foundation for extracting the
non-backtracking trace counts `N_k = tr(Bᵏ)` from the adjacency data. -/
theorem bass_charpolyRev :
    (1 - (X : R[X]) ^ 2) ^ (Fintype.card V) * (1 - (X : R[X]) • (G.hashimoto R).map C).det
      = (1 - (X : R[X]) ^ 2) ^ G.edgeFinset.card
        * (1 - (X : R[X]) • (G.adjMatrix R).map C
            + (X : R[X]) ^ 2 • ((G.degMatrix R - 1).map C)).det := by
  refine Polynomial.funext fun u => ?_
  simp only [eval_mul, eval_pow, eval_sub, eval_one, eval_X, eval_det_eq,
    map_eval_hashimoto, map_eval_adj]
  exact G.bass_determinant R u

/-- **The differentiated Bass identity** — composing Bass with Jacobi (lemma 1). Applying `d/dX` to
Bass's determinant formula and expanding both determinant derivatives by Jacobi's formula
(`Matrix.derivative_det`): the non-backtracking side `(1-X²)^|V|·det(1-X·B)` and the adjacency side
`(1-X²)^|E|·det(1-X·A+X²(D-1))` have equal derivatives, term by term. This is the polynomial heart of
the Ihara `N_k` spectral formula — the trace generating functions arise on dividing through by the
two determinants (both units in `R⟦X⟧`). -/
theorem derivative_bass :
    derivative ((1 - (X : R[X]) ^ 2) ^ Fintype.card V)
        * (1 - (X : R[X]) • (G.hashimoto R).map C).det
      + (1 - (X : R[X]) ^ 2) ^ Fintype.card V
        * ((1 - (X : R[X]) • (G.hashimoto R).map C).adjugate
          * (1 - (X : R[X]) • (G.hashimoto R).map C).map derivative).trace
    = derivative ((1 - (X : R[X]) ^ 2) ^ G.edgeFinset.card)
        * (1 - (X : R[X]) • (G.adjMatrix R).map C
            + (X : R[X]) ^ 2 • ((G.degMatrix R - 1).map C)).det
      + (1 - (X : R[X]) ^ 2) ^ G.edgeFinset.card
        * ((1 - (X : R[X]) • (G.adjMatrix R).map C
            + (X : R[X]) ^ 2 • ((G.degMatrix R - 1).map C)).adjugate
          * (1 - (X : R[X]) • (G.adjMatrix R).map C
            + (X : R[X]) ^ 2 • ((G.degMatrix R - 1).map C)).map derivative).trace := by
  have h := congrArg derivative (G.bass_charpolyRev R)
  rwa [derivative_mul, derivative_mul, Matrix.derivative_det, Matrix.derivative_det] at h

open scoped PowerSeries in
/-- **The isolated Ihara `N_k` identity** (cleared form). Differentiating Bass's identity in `R⟦X⟧`
and substituting Newton's identity for matrix traces (`Matrix.derivative_coe_charpolyRev`) on the
non-backtracking side isolates the `N_k = tr(Bᵏ)` generating function, expressed through the
adjacency data `Q = det(1 - X·A + X²(D-1))`:
`(1-X²)^|V| · det(1-X·B) · ∑ₖ tr(Bᵏ⁺¹)Xᵏ = det(1-X·B)·((1-X²)^|V|)′ - (1-X²)^|E|·Q′ - Q·((1-X²)^|E|)′`.
The two `(1-X²)`-powers and the determinants are units in `R⟦X⟧`, so dividing through gives the
generating function `∑ₖ N_{k+1} Xᵏ` purely in terms of the adjacency spectrum. -/
theorem ihara_Nk_isolated :
    (((1 - (X : R[X]) ^ 2) ^ Fintype.card V : R[X]) : R⟦X⟧)
        * ((1 - (X : R[X]) • (G.hashimoto R).map C).det : R⟦X⟧)
        * PowerSeries.mk (fun k => ((G.hashimoto R) ^ (k + 1)).trace)
      = ((1 - (X : R[X]) • (G.hashimoto R).map C).det : R⟦X⟧)
          * d⁄dX (((1 - (X : R[X]) ^ 2) ^ Fintype.card V : R[X]) : R⟦X⟧)
        - (((1 - (X : R[X]) ^ 2) ^ G.edgeFinset.card : R[X]) : R⟦X⟧)
          * d⁄dX ((1 - (X : R[X]) • (G.adjMatrix R).map C
              + (X : R[X]) ^ 2 • ((G.degMatrix R - 1).map C)).det : R⟦X⟧)
        - ((1 - (X : R[X]) • (G.adjMatrix R).map C
              + (X : R[X]) ^ 2 • ((G.degMatrix R - 1).map C)).det : R⟦X⟧)
          * d⁄dX (((1 - (X : R[X]) ^ 2) ^ G.edgeFinset.card : R[X]) : R⟦X⟧) := by
  have hbass := congrArg Polynomial.coeToPowerSeries.ringHom (G.bass_charpolyRev R)
  rw [map_mul, map_mul] at hbass
  simp only [Polynomial.coeToPowerSeries.ringHom_apply] at hbass
  have hN : d⁄dX ((1 - (X : R[X]) • (G.hashimoto R).map C).det : R⟦X⟧)
      = -((1 - (X : R[X]) • (G.hashimoto R).map C).det : R⟦X⟧)
        * PowerSeries.mk (fun k => ((G.hashimoto R) ^ (k + 1)).trace) :=
    Matrix.derivative_coe_charpolyRev (G.hashimoto R)
  have hd := congrArg (⇑(PowerSeries.derivative (R := R))) hbass
  rw [Derivation.leibniz, Derivation.leibniz, hN] at hd
  simp only [smul_eq_mul] at hd
  linear_combination -hd

open scoped PowerSeries in
/-- **The explicit Ihara `N_k` generating function.** Dividing `ihara_Nk_isolated` through by the
unit `(1-X²)^|V|·det(1-X·B)` (constant term `1`, inverted by `PowerSeries.invOfUnit`) yields the
non-backtracking trace power sums `∑ₖ tr(Bᵏ⁺¹) Xᵏ` explicitly in terms of the adjacency spectrum. -/
theorem ihara_Nk_explicit :
    PowerSeries.mk (fun k => ((G.hashimoto R) ^ (k + 1)).trace)
      = PowerSeries.invOfUnit
          ((((1 - (X : R[X]) ^ 2) ^ Fintype.card V : R[X]) : R⟦X⟧)
            * ((1 - (X : R[X]) • (G.hashimoto R).map C).det : R⟦X⟧)) 1
        * (((1 - (X : R[X]) • (G.hashimoto R).map C).det : R⟦X⟧)
            * d⁄dX (((1 - (X : R[X]) ^ 2) ^ Fintype.card V : R[X]) : R⟦X⟧)
          - (((1 - (X : R[X]) ^ 2) ^ G.edgeFinset.card : R[X]) : R⟦X⟧)
            * d⁄dX ((1 - (X : R[X]) • (G.adjMatrix R).map C
                + (X : R[X]) ^ 2 • ((G.degMatrix R - 1).map C)).det : R⟦X⟧)
          - ((1 - (X : R[X]) • (G.adjMatrix R).map C
                + (X : R[X]) ^ 2 • ((G.degMatrix R - 1).map C)).det : R⟦X⟧)
            * d⁄dX (((1 - (X : R[X]) ^ 2) ^ G.edgeFinset.card : R[X]) : R⟦X⟧)) := by
  have hcc : PowerSeries.constantCoeff
      ((((1 - (X : R[X]) ^ 2) ^ Fintype.card V : R[X]) : R⟦X⟧)
        * ((1 - (X : R[X]) • (G.hashimoto R).map C).det : R⟦X⟧)) = ((1 : Rˣ) : R) := by
    rw [map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, Polynomial.coeff_coe,
      Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_eq_eval_zero, eval_det_eq,
      map_eval_hashimoto, Units.val_one]
    simp
  have key : PowerSeries.invOfUnit
      ((((1 - (X : R[X]) ^ 2) ^ Fintype.card V : R[X]) : R⟦X⟧)
        * ((1 - (X : R[X]) • (G.hashimoto R).map C).det : R⟦X⟧)) 1
      * ((((1 - (X : R[X]) ^ 2) ^ Fintype.card V : R[X]) : R⟦X⟧)
        * ((1 - (X : R[X]) • (G.hashimoto R).map C).det : R⟦X⟧)) = 1 := by
    rw [mul_comm]; exact PowerSeries.mul_invOfUnit _ 1 hcc
  rw [← G.ihara_Nk_isolated R, ← mul_assoc, key, one_mul]

end SpectralField

section Ihara
open scoped PowerSeries
variable (R : Type*) [CommRing R]

/-- **The Ihara `N_k` generating function.** Specialising Newton's identity for matrix traces
(`Matrix.derivative_coe_charpolyRev`) to the Hashimoto non-backtracking operator `B = G.hashimoto R`: the
logarithmic derivative of the reciprocal Ihara zeta `det(1 - X·B) = charpolyRev B` generates the
non-backtracking closed-walk counts `N_{k+1} = tr(B^{k+1})`,
`(det(1 - X·B))′ = -det(1 - X·B) · ∑ₖ N_{k+1} Xᵏ`. -/
theorem ihara_Nk_genfn :
    d⁄dX (charpolyRev (G.hashimoto R) : R⟦X⟧)
      = -(charpolyRev (G.hashimoto R) : R⟦X⟧)
        * PowerSeries.mk fun k => ((G.hashimoto R) ^ (k + 1)).trace :=
  Matrix.derivative_coe_charpolyRev (G.hashimoto R)

end Ihara

end SimpleGraph
