/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.LinearAlgebra.Matrix.FinTwo
public import Formalizations.RingTheory.FreeField.ThreeAxes.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination

/-!
# Degenerate residues in the three-axes problem

Finite identities behind the degenerate-residue analysis of `s = u⁻² + v⁻² + w⁻²` in the free
field of `F₃` (`u = 1 + x`, `v = 1 + y`, `w = 1 + z`). All matrices are `2×2` over a commutative
ring unless stated.

## Main results

* `sandwich`: `M A M = tr(A M) • M − det M • adj A`; hence, for `det M = 0`,
  `annihilator_left`: `(M A M B − M B M A) M = 0` and `annihilator_right`.
* `det_add_adj`: `det(A + B) = det A + tr(adj A · B) + det B`.
* `adj_sq_leading`, `inv_target`: the leading coefficient of `s` along `Y = N + εΔ` with `N`
  square-zero: `adj(N + εΔ)² = ε • (τ • 1 − σ • N) + ε² • (adj Δ)²`.
* `realization_det`: `det [[A+B, A],[A, A+C]] · (det A det B det C)
  = det(det B det C • adj A + det A det C • adj B + det A det B • adj C)`.
* `D2`, `D3`, `comm2_det`, `comm3`: iterated conjugation differences at `x = N − 1`.
* `F2_witness`: an explicit rational witness with nonzero determinant.

`sandwich`, `det_add_adj`, `comm2_det` and `comm3` are restatements of the `2 × 2` identities of
`Formalizations.LinearAlgebra.Matrix.FinTwo` (`cm` is `⁅·, ·⁆`, `disc` is `Matrix.discr`);
`blk`, `det4`, `Nsq` and the witness matrices are in
`Formalizations.RingTheory.FreeField.ThreeAxes.Basic`.
-/

@[expose] public section

namespace ThreeAxes.DegenerateResidue

open Matrix

section General

variable {R : Type*} [CommRing R]

/-- (S) sandwich identity for 2×2 matrices
(`Matrix.mul_mul_eq_trace_smul_sub_det_smul_adjugate_fin_two`). -/
theorem sandwich (M A : M2 R) :
    M * A * M = trace (A * M) • M - det M • adjugate A :=
  mul_mul_eq_trace_smul_sub_det_smul_adjugate_fin_two M A

theorem annihilator_left (M A B : M2 R) (h : det M = 0) :
    (M * A * M * B - M * B * M * A) * M = 0 := by
  have hA := sandwich M A
  have hB := sandwich M B
  rw [h, zero_smul, sub_zero] at hA hB
  have e1 : M * A * M * B * M = trace (A * M) • (M * B * M) := by
    rw [hA]; simp [Matrix.mul_assoc]
  have e2 : M * B * M * A * M = trace (B * M) • (M * A * M) := by
    rw [hB]; simp [Matrix.mul_assoc]
  rw [sub_mul, e1, e2, hA, hB, smul_smul, smul_smul, mul_comm, sub_self]

theorem annihilator_right (M A B : M2 R) (h : det M = 0) :
    M * (A * M * B * M - B * M * A * M) = 0 := by
  have hA := sandwich M A
  have hB := sandwich M B
  rw [h, zero_smul, sub_zero] at hA hB
  have e1 : M * (A * M * B * M) = trace (A * M) • (M * B * M) := by
    rw [show M * (A * M * B * M) = (M * A * M) * B * M by simp [Matrix.mul_assoc], hA]
    simp [Matrix.mul_assoc]
  have e2 : M * (B * M * A * M) = trace (B * M) • (M * A * M) := by
    rw [show M * (B * M * A * M) = (M * B * M) * A * M by simp [Matrix.mul_assoc], hB]
    simp [Matrix.mul_assoc]
  rw [Matrix.mul_sub, e1, e2, hA, hB, smul_smul, smul_smul, mul_comm, sub_self]

/-- (C) determinant of a sum, 2×2 (`Matrix.det_add_fin_two`). -/
theorem det_add_adj (A B : M2 R) :
    det (A + B) = det A + trace (adjugate A * B) + det B :=
  det_add_fin_two A B

/-- (L) square of the adjugate along the arc: the ε⁰ term vanishes and the ε¹ term is τI − σN. -/
theorem adj_sq_leading (a b e : R) (D : M2 R) :
    adjugate (Nsq a b + e • D) ^ 2 =
      e • (trace (Nsq a b * D) • (1 : M2 R) - trace D • Nsq a b) + e ^ 2 • (adjugate D) ^ 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Nsq, sq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.adjugate_fin_two,
      Matrix.vecMul, dotProduct] <;> ring

theorem inv_target (a b t s : R) :
    (t • (1 : M2 R) + s • Nsq a b) * (t • (1 : M2 R) - s • Nsq a b) = t ^ 2 • (1 : M2 R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Nsq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring

/-- (H) realization identity, inverse-free form. -/
theorem realization_det (A B C : M2 R) :
    det (blk A B C) * (det A * det B * det C) =
      det ((det B * det C) • adjugate A + (det A * det C) • adjugate B + (det A * det B) • adjugate C) := by
  rw [det4]
  simp [blk, d3, Matrix.det_fin_two, Matrix.adjugate_fin_two]
  ring

/-- (D) conjugation differences at x = N − 1 with N = Nsq a b. -/
def Dx (a b : R) (T : M2 R) : M2 R := T - (Nsq a b - 1) * T * (-(1 + Nsq a b))

theorem D2 (a b : R) (T : M2 R) : Dx a b (Dx a b T) = (-2 : R) • (Nsq a b * T * Nsq a b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Dx, Nsq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.sub_apply,
      Matrix.vecMul, dotProduct] <;> ring

theorem D3 (a b : R) (T : M2 R) : Dx a b (Dx a b (Dx a b T)) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Dx, Nsq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.sub_apply] <;> ring

def cm (X T : M2 R) : M2 R := X * T - T * X
def disc (X : M2 R) : R := trace X ^ 2 - 4 * det X

/-- `cm` is the ring commutator `⁅X, T⁆`. -/
theorem cm_eq_lie (X T : M2 R) : cm X T = ⁅X, T⁆ := (Ring.lie_def X T).symm

/-- `disc` is Mathlib's `Matrix.discr` (`Matrix.discr_fin_two`). -/
theorem disc_eq_discr (X : M2 R) : disc X = discr X := (discr_fin_two X).symm

/-- `Matrix.det_lie_lie_eq_neg_discr_mul_det_lie_fin_two`, written with `cm` and `disc`. -/
theorem comm2_det (X T : M2 R) : det (cm X (cm X T)) = -(disc X) * det (cm X T) := by
  simp only [cm_eq_lie, disc_eq_discr]
  exact det_lie_lie_eq_neg_discr_mul_det_lie_fin_two X T

/-- `Matrix.lie_lie_lie_eq_discr_smul_lie_fin_two`, written with `cm` and `disc`. -/
theorem comm3 (X T : M2 R) : cm X (cm X (cm X T)) = disc X • cm X T := by
  simp only [cm_eq_lie, disc_eq_discr]
  exact lie_lie_lie_eq_discr_smul_lie_fin_two X T

end General

section Witness

/-- h = y u⁻¹ y⁻¹ + v⁻¹ + w⁻¹ at W; Dw = conjugation difference by x = Wx − 1. -/
def hW : Matrix (Fin 2) (Fin 2) ℚ := (Wy - 1) * Wxi * Xyi + Wyi + Wzi
def Dw (T : Matrix (Fin 2) (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ := T - (Wx - 1) * T * Xxi

theorem F2_witness :
    ((Wx - 1) * Xxi = 1 ∧ (Wy - 1) * Xyi = 1 ∧ Wx * Wxi = 1 ∧ Wy * Wyi = 1 ∧ Wz * Wzi = 1) ∧
    Dw (Dw hW) = !![-203/10, 704/5; -13/10, 203/10] ∧
    det (!![-203/10, 704/5; -13/10, 203/10] : Matrix (Fin 2) (Fin 2) ℚ) = -4581/20 := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals first
    | (ext i j; fin_cases i <;> fin_cases j <;>
        simp [Wx, Wy, Wz, Wxi, Wyi, Wzi, Xxi, Xyi, hW, Dw, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.one_apply, Matrix.sub_apply, Matrix.add_apply] <;> norm_num)
    | (simp [Matrix.det_fin_two]; norm_num)

end Witness

end ThreeAxes.DegenerateResidue
