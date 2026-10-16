/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

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
-/

@[expose] public section

namespace ThreeAxes.DegenerateResidue

open Matrix

section General

variable {R : Type*} [CommRing R]

abbrev M2 (R : Type*) [CommRing R] := Matrix (Fin 2) (Fin 2) R

/-- (S) sandwich identity for 2×2 matrices. -/
theorem sandwich (M A : M2 R) :
    M * A * M = trace (A * M) • M - det M • adjugate A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two,
      Matrix.adjugate_fin_two] <;> ring

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

/-- (C) determinant of a sum, 2×2. -/
theorem det_add_adj (A B : M2 R) :
    det (A + B) = det A + trace (adjugate A * B) + det B := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.adjugate_fin_two,
    Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  ring

/-- Square-zero rank-one matrix with kernel and image spanned by (a, b). -/
def Nsq (a b : R) : M2 R := !![a * b, -a ^ 2; b ^ 2, -(a * b)]

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

/-- 3×3 determinant polynomial. -/
def d3 (a b c d e f g h i : R) : R := a*e*i - a*f*h - b*d*i + b*f*g + c*d*h - c*e*g

theorem det4 (A : Matrix (Fin 4) (Fin 4) R) : det A =
    A 0 0 * d3 (A 1 1) (A 1 2) (A 1 3) (A 2 1) (A 2 2) (A 2 3) (A 3 1) (A 3 2) (A 3 3)
  - A 0 1 * d3 (A 1 0) (A 1 2) (A 1 3) (A 2 0) (A 2 2) (A 2 3) (A 3 0) (A 3 2) (A 3 3)
  + A 0 2 * d3 (A 1 0) (A 1 1) (A 1 3) (A 2 0) (A 2 1) (A 2 3) (A 3 0) (A 3 1) (A 3 3)
  - A 0 3 * d3 (A 1 0) (A 1 1) (A 1 2) (A 2 0) (A 2 1) (A 2 2) (A 3 0) (A 3 1) (A 3 2) := by
  rw [det_succ_row_zero]
  simp only [Fin.sum_univ_four, det_fin_three, submatrix_apply, d3]
  have e1 : (Fin.succAbove (1 : Fin 4) 2 : Fin 4) = 3 := rfl
  have e2 : (Fin.succAbove (2 : Fin 4) 2 : Fin 4) = 3 := rfl
  have e3 : (Fin.succAbove (3 : Fin 4) 2 : Fin 4) = 2 := rfl
  have e4 : (Fin.succAbove (2 : Fin 4) 1 : Fin 4) = 1 := rfl
  have e5 : (Fin.succAbove (3 : Fin 4) 1 : Fin 4) = 1 := rfl
  have e6 : (Fin.succAbove (1 : Fin 4) 1 : Fin 4) = 2 := rfl
  have e7 : (Fin.succAbove (0 : Fin 4) 2 : Fin 4) = 3 := rfl
  have e8 : (Fin.succAbove (0 : Fin 4) 1 : Fin 4) = 2 := rfl
  have e9 : (Fin.succAbove (0 : Fin 4) 0 : Fin 4) = 1 := rfl
  have f1 : (Fin.succAbove (1 : Fin 4) 0 : Fin 4) = 0 := rfl
  have f2 : (Fin.succAbove (2 : Fin 4) 0 : Fin 4) = 0 := rfl
  have f3 : (Fin.succAbove (3 : Fin 4) 0 : Fin 4) = 0 := rfl
  have g0 : (Fin.succ (0 : Fin 3) : Fin 4) = 1 := rfl
  have g1 : (Fin.succ (1 : Fin 3) : Fin 4) = 2 := rfl
  have g2 : (Fin.succ (2 : Fin 3) : Fin 4) = 3 := rfl
  simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, f1, f2, f3, g0, g1, g2]
  norm_num
  ring

def blk (A B C : M2 R) : Matrix (Fin 4) (Fin 4) R :=
  !![A 0 0 + B 0 0, A 0 1 + B 0 1, A 0 0, A 0 1;
     A 1 0 + B 1 0, A 1 1 + B 1 1, A 1 0, A 1 1;
     A 0 0, A 0 1, A 0 0 + C 0 0, A 0 1 + C 0 1;
     A 1 0, A 1 1, A 1 0 + C 1 0, A 1 1 + C 1 1]

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

theorem comm2_det (X T : M2 R) : det (cm X (cm X T)) = -(disc X) * det (cm X T) := by
  simp [cm, disc, Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem comm3 (X T : M2 R) : cm X (cm X (cm X T)) = disc X • cm X T := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cm, disc, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two,
      Matrix.sub_apply] <;> ring

end General

section Witness

def Wx : Matrix (Fin 2) (Fin 2) ℚ := !![7, -1; 1, 0]
def Wy : Matrix (Fin 2) (Fin 2) ℚ := !![1, -1; 2, -1]
def Wz : Matrix (Fin 2) (Fin 2) ℚ := !![2, -1; 7, -3]
def Wxi : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; -1, 7]
def Wyi : Matrix (Fin 2) (Fin 2) ℚ := !![-1, 1; -2, 1]
def Wzi : Matrix (Fin 2) (Fin 2) ℚ := !![-3, 1; -7, 2]
def Xxi : Matrix (Fin 2) (Fin 2) ℚ := !![1/5, -1/5; 1/5, -6/5]
def Xyi : Matrix (Fin 2) (Fin 2) ℚ := !![-1, 1/2; -1, 0]

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
