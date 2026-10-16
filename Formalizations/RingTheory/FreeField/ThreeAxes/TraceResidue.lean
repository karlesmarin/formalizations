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
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

/-!
# Residues along square-zero directions

Certificates for the residue / trace-direction mechanism in the three-axes problem.
Conventions: `Y_j = 1 + x_j` evaluated; `H0(Y) = [[Yx²+Yy², Yx²],[Yx², Yx²+Yz²]]`.

## Main results

* `polar`: `2×2` Cayley–Hamilton polarization `AB + BA = tr A • B + tr B • A + (tr(AB) − tr A tr B) • 1`;
  `polar_traceless`.
* `det_add_smul`: `det(A + εB) = det A + ε (tr A tr B − tr(AB)) + ε² det B`; `adjugate_add_smul`.
* `residue_sqzero`: `tr N = 0`, `det N = 0` ⇒ `det(N + εΔ) = ε (ε det Δ − tr(NΔ))` and
  `adj(N + εΔ) = −N + ε • adj Δ` (the residue does not see `tr Δ`); `inv_sub_one_sqzero`.
* `h4_general`: the determinant of `H0` at `A_j = τ_j • 1 + σ_j • N_j` in closed form.
* `arc_det`: an exact example along a square-zero arc.
* `witness`: an integer witness on the zero set of `det H0`, with `Y_j ∈ SL₂(ℤ)`.
-/

@[expose] public section

namespace ThreeAxes.TraceResidue

open Matrix

section General

variable {R : Type*} [CommRing R]

/-- (P) 2×2 Cayley–Hamilton polarization. -/
theorem polar (A B : Matrix (Fin 2) (Fin 2) R) :
    A * B + B * A = trace A • B + trace B • A + (trace (A * B) - trace A * trace B) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;> ring

/-- (P) traceless case. -/
theorem polar_traceless (N D : Matrix (Fin 2) (Fin 2) R) (hN : trace N = 0) :
    N * D + D * N = trace D • N + trace (N * D) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  rw [polar, hN]
  simp

/-- (D) determinant of a 2×2 pencil. -/
theorem det_add_smul (A B : Matrix (Fin 2) (Fin 2) R) (e : R) :
    det (A + e • B) = det A + e * (trace A * trace B - trace (A * B)) + e ^ 2 * det B := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- (D) the 2×2 adjugate is linear. -/
theorem adjugate_add_smul (A B : Matrix (Fin 2) (Fin 2) R) (e : R) :
    adjugate (A + e • B) = adjugate A + e • adjugate B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two] <;> ring

/-- (R) residue along a square-zero point: the leading term sees tr(NΔ), not tr Δ. -/
theorem residue_sqzero (N D : Matrix (Fin 2) (Fin 2) R) (e : R) (hT : trace N = 0) (hD : det N = 0) :
    det (N + e • D) = e * (e * det D - trace (N * D)) ∧ adjugate (N + e • D) = -N + e • adjugate D := by
  refine ⟨?_, ?_⟩
  · rw [det_add_smul, hT, hD]; ring
  · rw [adjugate_add_smul]
    congr 1
    have h : N 0 0 + N 1 1 = 0 := by simpa [Matrix.trace_fin_two] using hT
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two] <;> linear_combination h

/-- (R) inverse of X = N − 1 when N² = 0. -/
theorem inv_sub_one_sqzero (N : Matrix (Fin 2) (Fin 2) R) (h : N * N = 0) :
    (N - 1) * (-(1 + N)) = 1 := by
  noncomm_ring
  rw [h]; abel

/-- The square-zero rank-one matrix with kernel and image spanned by (a, b). -/
def Nsq (a b : R) : Matrix (Fin 2) (Fin 2) R := !![a * b, -a ^ 2; b ^ 2, -(a * b)]

theorem Nsq_sq (a b : R) : Nsq a b * Nsq a b = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Nsq, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- 3×3 determinant polynomial (same shape as `Matrix.det_fin_three`). -/
def d3 (a b c d e f g h i : R) : R := a*e*i - a*f*h - b*d*i + b*f*g + c*d*h - c*e*g

/-- Explicit 4×4 determinant: Laplace along row 0, minors by `d3`. -/
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

/-- 4×4 matrix [[A+B, A],[A, A+C]] built from 2×2 blocks. -/
def blk (A B C : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 4) (Fin 4) R :=
  !![A 0 0 + B 0 0, A 0 1 + B 0 1, A 0 0, A 0 1;
     A 1 0 + B 1 0, A 1 1 + B 1 1, A 1 0, A 1 1;
     A 0 0, A 0 1, A 0 0 + C 0 0, A 0 1 + C 0 1;
     A 1 0, A 1 1, A 1 0 + C 1 0, A 1 1 + C 1 1]

/-- (H) first coefficient of H0 along a trace-direction arc, general square-zero triple. -/
theorem h4_general (a0 b0 a1 b1 a2 b2 tx ty tz sx sy sz : R) :
    det (blk (tx • 1 + sx • Nsq a0 b0) (ty • 1 + sy • Nsq a1 b1) (tz • 1 + sz • Nsq a2 b2)) =
      (tx * ty + tx * tz + ty * tz) ^ 2
      + (a0 * b1 - a1 * b0) ^ 2 * tz ^ 2 * sx * sy
      + (a0 * b2 - a2 * b0) ^ 2 * ty ^ 2 * sx * sz
      + (a1 * b2 - a2 * b1) ^ 2 * tx ^ 2 * sy * sz := by
  rw [det4]
  simp [blk, Nsq, d3]
  ring

end General

section Example

/-- H0 as a 4×4 matrix. -/
def H0 {R : Type*} [CommRing R] (Yx Yy Yz : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 4) (Fin 4) R :=
  blk (Yx * Yx) (Yy * Yy) (Yz * Yz)

def Nx : Matrix (Fin 2) (Fin 2) ℚ := !![0, -1; 0, 0]
def Ny : Matrix (Fin 2) (Fin 2) ℚ := !![1, -1; 1, -1]
def Nz : Matrix (Fin 2) (Fin 2) ℚ := !![2, -1; 4, -2]

/-- (E) base point: square-zero and H0 = 0. -/
theorem base_point : Nx * Nx = 0 ∧ Ny * Ny = 0 ∧ Nz * Nz = 0 ∧ H0 Nx Ny Nz = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [Nx, Ny, Nz, H0, blk, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num)

/-- (E) residue of v6 (all τ_j = 1): Σ N_j + (1−Nx)(Ny+Nz)(1+Nx) + (1−Ny)Nx(1+Ny), with det 55. -/
theorem residue_v6 :
    Nx + Ny + Nz + (1 - Nx) * (Ny + Nz) * (1 + Nx) + (1 - Ny) * Nx * (1 + Ny) = !![11, -16; 11, -11] ∧
      det (!![11, -16; 11, -11] : Matrix (Fin 2) (Fin 2) ℚ) = 55 := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Nx, Ny, Nz, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> norm_num
  · simp [Matrix.det_fin_two]; norm_num

/-- (E) the arc Y_j = N_j + εΔ_j with Δx = !![σ, 0; −1, 0], Δy = !![0,0;−1,0], Δz = !![0,0;−3,1]. -/
def Yx (e s : ℚ) : Matrix (Fin 2) (Fin 2) ℚ := Nx + e • !![s, 0; -1, 0]
def Yy (e : ℚ) : Matrix (Fin 2) (Fin 2) ℚ := Ny + e • !![0, 0; -1, 0]
def Yz (e : ℚ) : Matrix (Fin 2) (Fin 2) ℚ := Nz + e • !![0, 0; -3, 1]

theorem arc_det (e s : ℚ) :
    det (H0 (Yx e s) (Yy e) (Yz e)) =
        e ^ 4 * (e ^ 2 * s ^ 2 - 4 * e * s + 2 * e + 4 * s + 9) ∧
      det (Yx e s) = -e ∧ det (Yy e) = -e ∧ det (Yz e) = -e := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [det4]
    simp [H0, blk, Yx, Yy, Yz, Nx, Ny, Nz, d3, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  all_goals simp [Yx, Yy, Yz, Nx, Ny, Nz, Matrix.det_fin_two]
  all_goals ring

end Example

section Witness

/-- (W) integer witness on Z(H0): Y_j ∈ SL₂(ℤ) (here over ℚ). -/
def Wx : Matrix (Fin 2) (Fin 2) ℚ := !![7, -1; 1, 0]
def Wy : Matrix (Fin 2) (Fin 2) ℚ := !![1, -1; 2, -1]
def Wz : Matrix (Fin 2) (Fin 2) ℚ := !![2, -1; 7, -3]
def Wxi : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; -1, 7]
def Wyi : Matrix (Fin 2) (Fin 2) ℚ := !![-1, 1; -2, 1]
def Wzi : Matrix (Fin 2) (Fin 2) ℚ := !![-3, 1; -7, 2]
/-- inverses of X_j = W_j − 1 -/
def Xxi : Matrix (Fin 2) (Fin 2) ℚ := !![1/5, -1/5; 1/5, -6/5]
def Xyi : Matrix (Fin 2) (Fin 2) ℚ := !![-1, 1/2; -1, 0]

/-- v6 = u⁻¹ + v⁻¹ + w⁻¹ + x v⁻¹ x⁻¹ + x w⁻¹ x⁻¹ + y u⁻¹ y⁻¹ evaluated at x_j = W_j − 1. -/
def v6W : Matrix (Fin 2) (Fin 2) ℚ :=
  Wxi + Wyi + Wzi + (Wx - 1) * Wyi * Xxi + (Wx - 1) * Wzi * Xxi + (Wy - 1) * Wxi * Xyi

theorem witness :
    (Wx * Wxi = 1 ∧ Wy * Wyi = 1 ∧ Wz * Wzi = 1) ∧
    ((Wx - 1) * Xxi = 1 ∧ (Wy - 1) * Xyi = 1 ∧ det (Wz - 1) = 3) ∧
    det (H0 Wx Wy Wz) = 0 ∧
    v6W = !![4/5, -43/10; 4/5, 56/5] ∧ det v6W = 62/5 := by
  have hv : v6W = !![4/5, -43/10; 4/5, 56/5] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Wx, Wy, Wxi, Wyi, Wzi, Xxi, Xyi, v6W, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.one_apply] <;> norm_num
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, hv, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Wx, Wxi, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Wy, Wyi, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Wz, Wzi, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Wx, Xxi, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Wy, Xyi, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
    norm_num
  · rw [Matrix.det_fin_two]
    simp [Wz]
    norm_num
  · rw [det4]
    simp [H0, blk, Wx, Wy, Wz, d3, Matrix.mul_apply, Fin.sum_univ_two]
    norm_num
  · rw [hv, Matrix.det_fin_two]
    simp
    norm_num

end Witness

end ThreeAxes.TraceResidue
