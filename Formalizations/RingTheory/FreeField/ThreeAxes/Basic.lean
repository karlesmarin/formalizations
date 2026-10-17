/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

/-!
# Common definitions for the three-axes files

Definitions shared by `Extractors`, `TraceResidue` and `DegenerateResidue`.

## Main definitions and results

* `M2 R`: `2 × 2` matrices over `R`.
* `d3`, `det4`: an explicit `4 × 4` determinant (Laplace along row `0`, `3 × 3` minors written out
  as `d3`, the polynomial of Mathlib's `Matrix.det_fin_three`). Mathlib has `det_fin_two` and
  `det_fin_three` but no `4 × 4` analogue.
* `blk A B C`: the `4 × 4` matrix `[[A + B, A], [A, A + C]]` built from `2 × 2` blocks.
* `Nsq a b`: the square-zero rank-one matrix with kernel and image spanned by `(a, b)`; `Nsq_sq`.
* `Wx`, `Wy`, `Wz` (and the inverses `Wxi`, `Wyi`, `Wzi`, `Xxi`, `Xyi`): the integer witness
  matrices used in `TraceResidue.witness` and `DegenerateResidue.F2_witness`.
-/

@[expose] public section

namespace ThreeAxes

open Matrix

section General

variable {R : Type*} [CommRing R]

/-- `2 × 2` matrices over `R`. -/
abbrev M2 (R : Type*) [CommRing R] := Matrix (Fin 2) (Fin 2) R

/-- `3 × 3` determinant polynomial (same shape as `Matrix.det_fin_three`). -/
def d3 (a b c d e f g h i : R) : R := a*e*i - a*f*h - b*d*i + b*f*g + c*d*h - c*e*g

/-- Explicit `4 × 4` determinant: Laplace along row `0`, minors by `d3`. -/
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

/-- The `4 × 4` matrix `[[A + B, A], [A, A + C]]` built from `2 × 2` blocks. -/
def blk (A B C : M2 R) : Matrix (Fin 4) (Fin 4) R :=
  !![A 0 0 + B 0 0, A 0 1 + B 0 1, A 0 0, A 0 1;
     A 1 0 + B 1 0, A 1 1 + B 1 1, A 1 0, A 1 1;
     A 0 0, A 0 1, A 0 0 + C 0 0, A 0 1 + C 0 1;
     A 1 0, A 1 1, A 1 0 + C 1 0, A 1 1 + C 1 1]

/-- The square-zero rank-one matrix with kernel and image spanned by `(a, b)`. -/
def Nsq (a b : R) : M2 R := !![a * b, -a ^ 2; b ^ 2, -(a * b)]

theorem Nsq_sq (a b : R) : Nsq a b * Nsq a b = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Nsq, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end General

section Witness

/-- Integer witness matrices `W_j ∈ SL₂(ℤ)` (over `ℚ`), with inverses `W_j⁻¹` and the inverses of
`W_j − 1` for `j = x, y`. -/
def Wx : Matrix (Fin 2) (Fin 2) ℚ := !![7, -1; 1, 0]
def Wy : Matrix (Fin 2) (Fin 2) ℚ := !![1, -1; 2, -1]
def Wz : Matrix (Fin 2) (Fin 2) ℚ := !![2, -1; 7, -3]
def Wxi : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; -1, 7]
def Wyi : Matrix (Fin 2) (Fin 2) ℚ := !![-1, 1; -2, 1]
def Wzi : Matrix (Fin 2) (Fin 2) ℚ := !![-3, 1; -7, 2]
def Xxi : Matrix (Fin 2) (Fin 2) ℚ := !![1/5, -1/5; 1/5, -6/5]
def Xyi : Matrix (Fin 2) (Fin 2) ℚ := !![-1, 1/2; -1, 0]

end Witness

end ThreeAxes
