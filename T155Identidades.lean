/-
Author: Carles Marín (with Claude as AI assistant).

T155Identidades: finite identities behind T154–T156 and the evening of 15-oct (atiyah-l2, 3XX).

* (B) `blk_det_formula`: det [[A+B, A],[A, A+C]] = det(A(B+C)) + det(B(A+C)) + det(C(A+B)) − det(AB) − det(AC) − det(BC)
      for 2×2 matrices over a commutative ring (T154 (3.5)).
* (E) `trace_extractor`: with K = XY − YX, E2(T) := {K,[XT+TX,Y]} − {[X²,Y],[T,Y]} satisfies
      E2(T) = (2·tr T) • K² (2×2). (T154 (3.2), doubled to avoid ½.)
* (D) `det_extractor`: E2(T)·T − 2•(K²·T²) = (2·det T) • K² (T154 (3.4), doubled).
* (Z) `H0_square_zero`: if X², Y², Z² vanish then the H0 block matrix vanishes (corank 4 at square-zero points:
      Lemma 1 of elevacion_modular_15oct).
* (S) `sharpness`: in a division ring, u (u⁻²+v⁻²) v = u⁻¹ v + u v⁻¹ (two-axis clearing, T154).
* (F) `fox_commutator`: in any ring with units x, y: x y x⁻¹ y⁻¹ − 1 = (1+x)(y x⁻¹ y⁻¹ + x⁻¹ y⁻¹) − (1+y)(x⁻¹ y⁻¹ + y⁻¹)
      (χ-twisted right Fox decomposition of a commutator; no z-term).
      `comaximal_intersection`: if u e + w f = 1 then u (1 − e u) = w (f u) — the element b of the counterexample to
      «extended NC» lies in uR ∩ wR.
* (A) `re_inv_one_add`: for z ∈ ℂ with ‖z‖ = 1 and z ≠ −1, Re (1+z)⁻¹ = 1/2 (accretivity of simple reciprocals).
* (P) `PM_partial_fractions`: (1−2du)/((1−(d+1)u)(1−du)) = (1−d)/(1−(d+1)u) + d/(1−du) (closed form of P_M,
      Kassel–Reutenauer §5.2).

Mathlib imports only; writes no .olean.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

namespace T155Identidades

open Matrix

section Comm

variable {R : Type*} [CommRing R]

abbrev M2 (R : Type*) [CommRing R] := Matrix (Fin 2) (Fin 2) R

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

/-- (B) block-determinant formula for H0. -/
theorem blk_det_formula (A B C : M2 R) :
    det (blk A B C) = det (A * (B + C)) + det (B * (A + C)) + det (C * (A + B))
      - det (A * B) - det (A * C) - det (B * C) := by
  rw [det4]
  simp [blk, d3, Matrix.det_fin_two]
  ring

def cm (P Q : M2 R) : M2 R := P * Q - Q * P
def acm (P Q : M2 R) : M2 R := P * Q + Q * P

/-- (E) doubled trace extractor. -/
def E2 (X Y T : M2 R) : M2 R :=
  acm (cm X Y) (cm (X * T + T * X) Y) - acm (cm (X * X) Y) (cm T Y)

theorem trace_extractor (X Y T : M2 R) :
    E2 X Y T = (2 * trace T) • (cm X Y * cm X Y) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [E2, cm, acm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;> ring

/-- (D) doubled determinant extractor. -/
theorem det_extractor (X Y T : M2 R) :
    E2 X Y T * T - (2 : R) • (cm X Y * cm X Y * (T * T)) = (2 * det T) • (cm X Y * cm X Y) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [E2, cm, acm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

/-- (Z) H0 vanishes at square-zero triples. -/
theorem H0_square_zero (X Y Z : M2 R) (hx : X * X = 0) (hy : Y * Y = 0) (hz : Z * Z = 0) :
    blk (X * X) (Y * Y) (Z * Z) = 0 := by
  rw [hx, hy, hz]
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [blk]

/-- (P) partial fractions behind the closed form of P_M. -/
theorem PM_partial_fractions {K : Type*} [Field K] (d u : K)
    (h1 : 1 - (d + 1) * u ≠ 0) (h2 : 1 - d * u ≠ 0) :
    (1 - 2 * d * u) / ((1 - (d + 1) * u) * (1 - d * u)) = (1 - d) / (1 - (d + 1) * u) + d / (1 - d * u) := by
  rw [div_add_div _ _ h1 h2]
  congr 1
  ring

end Comm

section NonComm

/-- (S) two-axis clearing in a division ring. -/
theorem sharpness {D : Type*} [DivisionRing D] (u v : D) (hu : u ≠ 0) (hv : v ≠ 0) :
    u * (u⁻¹ * u⁻¹ + v⁻¹ * v⁻¹) * v = u⁻¹ * v + u * v⁻¹ := by
  have h1 : u * u⁻¹ = 1 := mul_inv_cancel₀ hu
  have h2 : v⁻¹ * v = 1 := inv_mul_cancel₀ hv
  calc u * (u⁻¹ * u⁻¹ + v⁻¹ * v⁻¹) * v
      = (u * u⁻¹) * u⁻¹ * v + u * v⁻¹ * (v⁻¹ * v) := by noncomm_ring
    _ = u⁻¹ * v + u * v⁻¹ := by rw [h1, h2]; noncomm_ring

/-- (F) χ-twisted right Fox decomposition of a commutator (no z-term). -/
theorem fox_commutator {R : Type*} [Ring R] (x y : Rˣ) :
    (x : R) * y * ↑x⁻¹ * ↑y⁻¹ - 1 =
      (1 + x) * (y * ↑x⁻¹ * ↑y⁻¹ + ↑x⁻¹ * ↑y⁻¹) - (1 + y) * (↑x⁻¹ * ↑y⁻¹ + ↑y⁻¹) := by
  have hx : (x : R) * ↑x⁻¹ = 1 := Units.mul_inv x
  have hy : (y : R) * ↑y⁻¹ = 1 := Units.mul_inv y
  have : (1 + (x : R)) * (y * ↑x⁻¹ * ↑y⁻¹ + ↑x⁻¹ * ↑y⁻¹) - (1 + y) * (↑x⁻¹ * ↑y⁻¹ + ↑y⁻¹)
      = (x : R) * y * ↑x⁻¹ * ↑y⁻¹ + y * ↑x⁻¹ * ↑y⁻¹ - y * ↑x⁻¹ * ↑y⁻¹ + (↑x * ↑x⁻¹) * ↑y⁻¹
        - (y * ↑y⁻¹) - ↑y⁻¹ := by noncomm_ring
  rw [this, hx, hy]
  noncomm_ring

/-- (F) the element of the counterexample lies in uR ∩ wR. -/
theorem comaximal_intersection {R : Type*} [Ring R] (u w e f : R) (h : u * e + w * f = 1) :
    u * (1 - e * u) = w * (f * u) := by
  have : w * f = 1 - u * e := by rw [← h]; noncomm_ring
  calc u * (1 - e * u) = (1 - u * e) * u := by noncomm_ring
    _ = w * f * u := by rw [this]
    _ = w * (f * u) := by noncomm_ring

/-- (F′) minimal form: the commutator binomial is a Lie bracket times units:
    x y x⁻¹ y⁻¹ − 1 = ((1+x)(1+y) − (1+y)(1+x)) x⁻¹ y⁻¹. -/
theorem commutator_eq_bracket {R : Type*} [Ring R] (x y : Rˣ) :
    (x : R) * y * ↑x⁻¹ * ↑y⁻¹ - 1 = ((1 + x) * (1 + y) - (1 + y) * (1 + x)) * ↑x⁻¹ * ↑y⁻¹ := by
  have hx : (x : R) * ↑x⁻¹ = 1 := Units.mul_inv x
  have hy : (y : R) * ↑y⁻¹ = 1 := Units.mul_inv y
  have : ((1 + (x : R)) * (1 + y) - (1 + y) * (1 + x)) * ↑x⁻¹ * ↑y⁻¹
      = (x : R) * y * ↑x⁻¹ * ↑y⁻¹ - y * (x * ↑x⁻¹) * ↑y⁻¹ := by noncomm_ring
  rw [this, hx, mul_one, hy]

/-- (F″) minimal clearing mechanism: inverting ℓ = ab − ba makes a and b right comaximal. -/
theorem bracket_comaximal {D : Type*} [DivisionRing D] (a b : D) (h : a * b - b * a ≠ 0) :
    a * (b * (a * b - b * a)⁻¹) - b * (a * (a * b - b * a)⁻¹) = 1 := by
  have : a * (b * (a * b - b * a)⁻¹) - b * (a * (a * b - b * a)⁻¹) = (a * b - b * a) * (a * b - b * a)⁻¹ := by
    noncomm_ring
  rw [this, mul_inv_cancel₀ h]

end NonComm

/-- (A) accretivity of simple reciprocals on the unit circle. -/
theorem re_inv_one_add (z : ℂ) (hz : ‖z‖ = 1) (h : z ≠ -1) : ((1 + z)⁻¹).re = 1 / 2 := by
  have hn : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  have hn' : z.re * z.re + z.im * z.im = 1 := by rw [Complex.normSq_apply] at hn; exact hn
  have hre : 1 + z.re ≠ 0 := by
    intro h0
    have hr : z.re = -1 := by linarith
    have him : z.im = 0 := by nlinarith
    exact h (Complex.ext (by simp [hr]) (by simp [him]))
  rw [Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, zero_add]
  have : (1 + z.re) * (1 + z.re) + z.im * z.im = 2 * (1 + z.re) := by nlinarith
  rw [this]
  field_simp

end T155Identidades

#print axioms T155Identidades.blk_det_formula
#print axioms T155Identidades.trace_extractor
#print axioms T155Identidades.det_extractor
#print axioms T155Identidades.H0_square_zero
#print axioms T155Identidades.PM_partial_fractions
#print axioms T155Identidades.sharpness
#print axioms T155Identidades.fox_commutator
#print axioms T155Identidades.comaximal_intersection
#print axioms T155Identidades.re_inv_one_add
#print axioms T155Identidades.commutator_eq_bracket
#print axioms T155Identidades.bracket_comaximal
