/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.RingTheory.FreeField.ThreeAxes.ExactArc
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Data.List.Rotate

/-!
# The exact arc as a conjugate, and the parabolic family

The exact arc `exactArc i t η` of `ExactArc` is the conjugate of the antidiagonal matrix
`U₀ = !![0, -t; -η, 0]` by the `i`-th power of the unipotent matrix `K t = !![1, 0; t, 1]`.
Conjugating the square-zero matrix `N t = !![0, t; 0, 0]` by the same powers gives a family of
rank-one square-zero matrices whose cyclic products have an explicit trace.

## Main results

* `K_pow`: `(K t)^i = !![1, 0; i t, 1]`; `K_mul_K_neg`: `K t * K (-t) = 1`.
* `exactArc_eq_conj`: `exactArc i t η = (K t)^i * U₀ * (K (-t))^i`.
* `conj_mul_conj_eq_of_mul_eq`, `units_conj_mul_conj_eq`: if `U * U = c` with `c` central, every
  conjugate of `U` squares to `c` (the second through Mathlib's `Units.conj_pow`).
  `exactArc_sq_of_conj`: the square identity `exactArc_sq` recovered from `U₀ * U₀ = (t η) • 1`.
* `parabolic_eq_smul_col_mul_row`: `N_j = t • (c_j * r_j)` with `c_j = (1, j t)ᵀ`,
  `r_j = (-j t, 1)`; `row_mul_col`: `r_a * c_b = (b - a) t`; `parabolic_mul_self`: `N_j * N_j = 0`.
* `trace_prod_parabolic`: for a nonempty list `j₁, …, j_q`,
  `trace (N_{j₁} ⋯ N_{j_q}) = t^(2q) ∏ₗ (j_{l+1} − j_l)` with `j_{q+1} = j₁`;
  `cycDiff_eq_prod_rotate` writes the product as a product over `zip l (l.rotate 1)`.
* `det_one_add_allOnes`: `det (1 + J) = card n + 1` for the all-ones matrix `J`, from Mathlib's
  `Matrix.det_one_add_replicateCol_mul_replicateRow`.
-/

@[expose] public section

namespace ThreeAxes.ParabolicFamily

open Matrix ThreeAxes.ExactArc

variable {R : Type*} [CommRing R]

/-! ### The exact arc as a conjugate -/

/-- The unipotent matrix `!![1, 0; t, 1]`. -/
def K (t : R) : Matrix (Fin 2) (Fin 2) R := !![1, 0; t, 1]

/-- The antidiagonal matrix `!![0, -t; -η, 0] = −(t E₁₂ + η E₂₁)`. -/
def U0 (t η : R) : Matrix (Fin 2) (Fin 2) R := !![0, -t; -η, 0]

theorem K_mul_K (s t : R) : K s * K t = K (s + t) := by
  simp only [K, mul_fin_two]
  congr 1; ring_nf

theorem K_zero : K (0 : R) = 1 := by
  rw [K, one_fin_two]

theorem K_mul_K_neg (t : R) : K t * K (-t) = 1 := by
  rw [K_mul_K, add_neg_cancel, K_zero]

theorem K_neg_mul_K (t : R) : K (-t) * K t = 1 := by
  rw [K_mul_K, neg_add_cancel, K_zero]

theorem K_pow (t : R) (i : ℕ) : K t ^ i = !![1, 0; (i : R) * t, 1] := by
  induction i with
  | zero => simp [one_fin_two]
  | succ i ih =>
    rw [pow_succ, ih, K, mul_fin_two]
    congr 1; push_cast; ring_nf

theorem K_pow_eq (t : R) (i : ℕ) : K t ^ i = K ((i : R) * t) := by
  rw [K_pow, K]

theorem U0_mul_self (t η : R) : U0 t η * U0 t η = (t * η) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  simp only [U0, mul_fin_two, one_fin_two, smul_of, smul_cons, smul_empty]
  congr 1; ring_nf

/-- The exact arc with a parameter `i` in the ring is the conjugate of `U₀` by `K (i t)`. -/
theorem exactArc_eq_conj_K (i t η : R) :
    exactArc i t η = K (i * t) * U0 t η * K (-(i * t)) := by
  simp only [exactArc, K, U0, mul_fin_two]
  congr 1; ring_nf

/-- The exact arc is the conjugate of `U₀` by the `i`-th power of `K t`. -/
theorem exactArc_eq_conj (i : ℕ) (t η : R) :
    exactArc (i : R) t η = K t ^ i * U0 t η * K (-t) ^ i := by
  rw [K_pow_eq, K_pow_eq, exactArc_eq_conj_K, mul_neg]

/-- If `U * U = c` with `c` central and `h * g = g * h = 1`, then `(g U h)² = c`. -/
theorem conj_mul_conj_eq_of_mul_eq {A : Type*} [Ring A] (U c g h : A) (hU : U * U = c)
    (hc : ∀ x, Commute c x) (hhg : h * g = 1) (hgh : g * h = 1) :
    (g * U * h) * (g * U * h) = c := by
  calc (g * U * h) * (g * U * h) = g * U * (h * g) * U * h := by simp only [mul_assoc]
    _ = g * c * h := by rw [hhg, mul_one, mul_assoc g U U, hU]
    _ = c := by rw [← (hc g).eq, mul_assoc, hgh, mul_one]

/-- Conjugation by a unit preserves a central square (Mathlib's `Units.conj_pow` with `n = 2`). -/
theorem units_conj_mul_conj_eq {A : Type*} [Ring A] (U c : A) (g : Aˣ) (hU : U * U = c)
    (hc : ∀ x, Commute c x) :
    (↑g * U * ↑g⁻¹) * (↑g * U * ↑g⁻¹) = c := by
  rw [← sq, Units.conj_pow, sq, hU, ← (hc _).eq, mul_assoc, Units.mul_inv, mul_one]

/-- `exactArc_sq` again, as a corollary of `U₀ * U₀ = (t η) • 1` and conjugation. -/
theorem exactArc_sq_of_conj (i t η : R) :
    exactArc i t η * exactArc i t η = (t * η) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  rw [exactArc_eq_conj_K]
  exact conj_mul_conj_eq_of_mul_eq _ _ _ _ (U0_mul_self t η)
    (fun x => (Commute.one_left x).smul_left _) (K_neg_mul_K _) (K_mul_K_neg _)

/-! ### The parabolic family -/

/-- The square-zero matrix `!![0, t; 0, 0]`. -/
def N (t : R) : Matrix (Fin 2) (Fin 2) R := !![0, t; 0, 0]

/-- `N_j = (K t)^j * N t * (K (-t))^j`. -/
def parabolic (t : R) (j : ℕ) : Matrix (Fin 2) (Fin 2) R := K t ^ j * N t * K (-t) ^ j

/-- The column `(1, j t)ᵀ`. -/
def col (t : R) (j : ℕ) : Matrix (Fin 2) (Fin 1) R := !![1; (j : R) * t]

/-- The row `(-j t, 1)`. -/
def row (t : R) (j : ℕ) : Matrix (Fin 1) (Fin 2) R := !![-((j : R) * t), 1]

/-- The rank-one matrix `(1, a)ᵀ (-b, 1)`. -/
def outer (a b : R) : Matrix (Fin 2) (Fin 2) R := !![-b, 1; -(a * b), a]

theorem outer_mul_outer (a b a' b' : R) :
    outer a b * outer a' b' = (a' - b) • outer a b' := by
  simp only [outer, mul_fin_two, smul_of, smul_cons, smul_empty, smul_eq_mul]
  congr 1; ring_nf

theorem trace_outer (a b : R) : (outer a b).trace = a - b := by
  simp [outer, trace_fin_two]; ring

theorem parabolic_eq_outer (t : R) (j : ℕ) :
    parabolic t j = t • outer ((j : R) * t) ((j : R) * t) := by
  simp only [parabolic, K_pow, N, outer, mul_fin_two, smul_of, smul_cons, smul_empty, smul_eq_mul]
  congr 1; ring_nf

theorem col_mul_row (t : R) (a b : ℕ) : col t a * row t b = outer ((a : R) * t) ((b : R) * t) := by
  ext i k; fin_cases i <;> fin_cases k <;> simp [col, row, outer, Matrix.mul_apply]

theorem parabolic_eq_smul_col_mul_row (t : R) (j : ℕ) :
    parabolic t j = t • (col t j * row t j) := by
  rw [parabolic_eq_outer, col_mul_row]

theorem row_mul_col (t : R) (a b : ℕ) :
    row t a * col t b = of fun _ _ => ((b : R) - a) * t := by
  ext i k; fin_cases i; fin_cases k; simp [col, row, Matrix.mul_apply]; ring

theorem parabolic_mul_self (t : R) (j : ℕ) : parabolic t j * parabolic t j = 0 := by
  rw [parabolic_eq_outer, smul_mul_smul_comm, outer_mul_outer, sub_self, zero_smul, smul_zero]

/-- `∏ (j_{l+1} − j_l)` along the open chain `a, j₁, …, j_r`. -/
def chainDiff : ℕ → List ℕ → R
  | _, [] => 1
  | a, b :: bs => ((b : R) - a) * chainDiff b bs

/-- `∏ (j_{l+1} − j_l)` along the chain `a, j₁, …, j_r` closed by `f`. -/
def closedDiff (f : ℕ) : ℕ → List ℕ → R
  | a, [] => (f : R) - a
  | a, b :: bs => ((b : R) - a) * closedDiff f b bs

/-- The cyclic product `∏ₗ (j_{l+1} − j_l)`, `j_{q+1} = j₁`, of a list `j₁, …, j_q`. -/
def cycDiff : List ℕ → R
  | [] => 1
  | a :: bs => closedDiff a a bs

theorem closedDiff_eq (f a : ℕ) (bs : List ℕ) :
    (closedDiff f a bs : R) = chainDiff a bs * ((f : R) - bs.getLastD a) := by
  induction bs generalizing a with
  | nil => simp [closedDiff, chainDiff]
  | cons b bs ih => simp only [closedDiff, chainDiff, ih, List.getLastD_cons, mul_assoc]

theorem closedDiff_eq_prod_zip (f a : ℕ) (bs : List ℕ) :
    (closedDiff f a bs : R) =
      (((a :: bs).zip (bs ++ [f])).map fun p => ((p.2 : R) - p.1)).prod := by
  induction bs generalizing a with
  | nil => simp [closedDiff]
  | cons b bs ih => simp [closedDiff, ih]

/-- The cyclic product as a product over consecutive pairs of `l` and its rotation. -/
theorem cycDiff_eq_prod_rotate (l : List ℕ) :
    (cycDiff l : R) = ((l.zip (l.rotate 1)).map fun p => ((p.2 : R) - p.1)).prod := by
  cases l with
  | nil => simp [cycDiff]
  | cons a bs => rw [cycDiff, closedDiff_eq_prod_zip, List.rotate_cons_succ, List.rotate_zero]

theorem prod_parabolic (t : R) (a : ℕ) (bs : List ℕ) :
    ((a :: bs).map (parabolic t)).prod =
      (t ^ (2 * bs.length + 1) * chainDiff a bs) •
        outer ((a : R) * t) ((bs.getLastD a : ℕ) * t) := by
  induction bs generalizing a with
  | nil => simp [chainDiff, parabolic_eq_outer]
  | cons b bs ih =>
    rw [List.map_cons, List.prod_cons, ih, parabolic_eq_outer, smul_mul_smul_comm, outer_mul_outer,
      smul_smul, List.getLastD_cons, chainDiff, List.length_cons]
    congr 1
    ring

/-- The trace law: `trace (N_{j₁} ⋯ N_{j_q}) = t^(2q) ∏ₗ (j_{l+1} − j_l)`, `j_{q+1} = j₁`. -/
theorem trace_prod_parabolic (t : R) (l : List ℕ) (hl : l ≠ []) :
    (l.map (parabolic t)).prod.trace = t ^ (2 * l.length) * cycDiff l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a bs =>
    rw [prod_parabolic, trace_smul, trace_outer, cycDiff, closedDiff_eq, List.length_cons,
      smul_eq_mul]
    ring

/-! ### The all-ones matrix -/

/-- `det (1 + J) = card n + 1` for the all-ones matrix `J`
(Mathlib's `Matrix.det_one_add_replicateCol_mul_replicateRow`). -/
theorem det_one_add_allOnes (n : Type*) [Fintype n] [DecidableEq n] :
    (1 + of fun _ _ => (1 : R) : Matrix n n R).det = Fintype.card n + 1 := by
  have h : (of fun _ _ => (1 : R) : Matrix n n R) =
      replicateCol Unit (fun _ => (1 : R)) * replicateRow Unit (fun _ => (1 : R)) := by
    ext i k; simp [Matrix.mul_apply]
  rw [h, det_one_add_replicateCol_mul_replicateRow, add_comm]
  simp [dotProduct]

end ThreeAxes.ParabolicFamily
