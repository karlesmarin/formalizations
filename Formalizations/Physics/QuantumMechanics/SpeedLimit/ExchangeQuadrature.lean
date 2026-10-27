/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The exchange operator of two truncated oscillators

Two `d`-level oscillators (transmon-like ladders) coupled by an exchange interaction `g E`, where
`E = a† ⊗ a + a ⊗ a†` and `a` is the truncated annihilation operator, `a e_j = √j e_{j-1}`
(`bd i j = √j` if `j = i + 1`, else `0`). Let `Q = a + a†` be the quadrature and `λ` a real
eigenvalue of `Q` (the largest eigenvalue `λ_d` is the largest zero of the Hermite polynomial `He_d`,
`λ_d ~ 2 √d`, DLMF 18.16.17 for the asymptotics) and `κ_d = ‖E‖` the operator norm.

With ideal fast local control, the averaging framework of Wocjan–Rötteler–Janzing–Beth
(Phys. Rev. A 65, 042309) gives for the controlled-Z time the sandwich
`π / (4 g κ_d) ≤ T_CZ ≤ π / (2 g λ_d²)`; the upper bound comes from a quadrature-code construction
(`E` acts as `(1/2) Q ⊗ Q` on the quadrature code) and the lower bound from `κ_d`.
**None of this physics is formalized here**; this file proves only the purely matrix-analytic
sandwich between the two constants:

* `QSL.Exchange.exchange_norm_ge`: if `x` is a real unit eigenvector of `Q` with eigenvalue `λ`,
  then `λ² / 2 ≤ ‖E‖` (Rayleigh quotient at `x ⊗ x`);
* `QSL.Exchange.exchange_norm_le`: `‖E‖ ≤ 2 (d - 1)`, via `‖a‖ ≤ √(d - 1)`;
* `QSL.Exchange.ratio_sandwich`: `1 ≤ 2 ‖E‖ / λ² ≤ 4 (d - 1) / λ²`.

Not formalized: that `λ_d` is the *largest* eigenvalue, and the limit `4 (d - 1) / λ_d² → 1`
(it needs a lower bound `λ_d ≥ 2 √(d - 1) (1 - o(1))` on the top of the spectrum of the Jacobi
matrix `Q`, i.e. the spectral theorem plus a test vector).

## References

* P. Wocjan, M. Rötteler, D. Janzing, T. Beth, *Simulating Hamiltonians in quantum networks:
  efficient schemes and complexity bounds*, Phys. Rev. A 65 (2002) 042309.
* NIST Digital Library of Mathematical Functions, 18.16.17 (Hermite asymptotics).
-/

@[expose] public section

open scoped Matrix Kronecker
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace QSL.Exchange

section Basic

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- Squared-norm form of `Matrix.l2_opNorm_mulVec`. -/
lemma sum_sq_mulVec_le (A : Matrix m n ℝ) (x : n → ℝ) :
    ∑ i, (A *ᵥ x) i ^ 2 ≤ ‖A‖ ^ 2 * ∑ j, x j ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 x)
  have h0 : 0 ≤ ‖(EuclideanSpace.equiv m ℝ).symm (A *ᵥ x)‖ := norm_nonneg _
  have h2 := pow_le_pow_left₀ h0 h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  simpa [EuclideanSpace.equiv] using h2

/-- A sufficient condition for an operator-norm bound, in squared form. -/
lemma opNorm_le_of_sum_sq (A : Matrix m n ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : n → ℝ, ∑ i, (A *ᵥ x) i ^ 2 ≤ c ^ 2 * ∑ j, x j ^ 2) : ‖A‖ ≤ c := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  have hx := h x.ofLp
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simpa [Matrix.toEuclideanLin, Matrix.mulVec] using hx

end Basic

section Kron

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma norm_kronecker_one_le (A : Matrix ι ι ℝ) : ‖A ⊗ₖ (1 : Matrix κ κ ℝ)‖ ≤ ‖A‖ := by
  refine opNorm_le_of_sum_sq _ (norm_nonneg _) fun v => ?_
  have e : ∀ p : ι × κ, ((A ⊗ₖ (1 : Matrix κ κ ℝ)) *ᵥ v) p = (A *ᵥ fun k => v (k, p.2)) p.1 := by
    rintro ⟨i, j⟩
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.one_apply]
  simp only [e, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  calc _ ≤ ∑ j, ‖A‖ ^ 2 * ∑ k, v (k, j) ^ 2 :=
        Finset.sum_le_sum fun j _ => sum_sq_mulVec_le A _
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm (f := fun k j => v (k, j) ^ 2)]

lemma norm_one_kronecker_le (B : Matrix κ κ ℝ) : ‖(1 : Matrix ι ι ℝ) ⊗ₖ B‖ ≤ ‖B‖ := by
  refine opNorm_le_of_sum_sq _ (norm_nonneg _) fun v => ?_
  have e : ∀ p : ι × κ, (((1 : Matrix ι ι ℝ) ⊗ₖ B) *ᵥ v) p = (B *ᵥ fun l => v (p.1, l)) p.2 := by
    rintro ⟨i, j⟩
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.one_apply]
  simp only [e, Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => sum_sq_mulVec_le B _

lemma norm_kronecker_le (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) : ‖A ⊗ₖ B‖ ≤ ‖A‖ * ‖B‖ := by
  have : A ⊗ₖ B = (A ⊗ₖ (1 : Matrix κ κ ℝ)) * ((1 : Matrix ι ι ℝ) ⊗ₖ B) := by
    rw [← Matrix.mul_kronecker_mul, mul_one, one_mul]
  rw [this]
  exact (Matrix.l2_opNorm_mul _ _).trans
    (mul_le_mul (norm_kronecker_one_le A) (norm_one_kronecker_le B) (norm_nonneg _)
      (norm_nonneg _))

end Kron

variable {d : ℕ}

/-- The truncated annihilation operator on `d` levels: `a e_j = √j e_{j-1}`. -/
def bd (d : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => if (j : ℕ) = i + 1 then Real.sqrt j else 0

/-- The quadrature `Q = a + a†`. -/
def quad (d : ℕ) : Matrix (Fin d) (Fin d) ℝ := bd d + (bd d)ᵀ

/-- The exchange operator `E = a† ⊗ a + a ⊗ a†`. -/
def exch (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℝ :=
  (bd d)ᵀ ⊗ₖ bd d + bd d ⊗ₖ (bd d)ᵀ

/-! ### Upper bound -/

lemma bd_mulVec_apply (x : Fin d → ℝ) (i : Fin d) :
    (bd d *ᵥ x) i = if h : (i : ℕ) + 1 < d then Real.sqrt (i + 1) * x ⟨i + 1, h⟩ else 0 := by
  split_ifs with h
  · rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single ⟨i + 1, h⟩]
    · simp [bd]
    · intro j _ hj
      have : (j : ℕ) ≠ i + 1 := fun e => hj (Fin.ext e)
      simp [bd, this]
    · simp
  · rw [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : (j : ℕ) ≠ i + 1 := by have := j.2; omega
    simp [bd, this]

lemma sum_sq_bd_mulVec_le (x : Fin d → ℝ) :
    ∑ i, (bd d *ᵥ x) i ^ 2 ≤ ((d : ℝ) - 1) * ∑ j, x j ^ 2 := by
  set u : ℕ → ℝ := fun n => if h : n < d then x ⟨n, h⟩ ^ 2 else 0 with hu
  have hu0 : ∀ n, 0 ≤ u n := fun n => by
    simp only [hu]; split_ifs <;> positivity
  have step : ∀ i : Fin d, (bd d *ᵥ x) i ^ 2 ≤ ((d : ℝ) - 1) * u (i + 1) := by
    intro i
    rw [bd_mulVec_apply]
    by_cases h : (i : ℕ) + 1 < d
    · simp only [h, dite_eq_left, hu, mul_pow]
      have h1 : (i : ℝ) + 1 ≤ (d : ℝ) - 1 := by
        have : (i : ℕ) + 2 ≤ d := h
        have : ((i : ℕ) : ℝ) + 2 ≤ d := by exact_mod_cast this
        linarith
      rw [Real.sq_sqrt (by positivity)]
      exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    · simp [h, hu]
  calc ∑ i, (bd d *ᵥ x) i ^ 2 ≤ ∑ i : Fin d, ((d : ℝ) - 1) * u (i + 1) :=
        Finset.sum_le_sum fun i _ => step i
    _ = ((d : ℝ) - 1) * ∑ n ∈ Finset.range d, u (n + 1) := by
        rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun n => u (n + 1))]
    _ ≤ ((d : ℝ) - 1) * ∑ j, x j ^ 2 := by
        by_cases hd : (1 : ℝ) ≤ d
        · refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          have e1 : ∑ n ∈ Finset.range d, u (n + 1) + u 0 = ∑ n ∈ Finset.range (d + 1), u n := by
            rw [Finset.sum_range_succ' u d]
          have e2 : ∑ n ∈ Finset.range (d + 1), u n = ∑ n ∈ Finset.range d, u n := by
            rw [Finset.sum_range_succ]; simp [hu]
          have e3 : ∑ n ∈ Finset.range d, u n = ∑ j, x j ^ 2 := by
            rw [← Fin.sum_univ_eq_sum_range u d]
            simp [hu]
          linarith [hu0 0]
        · have : d = 0 := by
            by_contra h; apply hd; exact_mod_cast Nat.one_le_iff_ne_zero.2 h
          subst this
          simp

lemma norm_bd_le (hd : 1 ≤ d) : ‖bd d‖ ≤ Real.sqrt ((d : ℝ) - 1) := by
  refine opNorm_le_of_sum_sq _ (Real.sqrt_nonneg _) fun x => ?_
  rw [Real.sq_sqrt (by have : (1 : ℝ) ≤ d := by exact_mod_cast hd
                       linarith)]
  exact sum_sq_bd_mulVec_le x

/-- The exchange operator has norm at most `2 (d - 1)`. -/
theorem exchange_norm_le (hd : 1 ≤ d) : ‖exch d‖ ≤ 2 * ((d : ℝ) - 1) := by
  have hb := norm_bd_le hd
  have hbt : ‖(bd d)ᵀ‖ ≤ Real.sqrt ((d : ℝ) - 1) := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.l2_opNorm_conjTranspose]
    exact hb
  have hd' : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsq : Real.sqrt ((d : ℝ) - 1) * Real.sqrt ((d : ℝ) - 1) = (d : ℝ) - 1 :=
    Real.mul_self_sqrt hd'
  have s := Real.sqrt_nonneg ((d : ℝ) - 1)
  calc ‖exch d‖ ≤ ‖(bd d)ᵀ ⊗ₖ bd d‖ + ‖bd d ⊗ₖ (bd d)ᵀ‖ := norm_add_le _ _
    _ ≤ ‖(bd d)ᵀ‖ * ‖bd d‖ + ‖bd d‖ * ‖(bd d)ᵀ‖ :=
        add_le_add (norm_kronecker_le _ _) (norm_kronecker_le _ _)
    _ ≤ Real.sqrt ((d : ℝ) - 1) * Real.sqrt ((d : ℝ) - 1) +
        Real.sqrt ((d : ℝ) - 1) * Real.sqrt ((d : ℝ) - 1) :=
        add_le_add (mul_le_mul hbt hb (norm_nonneg _) s)
          (mul_le_mul hb hbt (norm_nonneg _) s)
    _ = 2 * ((d : ℝ) - 1) := by rw [hsq]; ring

/-! ### Lower bound -/

/-- The product vector `x ⊗ x`. -/
def sq (x : Fin d → ℝ) : Fin d × Fin d → ℝ := fun p => x p.1 * x p.2

lemma sum_sq_sq (x : Fin d → ℝ) : ∑ p, sq x p ^ 2 = (∑ i, x i ^ 2) ^ 2 := by
  simp only [sq, Fintype.sum_prod_type, mul_pow, pow_two (∑ i, x i ^ 2), Finset.sum_mul_sum]

lemma sq_dot_kronecker (M N : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    sq x ⬝ᵥ ((M ⊗ₖ N) *ᵥ sq x) = (x ⬝ᵥ (M *ᵥ x)) * (x ⬝ᵥ (N *ᵥ x)) := by
  simp only [dotProduct, Matrix.mulVec, sq, Fintype.sum_prod_type, Matrix.kroneckerMap_apply]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

lemma dot_transpose_mulVec (M : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    x ⬝ᵥ (Mᵀ *ᵥ x) = x ⬝ᵥ (M *ᵥ x) := by
  rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]

/-- The quadratic form of `E` on `x ⊗ x` is `2 (xᵀ a x)²`. -/
lemma sq_dot_exch (x : Fin d → ℝ) :
    sq x ⬝ᵥ (exch d *ᵥ sq x) = 2 * (x ⬝ᵥ (bd d *ᵥ x)) ^ 2 := by
  rw [exch, Matrix.add_mulVec, dotProduct_add, sq_dot_kronecker, sq_dot_kronecker,
    dot_transpose_mulVec]
  ring

/-- **Lower bound.** If `x` is a real unit eigenvector of the quadrature `Q = a + a†` with
eigenvalue `lam`, then `‖E‖ ≥ lam² / 2`. -/
theorem exchange_norm_ge (x : Fin d → ℝ) (hx : ∑ i, x i ^ 2 = 1) (lam : ℝ)
    (hQ : quad d *ᵥ x = lam • x) : lam ^ 2 / 2 ≤ ‖exch d‖ := by
  have hdot : x ⬝ᵥ (quad d *ᵥ x) = lam := by
    rw [hQ, dotProduct_smul, smul_eq_mul]
    have : x ⬝ᵥ x = 1 := by rw [← hx]; simp [dotProduct, pow_two]
    rw [this, mul_one]
  have hs : x ⬝ᵥ (bd d *ᵥ x) = lam / 2 := by
    rw [quad, Matrix.add_mulVec, dotProduct_add, dot_transpose_mulVec] at hdot
    linarith
  have hE : sq x ⬝ᵥ (exch d *ᵥ sq x) = lam ^ 2 / 2 := by
    rw [sq_dot_exch, hs]; ring
  have hw : ∑ p, sq x p ^ 2 = 1 := by rw [sum_sq_sq, hx]; norm_num
  have h1 := sum_sq_mulVec_le (exch d) (sq x)
  rw [hw, mul_one] at h1
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (sq x) (fun p => (exch d *ᵥ sq x) p)
  rw [hw, one_mul] at hcs
  have h2 : (lam ^ 2 / 2) ^ 2 ≤ ‖exch d‖ ^ 2 := by
    rw [← hE]
    exact hcs.trans h1
  exact le_of_sq_le_sq h2 (norm_nonneg _)

/-- Sandwich of the ratio `2 κ / λ²` between `1` and `4 (d - 1) / λ²`, `κ = ‖E‖`. -/
theorem ratio_sandwich (hd : 1 ≤ d) (x : Fin d → ℝ) (hx : ∑ i, x i ^ 2 = 1) (lam : ℝ)
    (hQ : quad d *ᵥ x = lam • x) (hlam : 0 < lam) :
    1 ≤ 2 * ‖exch d‖ / lam ^ 2 ∧
      2 * ‖exch d‖ / lam ^ 2 ≤ 4 * ((d : ℝ) - 1) / lam ^ 2 := by
  have hl2 : 0 < lam ^ 2 := by positivity
  have hge := exchange_norm_ge x hx lam hQ
  have hle := exchange_norm_le hd
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hl2]; linarith
  · rw [div_le_div_iff_of_pos_right hl2]; linarith

end QSL.Exchange

end
