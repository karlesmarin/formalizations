/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.SpecificLimits.Basic

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

Asymptotics (the ratio `2κ_d/λ_d²` is the quotient of the CZ-time upper and lower bounds above, so
`→ 1` says the two bounds agree to leading order):

* `QSL.Exchange.lamMax`: the largest eigenvalue `λ_d` of `Q`, the supremum of the Rayleigh quotient;
  `quad_form_le_lamMax` is the variational fact `⟪v, Q v⟫ ≤ λ_d ‖v‖²` and
  `exists_unit_eigenvector` gives a unit eigenvector for `λ_d` (Mathlib's
  `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional`);
* `QSL.Exchange.lamMax_ge`: the uniform test vector on the last `m` levels gives
  `λ_d ≥ 2 (1 - 1/m) √(d - m)` for `2 ≤ m < d`;
* `QSL.Exchange.ratio_le_explicit`: `2 ‖E_d‖ / λ_d² ≤ (d - 1) / ((d - m) (1 - 1/m)²)`;
* `QSL.Exchange.ratio_tendsto_one`: `2 ‖E_d‖ / λ_d² → 1` (take `m = ⌊√d⌋`).

The sharp rate `O(d^{-2/3})` (from the Plancherel–Rotach / Airy asymptotics of the zeros of `He_d`,
DLMF 18.16.17) is not formalized; the elementary rate obtained here is weaker. The CZ-time bounds
themselves are not formalized.

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

/-! ### The largest eigenvalue and the variational fact -/

section Variational

open scoped InnerProductSpace

/-- The quadrature as a linear map on Euclidean space. -/
def quadLin (d : ℕ) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
  Matrix.toEuclideanLin (quad d)

lemma quad_transpose (d : ℕ) : (quad d)ᵀ = quad d := by
  simp [quad, Matrix.transpose_add, add_comm]

lemma quadLin_isSymmetric (d : ℕ) : (quadLin d).IsSymmetric := by
  rw [quadLin, Matrix.isSymmetric_toEuclideanLin_iff, Matrix.IsHermitian,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  exact quad_transpose d

/-- The largest eigenvalue of the quadrature `Q_d`, as the supremum of its Rayleigh quotient. -/
def lamMax (d : ℕ) : ℝ :=
  ⨆ x : { x : EuclideanSpace ℝ (Fin d) // x ≠ 0 },
    RCLike.re (inner ℝ (quadLin d x) (x : EuclideanSpace ℝ (Fin d))) /
      ‖(x : EuclideanSpace ℝ (Fin d))‖ ^ 2

lemma inner_quadLin (x : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (quadLin d x) x = x.ofLp ⬝ᵥ (quad d *ᵥ x.ofLp) := by
  simp [quadLin, PiLp.inner_apply, dotProduct, Matrix.mulVec]

lemma norm_sq_euclid (x : EuclideanSpace ℝ (Fin d)) : ‖x‖ ^ 2 = ∑ i, x.ofLp i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]; simp

lemma bddAbove_lamMax (d : ℕ) :
    BddAbove (Set.range fun x : { x : EuclideanSpace ℝ (Fin d) // x ≠ 0 } =>
      RCLike.re (inner ℝ (quadLin d x) (x : EuclideanSpace ℝ (Fin d))) /
        ‖(x : EuclideanSpace ℝ (Fin d))‖ ^ 2) := by
  let T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    LinearMap.toContinuousLinearMap (quadLin d)
  refine ⟨‖T‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  have := T.rayleighQuotient_le_norm (x : EuclideanSpace ℝ (Fin d))
  exact (le_abs_self _).trans this

/-- Variational fact: `⟪v, Q v⟫ ≤ λ_d ‖v‖²`. -/
theorem quad_form_le_lamMax (v : Fin d → ℝ) :
    v ⬝ᵥ (quad d *ᵥ v) ≤ lamMax d * ∑ i, v i ^ 2 := by
  by_cases h0 : v = 0
  · subst h0; simp
  set x : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 v with hx
  have hxne : x ≠ 0 := fun h => h0 (by simpa [hx] using congrArg WithLp.ofLp h)
  have hn : 0 < ‖x‖ ^ 2 := by positivity
  have h1 := le_ciSup (bddAbove_lamMax d) (⟨x, hxne⟩ : { x : EuclideanSpace ℝ (Fin d) // x ≠ 0 })
  have h2 : inner ℝ (quadLin d x) x / ‖x‖ ^ 2 ≤ lamMax d := h1
  rw [div_le_iff₀ hn, inner_quadLin, norm_sq_euclid] at h2
  simpa [hx] using h2

/-- There is a unit eigenvector of `Q_d` with eigenvalue `λ_d` (`d ≥ 1`). -/
theorem exists_unit_eigenvector (hd : 1 ≤ d) :
    ∃ x : Fin d → ℝ, ∑ i, x i ^ 2 = 1 ∧ quad d *ᵥ x = lamMax d • x := by
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) := by
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  have hE := (quadLin_isSymmetric d).hasEigenvalue_iSup_of_finiteDimensional
  obtain ⟨y, hy⟩ := hE.exists_hasEigenvector
  have hyne : y ≠ 0 := hy.2
  have hyn : 0 < ‖y‖ := norm_pos_iff.2 hyne
  refine ⟨((‖y‖⁻¹ : ℝ) • y).ofLp, ?_, ?_⟩
  · have := norm_sq_euclid ((‖y‖⁻¹ : ℝ) • y)
    rw [← this, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hyn.ne']; norm_num
  · have hyeq : quadLin d y = lamMax d • y := hy.apply_eq_smul
    have h3 : quad d *ᵥ y.ofLp = lamMax d • y.ofLp := by
      simpa [quadLin] using congrArg WithLp.ofLp hyeq
    rw [WithLp.ofLp_smul, Matrix.mulVec_smul, h3, smul_comm]

end Variational

/-! ### Uniform test vector on the last `m` levels -/

section TestVector

/-- The indicator of the last `m` levels of the `d`-level ladder. -/
def tail (d m : ℕ) : Fin d → ℝ := fun i => if d - m ≤ (i : ℕ) then 1 else 0

lemma sum_sq_tail {m : ℕ} (hm : m ≤ d) : ∑ i, tail d m i ^ 2 = m := by
  have e : ∀ i : Fin d, tail d m i ^ 2 =
      (fun n : ℕ => if d - m ≤ n then (1 : ℝ) else 0) i := by
    intro i; simp only [tail]; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun i _ => e i),
    Fin.sum_univ_eq_sum_range (fun n : ℕ => if d - m ≤ n then (1 : ℝ) else 0) d,
    Finset.sum_boole]
  have : Finset.filter (fun n => d - m ≤ n) (Finset.range d) = Finset.Ico (d - m) d := by
    ext n; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [this, Nat.card_Ico]
  congr 1
  omega

lemma tail_term_nonneg {m : ℕ} (i : Fin d) : 0 ≤ tail d m i * (bd d *ᵥ tail d m) i := by
  rw [bd_mulVec_apply]
  unfold tail
  split_ifs <;> positivity

lemma tail_term {m : ℕ} (i : Fin d) :
    (if d - m ≤ (i : ℕ) ∧ (i : ℕ) + 1 < d then Real.sqrt ((d - m : ℕ) : ℝ) else 0) ≤
      tail d m i * (bd d *ᵥ tail d m) i := by
  by_cases h : d - m ≤ (i : ℕ) ∧ (i : ℕ) + 1 < d
  · obtain ⟨h1, h2⟩ := h
    have h3 : d - m ≤ (i : ℕ) + 1 := by omega
    simp only [h1, h2, and_self, ↓reduceIte, bd_mulVec_apply, tail, h3, ↓reduceDIte, one_mul,
      mul_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast h3)
  · simp only [h, ↓reduceIte]
    exact tail_term_nonneg i

lemma sum_tail_term {m : ℕ} (hm : 1 ≤ m) (hmd : m ≤ d) :
    ((m : ℝ) - 1) * Real.sqrt ((d : ℝ) - m) ≤ tail d m ⬝ᵥ (bd d *ᵥ tail d m) := by
  have hle : ∑ i : Fin d, (if d - m ≤ (i : ℕ) ∧ (i : ℕ) + 1 < d then
      Real.sqrt ((d - m : ℕ) : ℝ) else 0) ≤ tail d m ⬝ᵥ (bd d *ᵥ tail d m) :=
    Finset.sum_le_sum fun i _ => tail_term i
  have e : ∑ i : Fin d, (if d - m ≤ (i : ℕ) ∧ (i : ℕ) + 1 < d then
      Real.sqrt ((d - m : ℕ) : ℝ) else 0) = ((m : ℝ) - 1) * Real.sqrt ((d : ℝ) - m) := by
    rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => if d - m ≤ n ∧ n + 1 < d then
      Real.sqrt ((d - m : ℕ) : ℝ) else 0) d, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul]
    have : Finset.filter (fun n => d - m ≤ n ∧ n + 1 < d) (Finset.range d) =
        Finset.Ico (d - m) (d - 1) := by
      ext n; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [this, Nat.card_Ico, Nat.cast_sub hmd]
    have h1 : d - 1 - (d - m) = m - 1 := by omega
    rw [h1, Nat.cast_sub hm]
    simp
  linarith

/-- The quadratic form of `Q` on the test vector is `2 ⟪t, a t⟫`. -/
lemma tail_quad_form (m : ℕ) :
    tail d m ⬝ᵥ (quad d *ᵥ tail d m) = 2 * (tail d m ⬝ᵥ (bd d *ᵥ tail d m)) := by
  rw [quad, Matrix.add_mulVec, dotProduct_add, dot_transpose_mulVec]
  ring

/-- Lower bound on the top eigenvalue: `λ_d ≥ 2 (1 - 1/m) √(d - m)`, for `2 ≤ m < d`. -/
theorem lamMax_ge {m : ℕ} (hm : 2 ≤ m) (hmd : m < d) :
    2 * (1 - 1 / (m : ℝ)) * Real.sqrt ((d : ℝ) - m) ≤ lamMax d := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have h1 := quad_form_le_lamMax (tail d m)
  rw [sum_sq_tail hmd.le, tail_quad_form] at h1
  have h2 := sum_tail_term (d := d) (by omega : 1 ≤ m) hmd.le
  have h3 : 2 * (((m : ℝ) - 1) * Real.sqrt ((d : ℝ) - m)) ≤ lamMax d * m := by linarith
  have e : 2 * (1 - 1 / (m : ℝ)) * Real.sqrt ((d : ℝ) - m) =
      2 * (((m : ℝ) - 1) * Real.sqrt ((d : ℝ) - m)) / m := by
    field_simp
  rw [e, div_le_iff₀ hm0]
  exact h3

end TestVector

/-! ### Explicit bound and the limit -/

/-- Explicit upper bound of the ratio: `2 ‖E_d‖ / λ_d² ≤ (d - 1) / ((d - m) (1 - 1/m)²)`
for `2 ≤ m < d`. -/
theorem ratio_le_explicit {m : ℕ} (hm : 2 ≤ m) (hmd : m < d) :
    2 * ‖exch d‖ / (lamMax d) ^ 2 ≤
      ((d : ℝ) - 1) / (((d : ℝ) - m) * (1 - 1 / (m : ℝ)) ^ 2) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmd' : (m : ℝ) < d := by exact_mod_cast hmd
  have ha : 0 < 1 - 1 / (m : ℝ) := by
    have : 1 / (m : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hm'
    linarith
  have hb : 0 < (d : ℝ) - m := by linarith
  have hL := lamMax_ge hm hmd
  have hLpos : 0 < 2 * (1 - 1 / (m : ℝ)) * Real.sqrt ((d : ℝ) - m) := by positivity
  have hL2 : (2 * (1 - 1 / (m : ℝ)) * Real.sqrt ((d : ℝ) - m)) ^ 2 =
      4 * ((1 - 1 / (m : ℝ)) ^ 2 * ((d : ℝ) - m)) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hb.le]; ring
  have hlam2 : 4 * ((1 - 1 / (m : ℝ)) ^ 2 * ((d : ℝ) - m)) ≤ (lamMax d) ^ 2 := by
    rw [← hL2]; exact pow_le_pow_left₀ hLpos.le hL 2
  have hpos : 0 < 4 * ((1 - 1 / (m : ℝ)) ^ 2 * ((d : ℝ) - m)) := by positivity
  have hE := exchange_norm_le (d := d) (by omega)
  calc 2 * ‖exch d‖ / (lamMax d) ^ 2
      ≤ 4 * ((d : ℝ) - 1) / (lamMax d) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by linarith); linarith
    _ ≤ 4 * ((d : ℝ) - 1) / (4 * ((1 - 1 / (m : ℝ)) ^ 2 * ((d : ℝ) - m))) := by
        apply div_le_div_of_nonneg_left _ hpos hlam2
        have : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
        linarith
    _ = ((d : ℝ) - 1) / (((d : ℝ) - m) * (1 - 1 / (m : ℝ)) ^ 2) := by
        rw [mul_comm ((d : ℝ) - m)]
        field_simp

/-- The ratio is `≥ 1` once `d ≥ 3` (so that `λ_d > 0` by `lamMax_ge`). -/
theorem one_le_ratio (hd : 3 ≤ d) : 1 ≤ 2 * ‖exch d‖ / (lamMax d) ^ 2 := by
  obtain ⟨x, hx, hQ⟩ := exists_unit_eigenvector (d := d) (by omega)
  have hL := lamMax_ge (d := d) (m := 2) le_rfl (by omega)
  have hb : 0 < (d : ℝ) - (2 : ℕ) := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    push_cast; linarith
  have hs := Real.sqrt_pos.2 hb
  have h2 : (0 : ℝ) < 2 * (1 - 1 / ((2 : ℕ) : ℝ)) := by norm_num
  have : 0 < lamMax d := lt_of_lt_of_le (mul_pos h2 hs) hL
  exact (ratio_sandwich (by omega) x hx _ hQ this).1

/-- **Asymptotics.** `2 ‖E_d‖ / λ_d² → 1`, where `λ_d` is the largest eigenvalue of `Q_d`. -/
theorem ratio_tendsto_one :
    Filter.Tendsto (fun d : ℕ => 2 * ‖exch d‖ / (lamMax d) ^ 2) Filter.atTop (nhds 1) := by
  have hm_top : Filter.Tendsto (fun d : ℕ => (Nat.sqrt d : ℝ)) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_atTop.2 fun b => ⟨(⌈b⌉₊) ^ 2, fun d hd => ?_⟩
    have : ⌈b⌉₊ ≤ Nat.sqrt d := Nat.le_sqrt.2 (by nlinarith)
    exact (Nat.le_ceil b).trans (by exact_mod_cast this)
  have hinvm : Filter.Tendsto (fun d : ℕ => 1 / (Nat.sqrt d : ℝ)) Filter.atTop (nhds 0) := by
    exact (tendsto_inv_atTop_zero.comp hm_top).congr fun d => by simp [one_div]
  have hmd : Filter.Tendsto (fun d : ℕ => (Nat.sqrt d : ℝ) / d) Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinvm ?_ ?_
    · exact Filter.Eventually.of_forall fun d => by positivity
    · filter_upwards [Filter.eventually_ge_atTop 1] with d hd
      have h1 : 1 ≤ Nat.sqrt d := Nat.le_sqrt.2 (by omega)
      have h2 : Nat.sqrt d * Nat.sqrt d ≤ d := Nat.sqrt_le d
      have h1' : (0 : ℝ) < Nat.sqrt d := by exact_mod_cast h1
      have h3 : (0 : ℝ) < d := by exact_mod_cast hd
      have h2' : (Nat.sqrt d : ℝ) * Nat.sqrt d ≤ d := by exact_mod_cast h2
      rw [div_le_div_iff₀ h3 h1']
      linarith
  have hid : Filter.Tendsto (fun d : ℕ => 1 / (d : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hu : Filter.Tendsto (fun d : ℕ => (1 - 1 / (d : ℝ)) /
      ((1 - (Nat.sqrt d : ℝ) / d) * (1 - 1 / (Nat.sqrt d : ℝ)) ^ 2)) Filter.atTop (nhds 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ)).sub hid).div
      ((tendsto_const_nhds (x := (1 : ℝ)).sub hmd).mul
        ((tendsto_const_nhds (x := (1 : ℝ)).sub hinvm).pow 2)) (by norm_num)
    have h1 : ((1 : ℝ) - 0) / ((1 - 0) * (1 - 0) ^ 2) = 1 := by norm_num
    rw [h1] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 3] with d hd
    exact one_le_ratio hd
  · filter_upwards [Filter.eventually_ge_atTop 4] with d hd
    have hm2 : 2 ≤ Nat.sqrt d := Nat.le_sqrt.2 (by omega)
    have hmlt : Nat.sqrt d < d := Nat.sqrt_lt_self (by omega)
    refine (ratio_le_explicit hm2 hmlt).trans (le_of_eq ?_)
    have hd0 : (d : ℝ) ≠ 0 := by positivity
    have hm0 : (Nat.sqrt d : ℝ) ≠ 0 := by
      have : (0 : ℝ) < Nat.sqrt d := by exact_mod_cast (by omega : 0 < Nat.sqrt d)
      exact this.ne'
    have hdm : (d : ℝ) - Nat.sqrt d ≠ 0 := by
      have : (Nat.sqrt d : ℝ) < d := by exact_mod_cast hmlt
      linarith
    have hm1 : (Nat.sqrt d : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ Nat.sqrt d := by exact_mod_cast hm2
      linarith
    field_simp

end QSL.Exchange

end
