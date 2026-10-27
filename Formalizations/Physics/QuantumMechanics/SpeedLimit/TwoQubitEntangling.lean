/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.CStarAlgebra.Exponential
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A lower bound on the duration of an entangling two-qubit gate

Two qubits, `ℂ² ⊗ ℂ²` with basis indexed by `Fin 2 × Fin 2`, evolve under a Hamiltonian
`L + H`, where `L = A ⊗ 1 + 1 ⊗ B` is an arbitrary local (piecewise constant) control and `H` is
a Hermitian interaction of operator norm at most `J` (ħ = 1). The Bell vector
`Φ = (e₀₀ + e₁₁)/√2` is at L2-distance at least `√(2 − √2)` from every product vector, since
`|⟨Φ, a ⊗ b⟩| ≤ 1/√2`. Local unitaries preserve product vectors, so a gate that sends a product
vector to `Φ` is at operator distance at least `√(2 − √2)` from every local unitary `A ⊗ B`.
A Duhamel estimate `‖exp (X + Y) − exp X‖ ≤ ‖Y‖` for skew-Hermitian `X, Y` shows that each step
`exp (−i τ (L + H))` is within `τ ‖H‖` of the local unitary `exp (−i τ L)`, and telescoping over
the steps gives `√(2 − √2) ≤ J · ∑ τₖ`: the total time `∑ τₖ` is at least `√(2 − √2) / J`.

Matrices are over `ℂ` with the L2 operator norm (`Matrix.Norms.L2Operator`); vectors live in
`EuclideanSpace ℂ (Fin 2 × Fin 2)`.

## Main results

* `QSL.TwoQubit.norm_inner_bell_prodVec_le`: `‖⟪Φ, a ⊗ b⟫‖ ≤ 1/√2` for unit `a, b`
* `QSL.TwoQubit.sqrt_two_sub_sqrt_two_le_norm_bell_sub_prodVec`:
  `√(2 − √2) ≤ ‖Φ − a ⊗ b‖` for unit `a, b`
* `QSL.TwoQubit.sqrt_two_sub_sqrt_two_le_norm_sub_kronecker`: if `G` maps a unit product vector
  to `Φ`, then `√(2 − √2) ≤ ‖G − A ⊗ₖ B‖` for all unitary `A, B`
* `QSL.TwoQubit.norm_exp_add_sub_exp_le`: `‖exp (X + Y) − exp X‖ ≤ ‖Y‖` for skew-Hermitian `X, Y`
* `QSL.TwoQubit.entangling_time_lower_bound`: a controlled evolution
  `∏ exp (−i τₖ (Lₖ + H))` with `‖H‖ ≤ J` that sends a unit product vector to `Φ` satisfies
  `√(2 − √2) ≤ J · ∑ τₖ`

## References

* C. Marín, *The Clock That Never Ticks: a machine-checked path from the dilogarithm to quantum
  speed limits in Lean 4*, Zenodo (2026), doi:10.5281/zenodo.20675271.
-/

@[expose] public section

noncomputable section

open scoped Matrix Kronecker
open scoped Matrix.Norms.L2Operator
open NormedSpace

namespace QSL.TwoQubit

/-- Qubit vectors. -/
abbrev Vec2 := EuclideanSpace ℂ (Fin 2)
/-- Two-qubit vectors. -/
abbrev Vec4 := EuclideanSpace ℂ (Fin 2 × Fin 2)
/-- Single-qubit operators. -/
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ
/-- Two-qubit operators. -/
abbrev Mat4 := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- The product vector `(a ⊗ b) (i, j) = a i * b j`. -/
def prodVec (a b : Vec2) : Vec4 := WithLp.toLp 2 fun p => a p.1 * b p.2

/-- The Bell vector `Φ = (e₀₀ + e₁₁)/√2`. -/
def bell : Vec4 := WithLp.toLp 2 fun p => if p.1 = p.2 then (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else 0

/-- Action of a matrix on a Euclidean vector. -/
def act {n : Type*} [Fintype n] (M : Matrix n n ℂ) (v : EuclideanSpace ℂ n) :
    EuclideanSpace ℂ n := WithLp.toLp 2 (M *ᵥ v.ofLp)

private lemma norm_act_le {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ)
    (v : EuclideanSpace ℂ n) : ‖act M v‖ ≤ ‖M‖ * ‖v‖ :=
  M.l2_opNorm_mulVec v

private lemma norm_prodVec (a b : Vec2) : ‖prodVec a b‖ = ‖a‖ * ‖b‖ := by
  have h : ‖prodVec a b‖ ^ 2 = (‖a‖ * ‖b‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      EuclideanSpace.norm_sq_eq, Finset.sum_mul_sum, Fintype.sum_prod_type]
    simp [prodVec, mul_pow]
  exact (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).1 h

private lemma act_kronecker_prodVec (A B : Mat2) (a b : Vec2) :
    act (A ⊗ₖ B) (prodVec a b) = prodVec (act A a) (act B b) := by
  ext ⟨i, j⟩
  simp [act, prodVec, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply]
  ring

private lemma norm_bell : ‖bell‖ = 1 := by
  have h : ‖bell‖ ^ 2 = 1 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    simp [bell, Fin.sum_univ_two, inv_pow, Real.sq_sqrt]
    norm_num
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 h

private lemma sq_norm_two (a : Vec2) : ‖a 0‖ ^ 2 + ‖a 1‖ ^ 2 = ‖a‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]

/-- (1) Bell overlap: `‖⟪Φ, a ⊗ b⟫‖ ≤ 1/√2` for unit vectors `a, b ∈ ℂ²`. -/
theorem norm_inner_bell_prodVec_le (a b : Vec2) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖inner ℂ bell (prodVec a b)‖ ≤ (Real.sqrt 2)⁻¹ := by
  have e : inner ℂ bell (prodVec a b) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (a 0 * b 0 + a 1 * b 1) := by
    simp [PiLp.inner_apply, Fintype.sum_prod_type, Fin.sum_univ_two, bell, prodVec]
    ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h1 := sq_norm_two a
  have h2 := sq_norm_two b
  rw [ha] at h1
  rw [hb] at h2
  have : ‖a 0 * b 0 + a 1 * b 1‖ ≤ 1 := by
    calc ‖a 0 * b 0 + a 1 * b 1‖ ≤ ‖a 0 * b 0‖ + ‖a 1 * b 1‖ := norm_add_le _ _
      _ = ‖a 0‖ * ‖b 0‖ + ‖a 1‖ * ‖b 1‖ := by rw [norm_mul, norm_mul]
      _ ≤ 1 := by
        nlinarith [sq_nonneg (‖a 0‖ - ‖b 0‖), sq_nonneg (‖a 1‖ - ‖b 1‖)]
  have hpos : 0 ≤ (Real.sqrt 2)⁻¹ := by positivity
  nlinarith

/-- (2) Distance: `√(2 − √2) ≤ ‖Φ − a ⊗ b‖` for unit vectors `a, b ∈ ℂ²`. -/
theorem sqrt_two_sub_sqrt_two_le_norm_bell_sub_prodVec (a b : Vec2) (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) : Real.sqrt (2 - Real.sqrt 2) ≤ ‖bell - prodVec a b‖ := by
  have hv : ‖prodVec a b‖ = 1 := by rw [norm_prodVec, ha, hb, one_mul]
  have hre : RCLike.re (inner ℂ bell (prodVec a b)) ≤ (Real.sqrt 2)⁻¹ :=
    (RCLike.re_le_norm _).trans (norm_inner_bell_prodVec_le a b ha hb)
  have hs : (Real.sqrt 2)⁻¹ * 2 = Real.sqrt 2 := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have h0 : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    linarith
  have key : 2 - Real.sqrt 2 ≤ ‖bell - prodVec a b‖ ^ 2 := by
    rw [norm_sub_sq (𝕜 := ℂ), norm_bell, hv]
    linarith
  exact Real.sqrt_le_iff.2 ⟨norm_nonneg _, key⟩

private lemma act_act {n : Type*} [Fintype n] (M N : Matrix n n ℂ) (v : EuclideanSpace ℂ n) :
    act M (act N v) = act (M * N) v := by
  ext i
  simp [act, Matrix.mulVec_mulVec]

private lemma act_sub {n : Type*} [Fintype n] (M N : Matrix n n ℂ) (v : EuclideanSpace ℂ n) :
    act (M - N) v = act M v - act N v := by
  ext i
  simp [act, Matrix.sub_mulVec]

private lemma norm_act_unitary (A : Mat2) (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) (a : Vec2) :
    ‖act A a‖ = ‖a‖ := by
  have hn : ‖A‖ = 1 := CStarRing.norm_of_mem_unitary hA
  have h1 : ‖act A a‖ ≤ ‖a‖ := by
    simpa [hn] using norm_act_le A a
  have h2 : a = act Aᴴ (act A a) := by
    rw [act_act]
    have : Aᴴ * A = 1 := Matrix.mem_unitaryGroup_iff'.1 hA
    rw [this]
    ext i
    simp [act]
  have h3 : ‖a‖ ≤ ‖act A a‖ := by
    calc ‖a‖ = ‖act Aᴴ (act A a)‖ := by rw [← h2]
      _ ≤ ‖Aᴴ‖ * ‖act A a‖ := norm_act_le _ _
      _ = ‖act A a‖ := by rw [Matrix.l2_opNorm_conjTranspose, hn, one_mul]
  exact le_antisymm h1 h3

/-- (3) Entangling gates are far from local gates: if `G` maps a unit product vector to `Φ`,
then `√(2 − √2) ≤ ‖G − A ⊗ₖ B‖` for all unitary `2 × 2` matrices `A, B`. -/
theorem sqrt_two_sub_sqrt_two_le_norm_sub_kronecker (G : Mat4) (a b : Vec2) (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (hG : act G (prodVec a b) = bell) (A B : Mat2)
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    Real.sqrt (2 - Real.sqrt 2) ≤ ‖G - A ⊗ₖ B‖ := by
  have h1 := sqrt_two_sub_sqrt_two_le_norm_bell_sub_prodVec (act A a) (act B b)
    ((norm_act_unitary A hA a).trans ha) ((norm_act_unitary B hB b).trans hb)
  have e : act (G - A ⊗ₖ B) (prodVec a b) = bell - prodVec (act A a) (act B b) := by
    rw [act_sub, hG, act_kronecker_prodVec]
  have h2 := norm_act_le (G - A ⊗ₖ B) (prodVec a b)
  rw [e, norm_prodVec, ha, hb, mul_one, mul_one] at h2
  exact h1.trans h2

/-! ### Exponentials of skew-Hermitian matrices and the Duhamel estimate -/

private lemma exp_mem_unitary {n : Type*} [Fintype n] [DecidableEq n] (Z : Matrix n n ℂ)
    (hZ : Zᴴ = -Z) : exp Z ∈ Matrix.unitaryGroup n ℂ := by
  let +nondep : NormedAlgebra ℚ (Matrix n n ℂ) := .restrictScalars ℚ ℂ _
  exact exp_mem_unitary_of_mem_skewAdjoint
    (by simpa [skewAdjoint.mem_iff, Matrix.star_eq_conjTranspose] using hZ)

private lemma norm_exp_skew {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (Z : Matrix n n ℂ) (hZ : Zᴴ = -Z) : ‖exp Z‖ = 1 :=
  CStarRing.norm_of_mem_unitary (exp_mem_unitary Z hZ)

/-- (4) Duhamel step: for skew-Hermitian `X, Y`, `‖exp (X + Y) − exp X‖ ≤ ‖Y‖`. -/
theorem norm_exp_add_sub_exp_le {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (X Y : Matrix n n ℂ) (hX : Xᴴ = -X) (hY : Yᴴ = -Y) :
    ‖exp (X + Y) - exp X‖ ≤ ‖Y‖ := by
  have hXY : (X + Y)ᴴ = -(X + Y) := by rw [Matrix.conjTranspose_add, hX, hY, neg_add]
  have hs : ∀ (Z : Matrix n n ℂ), Zᴴ = -Z → ∀ t : ℝ, ‖exp (t • Z)‖ = 1 := by
    intro Z hZ t
    apply norm_exp_skew
    rw [Matrix.conjTranspose_smul, hZ]
    simp
  let f : ℝ → Matrix n n ℂ := fun t => exp (t • (X + Y)) * exp ((1 - t) • X)
  have hd : ∀ t : ℝ, HasDerivAt f (exp (t • (X + Y)) * Y * exp ((1 - t) • X)) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => exp (u • (X + Y))) (exp (t • (X + Y)) * (X + Y)) t :=
      hasDerivAt_exp_smul_const (X + Y) t
    have h2 : HasDerivAt (fun u : ℝ => exp (u • X)) (X * exp ((1 - t) • X)) (1 - t) :=
      hasDerivAt_exp_smul_const' X (1 - t)
    have h3 : HasDerivAt (fun u : ℝ => 1 - u) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub 1
    have h4 := HasDerivAt.scomp t h2 h3
    have h5 := h1.mul h4
    have h6 : HasDerivAt f (exp (t • (X + Y)) * (X + Y) * exp ((1 - t) • X) +
        exp (t • (X + Y)) * ((-1 : ℝ) • (X * exp ((1 - t) • X)))) t := h5
    refine h6.congr_deriv ?_
    simp only [neg_smul, one_smul, mul_neg]
    noncomm_ring
  have hb : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖exp (t • (X + Y)) * Y * exp ((1 - t) • X)‖ ≤ ‖Y‖ := by
    intro t _
    calc ‖exp (t • (X + Y)) * Y * exp ((1 - t) • X)‖
        ≤ ‖exp (t • (X + Y)) * Y‖ * ‖exp ((1 - t) • X)‖ := norm_mul_le _ _
      _ ≤ (‖exp (t • (X + Y))‖ * ‖Y‖) * ‖exp ((1 - t) • X)‖ := by
          gcongr; exact norm_mul_le _ _
      _ = ‖Y‖ := by rw [hs _ hXY, hs _ hX]; ring
  have := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := f)
    (fun t _ => (hd t).hasDerivWithinAt) hb
  simpa [f] using this

/-! ### Local evolutions and the main theorem -/

/-- `A ↦ A ⊗ₖ 1` as a ring homomorphism. -/
private def kronLeft : Mat2 →+* Mat4 where
  toFun A := A ⊗ₖ (1 : Mat2)
  map_one' := Matrix.one_kronecker_one
  map_mul' A B := by rw [← Matrix.mul_kronecker_mul, mul_one]
  map_zero' := Matrix.zero_kronecker _
  map_add' A B := Matrix.add_kronecker _ _ _

/-- `B ↦ 1 ⊗ₖ B` as a ring homomorphism. -/
private def kronRight : Mat2 →+* Mat4 where
  toFun B := (1 : Mat2) ⊗ₖ B
  map_one' := Matrix.one_kronecker_one
  map_mul' A B := by rw [← Matrix.mul_kronecker_mul, mul_one]
  map_zero' := Matrix.kronecker_zero _
  map_add' A B := Matrix.kronecker_add _ _ _

private lemma continuous_kronLeft : Continuous kronLeft := by
  refine continuous_matrix fun ⟨i, j⟩ ⟨k, l⟩ => ?_
  simp only [kronLeft, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    Matrix.kroneckerMap_apply]
  fun_prop

private lemma continuous_kronRight : Continuous kronRight := by
  refine continuous_matrix fun ⟨i, j⟩ ⟨k, l⟩ => ?_
  simp only [kronRight, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    Matrix.kroneckerMap_apply]
  fun_prop

private lemma exp_kronLeft (A : Mat2) : exp (A ⊗ₖ (1 : Mat2)) = exp A ⊗ₖ (1 : Mat2) := by
  let +nondep : NormedAlgebra ℚ Mat2 := .restrictScalars ℚ ℂ _
  exact (map_exp kronLeft continuous_kronLeft A).symm

private lemma exp_kronRight (B : Mat2) : exp ((1 : Mat2) ⊗ₖ B) = (1 : Mat2) ⊗ₖ exp B := by
  let +nondep : NormedAlgebra ℚ Mat2 := .restrictScalars ℚ ℂ _
  exact (map_exp kronRight continuous_kronRight B).symm

private lemma exp_local (A B : Mat2) :
    exp (A ⊗ₖ (1 : Mat2) + (1 : Mat2) ⊗ₖ B) = exp A ⊗ₖ exp B := by
  let +nondep : NormedAlgebra ℚ Mat4 := .restrictScalars ℚ ℂ _
  have hc : Commute (A ⊗ₖ (1 : Mat2)) ((1 : Mat2) ⊗ₖ B) := by
    show _ * _ = _ * _
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp
  rw [exp_add_of_commute hc, exp_kronLeft, exp_kronRight, ← Matrix.mul_kronecker_mul]
  simp

private lemma skew_smul {n : Type*} [Fintype n] (τ : ℝ) {M : Matrix n n ℂ} (hM : Mᴴ = M) :
    ((-(τ : ℂ) * Complex.I) • M)ᴴ = -((-(τ : ℂ) * Complex.I) • M) := by
  rw [Matrix.conjTranspose_smul, hM, ← neg_smul]
  congr 1
  apply Complex.ext <;> simp

private lemma hermitian_local (A B : Mat2) (hA : Aᴴ = A) (hB : Bᴴ = B) :
    (A ⊗ₖ (1 : Mat2) + (1 : Mat2) ⊗ₖ B)ᴴ = A ⊗ₖ (1 : Mat2) + (1 : Mat2) ⊗ₖ B := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker,
    hA, hB, Matrix.conjTranspose_one]

/-- One step of the controlled evolution: `exp (−i τ (A ⊗ 1 + 1 ⊗ B + H))`. -/
private def Ustep (H : Mat4) (s : ℝ × Mat2 × Mat2) : Mat4 :=
  exp ((-(s.1 : ℂ) * Complex.I) • (s.2.1 ⊗ₖ (1 : Mat2) + (1 : Mat2) ⊗ₖ s.2.2 + H))

/-- The local part of a step: `exp (−i τ A) ⊗ exp (−i τ B)`. -/
private def Vstep (s : ℝ × Mat2 × Mat2) : Mat4 :=
  exp ((-(s.1 : ℂ) * Complex.I) • s.2.1) ⊗ₖ exp ((-(s.1 : ℂ) * Complex.I) • s.2.2)

private lemma Vstep_eq (s : ℝ × Mat2 × Mat2) :
    Vstep s = exp ((-(s.1 : ℂ) * Complex.I) • (s.2.1 ⊗ₖ (1 : Mat2) + (1 : Mat2) ⊗ₖ s.2.2)) := by
  unfold Vstep
  rw [smul_add, ← Matrix.smul_kronecker, ← Matrix.kronecker_smul, exp_local]

private lemma step_core (L H : Mat4) (τ : ℝ) (hτ : 0 ≤ τ) (hL : Lᴴ = L) (hH : Hᴴ = H) :
    ‖exp ((-(τ : ℂ) * Complex.I) • (L + H))‖ ≤ 1 ∧ ‖exp ((-(τ : ℂ) * Complex.I) • L)‖ ≤ 1 ∧
      ‖exp ((-(τ : ℂ) * Complex.I) • (L + H)) - exp ((-(τ : ℂ) * Complex.I) • L)‖ ≤
        τ * ‖H‖ := by
  have hsL := skew_smul τ hL
  have hsH := skew_smul τ hH
  have hsum := skew_smul τ (show (L + H)ᴴ = L + H by rw [Matrix.conjTranspose_add, hL, hH])
  refine ⟨(norm_exp_skew _ hsum).le, (norm_exp_skew _ hsL).le, ?_⟩
  have key := norm_exp_add_sub_exp_le _ _ hsL hsH
  rw [smul_add]
  refine key.trans (le_of_eq ?_)
  rw [norm_smul]
  have : ‖(-(τ : ℂ) * Complex.I)‖ = τ := by
    simp [abs_of_nonneg hτ]
  rw [this]

private lemma step_facts (H : Mat4) (hH : Hᴴ = H) (J : ℝ) (hJ : ‖H‖ ≤ J)
    (s : ℝ × Mat2 × Mat2) (hτ : 0 ≤ s.1) (hA : s.2.1ᴴ = s.2.1) (hB : s.2.2ᴴ = s.2.2) :
    ‖Ustep H s‖ ≤ 1 ∧ ‖Vstep s‖ ≤ 1 ∧ ‖Ustep H s - Vstep s‖ ≤ J * s.1 := by
  obtain ⟨h1, h2, h3⟩ := step_core _ H s.1 hτ (hermitian_local _ _ hA hB) hH
  rw [Vstep_eq]
  refine ⟨h1, h2, h3.trans ?_⟩
  nlinarith

private lemma norm_list_prod_le (f : ℝ × Mat2 × Mat2 → Mat4) (l : List (ℝ × Mat2 × Mat2))
    (hf : ∀ s ∈ l, ‖f s‖ ≤ 1) : ‖(l.map f).prod‖ ≤ 1 := by
  induction l with
  | nil => simp
  | cons s l ih =>
    rw [List.map_cons, List.prod_cons]
    have h1 := hf s (by simp)
    have h2 := ih fun t ht => hf t (by simp [ht])
    calc ‖f s * (l.map f).prod‖ ≤ ‖f s‖ * ‖(l.map f).prod‖ := norm_mul_le _ _
      _ ≤ 1 := by nlinarith [norm_nonneg (f s), norm_nonneg (l.map f).prod]

private lemma norm_list_prod_sub_le (f g : ℝ × Mat2 × Mat2 → Mat4) (w : ℝ × Mat2 × Mat2 → ℝ)
    (l : List (ℝ × Mat2 × Mat2)) (hf : ∀ s ∈ l, ‖f s‖ ≤ 1) (hg : ∀ s ∈ l, ‖g s‖ ≤ 1)
    (hw : ∀ s ∈ l, ‖f s - g s‖ ≤ w s) :
    ‖(l.map f).prod - (l.map g).prod‖ ≤ (l.map w).sum := by
  induction l with
  | nil => simp
  | cons s l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, List.map_cons,
      List.sum_cons]
    have ih' := ih (fun t ht => hf t (by simp [ht])) (fun t ht => hg t (by simp [ht]))
      (fun t ht => hw t (by simp [ht]))
    have hP := norm_list_prod_le f l (fun t ht => hf t (by simp [ht]))
    have hgs := hg s (by simp)
    have hws := hw s (by simp)
    have e : f s * (l.map f).prod - g s * (l.map g).prod =
        (f s - g s) * (l.map f).prod + g s * ((l.map f).prod - (l.map g).prod) := by
      noncomm_ring
    rw [e]
    calc _ ≤ ‖(f s - g s) * (l.map f).prod‖ + ‖g s * ((l.map f).prod - (l.map g).prod)‖ :=
          norm_add_le _ _
      _ ≤ ‖f s - g s‖ * ‖(l.map f).prod‖ +
          ‖g s‖ * ‖(l.map f).prod - (l.map g).prod‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ w s + (l.map w).sum := by
          have := norm_nonneg (f s - g s)
          have := norm_nonneg (g s)
          have := norm_nonneg ((l.map f).prod - (l.map g).prod)
          nlinarith [norm_nonneg ((l.map f).prod)]

private lemma local_prod (l : List (ℝ × Mat2 × Mat2)) (hA : ∀ s ∈ l, s.2.1ᴴ = s.2.1)
    (hB : ∀ s ∈ l, s.2.2ᴴ = s.2.2) :
    ∃ P Q : Mat2, P ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ Q ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      (l.map Vstep).prod = P ⊗ₖ Q := by
  induction l with
  | nil => exact ⟨1, 1, one_mem _, one_mem _, by simp⟩
  | cons s l ih =>
    obtain ⟨P, Q, hP, hQ, h⟩ :=
      ih (fun t ht => hA t (by simp [ht])) (fun t ht => hB t (by simp [ht]))
    refine ⟨exp ((-(s.1 : ℂ) * Complex.I) • s.2.1) * P,
      exp ((-(s.1 : ℂ) * Complex.I) • s.2.2) * Q, mul_mem (exp_mem_unitary _ ?_) hP,
      mul_mem (exp_mem_unitary _ ?_) hQ, ?_⟩
    · exact skew_smul s.1 (hA s (by simp))
    · exact skew_smul s.1 (hB s (by simp))
    · rw [List.map_cons, List.prod_cons, h, Vstep, ← Matrix.mul_kronecker_mul]

/-- (5) Main theorem. Let `H` be a Hermitian interaction with `‖H‖ ≤ J` and let
`U = ∏ₖ exp (−i τₖ (Aₖ ⊗ 1 + 1 ⊗ Bₖ + H))` (an ordered product over the list `steps` of
triples `(τₖ, Aₖ, Bₖ)`, `τₖ ≥ 0`, `Aₖ, Bₖ` Hermitian) be a controlled evolution with arbitrary
local controls. If `U` maps a unit product vector `a ⊗ b` to the Bell vector `Φ`, then
`√(2 − √2) ≤ J · ∑ τₖ`. -/
theorem entangling_time_lower_bound (H : Mat4) (hH : H.IsHermitian) (J : ℝ) (hJ : ‖H‖ ≤ J)
    (steps : List (ℝ × Mat2 × Mat2)) (hτ : ∀ s ∈ steps, 0 ≤ s.1)
    (hA : ∀ s ∈ steps, s.2.1.IsHermitian) (hB : ∀ s ∈ steps, s.2.2.IsHermitian)
    (a b : Vec2) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hU : act (steps.map fun s => exp ((-(s.1 : ℂ) * Complex.I) •
        (s.2.1 ⊗ₖ (1 : Mat2) + (1 : Mat2) ⊗ₖ s.2.2 + H))).prod (prodVec a b) = bell) :
    Real.sqrt (2 - Real.sqrt 2) ≤ J * (steps.map Prod.fst).sum := by
  obtain ⟨P, Q, hP, hQ, hV⟩ := local_prod steps (fun s hs => (hA s hs).eq) (fun s hs => (hB s hs).eq)
  have h3 := sqrt_two_sub_sqrt_two_le_norm_sub_kronecker _ a b ha hb hU P Q hP hQ
  rw [← hV] at h3
  have facts := fun s (hs : s ∈ steps) =>
    step_facts H hH.eq J hJ s (hτ s hs) (hA s hs).eq (hB s hs).eq
  have h4 := norm_list_prod_sub_le (Ustep H) Vstep (fun s => J * s.1) steps
    (fun s hs => (facts s hs).1) (fun s hs => (facts s hs).2.1) (fun s hs => (facts s hs).2.2)
  have e : (steps.map fun s => J * s.1).sum = J * (steps.map Prod.fst).sum := by
    rw [List.sum_map_mul_left]
  rw [e] at h4
  exact h3.trans h4

end QSL.TwoQubit
