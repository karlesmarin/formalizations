/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.Physics.QuantumMechanics.SpeedLimit.TwoQubitEntangling
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.CStarAlgebra.Exponential
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The entangling time of a bounded interaction in any local dimension

Two quantum systems with finite index types `ι` and `κ` (arbitrary local dimensions, ancillas
included) evolve under `A ⊗ 1 + 1 ⊗ B + H`, where the local part is an arbitrary piecewise constant
control and `H` is a Hermitian interaction with `‖H‖ ≤ J` (ħ = 1). We measure distances between
unit vectors with the Fubini–Study angle `arccos ‖⟪u, v⟫‖`, which satisfies the triangle
inequality and is invariant under unitaries. A Duhamel estimate, split into `N` equal pieces and
letting `N → ∞`, shows that the angle between `exp (X + Y) ψ` and `exp X ψ` is at most `‖Y‖` for
skew-Hermitian `X, Y`. Chaining over the steps of the control, the final state of an evolution
started at a product vector lies within angle `J · ∑ τₖ` of a product vector. Hence, if every unit
product vector has overlap at most `λ` with the target state, `arccos λ ≤ J · ∑ τₖ`. For the
two-level Bell vector `(e₀₀ + e₁₁)/√2` inside qudits of any dimension `d ≥ 2`, `λ = 1/√2`, so the
total time is at least `π / (4 J)`; this is exact (attained by `J · Z ⊗ X` for qubits).

This sharpens `QSL.TwoQubit.entangling_time_lower_bound`, whose chord bound is `√(2 − √2)`.

## Main results

* `QSL.Qudit.fsAngle_le_fsAngle_add_fsAngle`: triangle inequality for the Fubini–Study angle
* `QSL.Qudit.fsAngle_act_act`: invariance under a unitary matrix
* `QSL.Qudit.fsAngle_exp_add_exp_le`: `fsAngle (exp (X + Y) ψ) (exp X ψ) ≤ ‖Y‖` for
  skew-Hermitian `X, Y` and unit `ψ`
* `QSL.Qudit.arccos_le_entangling_time`: `arccos λ ≤ J · ∑ τₖ` for any target whose overlap with
  unit product vectors is at most `λ`
* `QSL.Qudit.pi_div_four_le_entangling_time`, `QSL.Qudit.pi_div_four_le_entangling_time_fin`:
  preparing a two-level Bell vector from a product vector takes `J · ∑ τₖ ≥ π / 4`
* `QSL.Qudit.entangling_time_tight`: the bound is attained (`H = J · Z ⊗ X`, one step of length
  `π / (4 J)`)

## References

* W. Dür, G. Vidal, J. I. Cirac, N. Linden, S. Popescu, *Entanglement capabilities of nonlocal
  Hamiltonians*, Phys. Rev. Lett. 87 (2001) 137901.
* G. Vidal, K. Hammerer, J. I. Cirac, *Interaction cost of nonlocal gates*, Phys. Rev. Lett. 88
  (2002) 237902.
* B. Basyildiz, C. Jameson, Z. Gong, *Speed limits of two-qubit gates with qudits*, arXiv:2312.09218.
* Ł. Rudnicki, *Quantum speed limit helps interpret geometric measure of entanglement*,
  Phys. Rev. A 104 (2021) 032417, arXiv:2107.11877.
* C. Marín, *The Clock That Never Ticks: a machine-checked path from the dilogarithm to quantum
  speed limits in Lean 4*, Zenodo (2026), doi:10.5281/zenodo.20675271.
-/

@[expose] public section

noncomputable section

open scoped Matrix Kronecker
open scoped Matrix.Norms.L2Operator
open NormedSpace Filter Topology
open QSL.TwoQubit (act)

namespace QSL.Qudit

/-! ### The Fubini–Study angle -/

section Angle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The Fubini–Study angle `arccos ‖⟪u, v⟫‖` between (unit) vectors. -/
def fsAngle (u v : E) : ℝ := Real.arccos ‖inner ℂ u v‖

lemma fsAngle_nonneg (u v : E) : 0 ≤ fsAngle u v := Real.arccos_nonneg _

lemma fsAngle_self {u : E} (hu : ‖u‖ = 1) : fsAngle u u = 0 := by
  rw [fsAngle, inner_self_eq_norm_sq_to_K, hu]
  simp

private lemma inner_one_of_norm {u : E} (hu : ‖u‖ = 1) : inner ℂ u u = 1 := by
  rw [inner_self_eq_norm_sq_to_K, hu]
  simp

private lemma inner_proj (u v w : E) (hv : ‖v‖ = 1) :
    inner ℂ (u - inner ℂ v u • v) (w - inner ℂ v w • v) =
      inner ℂ u w - inner ℂ u v * inner ℂ v w := by
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    inner_conj_symm, inner_one_of_norm hv]
  ring

private lemma norm_proj {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖u - inner ℂ v u • v‖ = Real.sqrt (1 - ‖inner ℂ u v‖ ^ 2) := by
  have e : inner ℂ u v * inner ℂ v u = ((‖inner ℂ u v‖ ^ 2 : ℝ) : ℂ) := by
    rw [← inner_conj_symm v u, Complex.mul_conj']
    push_cast
    rfl
  have h' : ‖u - inner ℂ v u • v‖ ^ 2 = 1 - ‖inner ℂ u v‖ ^ 2 := by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), inner_proj u v u hv,
      inner_one_of_norm hu, e]
    simp only [map_sub, RCLike.re_to_complex, Complex.ofReal_re, Complex.one_re]
  rw [← h', Real.sqrt_sq (norm_nonneg _)]

private lemma norm_inner_le_one {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖inner ℂ u v‖ ≤ 1 :=
  (norm_inner_le_norm u v).trans (by rw [hu, hv, one_mul])

/-- (A) Triangle inequality for the Fubini–Study angle of unit vectors. -/
theorem fsAngle_le_fsAngle_add_fsAngle {u v w : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hw : ‖w‖ = 1) : fsAngle u w ≤ fsAngle u v + fsAngle v w := by
  set p := ‖inner ℂ u v‖ with hp
  set q := ‖inner ℂ v w‖ with hq
  have hp1 : p ≤ 1 := norm_inner_le_one hu hv
  have hq1 : q ≤ 1 := norm_inner_le_one hv hw
  have hp0 : 0 ≤ p := norm_nonneg _
  have hq0 : 0 ≤ q := norm_nonneg _
  have key : p * q - Real.sqrt (1 - p ^ 2) * Real.sqrt (1 - q ^ 2) ≤ ‖inner ℂ u w‖ := by
    have h1 : ‖inner ℂ u w - inner ℂ u v * inner ℂ v w‖ ≤
        Real.sqrt (1 - p ^ 2) * Real.sqrt (1 - q ^ 2) := by
      rw [← inner_proj u v w hv]
      refine (norm_inner_le_norm _ _).trans (le_of_eq ?_)
      rw [norm_proj hu hv, norm_proj hw hv, norm_inner_symm w v]
    have h2 := norm_sub_norm_le (inner ℂ u v * inner ℂ v w) (inner ℂ u w)
    rw [norm_mul, norm_sub_rev] at h2
    linarith
  have hα := Real.arccos_le_pi_div_two.2 hp0
  have hβ := Real.arccos_le_pi_div_two.2 hq0
  have hcos : Real.cos (Real.arccos p + Real.arccos q) =
      p * q - Real.sqrt (1 - p ^ 2) * Real.sqrt (1 - q ^ 2) := by
    rw [Real.cos_add, Real.cos_arccos (by linarith) hp1, Real.cos_arccos (by linarith) hq1,
      Real.sin_arccos, Real.sin_arccos]
  unfold fsAngle
  rw [← hp, ← hq]
  calc Real.arccos ‖inner ℂ u w‖ ≤ Real.arccos (Real.cos (Real.arccos p + Real.arccos q)) :=
        Real.arccos_le_arccos (hcos ▸ key)
    _ = Real.arccos p + Real.arccos q :=
        Real.arccos_cos (add_nonneg (Real.arccos_nonneg _) (Real.arccos_nonneg _))
          (by linarith [Real.pi_pos])

/-- Chord bound: unit vectors at distance at most `c` are at angle at most `arccos (1 − c²/2)`. -/
lemma fsAngle_le_of_norm_sub_le {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) {c : ℝ}
    (h : ‖x - y‖ ≤ c) : fsAngle x y ≤ Real.arccos (1 - c ^ 2 / 2) := by
  apply Real.arccos_le_arccos
  have e := norm_sub_sq (𝕜 := ℂ) x y
  rw [hx, hy] at e
  have hre := RCLike.re_le_norm (inner ℂ x y)
  have hc : ‖x - y‖ ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith

end Angle

/-- `arccos (1 − c²/2) = 2 arcsin (c/2) ≤ c / √(1 − c²/4)` for `0 ≤ c < 2`. -/
lemma arccos_one_sub_le {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 2) :
    Real.arccos (1 - c ^ 2 / 2) ≤ c / Real.sqrt (1 - c ^ 2 / 4) := by
  have hz0 : 0 ≤ c / 2 := by linarith
  have hz1 : c / 2 < 1 := by linarith
  have hs : Real.sin (Real.arcsin (c / 2)) = c / 2 := Real.sin_arcsin (by linarith) hz1.le
  have hcα : Real.cos (Real.arcsin (c / 2)) = Real.sqrt (1 - c ^ 2 / 4) := by
    rw [Real.cos_arcsin]; congr 1; ring
  have hα0 : 0 ≤ Real.arcsin (c / 2) := Real.arcsin_nonneg.2 hz0
  have hα1 : Real.arcsin (c / 2) < Real.pi / 2 := Real.arcsin_lt_pi_div_two.2 hz1
  have hpos : 0 ≤ 1 - c ^ 2 / 4 := by nlinarith
  have hcos : Real.cos (2 * Real.arcsin (c / 2)) = 1 - c ^ 2 / 2 := by
    rw [Real.cos_two_mul, hcα, Real.sq_sqrt hpos]; ring
  rw [← hcos, Real.arccos_cos (by linarith) (by linarith [Real.pi_pos])]
  have ht := Real.le_tan hα0 hα1
  rw [Real.tan_eq_sin_div_cos, hs, hcα] at ht
  calc 2 * Real.arcsin (c / 2) ≤ 2 * (c / 2 / Real.sqrt (1 - c ^ 2 / 4)) := by linarith
    _ = c / Real.sqrt (1 - c ^ 2 / 4) := by ring

/-! ### Unitary matrices acting on Euclidean vectors -/

section Act

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma act_mul (M N : Matrix n n ℂ) (v : EuclideanSpace ℂ n) :
    act (M * N) v = act M (act N v) := by
  ext i
  simp [act, Matrix.mulVec_mulVec]

lemma act_one (v : EuclideanSpace ℂ n) : act (1 : Matrix n n ℂ) v = v := by
  ext i
  simp [act]

omit [DecidableEq n] in
lemma act_sub (M N : Matrix n n ℂ) (v : EuclideanSpace ℂ n) :
    act (M - N) v = act M v - act N v := by
  ext i
  simp [act, Matrix.sub_mulVec]

lemma inner_act_act {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (u v : EuclideanSpace ℂ n) : inner ℂ (act U u) (act U v) = inner ℂ u v := by
  have h1 : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.1 hU
  simp only [act, EuclideanSpace.inner_eq_star_dotProduct]
  rw [Matrix.star_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, h1,
    Matrix.vecMul_one, dotProduct_comm]

lemma norm_act_of_mem {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (v : EuclideanSpace ℂ n) : ‖act U v‖ = ‖v‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_act_act hU, ← norm_eq_sqrt_re_inner (𝕜 := ℂ)]

/-- (A') The Fubini–Study angle is invariant under a unitary applied to both vectors. -/
theorem fsAngle_act_act {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (u v : EuclideanSpace ℂ n) : fsAngle (act U u) (act U v) = fsAngle u v := by
  rw [fsAngle, inner_act_act hU, fsAngle]

lemma exp_mem_unitaryGroup (Z : Matrix n n ℂ) (hZ : Zᴴ = -Z) :
    exp Z ∈ Matrix.unitaryGroup n ℂ := by
  let +nondep : NormedAlgebra ℚ (Matrix n n ℂ) := .restrictScalars ℚ ℂ _
  exact exp_mem_unitary_of_mem_skewAdjoint
    (by simpa [skewAdjoint.mem_iff, Matrix.star_eq_conjTranspose] using hZ)

omit [Fintype n] [DecidableEq n] in
private lemma skew_inv_smul (N : ℕ) {Z : Matrix n n ℂ} (hZ : Zᴴ = -Z) :
    (((N : ℂ)⁻¹) • Z)ᴴ = -(((N : ℂ)⁻¹) • Z) := by
  rw [Matrix.conjTranspose_smul, hZ, smul_neg]
  congr 2
  simp

/-- (B) Step bound: for skew-Hermitian `X, Y` and a unit vector `ψ`, the Fubini–Study angle
between `exp (X + Y) ψ` and `exp X ψ` is at most `‖Y‖`. -/
theorem fsAngle_exp_add_exp_le (X Y : Matrix n n ℂ) (hX : Xᴴ = -X) (hY : Yᴴ = -Y)
    (ψ : EuclideanSpace ℂ n) (hψ : ‖ψ‖ = 1) :
    fsAngle (act (exp (X + Y)) ψ) (act (exp X) ψ) ≤ ‖Y‖ := by
  have : Nonempty n := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have h0 : ψ = 0 := by
      ext i
      exact isEmptyElim i
    rw [h0, norm_zero] at hψ
    exact zero_ne_one hψ
  -- the bound for `N` pieces
  have hbound : ∀ N : ℕ, 0 < N → ‖Y‖ / N < 2 →
      fsAngle (act (exp (X + Y)) ψ) (act (exp X) ψ) ≤
        ‖Y‖ / Real.sqrt (1 - (‖Y‖ / N) ^ 2 / 4) := by
    intro N hN hc2
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    set X' := ((N : ℂ)⁻¹) • X with hX'
    set Y' := ((N : ℂ)⁻¹) • Y with hY'
    have hsX := skew_inv_smul N hX
    have hsY := skew_inv_smul N hY
    have hsXY : (X' + Y')ᴴ = -(X' + Y') := by
      rw [Matrix.conjTranspose_add, hsX, hsY, neg_add]
    set P := exp (X' + Y')
    set Q := exp X'
    have hP : P ∈ Matrix.unitaryGroup n ℂ := exp_mem_unitaryGroup _ hsXY
    have hQ : Q ∈ Matrix.unitaryGroup n ℂ := exp_mem_unitaryGroup _ hsX
    have hnY : ‖Y'‖ = ‖Y‖ / N := by
      rw [hY', norm_smul, norm_inv, Complex.norm_natCast, inv_mul_eq_div]
    set c := ‖Y‖ / N with hc
    have hc0 : 0 ≤ c := by positivity
    have hPQ : ‖P - Q‖ ≤ c := hnY ▸ QSL.TwoQubit.norm_exp_add_sub_exp_le X' Y' hsX hsY
    have hstep : ∀ φ : EuclideanSpace ℂ n, ‖φ‖ = 1 →
        fsAngle (act P φ) (act Q φ) ≤ Real.arccos (1 - c ^ 2 / 2) := by
      intro φ hφ
      refine fsAngle_le_of_norm_sub_le ((norm_act_of_mem hP φ).trans hφ)
        ((norm_act_of_mem hQ φ).trans hφ) ?_
      rw [← act_sub]
      refine (Matrix.l2_opNorm_mulVec (P - Q) φ).trans ?_
      rw [hφ, mul_one]
      exact hPQ
    have htel : ∀ m : ℕ, ∀ φ : EuclideanSpace ℂ n, ‖φ‖ = 1 →
        fsAngle (act (P ^ m) φ) (act (Q ^ m) φ) ≤ m * Real.arccos (1 - c ^ 2 / 2) := by
      intro m
      induction m with
      | zero =>
        intro φ hφ
        simp [act_one, fsAngle_self hφ]
      | succ m ih =>
        intro φ hφ
        have hPm : ‖act (P ^ m) φ‖ = 1 := (norm_act_of_mem (pow_mem hP m) φ).trans hφ
        have hQm : ‖act (Q ^ m) φ‖ = 1 := (norm_act_of_mem (pow_mem hQ m) φ).trans hφ
        rw [pow_succ', pow_succ', act_mul, act_mul]
        have t := fsAngle_le_fsAngle_add_fsAngle
          ((norm_act_of_mem hP _).trans hPm) ((norm_act_of_mem hP _).trans hQm)
          ((norm_act_of_mem hQ _).trans hQm)
        rw [fsAngle_act_act hP] at t
        have h1 := ih φ hφ
        have h2 := hstep _ hQm
        push_cast
        linarith
    have hexp : ∀ Z : Matrix n n ℂ, exp Z = exp (((N : ℂ)⁻¹) • Z) ^ N := by
      intro Z
      let +nondep : NormedAlgebra ℚ (Matrix n n ℂ) := .restrictScalars ℚ ℂ _
      rw [← exp_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN', one_smul]
    have e1 : exp (X + Y) = P ^ N := by
      rw [hexp (X + Y), smul_add]
    have e2 : exp X = Q ^ N := hexp X
    rw [e1, e2]
    refine (htel N ψ hψ).trans ?_
    have ha := arccos_one_sub_le hc0 hc2
    calc (N : ℝ) * Real.arccos (1 - c ^ 2 / 2) ≤ N * (c / Real.sqrt (1 - c ^ 2 / 4)) :=
          mul_le_mul_of_nonneg_left ha hNr.le
      _ = ‖Y‖ / Real.sqrt (1 - c ^ 2 / 4) := by
          rw [hc]; field_simp
  -- let `N → ∞`
  have h0 : Tendsto (fun N : ℕ => ‖Y‖ / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have h1 : Tendsto (fun N : ℕ => ‖Y‖ / Real.sqrt (1 - (‖Y‖ / N) ^ 2 / 4)) atTop
      (𝓝 (‖Y‖ / Real.sqrt (1 - 0 ^ 2 / 4))) :=
    tendsto_const_nhds.div ((tendsto_const_nhds.sub ((h0.pow 2).div_const 4)).sqrt)
      (by norm_num)
  have e : ‖Y‖ / Real.sqrt (1 - 0 ^ 2 / 4) = ‖Y‖ := by norm_num
  rw [e] at h1
  refine ge_of_tendsto h1 ?_
  filter_upwards [h0.eventually (gt_mem_nhds two_pos), eventually_gt_atTop 0] with N hN2 hN0
  exact hbound N hN0 hN2

end Act

/-! ### Bipartite systems with arbitrary local dimensions -/

section Bipartite

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The product vector `(a ⊗ b) (i, j) = a i * b j`. -/
def prodVec (a : EuclideanSpace ℂ ι) (b : EuclideanSpace ℂ κ) : EuclideanSpace ℂ (ι × κ) :=
  WithLp.toLp 2 fun p => a p.1 * b p.2

omit [DecidableEq ι] [DecidableEq κ] in
lemma norm_prodVec (a : EuclideanSpace ℂ ι) (b : EuclideanSpace ℂ κ) :
    ‖prodVec a b‖ = ‖a‖ * ‖b‖ := by
  have h : ‖prodVec a b‖ ^ 2 = (‖a‖ * ‖b‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      EuclideanSpace.norm_sq_eq, Finset.sum_mul_sum, Fintype.sum_prod_type]
    simp [prodVec, mul_pow]
  exact (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).1 h

omit [DecidableEq ι] [DecidableEq κ] in
lemma act_kronecker_prodVec (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) (a : EuclideanSpace ℂ ι)
    (b : EuclideanSpace ℂ κ) : act (A ⊗ₖ B) (prodVec a b) = prodVec (act A a) (act B b) := by
  ext ⟨i, j⟩
  simp [act, prodVec, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun (x : ι) _ => Finset.sum_congr rfl fun (y : κ) _ => ?_
  ring

/-- `A ↦ A ⊗ₖ 1` as a ring homomorphism. -/
private def kronLeft : Matrix ι ι ℂ →+* Matrix (ι × κ) (ι × κ) ℂ where
  toFun A := A ⊗ₖ (1 : Matrix κ κ ℂ)
  map_one' := Matrix.one_kronecker_one
  map_mul' A B := by rw [← Matrix.mul_kronecker_mul, mul_one]
  map_zero' := Matrix.zero_kronecker _
  map_add' A B := Matrix.add_kronecker _ _ _

/-- `B ↦ 1 ⊗ₖ B` as a ring homomorphism. -/
private def kronRight : Matrix κ κ ℂ →+* Matrix (ι × κ) (ι × κ) ℂ where
  toFun B := (1 : Matrix ι ι ℂ) ⊗ₖ B
  map_one' := Matrix.one_kronecker_one
  map_mul' A B := by rw [← Matrix.mul_kronecker_mul, mul_one]
  map_zero' := Matrix.kronecker_zero _
  map_add' A B := Matrix.kronecker_add _ _ _

private lemma continuous_kronLeft : Continuous (kronLeft (ι := ι) (κ := κ)) := by
  refine continuous_matrix fun ⟨i, j⟩ ⟨k, l⟩ => ?_
  simp only [kronLeft, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    Matrix.kroneckerMap_apply]
  fun_prop

private lemma continuous_kronRight : Continuous (kronRight (ι := ι) (κ := κ)) := by
  refine continuous_matrix fun ⟨i, j⟩ ⟨k, l⟩ => ?_
  simp only [kronRight, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    Matrix.kroneckerMap_apply]
  fun_prop

/-- `exp (A ⊗ 1 + 1 ⊗ B) = exp A ⊗ exp B`. -/
lemma exp_local (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    exp (A ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ B) = exp A ⊗ₖ exp B := by
  let +nondep : NormedAlgebra ℚ (Matrix (ι × κ) (ι × κ) ℂ) := .restrictScalars ℚ ℂ _
  have hc : Commute (A ⊗ₖ (1 : Matrix κ κ ℂ)) ((1 : Matrix ι ι ℂ) ⊗ₖ B) := by
    show _ * _ = _ * _
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp
  have hl : exp (A ⊗ₖ (1 : Matrix κ κ ℂ)) = exp A ⊗ₖ (1 : Matrix κ κ ℂ) := by
    let +nondep : NormedAlgebra ℚ (Matrix ι ι ℂ) := .restrictScalars ℚ ℂ _
    exact (map_exp (kronLeft (κ := κ)) continuous_kronLeft A).symm
  have hr : exp ((1 : Matrix ι ι ℂ) ⊗ₖ B) = (1 : Matrix ι ι ℂ) ⊗ₖ exp B := by
    let +nondep : NormedAlgebra ℚ (Matrix κ κ ℂ) := .restrictScalars ℚ ℂ _
    exact (map_exp (kronRight (ι := ι)) continuous_kronRight B).symm
  rw [exp_add_of_commute hc, hl, hr, ← Matrix.mul_kronecker_mul]
  simp

private lemma skew_smul {m : Type*} [Fintype m] (τ : ℝ) {M : Matrix m m ℂ} (hM : Mᴴ = M) :
    ((-(τ : ℂ) * Complex.I) • M)ᴴ = -((-(τ : ℂ) * Complex.I) • M) := by
  rw [Matrix.conjTranspose_smul, hM, ← neg_smul]
  congr 1
  apply Complex.ext <;> simp

/-- One step of the controlled evolution: `exp (−i τ (A ⊗ 1 + 1 ⊗ B + H))`. -/
private def Ustep (H : Matrix (ι × κ) (ι × κ) ℂ) (s : ℝ × Matrix ι ι ℂ × Matrix κ κ ℂ) :
    Matrix (ι × κ) (ι × κ) ℂ :=
  exp ((-(s.1 : ℂ) * Complex.I) • (s.2.1 ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ s.2.2 + H))

/-- The local part of a step: `exp (−i τ A) ⊗ exp (−i τ B)`. -/
private def Vstep (s : ℝ × Matrix ι ι ℂ × Matrix κ κ ℂ) : Matrix (ι × κ) (ι × κ) ℂ :=
  exp ((-(s.1 : ℂ) * Complex.I) • s.2.1) ⊗ₖ exp ((-(s.1 : ℂ) * Complex.I) • s.2.2)

private lemma Vstep_eq (s : ℝ × Matrix ι ι ℂ × Matrix κ κ ℂ) :
    Vstep s = exp ((-(s.1 : ℂ) * Complex.I) •
      (s.2.1 ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ s.2.2)) := by
  unfold Vstep
  rw [smul_add, ← Matrix.smul_kronecker, ← Matrix.kronecker_smul, exp_local]

omit [Fintype ι] [Fintype κ] in
private lemma hermitian_local (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) (hA : Aᴴ = A) (hB : Bᴴ = B) :
    (A ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ B)ᴴ =
      A ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ B := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker,
    hA, hB, Matrix.conjTranspose_one, Matrix.conjTranspose_one]

private lemma Ustep_mem (H : Matrix (ι × κ) (ι × κ) ℂ) (hH : Hᴴ = H)
    (s : ℝ × Matrix ι ι ℂ × Matrix κ κ ℂ) (hA : s.2.1ᴴ = s.2.1) (hB : s.2.2ᴴ = s.2.2) :
    Ustep H s ∈ Matrix.unitaryGroup (ι × κ) ℂ :=
  exp_mem_unitaryGroup _ (skew_smul s.1 (by
    rw [Matrix.conjTranspose_add, hermitian_local _ _ hA hB, hH]))

private lemma Vstep_mem (s : ℝ × Matrix ι ι ℂ × Matrix κ κ ℂ) (hA : s.2.1ᴴ = s.2.1)
    (hB : s.2.2ᴴ = s.2.2) : Vstep s ∈ Matrix.unitaryGroup (ι × κ) ℂ := by
  rw [Vstep_eq]
  exact exp_mem_unitaryGroup _ (skew_smul s.1 (hermitian_local _ _ hA hB))

private lemma step_angle (H : Matrix (ι × κ) (ι × κ) ℂ) (hH : Hᴴ = H) (J : ℝ) (hJ : ‖H‖ ≤ J)
    (s : ℝ × Matrix ι ι ℂ × Matrix κ κ ℂ) (hτ : 0 ≤ s.1) (hA : s.2.1ᴴ = s.2.1)
    (hB : s.2.2ᴴ = s.2.2) (φ : EuclideanSpace ℂ (ι × κ)) (hφ : ‖φ‖ = 1) :
    fsAngle (act (Ustep H s) φ) (act (Vstep s) φ) ≤ J * s.1 := by
  have h := fsAngle_exp_add_exp_le _ _ (skew_smul s.1 (hermitian_local _ _ hA hB))
    (skew_smul s.1 hH) φ hφ
  rw [← smul_add, norm_smul] at h
  have hn : ‖(-(s.1 : ℂ) * Complex.I)‖ = s.1 := by
    simp [abs_of_nonneg hτ]
  rw [hn] at h
  rw [Vstep_eq]
  refine h.trans ?_
  nlinarith [norm_nonneg H]

private lemma chain (H : Matrix (ι × κ) (ι × κ) ℂ) (hH : Hᴴ = H) (J : ℝ) (hJ : ‖H‖ ≤ J)
    (l : List (ℝ × Matrix ι ι ℂ × Matrix κ κ ℂ)) (hτ : ∀ s ∈ l, 0 ≤ s.1)
    (hA : ∀ s ∈ l, s.2.1ᴴ = s.2.1) (hB : ∀ s ∈ l, s.2.2ᴴ = s.2.2) :
    (l.map (Ustep H)).prod ∈ Matrix.unitaryGroup (ι × κ) ℂ ∧
      (l.map Vstep).prod ∈ Matrix.unitaryGroup (ι × κ) ℂ ∧
      ∀ φ : EuclideanSpace ℂ (ι × κ), ‖φ‖ = 1 →
        fsAngle (act (l.map (Ustep H)).prod φ) (act (l.map Vstep).prod φ) ≤
          J * (l.map Prod.fst).sum := by
  induction l with
  | nil => exact ⟨by simp, by simp, fun φ hφ => by simp [act_one, fsAngle_self hφ]⟩
  | cons s l ih =>
    obtain ⟨hU, hV, hang⟩ := ih (fun t ht => hτ t (by simp [ht]))
      (fun t ht => hA t (by simp [ht])) (fun t ht => hB t (by simp [ht]))
    have hAs := hA s (by simp)
    have hBs := hB s (by simp)
    have hUs := Ustep_mem H hH s hAs hBs
    have hVs := Vstep_mem s hAs hBs
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    refine ⟨mul_mem hUs hU, mul_mem hVs hV, fun φ hφ => ?_⟩
    rw [act_mul, act_mul]
    have hu := (norm_act_of_mem hU φ).trans hφ
    have hv := (norm_act_of_mem hV φ).trans hφ
    have t := fsAngle_le_fsAngle_add_fsAngle ((norm_act_of_mem hUs _).trans hu)
      ((norm_act_of_mem hUs _).trans hv) ((norm_act_of_mem hVs _).trans hv)
    rw [fsAngle_act_act hUs] at t
    have h1 := hang φ hφ
    have h2 := step_angle H hH J hJ s (hτ s (by simp)) hAs hBs _ hv
    rw [mul_add]
    linarith

private lemma local_prod (l : List (ℝ × Matrix ι ι ℂ × Matrix κ κ ℂ))
    (hA : ∀ s ∈ l, s.2.1ᴴ = s.2.1) (hB : ∀ s ∈ l, s.2.2ᴴ = s.2.2) :
    ∃ (P : Matrix ι ι ℂ) (Q : Matrix κ κ ℂ), P ∈ Matrix.unitaryGroup ι ℂ ∧
      Q ∈ Matrix.unitaryGroup κ ℂ ∧ (l.map Vstep).prod = P ⊗ₖ Q := by
  induction l with
  | nil => exact ⟨1, 1, one_mem _, one_mem _, by simp⟩
  | cons s l ih =>
    obtain ⟨P, Q, hP, hQ, h⟩ :=
      ih (fun t ht => hA t (by simp [ht])) (fun t ht => hB t (by simp [ht]))
    refine ⟨exp ((-(s.1 : ℂ) * Complex.I) • s.2.1) * P,
      exp ((-(s.1 : ℂ) * Complex.I) • s.2.2) * Q, mul_mem (exp_mem_unitaryGroup _ ?_) hP,
      mul_mem (exp_mem_unitaryGroup _ ?_) hQ, ?_⟩
    · exact skew_smul s.1 (hA s (by simp))
    · exact skew_smul s.1 (hB s (by simp))
    · rw [List.map_cons, List.prod_cons, h, Vstep, ← Matrix.mul_kronecker_mul]

/-- (C) General entangling-time bound, any local dimensions. Let `H` be a Hermitian interaction
with `‖H‖ ≤ J`, and `U = ∏ₖ exp (−i τₖ (Aₖ ⊗ 1 + 1 ⊗ Bₖ + H))` (ordered product over `steps`,
`τₖ ≥ 0`, `Aₖ, Bₖ` Hermitian). If `U` maps the unit product vector `a ⊗ b` to `Φ`, and every unit
product vector has overlap at most `λ` with `Φ`, then `arccos λ ≤ J · ∑ τₖ`. -/
theorem arccos_le_entangling_time (H : Matrix (ι × κ) (ι × κ) ℂ) (hH : H.IsHermitian) (J : ℝ)
    (hJ : ‖H‖ ≤ J) (steps : List (ℝ × Matrix ι ι ℂ × Matrix κ κ ℂ))
    (hτ : ∀ s ∈ steps, 0 ≤ s.1) (hA : ∀ s ∈ steps, s.2.1.IsHermitian)
    (hB : ∀ s ∈ steps, s.2.2.IsHermitian) (a : EuclideanSpace ℂ ι) (b : EuclideanSpace ℂ κ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (Φ : EuclideanSpace ℂ (ι × κ))
    (hU : act (steps.map fun s => exp ((-(s.1 : ℂ) * Complex.I) •
        (s.2.1 ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ s.2.2 + H))).prod
        (prodVec a b) = Φ)
    (lam : ℝ) (hlam : ∀ (x : EuclideanSpace ℂ ι) (y : EuclideanSpace ℂ κ), ‖x‖ = 1 → ‖y‖ = 1 →
        ‖inner ℂ Φ (prodVec x y)‖ ≤ lam) :
    Real.arccos lam ≤ J * (steps.map Prod.fst).sum := by
  obtain ⟨-, -, hang⟩ := chain H hH.eq J hJ steps hτ (fun s hs => (hA s hs).eq)
    (fun s hs => (hB s hs).eq)
  obtain ⟨P, Q, hP, hQ, hV⟩ := local_prod steps (fun s hs => (hA s hs).eq)
    (fun s hs => (hB s hs).eq)
  have hab : ‖prodVec a b‖ = 1 := by rw [norm_prodVec, ha, hb, one_mul]
  have h1 := hang (prodVec a b) hab
  rw [hV, act_kronecker_prodVec] at h1
  change fsAngle (act (steps.map fun s => exp ((-(s.1 : ℂ) * Complex.I) •
        (s.2.1 ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ s.2.2 + H))).prod
        (prodVec a b)) _ ≤ _ at h1
  rw [hU] at h1
  refine le_trans (Real.arccos_le_arccos ?_) h1
  exact hlam _ _ ((norm_act_of_mem hP a).trans ha) ((norm_act_of_mem hQ b).trans hb)

/-- The two-level Bell vector `(e_{i₀ j₀} + e_{i₁ j₁}) / √2`. -/
def bellPair (i₀ i₁ : ι) (j₀ j₁ : κ) : EuclideanSpace ℂ (ι × κ) :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (EuclideanSpace.single (i₀, j₀) 1 + EuclideanSpace.single (i₁, j₁) 1)

private lemma sq_two_coords_le {m : Type*} [Fintype m] [DecidableEq m] {i₀ i₁ : m}
    (h : i₀ ≠ i₁) (a : EuclideanSpace ℂ m) : ‖a i₀‖ ^ 2 + ‖a i₁‖ ^ 2 ≤ ‖a‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {i₀, i₁})
    (f := fun i => ‖a i‖ ^ 2) (fun _ _ _ => sq_nonneg _)
  rwa [Finset.sum_pair h] at this

/-- Overlap of the two-level Bell vector with unit product vectors: at most `1/√2`. -/
theorem norm_inner_bellPair_prodVec_le {i₀ i₁ : ι} {j₀ j₁ : κ} (hi : i₀ ≠ i₁) (hj : j₀ ≠ j₁)
    (a : EuclideanSpace ℂ ι) (b : EuclideanSpace ℂ κ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖inner ℂ (bellPair i₀ i₁ j₀ j₁) (prodVec a b)‖ ≤ (Real.sqrt 2)⁻¹ := by
  have e : inner ℂ (bellPair i₀ i₁ j₀ j₁) (prodVec a b) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (a i₀ * b j₀ + a i₁ * b j₁) := by
    simp [bellPair, inner_smul_left, inner_add_left, EuclideanSpace.inner_single_left, prodVec]
    ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h1 := sq_two_coords_le hi a
  have h2 := sq_two_coords_le hj b
  rw [ha] at h1
  rw [hb] at h2
  have : ‖a i₀ * b j₀ + a i₁ * b j₁‖ ≤ 1 := by
    calc ‖a i₀ * b j₀ + a i₁ * b j₁‖ ≤ ‖a i₀ * b j₀‖ + ‖a i₁ * b j₁‖ := norm_add_le _ _
      _ = ‖a i₀‖ * ‖b j₀‖ + ‖a i₁‖ * ‖b j₁‖ := by rw [norm_mul, norm_mul]
      _ ≤ 1 := by
        nlinarith [sq_nonneg (‖a i₀‖ - ‖b j₀‖), sq_nonneg (‖a i₁‖ - ‖b j₁‖)]
  have hpos : 0 ≤ (Real.sqrt 2)⁻¹ := by positivity
  nlinarith

lemma arccos_inv_sqrt_two : Real.arccos (Real.sqrt 2)⁻¹ = Real.pi / 4 := by
  have h : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
    rw [eq_div_iff two_ne_zero, inv_mul_eq_div, div_eq_iff (by positivity)]
    exact (Real.mul_self_sqrt (by norm_num)).symm
  rw [h, ← Real.cos_pi_div_four, Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]

/-- (D) Preparing a two-level Bell vector `(e_{i₀ j₀} + e_{i₁ j₁}) / √2` from a unit product
vector with a bounded interaction `‖H‖ ≤ J` and arbitrary local controls takes
`J · ∑ τₖ ≥ π / 4`, in any local dimensions. -/
theorem pi_div_four_le_entangling_time (H : Matrix (ι × κ) (ι × κ) ℂ) (hH : H.IsHermitian)
    (J : ℝ) (hJ : ‖H‖ ≤ J) (steps : List (ℝ × Matrix ι ι ℂ × Matrix κ κ ℂ))
    (hτ : ∀ s ∈ steps, 0 ≤ s.1) (hA : ∀ s ∈ steps, s.2.1.IsHermitian)
    (hB : ∀ s ∈ steps, s.2.2.IsHermitian) (a : EuclideanSpace ℂ ι) (b : EuclideanSpace ℂ κ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) {i₀ i₁ : ι} {j₀ j₁ : κ} (hi : i₀ ≠ i₁) (hj : j₀ ≠ j₁)
    (hU : act (steps.map fun s => exp ((-(s.1 : ℂ) * Complex.I) •
        (s.2.1 ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ s.2.2 + H))).prod
        (prodVec a b) = bellPair i₀ i₁ j₀ j₁) :
    Real.pi / 4 ≤ J * (steps.map Prod.fst).sum := by
  rw [← arccos_inv_sqrt_two]
  exact arccos_le_entangling_time H hH J hJ steps hτ hA hB a b ha hb _ hU _
    fun x y hx hy => norm_inner_bellPair_prodVec_le hi hj x y hx hy

end Bipartite

/-- (D, qudits) For two qudits of dimension `d ≥ 2`, preparing `(e₀₀ + e₁₁)/√2` from a unit
product vector takes `J · ∑ τₖ ≥ π / 4`. -/
theorem pi_div_four_le_entangling_time_fin (d : ℕ) (hd : 2 ≤ d)
    (H : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hH : H.IsHermitian) (J : ℝ) (hJ : ‖H‖ ≤ J)
    (steps : List (ℝ × Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d) (Fin d) ℂ))
    (hτ : ∀ s ∈ steps, 0 ≤ s.1) (hA : ∀ s ∈ steps, s.2.1.IsHermitian)
    (hB : ∀ s ∈ steps, s.2.2.IsHermitian) (a b : EuclideanSpace ℂ (Fin d))
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hU : act (steps.map fun s => exp ((-(s.1 : ℂ) * Complex.I) •
        (s.2.1 ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ) + (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ s.2.2 + H))).prod
        (prodVec a b) = bellPair ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨0, by omega⟩ ⟨1, by omega⟩) :
    Real.pi / 4 ≤ J * (steps.map Prod.fst).sum :=
  pi_div_four_le_entangling_time H hH J hJ steps hτ hA hB a b ha hb
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) hU

/-! ### Tightness: `J · Z ⊗ X` reaches the Bell vector at `J · τ = π / 4` -/

section Tight

/-- `(1/√2 : ℂ)`. -/
private def rc : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)

private lemma rc_eq : ((Real.sqrt 2 : ℂ))⁻¹ = rc := by
  rw [rc, Complex.ofReal_inv]

private lemma rc_mul_rc : rc * rc = 1 / 2 := by
  have h : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num
  rw [rc, ← Complex.ofReal_mul, h]
  norm_num

private lemma inv_sqrt_two_eq : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
  rw [eq_div_iff two_ne_zero, inv_mul_eq_div, div_eq_iff (by positivity)]
  exact (Real.mul_self_sqrt (by norm_num)).symm

/-- The Hadamard matrix. -/
private def had : Matrix (Fin 2) (Fin 2) ℂ := rc • !![1, 1; 1, -1]

/-- `W = 1 ⊗ Had`. -/
private def Wm : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ had

/-- `Z ⊗ Z = diag(1, −1, −1, 1)`. -/
private def zz (p : Fin 2 × Fin 2) : ℂ := if p.1 = p.2 then 1 else -1

private lemma had_conj : hadᴴ = had := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [had, Matrix.conjTranspose_apply, rc]

private lemma had_mul_had : had * had = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [had, Matrix.mul_apply, Fin.sum_univ_two] <;>
    linear_combination 2 * rc_mul_rc

private lemma Wm_conj : Wmᴴ = Wm := by
  rw [Wm, Matrix.conjTranspose_kronecker, had_conj, Matrix.conjTranspose_one]

private lemma Wm_mul_Wm : Wm * Wm = 1 := by
  rw [Wm, ← Matrix.mul_kronecker_mul, had_mul_had, mul_one, Matrix.one_kronecker_one]

private lemma zz_conj : (Matrix.diagonal zz)ᴴ = Matrix.diagonal zz := by
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  simp only [Pi.star_apply, zz]
  split_ifs <;> simp

private lemma zz_mul_zz : Matrix.diagonal zz * Matrix.diagonal zz = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext p
  simp only [zz]
  split_ifs <;> simp

/-- `M = W (Z ⊗ Z) W = Z ⊗ X`. -/
private def Mzx : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := Wm * Matrix.diagonal zz * Wm

private lemma Mzx_conj : Mzxᴴ = Mzx := by
  rw [Mzx, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Wm_conj, zz_conj, mul_assoc]

private lemma Mzx_mem : Mzx ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Mzx_conj, Mzx]
  calc Wm * Matrix.diagonal zz * Wm * (Wm * Matrix.diagonal zz * Wm)
      = Wm * Matrix.diagonal zz * (Wm * Wm) * Matrix.diagonal zz * Wm := by noncomm_ring
    _ = 1 := by rw [Wm_mul_Wm, mul_one, mul_assoc Wm, zz_mul_zz, mul_one, Wm_mul_Wm]

/-- The exponent `−i (π/4) zz`. -/
private def fexp (p : Fin 2 × Fin 2) : ℂ :=
  (((if p.1 = p.2 then -(Real.pi / 4) else Real.pi / 4 : ℝ)) : ℂ) * Complex.I

private lemma exp_diag_fexp : exp (Matrix.diagonal fexp) =
    Matrix.diagonal fun p => if p.1 = p.2 then rc - rc * Complex.I else rc + rc * Complex.I := by
  let +nondep : NormedAlgebra ℚ ℂ := .restrictScalars ℚ ℂ _
  rw [Matrix.exp_diagonal]
  congr 1
  funext p
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, fexp, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]
  have h : Real.cos (Real.pi / 4) = (Real.sqrt 2)⁻¹ := by
    rw [Real.cos_pi_div_four, inv_sqrt_two_eq]
  have h' : Real.sin (Real.pi / 4) = (Real.sqrt 2)⁻¹ := by
    rw [Real.sin_pi_div_four, inv_sqrt_two_eq]
  split_ifs
  · rw [Real.cos_neg, Real.sin_neg, h, h']; push_cast; rw [rc_eq]; ring
  · rw [h, h']; rfl

/-- (E) Tightness: for two qubits, `H = J · Z ⊗ X` and one step of length `π / (4 J)` with no
local control map the unit product vector `((1, −i)/√2) ⊗ ((1, i)/√2)` to the Bell vector, so the
bound `π / 4 ≤ J · ∑ τₖ` of `pi_div_four_le_entangling_time` is attained. -/
theorem entangling_time_tight (J : ℝ) (hJ : 0 < J) :
    ∃ (H : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
      (steps : List (ℝ × Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ))
      (a b : EuclideanSpace ℂ (Fin 2)),
      H.IsHermitian ∧ ‖H‖ ≤ J ∧ (∀ s ∈ steps, 0 ≤ s.1) ∧ (∀ s ∈ steps, s.2.1.IsHermitian) ∧
      (∀ s ∈ steps, s.2.2.IsHermitian) ∧ ‖a‖ = 1 ∧ ‖b‖ = 1 ∧
      act (steps.map fun s => exp ((-(s.1 : ℂ) * Complex.I) •
        (s.2.1 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) + (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ s.2.2 + H))).prod
        (prodVec a b) = bellPair 0 1 0 1 ∧
      J * (steps.map Prod.fst).sum = Real.pi / 4 := by
  have hJ0 : (J : ℂ) ≠ 0 := by exact_mod_cast hJ.ne'
  refine ⟨(J : ℂ) • Mzx, [(Real.pi / (4 * J), 0, 0)], WithLp.toLp 2 ![rc, -(rc * Complex.I)],
    WithLp.toLp 2 ![rc, rc * Complex.I], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show ((J : ℂ) • Mzx)ᴴ = (J : ℂ) • Mzx
    rw [Matrix.conjTranspose_smul, Mzx_conj]
    simp
  · rw [norm_smul, CStarRing.norm_of_mem_unitary Mzx_mem, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hJ.le]
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst hs
    positivity
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst hs
    exact Matrix.isHermitian_zero
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst hs
    exact Matrix.isHermitian_zero
  · have : ‖WithLp.toLp 2 ![rc, -(rc * Complex.I)]‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      simp [rc]
      norm_num
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 (by rw [this, one_pow])
  · have :‖WithLp.toLp 2 ![rc, rc * Complex.I]‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      simp [rc]
      norm_num
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 (by rw [this, one_pow])
  · have hstep : (-((Real.pi / (4 * J) : ℝ) : ℂ) * Complex.I) •
        ((0 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) +
          (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (0 : Matrix (Fin 2) (Fin 2) ℂ) + (J : ℂ) • Mzx) =
        Wm * Matrix.diagonal fexp * Wm⁻¹ := by
      rw [Matrix.inv_eq_right_inv Wm_mul_Wm, Matrix.zero_kronecker, Matrix.kronecker_zero,
        zero_add, zero_add, smul_smul, Mzx, ← Matrix.smul_mul, ← Matrix.mul_smul,
        ← Matrix.diagonal_smul]
      congr 1
      congr 1
      congr 1
      funext p
      simp only [Pi.smul_apply, smul_eq_mul, zz, fexp]
      split_ifs
      · push_cast; field_simp
      · push_cast; field_simp
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [hstep, Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse Wm_mul_Wm)),
      Matrix.inv_eq_right_inv Wm_mul_Wm, exp_diag_fexp]
    have h5 : rc ^ 5 = rc / 4 := by
      have e : rc ^ 5 = rc * (rc * rc) * (rc * rc) := by ring
      rw [e, rc_mul_rc]; ring
    have hI3 : Complex.I ^ 3 = -Complex.I := by
      rw [pow_succ, Complex.I_sq]; ring
    ext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp [act, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, Wm, had,
        Matrix.kroneckerMap_apply, Matrix.diagonal, prodVec, bellPair, Matrix.mul_apply,
        rc_eq] <;>
      ring_nf <;>
      simp only [h5, Complex.I_sq, hI3] <;>
      ring
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    field_simp

end Tight

end QSL.Qudit
