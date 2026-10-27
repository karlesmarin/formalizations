/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.Physics.QuantumMechanics.SpeedLimit.GateEigenphases
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
public import Mathlib.Algebra.Order.Round

/-!
# Gate time from the spectral arc of the eigenphases

An ordered product `U = ∏ₖ exp (−i τₖ Hₖ)` (`τₖ ≥ 0`, `Hₖ` Hermitian) whose Hamiltonians have
spectral half-width `‖Hₖ − cₖ • 1‖ ≤ Ω / 2` satisfies, up to the global phase `e^{−i ∑ τₖ cₖ}`,
`V = ∏ₖ exp (−i τₖ (Hₖ − cₖ))`, and `V` moves every unit vector by at most `(Ω / 2) ∑ τₖ` in the
*sphere angle* `sAngle u v = arccos (Re ⟪u, v⟫)` (not the projective Fubini–Study angle, which
forgets the phase). Consequently every eigenvalue `e^{iθ}` of `V` has `|θ| ≤ (Ω / 2) ∑ τₖ`
(representative `θ ∈ [−π, π]`): all eigenphases of the gate lie in an arc of length `Ω ∑ τₖ`
modulo `2π`. This removes the restriction `|Δφ| ≤ π` of `QSL.Gate.gate_time_ge_eigenphase_gap`.

This is the finite-dimensional, piecewise-constant version of the classical spectral-arc bound
for products of unitaries (Nudel'man–Švarcman 1958; Thompson 1986; Miglioli, arXiv:2310.06331,
Thm 4.4 / Cor 4.5). Nelson and Barnes, arXiv:2604.23031, eq. (3) state `T ≥ Δφ⋆ / Ω`. The proof
is elementary: the sphere angle satisfies the triangle inequality (Mathlib's
`InnerProductGeometry.angle_le_angle_add_angle`), is invariant under unitaries, and a Duhamel
estimate with `N` equal pieces and `N → ∞` bounds one step.

For the two-qubit gate `exp (i π/4 (2 Z⊗I + I⊗Z)) = diag (e^{3iπ/4}, e^{iπ/4}, e^{−iπ/4}, e^{−3iπ/4})`
(Nelson–Barnes, Table I) four eigenphases spaced by `π/2` do not fit in an arc shorter than `3π/2`,
so `Ω ∑ τₖ ≥ 3π/2`.

## Main results

* `QSL.Gate.sAngle`: the sphere angle `arccos (Re ⟪u, v⟫)`
* `QSL.Gate.sAngle_le_sAngle_add_sAngle`, `QSL.Gate.sAngle_act_act`: triangle inequality,
  invariance under a unitary
* `QSL.Gate.sAngle_exp_le`: `sAngle (exp Y ψ) ψ ≤ ‖Y‖` for skew-Hermitian `Y`
* `QSL.Gate.sAngle_centred_le_time`: `sAngle (V v) v ≤ (Ω / 2) ∑ τₖ` for the centred product `V`
* `QSL.Gate.abs_le_of_eigen`: `|θ| ≤ (Ω / 2) ∑ τₖ` for an eigenphase `θ ∈ [−π, π]` of `V`
* `QSL.Gate.spectral_arc_le_time`: all eigenphases of `G` fit in an arc of length `Ω ∑ τₖ`
* `QSL.Gate.u4d_time_ge`: `3π/2 ≤ Ω ∑ τₖ` for `diag (e^{3iπ/4}, e^{iπ/4}, e^{−iπ/4}, e^{−3iπ/4})`

## References

* A. A. Nudel'man, P. A. Švarcman, *The spectrum of the product of unitary matrices* (Russian),
  Uspehi Mat. Nauk 13 (1958), no. 6 (84), 111–117 (as cited in Miglioli).
* R. C. Thompson, *Proof of a conjectured exponential formula*, Linear and Multilinear Algebra 19
  (1986), no. 2, 187–197 (as cited in Miglioli).
* M. Miglioli, *Geometry of spectral bounds of curves of unitary operators*, arXiv:2310.06331,
  Thm 4.4 and Cor 4.5.
* H. Nelson, E. Barnes, *How fast can a quantum gate be? Exact speed limits from geometry*,
  arXiv:2604.23031 (2026), eq. (3) and Table I.
-/

@[expose] public section

noncomputable section

open scoped Matrix
open scoped Matrix.Norms.L2Operator
open NormedSpace Filter Topology
open QSL.TwoQubit (act)
open QSL.Qudit

namespace QSL.Gate

/-! ### The sphere angle -/

section Sphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The sphere angle `arccos (Re ⟪u, v⟫)` between (unit) vectors; unlike `fsAngle` it keeps the
phase. -/
def sAngle (u v : E) : ℝ := Real.arccos (inner ℂ u v).re

lemma sAngle_comm (u v : E) : sAngle u v = sAngle v u := by
  have h := inner_conj_symm (𝕜 := ℂ) u v
  rw [sAngle, sAngle, ← h, Complex.conj_re]

lemma sAngle_self {u : E} (hu : ‖u‖ = 1) : sAngle u u = 0 := by
  rw [sAngle, inner_self_eq_norm_sq_to_K, hu]
  simp

/-- Triangle inequality for the sphere angle of unit vectors (from Mathlib's
`InnerProductGeometry.angle_le_angle_add_angle` for the underlying real inner product space). -/
theorem sAngle_le_sAngle_add_sAngle {u v w : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    sAngle u w ≤ sAngle u v + sAngle v w := by
  let _ : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  have key : ∀ {a b : E}, ‖a‖ = 1 → ‖b‖ = 1 → sAngle a b = InnerProductGeometry.angle a b := by
    intro a b ha hb
    unfold InnerProductGeometry.angle
    rw [ha, hb, mul_one, div_one]
    rfl
  rw [key hu hw, key hu hv, key hv hw]
  exact InnerProductGeometry.angle_le_angle_add_angle u v w

/-- Chord bound: unit vectors at distance at most `c` are at sphere angle at most
`arccos (1 − c²/2)`. -/
lemma sAngle_le_of_norm_sub_le {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) {c : ℝ}
    (h : ‖x - y‖ ≤ c) : sAngle x y ≤ Real.arccos (1 - c ^ 2 / 2) := by
  apply Real.arccos_le_arccos
  have e := norm_sub_sq (𝕜 := ℂ) x y
  rw [hx, hy] at e
  have hc : ‖x - y‖ ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  have e' : (inner ℂ x y).re = (1 ^ 2 + 1 ^ 2 - ‖x - y‖ ^ 2) / 2 := by
    simp only [RCLike.re_to_complex] at e
    linarith
  rw [e']
  nlinarith

end Sphere

/-! ### Unitary invariance -/

section Unitary

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The sphere angle is invariant under a unitary applied to both vectors. -/
theorem sAngle_act_act {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (u v : EuclideanSpace ℂ n) : sAngle (act U u) (act U v) = sAngle u v := by
  rw [sAngle, inner_act_act hU, sAngle]

omit [Fintype n] [DecidableEq n] in
private lemma skew_smul (τ : ℝ) {M : Matrix n n ℂ} (hM : Mᴴ = M) :
    ((-(τ : ℂ) * Complex.I) • M)ᴴ = -((-(τ : ℂ) * Complex.I) • M) := by
  rw [Matrix.conjTranspose_smul, hM, ← neg_smul]
  congr 1
  apply Complex.ext <;> simp

/-! ### One step: `sAngle (exp Y ψ) ψ ≤ ‖Y‖` -/

/-- **Duhamel step on the sphere.** For skew-Hermitian `Y` and a unit vector `ψ`,
`sAngle (exp Y ψ) ψ ≤ ‖Y‖`. -/
theorem sAngle_exp_le (Y : Matrix n n ℂ) (hY : Yᴴ = -Y) (ψ : EuclideanSpace ℂ n)
    (hψ : ‖ψ‖ = 1) : sAngle (act (exp Y) ψ) ψ ≤ ‖Y‖ := by
  have : Nonempty n := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have h0 : ψ = 0 := by
      ext i
      exact isEmptyElim i
    rw [h0, norm_zero] at hψ
    exact zero_ne_one hψ
  have hbound : ∀ N : ℕ, 0 < N → ‖Y‖ / N < 2 →
      sAngle (act (exp Y) ψ) ψ ≤ ‖Y‖ / Real.sqrt (1 - (‖Y‖ / N) ^ 2 / 4) := by
    intro N hN hc2
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    set Y' := ((N : ℂ)⁻¹) • Y with hY'
    have hsY : Y'ᴴ = -Y' := by
      rw [hY', Matrix.conjTranspose_smul, hY, smul_neg]
      congr 2
      simp
    set P := exp Y'
    have hP : P ∈ Matrix.unitaryGroup n ℂ := exp_mem_unitaryGroup _ hsY
    have hnY : ‖Y'‖ = ‖Y‖ / N := by
      rw [hY', norm_smul, norm_inv, Complex.norm_natCast, inv_mul_eq_div]
    set c := ‖Y‖ / N with hc
    have hc0 : 0 ≤ c := by positivity
    have hPQ : ‖P - 1‖ ≤ c := by
      have := QSL.TwoQubit.norm_exp_add_sub_exp_le (0 : Matrix n n ℂ) Y' (by simp) hsY
      rw [zero_add, exp_zero] at this
      exact hnY ▸ this
    have hstep : ∀ φ : EuclideanSpace ℂ n, ‖φ‖ = 1 →
        sAngle (act P φ) φ ≤ Real.arccos (1 - c ^ 2 / 2) := by
      intro φ hφ
      refine sAngle_le_of_norm_sub_le ((norm_act_of_mem hP φ).trans hφ) hφ ?_
      have : act P φ - φ = act (P - 1) φ := by rw [act_sub, act_one]
      rw [this]
      refine (Matrix.l2_opNorm_mulVec (P - 1) φ).trans ?_
      rw [hφ, mul_one]
      exact hPQ
    have htel : ∀ m : ℕ, ∀ φ : EuclideanSpace ℂ n, ‖φ‖ = 1 →
        sAngle (act (P ^ m) φ) φ ≤ m * Real.arccos (1 - c ^ 2 / 2) := by
      intro m
      induction m with
      | zero =>
        intro φ hφ
        simp [act_one, sAngle_self hφ]
      | succ m ih =>
        intro φ hφ
        have hPm : ‖act (P ^ m) φ‖ = 1 := (norm_act_of_mem (pow_mem hP m) φ).trans hφ
        have hPφ : ‖act P φ‖ = 1 := (norm_act_of_mem hP φ).trans hφ
        rw [pow_succ', act_mul]
        have t := sAngle_le_sAngle_add_sAngle ((norm_act_of_mem hP _).trans hPm) hPφ hφ
        rw [sAngle_act_act hP] at t
        have h1 := ih φ hφ
        have h2 := hstep φ hφ
        push_cast
        linarith
    have hexp : exp Y = P ^ N := by
      let +nondep : NormedAlgebra ℚ (Matrix n n ℂ) := .restrictScalars ℚ ℂ _
      rw [← exp_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, hY', smul_smul, mul_inv_cancel₀ hN', one_smul]
    rw [hexp]
    refine (htel N ψ hψ).trans ?_
    have ha := arccos_one_sub_le hc0 hc2
    calc (N : ℝ) * Real.arccos (1 - c ^ 2 / 2) ≤ N * (c / Real.sqrt (1 - c ^ 2 / 4)) :=
          mul_le_mul_of_nonneg_left ha hNr.le
      _ = ‖Y‖ / Real.sqrt (1 - c ^ 2 / 4) := by
          rw [hc]; field_simp
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

/-! ### The chain -/

omit [Fintype n] in
private lemma herm_centre (c : ℝ) {H : Matrix n n ℂ} (hH : Hᴴ = H) :
    (H - (c : ℂ) • (1 : Matrix n n ℂ))ᴴ = H - (c : ℂ) • (1 : Matrix n n ℂ) := by
  rw [Matrix.conjTranspose_sub, hH, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  simp

/-- The centred evolution of one step: `exp (−i τ (H − c • 1))`. -/
def centredStep (s : ℝ × ℝ × Matrix n n ℂ) : Matrix n n ℂ :=
  exp ((-(s.1 : ℂ) * Complex.I) • (s.2.2 - (s.2.1 : ℂ) • (1 : Matrix n n ℂ)))

private lemma chain (Ω : ℝ) (l : List (ℝ × ℝ × Matrix n n ℂ)) (hτ : ∀ s ∈ l, 0 ≤ s.1)
    (hH : ∀ s ∈ l, s.2.2ᴴ = s.2.2)
    (hΩ : ∀ s ∈ l, ‖s.2.2 - (s.2.1 : ℂ) • (1 : Matrix n n ℂ)‖ ≤ Ω / 2) :
    (l.map centredStep).prod ∈ Matrix.unitaryGroup n ℂ ∧
      ∀ φ : EuclideanSpace ℂ n, ‖φ‖ = 1 →
        sAngle (act (l.map centredStep).prod φ) φ ≤ Ω / 2 * (l.map Prod.fst).sum := by
  induction l with
  | nil => exact ⟨by simp, fun φ hφ => by simp [act_one, sAngle_self hφ]⟩
  | cons s l ih =>
    obtain ⟨hU, hang⟩ := ih (fun t ht => hτ t (by simp [ht])) (fun t ht => hH t (by simp [ht]))
      (fun t ht => hΩ t (by simp [ht]))
    have hsk := skew_smul s.1 (herm_centre s.2.1 (hH s (by simp)))
    have hUs : centredStep s ∈ Matrix.unitaryGroup n ℂ := exp_mem_unitaryGroup _ hsk
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    refine ⟨mul_mem hUs hU, fun φ hφ => ?_⟩
    rw [act_mul]
    have hu := (norm_act_of_mem hU φ).trans hφ
    have t := sAngle_le_sAngle_add_sAngle ((norm_act_of_mem hUs _).trans hu)
      ((norm_act_of_mem hUs _).trans hφ) hφ
    rw [sAngle_act_act hUs] at t
    have h1 := hang φ hφ
    have hτs := hτ s (by simp)
    have h2 : sAngle (act (centredStep s) φ) φ ≤ Ω / 2 * s.1 := by
      refine (sAngle_exp_le _ hsk φ hφ).trans ?_
      have hn : ‖(-(s.1 : ℂ) * Complex.I)‖ = s.1 := by
        simp [abs_of_nonneg hτs]
      rw [norm_smul, hn, mul_comm]
      exact mul_le_mul_of_nonneg_right (hΩ s (by simp)) hτs
    rw [mul_add]
    linarith

/-- **Sphere-angle bound for the centred product.** Let `V = ∏ₖ exp (−i τₖ (Hₖ − cₖ • 1))` with
`τₖ ≥ 0`, `Hₖ` Hermitian and `‖Hₖ − cₖ • 1‖ ≤ Ω / 2`. Then `sAngle (V v) v ≤ (Ω / 2) · ∑ τₖ` for
every unit vector `v`. -/
theorem sAngle_centred_le_time (Ω : ℝ) (steps : List (ℝ × ℝ × Matrix n n ℂ))
    (hτ : ∀ s ∈ steps, 0 ≤ s.1) (hH : ∀ s ∈ steps, s.2.2.IsHermitian)
    (hΩ : ∀ s ∈ steps, ‖s.2.2 - (s.2.1 : ℂ) • (1 : Matrix n n ℂ)‖ ≤ Ω / 2)
    (v : EuclideanSpace ℂ n) (hv : ‖v‖ = 1) :
    sAngle (act (steps.map centredStep).prod v) v ≤ Ω / 2 * (steps.map Prod.fst).sum :=
  (chain Ω steps hτ (fun s hs => (hH s hs).eq) hΩ).2 v hv

/-! ### Eigenphases of the centred product -/

omit [DecidableEq n] in
/-- If `ξ` is a unit eigenvector, `V ξ = e^{iθ} ξ`, with `|θ| ≤ π`, then `sAngle (V ξ) ξ = |θ|`,
and by the chain bound `|θ| ≤ (Ω / 2) ∑ τₖ`. -/
theorem sAngle_eigen {V : Matrix n n ℂ} {ξ : EuclideanSpace ℂ n} (hξ : ‖ξ‖ = 1) {θ : ℝ}
    (hθ : |θ| ≤ Real.pi) (hV : act V ξ = Complex.exp (θ * Complex.I) • ξ) :
    sAngle (act V ξ) ξ = |θ| := by
  have hin : inner ℂ (act V ξ) ξ = Complex.exp (-(θ : ℂ) * Complex.I) := by
    rw [hV, inner_smul_left, inner_self_eq_norm_sq_to_K, hξ]
    simp [← Complex.exp_conj]
  rw [sAngle, hin]
  have : (Complex.exp (-(θ : ℂ) * Complex.I)).re = Real.cos θ := by
    have := Complex.exp_ofReal_mul_I_re (-θ)
    rw [Real.cos_neg] at this
    simpa using this
  rw [this, ← Real.cos_abs]
  exact Real.arccos_cos (abs_nonneg _) hθ

/-- **Eigenphase bound.** In the situation of `sAngle_centred_le_time`, an eigenvalue `e^{iθ}` of
`V` with unit eigenvector and `|θ| ≤ π` has `|θ| ≤ (Ω / 2) · ∑ τₖ`. -/
theorem abs_le_of_eigen (Ω : ℝ) (steps : List (ℝ × ℝ × Matrix n n ℂ))
    (hτ : ∀ s ∈ steps, 0 ≤ s.1) (hH : ∀ s ∈ steps, s.2.2.IsHermitian)
    (hΩ : ∀ s ∈ steps, ‖s.2.2 - (s.2.1 : ℂ) • (1 : Matrix n n ℂ)‖ ≤ Ω / 2)
    (ξ : EuclideanSpace ℂ n) (hξ : ‖ξ‖ = 1) {θ : ℝ} (hθ : |θ| ≤ Real.pi)
    (hV : act (steps.map centredStep).prod ξ = Complex.exp (θ * Complex.I) • ξ) :
    |θ| ≤ Ω / 2 * (steps.map Prod.fst).sum := by
  have h := sAngle_centred_le_time Ω steps hτ hH hΩ ξ hξ
  rwa [sAngle_eigen hξ hθ hV] at h

/-! ### Relating `U` to the centred product -/

private lemma exp_scalar (z : ℂ) :
    exp (z • (1 : Matrix n n ℂ)) = Complex.exp z • (1 : Matrix n n ℂ) := by
  let +nondep : NormedAlgebra ℚ ℂ := .restrictScalars ℚ ℂ _
  rw [Matrix.smul_one_eq_diagonal, Matrix.exp_diagonal, Matrix.smul_one_eq_diagonal]
  congr 1
  funext p
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]

private lemma exp_step (s : ℝ × ℝ × Matrix n n ℂ) :
    exp ((-(s.1 : ℂ) * Complex.I) • s.2.2) =
      Complex.exp ((-(s.1 : ℂ) * Complex.I) * s.2.1) • centredStep s := by
  let +nondep : NormedAlgebra ℚ (Matrix n n ℂ) := .restrictScalars ℚ ℂ _
  have h : (-(s.1 : ℂ) * Complex.I) • s.2.2 =
      ((-(s.1 : ℂ) * Complex.I) * s.2.1) • (1 : Matrix n n ℂ) +
        (-(s.1 : ℂ) * Complex.I) • (s.2.2 - (s.2.1 : ℂ) • (1 : Matrix n n ℂ)) := by
    rw [smul_sub, smul_smul]
    abel
  have hc : Commute (((-(s.1 : ℂ) * Complex.I) * s.2.1) • (1 : Matrix n n ℂ))
      ((-(s.1 : ℂ) * Complex.I) • (s.2.2 - (s.2.1 : ℂ) • (1 : Matrix n n ℂ))) := by
    show _ * _ = _ * _
    simp only [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
    exact smul_comm _ _ _
  rw [h, exp_add_of_commute hc, exp_scalar, Matrix.smul_mul, one_mul]
  rfl

/-- The total centring phase `∑ τₖ cₖ`. -/
def phaseSum (steps : List (ℝ × ℝ × Matrix n n ℂ)) : ℝ :=
  (steps.map fun s => s.1 * s.2.1).sum

private lemma prod_U (steps : List (ℝ × ℝ × Matrix n n ℂ)) :
    (steps.map fun s => exp ((-(s.1 : ℂ) * Complex.I) • s.2.2)).prod =
      Complex.exp (((-phaseSum steps : ℝ) : ℂ) * Complex.I) • (steps.map centredStep).prod := by
  induction steps with
  | nil => simp [phaseSum]
  | cons s l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [ih, exp_step, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    rw [← Complex.exp_add]
    congr 1
    simp only [phaseSum, List.map_cons, List.sum_cons]
    push_cast
    ring

omit [DecidableEq n] in
private lemma act_smul_mat (a : ℂ) (M : Matrix n n ℂ) (v : EuclideanSpace ℂ n) :
    act (a • M) v = a • act M v := by
  ext i
  simp [act, Matrix.smul_mulVec]

/-- **Spectral arc of a product of evolutions** (finite-dimensional Nudel'man–Švarcman /
Thompson / Miglioli, arXiv:2310.06331, Thm 4.4 / Cor 4.5). Let `U = ∏ₖ exp (−i τₖ Hₖ)` with
`τₖ ≥ 0`, `Hₖ` Hermitian and `‖Hₖ − cₖ • 1‖ ≤ Ω / 2`, and suppose `U = ω • G` (global phase `ω`).
If `G eⱼ = e^{i φⱼ} eⱼ` for unit vectors `eⱼ` (any family), then there is a centre `β` such that
every eigenphase satisfies `|φⱼ − β − 2π mⱼ| ≤ (Ω / 2) · ∑ τₖ` for some integer `mⱼ`: all
eigenphases lie in an arc of length `Ω ∑ τₖ` modulo `2π`. No restriction on the size of the
eigenphase gaps (cf. `gate_time_ge_eigenphase_gap`, gaps `≤ π`). -/
theorem spectral_arc_le_time (Ω : ℝ) (steps : List (ℝ × ℝ × Matrix n n ℂ))
    (hτ : ∀ s ∈ steps, 0 ≤ s.1) (hH : ∀ s ∈ steps, s.2.2.IsHermitian)
    (hΩ : ∀ s ∈ steps, ‖s.2.2 - (s.2.1 : ℂ) • (1 : Matrix n n ℂ)‖ ≤ Ω / 2)
    (ω : ℂ) (G : Matrix n n ℂ)
    (hUG : (steps.map fun s => exp ((-(s.1 : ℂ) * Complex.I) • s.2.2)).prod = ω • G)
    {ι : Type*} (e : ι → EuclideanSpace ℂ n) (he : ∀ j, ‖e j‖ = 1) (φ : ι → ℝ)
    (hG : ∀ j, act G (e j) = Complex.exp (φ j * Complex.I) • e j) :
    ∃ β : ℝ, ∀ j, ∃ m : ℤ, |φ j - β - 2 * Real.pi * m| ≤ Ω / 2 * (steps.map Prod.fst).sum := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨j0⟩⟩
  · exact ⟨0, fun j => isEmptyElim j⟩
  obtain ⟨hV, -⟩ := chain Ω steps hτ (fun s hs => (hH s hs).eq) hΩ
  have hVU : (steps.map centredStep).prod =
      Complex.exp ((phaseSum steps : ℂ) * Complex.I) • ω • G := by
    rw [← hUG, prod_U, smul_smul, ← Complex.exp_add]
    have : (phaseSum steps : ℂ) * Complex.I + ((-phaseSum steps : ℝ) : ℂ) * Complex.I = 0 := by
      push_cast; ring
    rw [this, Complex.exp_zero, one_smul]
  obtain ⟨κ, hκ⟩ : ∃ κ : ℂ, κ = Complex.exp ((phaseSum steps : ℂ) * Complex.I) * ω := ⟨_, rfl⟩
  have hVe : ∀ j, act (steps.map centredStep).prod (e j) =
      (κ * Complex.exp (φ j * Complex.I)) • e j := by
    intro j
    rw [hVU, act_smul_mat, act_smul_mat, hG, smul_smul, smul_smul, hκ, mul_assoc]
  have hκ1 : ‖κ‖ = 1 := by
    have h1 := norm_act_of_mem hV (e j0)
    rw [hVe, norm_smul, norm_mul, he, Complex.norm_exp_ofReal_mul_I] at h1
    linarith
  obtain ⟨a, ha⟩ : ∃ a : ℝ, κ = Complex.exp (a * Complex.I) := by
    refine ⟨Complex.arg κ, ?_⟩
    have := Complex.norm_mul_exp_arg_mul_I κ
    rw [hκ1, Complex.ofReal_one, one_mul] at this
    exact this.symm
  refine ⟨-a, fun j => ?_⟩
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = φ j + a := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : ℤ, m = round (x / (2 * Real.pi)) := ⟨_, rfl⟩
  have hpi := Real.pi_pos
  have hθ : |x - 2 * Real.pi * m| ≤ Real.pi := by
    have h := abs_sub_round (x / (2 * Real.pi))
    rw [← hm] at h
    have e1 : x - 2 * Real.pi * m = 2 * Real.pi * (x / (2 * Real.pi) - m) := by
      field_simp
    rw [e1, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    nlinarith
  have hV' : act (steps.map centredStep).prod (e j) =
      Complex.exp (((x - 2 * Real.pi * m : ℝ) : ℂ) * Complex.I) • e j := by
    rw [hVe, ha]
    congr 1
    rw [← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨m, ?_⟩
    rw [hx]
    push_cast
    ring
  have := abs_le_of_eigen Ω steps hτ hH hΩ (e j) (he j) hθ hV'
  refine ⟨m, ?_⟩
  rw [show φ j - -a - 2 * Real.pi * m = x - 2 * Real.pi * m by rw [hx]; ring]
  exact this

end Unitary

/-! ### The gate `exp (i π/4 (2 Z⊗I + I⊗Z))` of Nelson–Barnes -/

/-- The two-qubit gate `diag (e^{3iπ/4}, e^{iπ/4}, e^{−iπ/4}, e^{−3iπ/4})`
`= exp (i π/4 (2 Z⊗I + I⊗Z))` (Nelson–Barnes, arXiv:2604.23031, Table I), with eigenphases
`3π/4 − j π/2`, `j = 0, 1, 2, 3`. -/
def u4d : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal fun j =>
    Complex.exp (((3 * Real.pi / 4 - ((j : ℕ) : ℝ) * Real.pi / 2 : ℝ) : ℂ) * Complex.I)

private lemma int_zero_of_lt {k : ℤ} (h : |Real.pi / 2 - 2 * Real.pi * k| < 3 * Real.pi / 2) :
    k = 0 := by
  have hp := Real.pi_pos
  rw [abs_lt] at h
  obtain ⟨h1, h2⟩ := h
  have a1 : (k : ℝ) < 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  have a2 : (-1 : ℝ) < k := by
    by_contra hc
    push Not at hc
    nlinarith
  have b1 : k < 1 := by exact_mod_cast a1
  have b2 : -1 < k := by exact_mod_cast a2
  omega

/-- **`U₄d` needs time `3π / (2 Ω)`.** Any ordered product `∏ₖ exp (−i τₖ Hₖ)` (`τₖ ≥ 0`, `Hₖ`
Hermitian on two qubits, `‖Hₖ − cₖ • 1‖ ≤ Ω / 2`) equal to `u4d` up to a global phase has
`3π / 2 ≤ Ω · ∑ τₖ`: four eigenphases spaced by `π/2` do not fit in an arc shorter than `3π/2`
(`spectral_arc_le_time`). Nelson–Barnes, arXiv:2604.23031, Table I. -/
theorem u4d_time_ge (Ω : ℝ) (steps : List (ℝ × ℝ × Matrix (Fin 4) (Fin 4) ℂ))
    (hτ : ∀ s ∈ steps, 0 ≤ s.1) (hH : ∀ s ∈ steps, s.2.2.IsHermitian)
    (hΩ : ∀ s ∈ steps, ‖s.2.2 - (s.2.1 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)‖ ≤ Ω / 2)
    (ω : ℂ)
    (hUG : (steps.map fun s => exp ((-(s.1 : ℂ) * Complex.I) • s.2.2)).prod = ω • u4d) :
    3 * Real.pi / 2 ≤ Ω * (steps.map Prod.fst).sum := by
  obtain ⟨β, hβ⟩ := spectral_arc_le_time Ω steps hτ hH hΩ ω u4d hUG
    (fun j : Fin 4 => EuclideanSpace.single j (1 : ℂ)) (by simp)
    (fun j : Fin 4 => 3 * Real.pi / 4 - ((j : ℕ) : ℝ) * Real.pi / 2)
    (by
      intro j
      ext i
      by_cases h : i = j <;> simp [act, u4d, h])
  obtain ⟨m0, h0⟩ := hβ 0
  obtain ⟨m1, h1⟩ := hβ 1
  obtain ⟨m2, h2⟩ := hβ 2
  obtain ⟨m3, h3⟩ := hβ 3
  have c0 : (((0 : Fin 4) : ℕ) : ℝ) = 0 := by simp
  have c1 : (((1 : Fin 4) : ℕ) : ℝ) = 1 := by simp
  have c2 : (((2 : Fin 4) : ℕ) : ℝ) = 2 := by simp
  have c3 : (((3 : Fin 4) : ℕ) : ℝ) = 3 := by simp
  simp only [c0, c1, c2, c3] at h0 h1 h2 h3
  rw [abs_le] at h0 h1 h2 h3
  by_contra hlt
  push Not at hlt
  have hp := Real.pi_pos
  have hA : Ω / 2 * (steps.map Prod.fst).sum < 3 * Real.pi / 4 := by linarith
  have e01 : m0 - m1 = 0 := by
    apply int_zero_of_lt
    push_cast
    rw [abs_lt]
    constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]
  have e12 : m1 - m2 = 0 := by
    apply int_zero_of_lt
    push_cast
    rw [abs_lt]
    constructor <;> linarith [h2.1, h2.2, h1.1, h1.2]
  have e23 : m2 - m3 = 0 := by
    apply int_zero_of_lt
    push_cast
    rw [abs_lt]
    constructor <;> linarith [h2.1, h2.2, h3.1, h3.2]
  have f01 : (m0 : ℝ) = m1 := by exact_mod_cast sub_eq_zero.1 e01
  have f12 : (m1 : ℝ) = m2 := by exact_mod_cast sub_eq_zero.1 e12
  have f23 : (m2 : ℝ) = m3 := by exact_mod_cast sub_eq_zero.1 e23
  rw [← f23, ← f12, ← f01] at h3
  linarith [h0.1, h0.2, h3.1, h3.2]

end QSL.Gate
