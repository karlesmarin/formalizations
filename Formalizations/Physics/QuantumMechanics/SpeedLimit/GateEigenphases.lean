/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.Physics.QuantumMechanics.SpeedLimit.QuditEntangling
public import Mathlib.Analysis.Complex.Trigonometric

/-!
# Gate-time lower bound from the eigenphase gap

A gate `G` is implemented, up to a global phase, by an ordered product
`U = ∏ₖ exp (−i τₖ Hₖ)` of piecewise constant evolutions (`τₖ ≥ 0`, `Hₖ` Hermitian, ħ = 1) whose
Hamiltonians have spectral half-width at most `Ω / 2`, i.e. `‖Hₖ − cₖ • 1‖ ≤ Ω / 2` for real
`cₖ`. Then the total time is at least `Δφ / Ω`, where `Δφ` is the gap between two eigenphases of
`G` on orthonormal eigenvectors.

Nelson and Barnes, *How fast can a quantum gate be? Exact speed limits from geometry*,
arXiv:2604.23031 (2026), eq. (3), state the general bound `T ≥ Δφ⋆ / Ω_max`. This file gives an
elementary proof via the shifted Mandelstam–Tamm bound (Duhamel estimate of
`QSL.Qudit.fsAngle_exp_add_exp_le` plus the triangle inequality of the Fubini–Study angle), and
only for gaps `Δφ ≤ π`. Nothing is claimed here about gaps larger than `π`; the full range is in
`Formalizations.Physics.QuantumMechanics.SpeedLimit.SpectralArc` (sphere angle, spectral arc).

For the two-qubit controlled-Z gate `diag (1, 1, 1, −1)` the eigenphases `0` and `π` give
`T ≥ π / Ω`, matching `T⋆ (CZ) = π / Ω` of Nelson–Barnes (Table I).

## Main results

* `QSL.Gate.fsAngle_le_time_halfWidth`: `fsAngle (U v) v ≤ (Ω / 2) · ∑ τₖ` for unit `v`
* `QSL.Gate.gate_time_ge_eigenphase_gap`: `|φⱼ − φₖ| ≤ Ω · ∑ τₖ` when `U = ω • G`, `G` has
  eigenvectors `eⱼ ⊥ eₖ` with eigenphases `φⱼ, φₖ`, and `|φⱼ − φₖ| ≤ π`
* `QSL.Gate.cz_time_ge`: `π ≤ Ω · ∑ τₖ` for the controlled-Z gate

## References

* H. Nelson, E. Barnes, *How fast can a quantum gate be? Exact speed limits from geometry*,
  arXiv:2604.23031 (2026).
-/

@[expose] public section

noncomputable section

open scoped Matrix
open scoped Matrix.Norms.L2Operator
open NormedSpace
open QSL.TwoQubit (act)
open QSL.Qudit

namespace QSL.Gate

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
private lemma skew_smul (τ : ℝ) {M : Matrix n n ℂ} (hM : Mᴴ = M) :
    ((-(τ : ℂ) * Complex.I) • M)ᴴ = -((-(τ : ℂ) * Complex.I) • M) := by
  rw [Matrix.conjTranspose_smul, hM, ← neg_smul]
  congr 1
  apply Complex.ext <;> simp

omit [Fintype n] in
private lemma real_smul_one_conj (c : ℝ) :
    ((c : ℂ) • (1 : Matrix n n ℂ))ᴴ = (c : ℂ) • (1 : Matrix n n ℂ) := by
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  simp

omit [DecidableEq n] in
private lemma norm_eq_one_of_unit {u : EuclideanSpace ℂ n} (hu : ‖u‖ = 1) :
    inner ℂ u u = 1 := by
  rw [inner_self_eq_norm_sq_to_K, hu]
  simp

omit [DecidableEq n] in
/-- A global phase `z • φ` does not change the Fubini–Study angle to `φ`. -/
private lemma fsAngle_phase {φ : EuclideanSpace ℂ n} (hφ : ‖φ‖ = 1) {z : ℂ} (hz : ‖z‖ = 1) :
    fsAngle (z • φ) φ = 0 := by
  rw [fsAngle, inner_smul_left, norm_eq_one_of_unit hφ, mul_one]
  simp [hz]

omit [DecidableEq n] in
private lemma act_smul_mat (ω : ℂ) (G : Matrix n n ℂ) (v : EuclideanSpace ℂ n) :
    act (ω • G) v = ω • act G v := by
  ext i
  simp [act, Matrix.smul_mulVec]

omit [DecidableEq n] in
private lemma act_add' (G : Matrix n n ℂ) (u v : EuclideanSpace ℂ n) :
    act G (u + v) = act G u + act G v := by
  ext i
  simp [act, Matrix.mulVec_add]

omit [DecidableEq n] in
private lemma act_smul_vec (G : Matrix n n ℂ) (z : ℂ) (v : EuclideanSpace ℂ n) :
    act G (z • v) = z • act G v := by
  ext i
  simp [act, Matrix.mulVec_smul]

/-- Action of a scalar matrix. -/
private lemma act_diagonal_const (z : ℂ) (φ : EuclideanSpace ℂ n) :
    act (Matrix.diagonal fun _ => z) φ = z • φ := by
  ext i
  simp [act]

/-- One step: `exp (−i τ H)` moves a unit vector by Fubini–Study angle at most `‖H − c‖ · τ`. -/
private lemma step_bound (τ c : ℝ) (hτ : 0 ≤ τ) (H : Matrix n n ℂ) (hH : Hᴴ = H) (Ω : ℝ)
    (hΩ : ‖H - (c : ℂ) • (1 : Matrix n n ℂ)‖ ≤ Ω / 2) (φ : EuclideanSpace ℂ n)
    (hφ : ‖φ‖ = 1) :
    fsAngle (act (exp ((-(τ : ℂ) * Complex.I) • H)) φ) φ ≤ Ω / 2 * τ := by
  set X : Matrix n n ℂ := (-(τ : ℂ) * Complex.I) • ((c : ℂ) • (1 : Matrix n n ℂ)) with hXdef
  set Y : Matrix n n ℂ := (-(τ : ℂ) * Complex.I) • (H - (c : ℂ) • (1 : Matrix n n ℂ)) with hYdef
  have hHc : (H - (c : ℂ) • (1 : Matrix n n ℂ))ᴴ = H - (c : ℂ) • (1 : Matrix n n ℂ) := by
    rw [Matrix.conjTranspose_sub, hH, real_smul_one_conj]
  have hX := skew_smul τ (real_smul_one_conj (n := n) c)
  have hY := skew_smul τ hHc
  have h := fsAngle_exp_add_exp_le X Y hX hY φ hφ
  have hXY : X + Y = (-(τ : ℂ) * Complex.I) • H := by
    rw [hXdef, hYdef, ← smul_add]
    congr 1
    abel
  have hn : ‖(-(τ : ℂ) * Complex.I)‖ = τ := by
    simp [abs_of_nonneg hτ]
  have hYn : ‖Y‖ ≤ Ω / 2 * τ := by
    rw [hYdef, norm_smul, hn, mul_comm]
    exact mul_le_mul_of_nonneg_right hΩ hτ
  have hXd : X = Matrix.diagonal fun _ => (-(τ : ℂ) * Complex.I) * c := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hXdef]
    · simp [hXdef, hij]
  have hexpX : act (exp X) φ = Complex.exp ((-(τ : ℂ) * Complex.I) * c) • φ := by
    let +nondep : NormedAlgebra ℚ ℂ := .restrictScalars ℚ ℂ _
    rw [hXd, Matrix.exp_diagonal]
    have : (exp fun _ : n => (-(τ : ℂ) * Complex.I) * c) =
        fun _ => Complex.exp ((-(τ : ℂ) * Complex.I) * c) := by
      funext p
      rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
    rw [this]
    exact act_diagonal_const _ _
  have hz : ‖Complex.exp ((-(τ : ℂ) * Complex.I) * c)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hexpXU : exp X ∈ Matrix.unitaryGroup n ℂ := exp_mem_unitaryGroup _ hX
  have hexpXYU : exp (X + Y) ∈ Matrix.unitaryGroup n ℂ := by
    refine exp_mem_unitaryGroup _ ?_
    rw [Matrix.conjTranspose_add, hX, hY, neg_add]
  have t := fsAngle_le_fsAngle_add_fsAngle ((norm_act_of_mem hexpXYU φ).trans hφ)
    ((norm_act_of_mem hexpXU φ).trans hφ) hφ
  rw [hexpX, fsAngle_phase hφ hz] at t
  rw [hXY] at t
  rw [hexpX, hXY] at h
  linarith

private lemma chain (Ω : ℝ) (l : List (ℝ × ℝ × Matrix n n ℂ)) (hτ : ∀ s ∈ l, 0 ≤ s.1)
    (hH : ∀ s ∈ l, s.2.2ᴴ = s.2.2)
    (hΩ : ∀ s ∈ l, ‖s.2.2 - (s.2.1 : ℂ) • (1 : Matrix n n ℂ)‖ ≤ Ω / 2) :
    (l.map fun s => exp ((-(s.1 : ℂ) * Complex.I) • s.2.2)).prod ∈ Matrix.unitaryGroup n ℂ ∧
      ∀ φ : EuclideanSpace ℂ n, ‖φ‖ = 1 →
        fsAngle (act (l.map fun s => exp ((-(s.1 : ℂ) * Complex.I) • s.2.2)).prod φ) φ ≤
          Ω / 2 * (l.map Prod.fst).sum := by
  induction l with
  | nil => exact ⟨by simp, fun φ hφ => by simp [act_one, fsAngle_self hφ]⟩
  | cons s l ih =>
    obtain ⟨hU, hang⟩ := ih (fun t ht => hτ t (by simp [ht])) (fun t ht => hH t (by simp [ht]))
      (fun t ht => hΩ t (by simp [ht]))
    have hUs : exp ((-(s.1 : ℂ) * Complex.I) • s.2.2) ∈ Matrix.unitaryGroup n ℂ :=
      exp_mem_unitaryGroup _ (skew_smul s.1 (hH s (by simp)))
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    refine ⟨mul_mem hUs hU, fun φ hφ => ?_⟩
    rw [act_mul]
    have hu := (norm_act_of_mem hU φ).trans hφ
    have t := fsAngle_le_fsAngle_add_fsAngle ((norm_act_of_mem hUs _).trans hu)
      ((norm_act_of_mem hUs _).trans hφ) hφ
    rw [fsAngle_act_act hUs] at t
    have h1 := hang φ hφ
    have h2 := step_bound s.1 s.2.1 (hτ s (by simp)) s.2.2 (hH s (by simp)) Ω
      (hΩ s (by simp)) φ hφ
    rw [mul_add]
    linarith

/-- **Mandelstam–Tamm bound for a product of evolutions.** If `U = ∏ₖ exp (−i τₖ Hₖ)` with
`τₖ ≥ 0`, `Hₖ` Hermitian and `‖Hₖ − cₖ • 1‖ ≤ Ω / 2` for real `cₖ`, then every unit vector `v`
satisfies `fsAngle (U v) v ≤ (Ω / 2) · ∑ τₖ`. -/
theorem fsAngle_le_time_halfWidth (Ω : ℝ) (steps : List (ℝ × ℝ × Matrix n n ℂ))
    (hτ : ∀ s ∈ steps, 0 ≤ s.1) (hH : ∀ s ∈ steps, s.2.2.IsHermitian)
    (hΩ : ∀ s ∈ steps, ‖s.2.2 - (s.2.1 : ℂ) • (1 : Matrix n n ℂ)‖ ≤ Ω / 2)
    (v : EuclideanSpace ℂ n) (hv : ‖v‖ = 1) :
    fsAngle (act (steps.map fun s => exp ((-(s.1 : ℂ) * Complex.I) • s.2.2)).prod v) v ≤
      Ω / 2 * (steps.map Prod.fst).sum :=
  (chain Ω steps hτ (fun s hs => (hH s hs).eq) hΩ).2 v hv

private lemma two_cos_sum (a b : ℝ) :
    ‖Complex.exp (a * Complex.I) + Complex.exp (b * Complex.I)‖ =
      2 * Real.cos ((a - b) / 2) ∨
    ‖Complex.exp (a * Complex.I) + Complex.exp (b * Complex.I)‖ =
      -(2 * Real.cos ((a - b) / 2)) := by
  have e : Complex.exp (a * Complex.I) + Complex.exp (b * Complex.I) =
      Complex.exp (((a + b) / 2 : ℝ) * Complex.I) * (2 * (Real.cos ((a - b) / 2) : ℂ)) := by
    have h1 : Complex.exp (a * Complex.I) = Complex.exp (((a + b) / 2 : ℝ) * Complex.I) *
        Complex.exp (((a - b) / 2 : ℝ) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have h2 : Complex.exp (b * Complex.I) = Complex.exp (((a + b) / 2 : ℝ) * Complex.I) *
        Complex.exp (-(((a - b) / 2 : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [h1, h2, ← mul_add, Complex.ofReal_cos, Complex.two_cos]
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul]
  simp only [Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
  rcases le_total 0 (Real.cos ((a - b) / 2)) with h | h
  · left; rw [abs_of_nonneg h]
  · right; rw [abs_of_nonpos h]; ring

/-- **Gate time from the eigenphase gap** (gaps `≤ π` only). Let `U = ∏ₖ exp (−i τₖ Hₖ)` with
`τₖ ≥ 0`, `Hₖ` Hermitian, `‖Hₖ − cₖ • 1‖ ≤ Ω / 2`, and suppose `U = ω • G` for a complex scalar
`ω` (global phase). If `G eⱼ = e^{i φⱼ} eⱼ` and `G eₖ = e^{i φₖ} eₖ` for orthonormal `eⱼ, eₖ`
with `|φⱼ − φₖ| ≤ π`, then `|φⱼ − φₖ| ≤ Ω · ∑ τₖ`.
Cf. Nelson–Barnes, arXiv:2604.23031, eq. (3); this is an elementary proof for gaps `≤ π`. -/
theorem gate_time_ge_eigenphase_gap (Ω : ℝ) (steps : List (ℝ × ℝ × Matrix n n ℂ))
    (hτ : ∀ s ∈ steps, 0 ≤ s.1) (hH : ∀ s ∈ steps, s.2.2.IsHermitian)
    (hΩ : ∀ s ∈ steps, ‖s.2.2 - (s.2.1 : ℂ) • (1 : Matrix n n ℂ)‖ ≤ Ω / 2)
    (ω : ℂ) (G : Matrix n n ℂ)
    (hUG : (steps.map fun s => exp ((-(s.1 : ℂ) * Complex.I) • s.2.2)).prod = ω • G)
    (ej ek : EuclideanSpace ℂ n) (hj : ‖ej‖ = 1) (hk : ‖ek‖ = 1) (hjk : inner ℂ ej ek = 0)
    (φj φk : ℝ) (hGj : act G ej = Complex.exp (φj * Complex.I) • ej)
    (hGk : act G ek = Complex.exp (φk * Complex.I) • ek) (hgap : |φj - φk| ≤ Real.pi) :
    |φj - φk| ≤ Ω * (steps.map Prod.fst).sum := by
  obtain ⟨hU, -⟩ := chain Ω steps hτ (fun s hs => (hH s hs).eq) hΩ
  set a := Complex.exp (φj * Complex.I) with ha
  set b := Complex.exp (φk * Complex.I) with hb
  have han : ‖a‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hbn : ‖b‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hkj : inner ℂ ek ej = 0 := by rw [← inner_conj_symm, hjk]; simp
  have hωn : ‖ω‖ = 1 := by
    have h1 := norm_act_of_mem (hUG ▸ hU) ej
    rw [act_smul_mat, hGj, smul_smul, norm_smul, norm_mul, han, hj] at h1
    linarith
  -- the unit vector `v = (ej + ek) / ‖ej + ek‖`
  have hs2 : ‖ej + ek‖ ^ 2 = 2 := by
    rw [norm_add_sq (𝕜 := ℂ), hjk, hj, hk]
    simp
    norm_num
  have hs0 : ‖ej + ek‖ ≠ 0 := by
    intro h; rw [h] at hs2; norm_num at hs2
  set s := ‖ej + ek‖ with hsdef
  set v : EuclideanSpace ℂ n := ((s⁻¹ : ℝ) : ℂ) • (ej + ek) with hvdef
  have hv : ‖v‖ = 1 := by
    rw [hvdef, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      ← hsdef]
    exact inv_mul_cancel₀ hs0
  have hr2 : ((s⁻¹ : ℝ) : ℂ) * ((s⁻¹ : ℝ) : ℂ) = 1 / 2 := by
    have : s⁻¹ * s⁻¹ = 1 / 2 := by
      rw [← mul_inv, ← sq, hs2]; norm_num
    rw [← Complex.ofReal_mul, this]; push_cast; rfl
  have hGv : act G v = ((s⁻¹ : ℝ) : ℂ) • (a • ej + b • ek) := by
    rw [hvdef, act_smul_vec, act_add', hGj, hGk]
  have hin : inner ℂ v (act (ω • G) v) = ω * ((a + b) / 2) := by
    rw [act_smul_mat, inner_smul_right, hGv, hvdef, inner_smul_left, inner_smul_right,
      inner_add_left, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
      inner_smul_right, inner_smul_right, norm_eq_one_of_unit hj, norm_eq_one_of_unit hk, hjk,
      hkj]
    simp only [Complex.conj_ofReal]
    linear_combination ω * (a + b) * hr2
  have hcos : ‖inner ℂ v (act (ω • G) v)‖ = Real.cos ((φj - φk) / 2) := by
    have hcnn : 0 ≤ Real.cos ((φj - φk) / 2) := by
      apply Real.cos_nonneg_of_mem_Icc
      have := abs_le.1 hgap
      exact ⟨by linarith, by linarith⟩
    rw [hin, norm_mul, hωn, one_mul, norm_div, Complex.norm_ofNat]
    rcases two_cos_sum φj φk with h | h
    · rw [h]; ring
    · have h0 : 0 ≤ ‖a + b‖ := norm_nonneg _
      have : Real.cos ((φj - φk) / 2) = 0 := by linarith
      rw [h, this]; simp
  have hang := fsAngle_le_time_halfWidth Ω steps hτ hH hΩ v hv
  rw [hUG, fsAngle, norm_inner_symm, hcos] at hang
  have hacos : Real.arccos (Real.cos ((φj - φk) / 2)) = |φj - φk| / 2 := by
    rw [← Real.cos_abs, abs_div, abs_two]
    exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])
  rw [hacos] at hang
  linarith

/-- The controlled-Z gate `diag (1, 1, 1, −1)` on two qubits. -/
def cz : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.diagonal fun p => if p = (1, 1) then -1 else 1

/-- **CZ needs time `π / Ω`.** Any ordered product `∏ₖ exp (−i τₖ Hₖ)` (`τₖ ≥ 0`, `Hₖ` Hermitian
on two qubits, `‖Hₖ − cₖ • 1‖ ≤ Ω / 2`) equal to the controlled-Z gate up to a global phase has
`π ≤ Ω · ∑ τₖ`. The eigenphases of CZ on `e₀₀` and `e₁₁` are `0` and `π`. This matches
`T⋆ (CZ) = π / Ω` of Nelson–Barnes, arXiv:2604.23031, Table I. -/
theorem cz_time_ge (Ω : ℝ) (steps : List (ℝ × ℝ × Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
    (hτ : ∀ s ∈ steps, 0 ≤ s.1) (hH : ∀ s ∈ steps, s.2.2.IsHermitian)
    (hΩ : ∀ s ∈ steps,
      ‖s.2.2 - (s.2.1 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤ Ω / 2)
    (ω : ℂ)
    (hUG : (steps.map fun s => exp ((-(s.1 : ℂ) * Complex.I) • s.2.2)).prod = ω • cz) :
    Real.pi ≤ Ω * (steps.map Prod.fst).sum := by
  have h := gate_time_ge_eigenphase_gap Ω steps hτ hH hΩ ω cz hUG
    (EuclideanSpace.single ((0 : Fin 2), (0 : Fin 2)) 1)
    (EuclideanSpace.single ((1 : Fin 2), (1 : Fin 2)) 1) (by simp) (by simp)
    (by simp [EuclideanSpace.inner_single_left]) 0 Real.pi
    (by
      ext i
      simp [act, cz, PiLp.single_apply])
    (by
      ext i
      simp [act, cz, PiLp.single_apply]
      split_ifs <;> simp)
    (by simp [abs_of_nonneg Real.pi_pos.le])
  simpa [abs_of_nonneg Real.pi_pos.le] using h

end QSL.Gate
