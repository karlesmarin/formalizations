/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Saturation of the Mandelstam–Tamm integral bound by fixed-axis two-level pulses

For a time-dependent Hamiltonian the integral form of the Mandelstam–Tamm bound
(Mandelstam–Tamm 1945) reads `arccos |⟨ψ(0), ψ(T)⟩| ≤ ∫₀ᵀ ΔE(t) dt` (`ℏ = 1`).
Here we show that it is an equality for every fixed-axis two-level pulse
`H(t) = f(t) σₓ / 2` with `f ≥ 0`, as long as the total rotation angle `θ(T) = ∫₀ᵀ f` is at most `π`.

The state is `ψ = exp(−i θ σₓ / 2) |0⟩ = cos(θ/2) |0⟩ − i sin(θ/2) |1⟩`; it depends on the pulse only
through the accumulated angle `θ(t) = ∫₀ᵗ f`. Then `⟨σₓ⟩ = 0`, so `ΔE(t) = f(t)/2`,
`∫₀ᵀ ΔE = θ(T)/2` and `|⟨ψ(0), ψ(T)⟩| = |cos(θ(T)/2)|`.

Scope: the trajectory `ψ(t) = qubitState (∫₀ᵗ f)` is used as the evolution; for continuous `f` we
prove (`hasDerivAt_trajectory`) that it solves the Schrödinger equation `ψ′ = −i (f σₓ / 2) ψ`
with `ψ(0) = |0⟩` (uniqueness is not proved). The statements without the `Continuous f`
hypothesis are about the trajectory only.

## Main results

* `QSL.FixedAxis.energyStd_qubitState`: `ΔE = a/2` for `H = (a/2) σₓ` on every `qubitState θ`
* `QSL.FixedAxis.arccos_overlap_qubitState`: `arccos ‖⟪ψ(0), ψ(θ)⟫‖ = θ/2` for `0 ≤ θ ≤ π`
* `QSL.FixedAxis.mandelstam_tamm_integral_eq`: for `f ≥ 0` with `∫₀ᵀ f ≤ π`,
  `∫₀ᵀ ΔE(t) dt = arccos ‖⟪ψ(0), ψ(T)⟫‖`
* `QSL.FixedAxis.pi_pulse_quantum_speed_limit_ratio`: for `∫₀ᵀ f = π` the final state is orthogonal
  to the initial one and `∫₀ᵀ ΔE = π/2`: the Mandelstam–Tamm ratio is exactly `1`, whatever `f`
* `QSL.FixedAxis.arccos_overlap_lt_of_pi_lt`: strict inequality for `π < θ < 3π`

## References

* L. Mandelstam, I. Tamm, *The uncertainty relation between energy and time in non-relativistic
  quantum mechanics*, J. Phys. USSR 9 (1945) 249–254.
-/

@[expose] public section

noncomputable section
open scoped Real

namespace QSL.FixedAxis

/-- Qubit vectors. -/
abbrev Vec2 := EuclideanSpace ℂ (Fin 2)
/-- Single-qubit operators. -/
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- The Pauli matrix `σₓ`. -/
def sigmaX : Mat2 := !![0, 1; 1, 0]

/-- The Hamiltonian `(a/2) σₓ`. -/
def hamX (a : ℝ) : Mat2 := ((a / 2 : ℝ) : ℂ) • sigmaX

/-- Action of a matrix on a vector. -/
def act (M : Mat2) (v : Vec2) : Vec2 := WithLp.toLp 2 (M.mulVec v.ofLp)

/-- The vector `c |0⟩ − i s |1⟩` for real `c, s`. -/
def qubitVec (c s : ℝ) : Vec2 := WithLp.toLp 2 ![(c : ℂ), -Complex.I * (s : ℂ)]

/-- The state `exp (−i θ σₓ / 2) |0⟩ = cos (θ/2) |0⟩ − i sin (θ/2) |1⟩`. -/
def qubitState (θ : ℝ) : Vec2 := qubitVec (Real.cos (θ / 2)) (Real.sin (θ / 2))

/-- Expectation value `⟨v, M v⟩`. -/
def expect (M : Mat2) (v : Vec2) : ℂ := inner ℂ v (act M v)

/-- Energy standard deviation `ΔE = √(⟨H²⟩ − ⟨H⟩²)` of the state `v` for the Hamiltonian `H`. -/
def energyStd (H : Mat2) (v : Vec2) : ℝ :=
  Real.sqrt ((expect (H * H) v).re - ((expect H v).re) ^ 2)

lemma expect_sigmaX_qubitVec (c s : ℝ) : expect sigmaX (qubitVec c s) = 0 := by
  simp [expect, act, qubitVec, sigmaX, PiLp.inner_apply, Fin.sum_univ_two]
  ring

lemma expect_sigmaX (θ : ℝ) : expect sigmaX (qubitState θ) = 0 :=
  expect_sigmaX_qubitVec _ _

lemma norm_qubitState (θ : ℝ) : ‖qubitState θ‖ ^ 2 = 1 := by
  have h : ∀ c s : ℝ, ‖qubitVec c s‖ ^ 2 = c ^ 2 + s ^ 2 := by
    intro c s
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp [qubitVec]
  rw [qubitState, h]
  exact (add_comm _ _).trans (Real.sin_sq_add_cos_sq (θ / 2))

lemma expect_sq (a θ : ℝ) :
    (expect (hamX a * hamX a) (qubitState θ)) = ((a / 2) ^ 2 : ℝ) := by
  have h : hamX a * hamX a = (((a / 2) ^ 2 : ℝ) : ℂ) • (1 : Mat2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hamX, sigmaX, Matrix.mul_apply, Fin.sum_univ_two] <;>
      ring
  rw [h]
  have hact : act ((((a / 2) ^ 2 : ℝ) : ℂ) • (1 : Mat2)) (qubitState θ)
      = (((a / 2) ^ 2 : ℝ) : ℂ) • qubitState θ := by
    ext i
    simp [act, Matrix.smul_mulVec]
  have : expect ((((a / 2) ^ 2 : ℝ) : ℂ) • (1 : Mat2)) (qubitState θ)
      = (((a / 2) ^ 2 : ℝ) : ℂ) * ((‖qubitState θ‖ ^ 2 : ℝ) : ℂ) := by
    rw [expect, hact, inner_smul_right, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [this, norm_qubitState]
  simp

/-- **Pointwise:** for `H = (a/2) σₓ` the energy standard deviation of every state
`exp (−i θ σₓ / 2) |0⟩` equals `|a|/2` (`= a/2` for `a ≥ 0`). -/
theorem energyStd_qubitState (a θ : ℝ) (ha : 0 ≤ a) :
    energyStd (hamX a) (qubitState θ) = a / 2 := by
  have h1 : expect (hamX a) (qubitState θ) = 0 := by
    have : expect (hamX a) (qubitState θ) = ((a / 2 : ℝ) : ℂ) * expect sigmaX (qubitState θ) := by
      simp [expect, act, hamX, Matrix.smul_mulVec, inner_smul_right]
    rw [this, expect_sigmaX, mul_zero]
  unfold energyStd
  rw [expect_sq, h1]
  simp only [Complex.ofReal_re, Complex.zero_re, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, sub_zero]
  exact Real.sqrt_sq (by positivity)

/-- The overlap `⟨ψ(0), ψ(θ)⟩ = cos (θ/2)`. -/
lemma inner_qubitState_zero (θ : ℝ) :
    inner ℂ (qubitState 0) (qubitState θ) = ((Real.cos (θ / 2) : ℝ) : ℂ) := by
  simp [qubitState, qubitVec, PiLp.inner_apply, Fin.sum_univ_two]

/-- **Saturation, trajectory form:** for `0 ≤ θ ≤ π`, `arccos ‖⟪ψ(0), ψ(θ)⟫‖ = θ/2`. -/
theorem arccos_overlap_qubitState {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ ≤ π) :
    Real.arccos ‖inner ℂ (qubitState 0) (qubitState θ)‖ = θ / 2 := by
  rw [inner_qubitState_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩)]
  exact Real.arccos_cos (by linarith) (by linarith)

/-- Strictness beyond a `π` pulse: for `π < θ < 3π` (so that the pulse overshoots), the bound
is strict, `arccos ‖⟪ψ(0), ψ(θ)⟫‖ < θ/2`. -/
theorem arccos_overlap_lt_of_pi_lt {θ : ℝ} (h0 : π < θ) (h1 : θ < 3 * π) :
    Real.arccos ‖inner ℂ (qubitState 0) (qubitState θ)‖ < θ / 2 := by
  rw [inner_qubitState_zero, Complex.norm_real, Real.norm_eq_abs]
  have hneg : Real.cos (θ / 2) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
  have : |Real.cos (θ / 2)| = Real.cos |θ / 2 - π| := by
    rw [Real.cos_abs, Real.cos_sub_pi, abs_of_neg hneg]
  rw [this, Real.arccos_cos (abs_nonneg _)]
  · rw [abs_lt]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith [Real.pi_pos]

/-- **Time-dependent form.** For a pulse `f ≥ 0` with `θ(T) = ∫₀ᵀ f ≤ π`, the trajectory
`ψ(t) = qubitState (∫₀ᵗ f)` of `H(t) = f(t) σₓ / 2` satisfies the Mandelstam–Tamm integral bound
with **equality**: `∫₀ᵀ ΔE(t) dt = arccos ‖⟪ψ(0), ψ(T)⟫‖`. -/
theorem mandelstam_tamm_integral_eq {f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ∀ t ∈ Set.Icc 0 T, 0 ≤ f t)    (hπ : ∫ t in (0 : ℝ)..T, f t ≤ π) :
    ∫ t in (0 : ℝ)..T, energyStd (hamX (f t)) (qubitState (∫ s in (0 : ℝ)..t, f s))
      = Real.arccos ‖inner ℂ (qubitState (∫ s in (0 : ℝ)..0, f s))
          (qubitState (∫ s in (0 : ℝ)..T, f s))‖ := by
  have hθ0 : 0 ≤ ∫ t in (0 : ℝ)..T, f t :=
    intervalIntegral.integral_nonneg hT hf
  have hcongr : ∫ t in (0 : ℝ)..T, energyStd (hamX (f t)) (qubitState (∫ s in (0 : ℝ)..t, f s))
      = ∫ t in (0 : ℝ)..T, f t / 2 := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le hT] at ht
    exact energyStd_qubitState _ _ (hf t ht)
  rw [hcongr, intervalIntegral.integral_div, intervalIntegral.integral_same,
    arccos_overlap_qubitState (by simpa using hθ0) hπ]

/-- **The trajectory solves the Schrödinger equation.** For continuous `f`, the curve
`ψ(t) = qubitState (∫₀ᵗ f)` satisfies `ψ′(t) = −i H(t) ψ(t)` with `H(t) = f(t) σₓ / 2`
(`ℏ = 1`). -/
theorem hasDerivAt_trajectory {f : ℝ → ℝ} (hf : Continuous f) (t : ℝ) :
    HasDerivAt (fun t => qubitState (∫ s in (0 : ℝ)..t, f s))
      (-Complex.I • act (hamX (f t)) (qubitState (∫ s in (0 : ℝ)..t, f s))) t := by
  have hθ : HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, f s) (f t) t :=
    (hf.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hh : HasDerivAt (fun t => (∫ s in (0 : ℝ)..t, f s) / 2) (f t / 2) t := hθ.div_const 2
  have hc : HasDerivAt (fun t => Real.cos ((∫ s in (0 : ℝ)..t, f s) / 2))
      (-Real.sin ((∫ s in (0 : ℝ)..t, f s) / 2) * (f t / 2)) t :=
    (Real.hasDerivAt_cos _).comp t hh
  have hs : HasDerivAt (fun t => Real.sin ((∫ s in (0 : ℝ)..t, f s) / 2))
      (Real.cos ((∫ s in (0 : ℝ)..t, f s) / 2) * (f t / 2)) t :=
    (Real.hasDerivAt_sin _).comp t hh
  have h0 := hc.ofReal_comp
  have h1 := (hs.ofReal_comp).const_mul (-Complex.I)
  have hg : HasDerivAt (fun t : ℝ => (![((Real.cos ((∫ s in (0 : ℝ)..t, f s) / 2) : ℝ) : ℂ),
        -Complex.I * ((Real.sin ((∫ s in (0 : ℝ)..t, f s) / 2) : ℝ) : ℂ)] : Fin 2 → ℂ))
      ![((-Real.sin ((∫ s in (0 : ℝ)..t, f s) / 2) * (f t / 2) : ℝ) : ℂ),
        -Complex.I * ((Real.cos ((∫ s in (0 : ℝ)..t, f s) / 2) * (f t / 2) : ℝ) : ℂ)] t :=
    hasDerivAt_pi.2 (Fin.forall_fin_two.2 ⟨h0, h1⟩)
  have hq := (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2
    (![((Real.cos ((∫ s in (0 : ℝ)..t, f s) / 2) : ℝ) : ℂ),
        -Complex.I * ((Real.sin ((∫ s in (0 : ℝ)..t, f s) / 2) : ℝ) : ℂ)] : Fin 2 → ℂ))
  have key := hq.comp_hasDerivAt t hg
  refine HasDerivAt.congr_deriv key ?_
  ext i
  fin_cases i
  · simp [act, hamX, sigmaX, qubitState, qubitVec]
    linear_combination (-1 : ℂ) * (Complex.sin (↑(∫ (s : ℝ) in (0 : ℝ)..t, f s) / 2) * (↑(f t) / 2))
      * Complex.I_sq
  · simp [act, hamX, sigmaX, qubitState, qubitVec]

/-- **Mandelstam–Tamm saturation for the Schrödinger solution.** For continuous `f ≥ 0` on `[0,T]`
with `∫₀ᵀ f ≤ π`, the curve `ψ(t) = qubitState (∫₀ᵗ f)` is a solution of
`ψ′ = −i (f σₓ/2) ψ` with `ψ(0) = |0⟩` (`qubitState 0`), and along it the Mandelstam–Tamm integral
bound is an equality, `∫₀ᵀ ΔE(t) dt = arccos ‖⟪ψ(0), ψ(T)⟫‖`. (Uniqueness of the solution is
not proved; it is standard for linear ODEs.) -/
theorem mandelstam_tamm_integral_eq_solution {f : ℝ → ℝ} (hfc : Continuous f) {T : ℝ}
    (hT : 0 ≤ T) (hf : ∀ t ∈ Set.Icc 0 T, 0 ≤ f t) (hπ : ∫ t in (0 : ℝ)..T, f t ≤ π) :
    (∀ t, HasDerivAt (fun t => qubitState (∫ s in (0 : ℝ)..t, f s))
      (-Complex.I • act (hamX (f t)) (qubitState (∫ s in (0 : ℝ)..t, f s))) t) ∧
    qubitState (∫ s in (0 : ℝ)..0, f s) = qubitState 0 ∧
    ∫ t in (0 : ℝ)..T, energyStd (hamX (f t)) (qubitState (∫ s in (0 : ℝ)..t, f s))
      = Real.arccos ‖inner ℂ (qubitState (∫ s in (0 : ℝ)..0, f s))
          (qubitState (∫ s in (0 : ℝ)..T, f s))‖ :=
  ⟨hasDerivAt_trajectory hfc, by rw [intervalIntegral.integral_same],
    mandelstam_tamm_integral_eq hT hf hπ⟩

/-- **Corollary (shape independence).** If `f ≥ 0` and `∫₀ᵀ f = π`, the final state of the pulse
is orthogonal to the initial state and `∫₀ᵀ ΔE = π/2`: the Mandelstam–Tamm ratio
`(∫ΔE)/arccos|⟨ψ₀,ψ_T⟩|` is exactly `1`, for every shape `f`. -/
theorem pi_pulse_quantum_speed_limit_ratio {f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ∀ t ∈ Set.Icc 0 T, 0 ≤ f t)    (hπ : ∫ t in (0 : ℝ)..T, f t = π) :
    inner ℂ (qubitState (∫ s in (0 : ℝ)..0, f s)) (qubitState (∫ s in (0 : ℝ)..T, f s)) = 0 ∧
    ∫ t in (0 : ℝ)..T, energyStd (hamX (f t)) (qubitState (∫ s in (0 : ℝ)..t, f s)) = π / 2 := by
  constructor
  · rw [intervalIntegral.integral_same, inner_qubitState_zero, hπ]
    simp
  · rw [mandelstam_tamm_integral_eq hT hf hπ.le, intervalIntegral.integral_same,
      arccos_overlap_qubitState (hπ ▸ Real.pi_pos.le) hπ.le, hπ]

end QSL.FixedAxis
