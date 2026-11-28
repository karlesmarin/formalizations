/-
Usage examples of the reusable layer, area Analysis, with the minimal import of that area: the
same code a user pastes into a file of their own project (README, section "Reusable layer").
-/
import Formalizations.Reusable.Analysis

open Formalizations.Reusable Real Set

/-- The zero set of a solution of `y'' = x y` is not bounded below. -/
example (f f' : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (x * f x) x) : ¬ BddBelow {x | f x = 0} := by
  rintro ⟨m, hm⟩
  obtain ⟨x, hx, h0⟩ := airy_eq_zeros_unbounded_below f f' hf hf' m
  exact absurd (hm h0) (not_le.2 hx)

/-- Glasser's integral at `a = 0`, `b = 1`: `∫_{v>0} v^{-1/2} e^{-v} dv = √π`. -/
example : ∫ v in Ioi (0 : ℝ), v ^ (-(1 : ℝ) / 2) * Real.exp (-0 / v - 1 * v) = Real.sqrt π := by
  simpa using glasser_integral (a := 0) (b := 1) le_rfl one_pos

/-- The product of sines for `n = 6`. -/
example : ∏ k ∈ Finset.Ico (1 : ℕ) 6, 2 * Real.sin (k * π / 6) = 6 := by
  have := prod_two_sin_mul_pi_div 6 (by norm_num)
  push_cast at this
  exact this

/-- Eneström–Kakeya: `1 + z/2 + z²/3` (coefficients `1 ≥ 1/2 ≥ 1/3 > 0`) has no zero in the open
unit disc. -/
example {z : ℂ} (hz : ‖z‖ < 1) : (1 : ℂ) + z / 2 + z ^ 2 / 3 ≠ 0 := by
  have h := enestrom_kakeya_ne_zero (n := 2) (fun k => 1 / ((k : ℝ) + 1))
    (fun k _ => by positivity)
    (fun k _ => one_div_le_one_div_of_le (by positivity) (by push_cast; linarith)) hz
  convert h using 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  ring

/-- Generalised Hlawka for `n = 4` vectors of `ℝ`: `d₂ + d₃ ≤ 3 (d₁ + d₄)`. -/
example (x : Fin 4 → ℝ) :
    ∑ k ∈ Finset.Icc 2 (4 - 1), ∑ S ∈ (Finset.univ : Finset (Fin 4)).powersetCard k, ‖∑ i ∈ S, x i‖
      ≤ (2 ^ (4 - 2) - 1 : ℝ) * (∑ i, ‖x i‖ + ‖∑ i, x i‖) :=
  hlawka_generalised (by norm_num) x


/-- Zieliński–Zych at `α = 1` (the Margolus–Levitin case): `0 ≤ x − π/2 + (π/2) cos x + sin x` for `x ≥ 0`. -/
example {x : ℝ} (hx : 0 ≤ x) : 0 ≤ x - π / 2 + π / 2 * Real.cos x + Real.sin x := by
  have h := zielinski_zych_inequality one_pos hx
  simpa using h

/-- Margolus–Levitin: the orthogonalization time is at least `π / (2 Ebar)` when `Ebar > 0`. -/
example {p E : ℕ → ℝ} {Ebar τ : ℝ} (hp : ∀ n, 0 ≤ p n) (hE : ∀ n, 0 ≤ E n) (hτ : 0 ≤ τ)
    (hsum : HasSum p 1) (hmean : HasSum (fun n => p n * E n) Ebar)
    (hRe : HasSum (fun n => p n * Real.cos (E n * τ)) 0)
    (hIm : HasSum (fun n => p n * Real.sin (E n * τ)) 0) (hpos : 0 < Ebar) :
    Real.pi / (2 * Ebar) ≤ τ := by
  have h := margolus_levitin hp hE hτ hsum hmean hRe hIm
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- The hypotheses of Margolus–Levitin can all hold, and the bound is then attained: a two-level system
with energies `0` and `2`, equal weights, mean energy `1`, becomes orthogonal at `τ = π/2`, and
`π = 2 · 1 · (π/2)`. (Non-vacuity check.) -/
example : ∃ (p E : ℕ → ℝ) (Ebar τ : ℝ), (∀ n, 0 ≤ p n) ∧ (∀ n, 0 ≤ E n) ∧ 0 ≤ τ ∧ HasSum p 1 ∧
    HasSum (fun n => p n * E n) Ebar ∧ HasSum (fun n => p n * Real.cos (E n * τ)) 0 ∧
    HasSum (fun n => p n * Real.sin (E n * τ)) 0 ∧ Real.pi = 2 * Ebar * τ := by
  have hpi : (2 : ℝ) * (Real.pi / 2) = Real.pi := by ring
  have hz : ∀ g : ℕ → ℝ, (∀ n, 2 ≤ n → g n = 0) → HasSum g (∑ n ∈ Finset.range 2, g n) := by
    intro g hg
    exact hasSum_sum_of_ne_finset_zero fun n hn => hg n (by simp at hn; omega)
  let p : ℕ → ℝ := fun n => if n < 2 then 1 / 2 else 0
  let E : ℕ → ℝ := fun n => if n = 1 then 2 else 0
  have hp0 : ∀ n, 2 ≤ n → p n = 0 := fun n hn => by
    simp only [p]; split_ifs with h
    · exact absurd h (by omega)
    · rfl
  refine ⟨p, E, 1, Real.pi / 2, fun n => ?_, fun n => ?_, by positivity, ?_, ?_, ?_, ?_, by ring⟩
  · simp only [p]; split_ifs <;> norm_num
  · simp only [E]; split_ifs <;> norm_num
  · convert hz p hp0 using 1
    norm_num [Finset.sum_range_succ, p]
  · convert hz (fun n => p n * E n) (fun n hn => by simp only [hp0 n hn, zero_mul]) using 1
    norm_num [Finset.sum_range_succ, p, E]
  · convert hz (fun n => p n * Real.cos (E n * (Real.pi / 2)))
      (fun n hn => by simp only [hp0 n hn, zero_mul]) using 1
    norm_num [Finset.sum_range_succ, p, E, hpi]
  · convert hz (fun n => p n * Real.sin (E n * (Real.pi / 2)))
      (fun n hn => by simp only [hp0 n hn, zero_mul]) using 1
    norm_num [Finset.sum_range_succ, p, E, hpi]

/-- A distribution with unit mean absolute energy deviation needs at least one unit of time. -/
example {p E : ℕ → ℝ} {Ebar τ : ℝ} (hp : ∀ n, 0 ≤ p n) (hτ : 0 ≤ τ) (hsum : HasSum p 1)
    (hdev : HasSum (fun n => p n * |E n - Ebar|) 1)
    (horth : HasSum (fun n => (p n : ℂ) * Complex.exp ((-(E n * τ) : ℝ) * Complex.I)) 0) :
    1 ≤ τ := by
  simpa only [one_mul] using mandelstam_tamm_L1 hp hτ hsum hdev horth

open MeasureTheory ProbabilityTheory in
/-- The kurtosis bound for a Gaussian variance mixture. -/
example (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h₂ : MemLp (fun v : ℝ => v) 2 μ) (h₀ : ∀ᵐ v ∂μ, 0 ≤ v)
    (hmean : 0 < ∫ v, v ∂μ) :
    3 ≤ (∫ ω, (Real.sqrt ω.1 * ω.2) ^ 4 ∂(μ.prod (gaussianReal 0 1))) /
      (∫ ω, (Real.sqrt ω.1 * ω.2) ^ 2 ∂(μ.prod (gaussianReal 0 1))) ^ 2 :=
  (variance_mixture_kurtosis_identity μ h₂ h₀ hmean).2.2
