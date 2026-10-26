/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Where the antipodal floor fails

For a non-increasing sequence q k ≥ 0 tending to 0 and f(z) = ∑ q k z^k, complete monotonicity puts
the minimum of Re f and of |f| on the unit circle at z = −1 (Polylog.le_norm_of_tendsto), and so
does four times monotonicity (Fejér, 1937). Two exact examples show that weaker shape conditions do
not: a three times monotone sequence (the coefficients of 6 + 3z + z² + 1/(1 − z/2)) whose real part
at cos θ = −3/4 is 73/16, below its value 14/3 at z = −1; and a log-convex (hence convex) sequence
(q k = (3/4)^k for k ≤ 3, then ratio 7/8) whose real part at e^{2πi/3} is 381/27040 below its value
47/80 at z = −1, and whose modulus at z* = (−7 + i√15)/8 is below 47/80 too.

## Main results

* `Polylog.fdiff`: iterated forward differences Δ^j q k
* `Polylog.cex3_monotone_three`: the first example is three times monotone
* `Polylog.cex3_not_four`: but not four times: Δ⁴ q 1 = −31/32
* `Polylog.cex3_antipode`: its value at z = −1 is 14/3
* `Polylog.cex3_re`: its real part at cos θ = −3/4 is 73/16
* `Polylog.cexLC_logConvex`: the second example is log-convex
* `Polylog.cexLC_convex`: and convex
* `Polylog.cexLC_antipode`: its value at z = −1 is 47/80
* `Polylog.cexLC_re`: its real part at e^{2πi/3} is 47/80 − 381/27040
* `Polylog.cexLC_normSq`: |f(z*)|² = (47/80)² − 57/42200 at z* = (−7 + i√15)/8
* `Polylog.cex3_normSq`: |g(z*)|² = (14/3)² − 635/2448 at z* = (−7 + i√15)/8

## References

* C. Marín, *The Clock That Never Ticks: a machine-checked path from the dilogarithm to quantum
  speed limits in Lean 4*, Zenodo (2026), doi:10.5281/zenodo.20675271, `thm:clock`.
-/

@[expose] public section

open Filter Topology Complex

namespace Polylog

/-- Iterated forward differences: `fdiff 0 q = q`, `fdiff (j+1) q k = fdiff j q k - fdiff j q (k+1)`. -/
def fdiff : ℕ → (ℕ → ℝ) → ℕ → ℝ
  | 0, q => q
  | j + 1, q => fun k => fdiff j q k - fdiff j q (k + 1)

/-- `fdiff j q k` only depends on the values of `q` from `k` on. -/
lemma fdiff_congr {q q' : ℕ → ℝ} (j : ℕ) :
    ∀ k : ℕ, (∀ m, k ≤ m → q m = q' m) → fdiff j q k = fdiff j q' k := by
  induction j with
  | zero => intro k h; exact h k le_rfl
  | succ j ih =>
    intro k h
    simp only [fdiff]
    rw [ih k h, ih (k + 1) (fun m hm => h m (by omega))]

/-- Iterated differences of a geometric sequence. -/
lemma fdiff_geom (a r : ℝ) (j k : ℕ) :
    fdiff j (fun k => a * r ^ k) k = a * r ^ k * (1 - r) ^ j := by
  induction j generalizing k with
  | zero => simp [fdiff]
  | succ j ih =>
    simp only [fdiff]
    rw [ih k, ih (k + 1)]
    ring

/-- `Re (exp (θ i) ^ k) = cos (k θ)`. -/
lemma re_pow_exp (θ : ℝ) (k : ℕ) : ((Complex.exp (θ * I)) ^ k).re = Real.cos (k * θ) := by
  rw [← Complex.exp_nat_mul]
  have : (k : ℂ) * (θ * I) = ((k * θ : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

/-! ### Three times monotone is not enough -/

/-- The coefficients of `6 + 3z + z² + 1/(1 - z/2)`: `7, 7/2, 5/4`, then `2^{-k}`. -/
noncomputable def cex3 (k : ℕ) : ℝ :=
  (if k = 0 then 6 else 0) + (if k = 1 then 3 else 0) + (if k = 2 then 1 else 0) + (1 / 2) ^ k

lemma cex3_ge {k : ℕ} (hk : 3 ≤ k) : cex3 k = (1 / 2) ^ k := by
  unfold cex3
  simp [show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega]

/-- `cex3` is three times monotone: `Δ^j cex3 k ≥ 0` for `j ≤ 3` and every `k`. -/
theorem cex3_monotone_three {j : ℕ} (hj : j ≤ 3) (k : ℕ) : 0 ≤ fdiff j cex3 k := by
  by_cases hk : 3 ≤ k
  · rw [fdiff_congr (q' := fun k => 1 * (1 / 2 : ℝ) ^ k) j k
      (fun m hm => by rw [cex3_ge (by omega)]; ring), fdiff_geom]
    exact mul_nonneg (by positivity) (pow_nonneg (by norm_num) _)
  · have hk' : k < 3 := by omega
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hj' with rfl | rfl | rfl | rfl <;> rcases hk3 with rfl | rfl | rfl <;>
      simp [fdiff, cex3] <;> norm_num

/-- `cex3` is not four times monotone: `Δ⁴ cex3 1 = -31/32`. -/
theorem cex3_not_four : fdiff 4 cex3 1 = -31 / 32 := by
  simp [fdiff, cex3]
  norm_num

/-- The generating function of `cex3`, in `ℂ`. -/
lemma cex3_hasSum_complex (z : ℂ) (hz : ‖z / 2‖ < 1) :
    HasSum (fun k : ℕ => (cex3 k : ℂ) * z ^ k) (6 + 3 * z + z ^ 2 + (1 - z / 2)⁻¹) := by
  have h0 : HasSum (fun k : ℕ => if k = 0 then (6 : ℂ) else 0) 6 := hasSum_ite_eq 0 6
  have h1 : HasSum (fun k : ℕ => if k = 1 then 3 * z else 0) (3 * z) := hasSum_ite_eq 1 (3 * z)
  have h2 : HasSum (fun k : ℕ => if k = 2 then z ^ 2 else 0) (z ^ 2) := hasSum_ite_eq 2 (z ^ 2)
  have h3 := hasSum_geometric_of_norm_lt_one hz
  have := ((h0.add h1).add h2).add h3
  convert this using 1
  funext k
  rcases k with _ | _ | _ | k <;> simp [cex3, div_pow] <;> ring

lemma norm_half {z : ℂ} (hz : ‖z‖ = 1) : ‖z / 2‖ < 1 := by
  rw [norm_div, hz]; norm_num

/-- The value at `z = -1`: `∑ (-1)^k cex3 k = 14/3`. -/
theorem cex3_antipode : HasSum (fun k : ℕ => (-1) ^ k * cex3 k) (14 / 3) := by
  have h := cex3_hasSum_complex (-1) (by norm_num)
  have h' : HasSum (fun k : ℕ => (((-1) ^ k * cex3 k : ℝ) : ℂ)) ((14 / 3 : ℝ) : ℂ) := by
    convert h using 1
    · funext k; push_cast; ring
    · push_cast; norm_num
  exact Complex.hasSum_ofReal.mp h'

/-- The real part at `cos θ = -3/4` is `73/16 < 14/3`. -/
theorem cex3_re : HasSum (fun k : ℕ => cex3 k * Real.cos (k * Real.arccos (-3 / 4))) (73 / 16) := by
  set θ := Real.arccos (-3 / 4) with hθ
  set z : ℂ := Complex.exp (θ * I) with hzdef
  have hn : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have h := cex3_hasSum_complex z (norm_half hn)
  have hre := Complex.hasSum_re h
  have hc : Real.cos θ = -3 / 4 := Real.cos_arccos (by norm_num) (by norm_num)
  have ha : z.re = -3 / 4 := by rw [hzdef, Complex.exp_ofReal_mul_I_re, hc]
  have hb : z.im ^ 2 = 7 / 16 := by
    have : z.im = Real.sin θ := Complex.exp_ofReal_mul_I_im θ
    rw [this]
    have := Real.sin_sq_add_cos_sq θ
    rw [hc] at this
    linarith
  convert hre using 1
  · funext k
    rw [Complex.re_ofReal_mul, hzdef, re_pow_exp]
  · have e : (6 + 3 * z + z ^ 2 + (1 - z / 2)⁻¹ : ℂ).re
        = 6 + 3 * z.re + (z.re * z.re - z.im * z.im)
          + (1 - z.re / 2) / ((1 - z.re / 2) * (1 - z.re / 2) + (z.im / 2) * (z.im / 2)) := by
      simp [Complex.inv_re, Complex.normSq_apply, pow_two]
    rw [e, ha]
    have hb' : z.im * z.im = 7 / 16 := by rw [← pow_two]; exact hb
    have : (z.im / 2) * (z.im / 2) = 7 / 64 := by
      rw [div_mul_div_comm, hb']; norm_num
    rw [this, hb']
    norm_num

/-! ### Log-convex and convex is not enough -/

/-- `1, 3/4, 9/16`, then `27/64 · (7/8)^{k-3}`. -/
noncomputable def cexLC (k : ℕ) : ℝ :=
  if k = 0 then 1 else if k = 1 then 3 / 4 else if k = 2 then 9 / 16 else 27 / 64 * (7 / 8) ^ (k - 3)

@[simp] lemma cexLC_zero : cexLC 0 = 1 := by simp [cexLC]
@[simp] lemma cexLC_one : cexLC 1 = 3 / 4 := by simp [cexLC]
@[simp] lemma cexLC_two : cexLC 2 = 9 / 16 := by simp [cexLC]
lemma cexLC_add3 (m : ℕ) : cexLC (m + 3) = 27 / 64 * (7 / 8) ^ m := by
  unfold cexLC
  simp [show m + 3 ≠ 1 by omega, show m + 3 ≠ 2 by omega]

/-- `cexLC` is positive. -/
theorem cexLC_pos (k : ℕ) : 0 < cexLC k := by
  rcases k with _ | _ | _ | m
  · simp
  · simp
  · simp
  · rw [cexLC_add3]; positivity

/-- `cexLC` is non-increasing. -/
theorem cexLC_antitone : Antitone cexLC := by
  apply antitone_nat_of_succ_le
  intro n
  rcases n with _ | _ | _ | m
  · simp; norm_num
  · simp; norm_num
  · rw [show 2 + 1 = 0 + 3 by rfl, cexLC_add3]; simp; norm_num
  · rw [show m + 1 + 1 + 1 + 1 = (m + 1) + 3 by ring, cexLC_add3, cexLC_add3]
    have : (0 : ℝ) ≤ 27 / 64 * (7 / 8) ^ m := by positivity
    rw [pow_succ]
    nlinarith

/-- `cexLC` is log-convex: `q (k+1) ^ 2 ≤ q k · q (k+2)`. -/
theorem cexLC_logConvex (k : ℕ) : cexLC (k + 1) ^ 2 ≤ cexLC k * cexLC (k + 2) := by
  rcases k with _ | _ | _ | m
  · simp; norm_num
  · simp [show 1 + 2 = 0 + 3 by rfl, cexLC_add3]; norm_num
  · simp [show 2 + 1 = 0 + 3 by rfl, show 2 + 2 = 1 + 3 by rfl, cexLC_add3]; norm_num
  · rw [show m + 1 + 1 + 1 + 1 = (m + 1) + 3 by ring, show m + 1 + 1 + 1 = m + 3 by ring,
      show m + 1 + 1 + 1 + 2 = (m + 2) + 3 by ring, cexLC_add3, cexLC_add3, cexLC_add3]
    apply le_of_eq
    ring

/-- `cexLC` is convex: `Δ² cexLC k ≥ 0`. -/
theorem cexLC_convex (k : ℕ) : 0 ≤ fdiff 2 cexLC k := by
  simp only [fdiff]
  rcases k with _ | _ | _ | m
  · simp [show 0 + 1 + 1 = 2 by rfl]; norm_num
  · simp [show 1 + 1 = 2 by rfl, show 1 + 1 + 1 = 0 + 3 by rfl, cexLC_add3]; norm_num
  · simp [show 2 + 1 = 0 + 3 by rfl, show 2 + 1 + 1 = 1 + 3 by rfl, cexLC_add3]; norm_num
  · rw [show m + 1 + 1 + 1 = m + 3 by ring, show m + 1 + 1 + 1 + 1 = (m + 1) + 3 by ring,
      show m + 1 + 1 + 1 + 1 + 1 = (m + 2) + 3 by ring, cexLC_add3, cexLC_add3, cexLC_add3]
    have e : 27 / 64 * (7 / 8 : ℝ) ^ m - 27 / 64 * (7 / 8) ^ (m + 1)
        - (27 / 64 * (7 / 8) ^ (m + 1) - 27 / 64 * (7 / 8) ^ (m + 2))
        = 27 / 64 * (7 / 8) ^ m * (1 / 8) ^ 2 := by ring
    rw [e]; positivity

/-- The generating function of `cexLC`, in `ℂ`. -/
lemma cexLC_hasSum_complex (z : ℂ) (hz : ‖z‖ ≤ 1) :
    HasSum (fun k : ℕ => (cexLC k : ℂ) * z ^ k)
      (1 + 3 / 4 * z + 9 / 16 * z ^ 2 + 27 / 64 * z ^ 3 * (1 - 7 / 8 * z)⁻¹) := by
  have hr : ‖(7 / 8 : ℂ) * z‖ < 1 := by
    rw [norm_mul]
    have : ‖(7 / 8 : ℂ)‖ = 7 / 8 := by norm_num
    rw [this]
    nlinarith [norm_nonneg z]
  have g := (hasSum_geometric_of_norm_lt_one hr).mul_left (27 / 64 * z ^ 3)
  have h2 : HasSum (fun n : ℕ => (cexLC (n + 3) : ℂ) * z ^ (n + 3))
      (27 / 64 * z ^ 3 * (1 - 7 / 8 * z)⁻¹) := by
    convert g using 1
    funext n
    rw [cexLC_add3]
    push_cast
    ring
  have h3 := (hasSum_nat_add_iff (f := fun k : ℕ => (cexLC k : ℂ) * z ^ k) 3).mp h2
  convert h3 using 1
  simp [Finset.sum_range_succ]
  ring

/-- The value at `z = -1`: `∑ (-1)^k cexLC k = 47/80`. -/
theorem cexLC_antipode : HasSum (fun k : ℕ => (-1) ^ k * cexLC k) (47 / 80) := by
  have h := cexLC_hasSum_complex (-1) (by norm_num)
  have h' : HasSum (fun k : ℕ => (((-1) ^ k * cexLC k : ℝ) : ℂ)) ((47 / 80 : ℝ) : ℂ) := by
    convert h using 1
    · funext k; push_cast; ring
    · push_cast; norm_num
  exact Complex.hasSum_ofReal.mp h'

/-- The real part at `z = e^{2πi/3}` is `47/80 - 381/27040`, below the value at `z = -1`. -/
theorem cexLC_re :
    HasSum (fun k : ℕ => cexLC k * Real.cos (k * (2 * Real.pi / 3))) (47 / 80 - 381 / 27040) := by
  set θ : ℝ := 2 * Real.pi / 3 with hθ
  set z : ℂ := Complex.exp (θ * I) with hzdef
  have hn : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have h := cexLC_hasSum_complex z hn.le
  have hre := Complex.hasSum_re h
  have hc : Real.cos θ = -1 / 2 := by
    rw [hθ, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]; norm_num
  have ha : z.re = -1 / 2 := by rw [hzdef, Complex.exp_ofReal_mul_I_re, hc]
  have hb : z.im * z.im = 3 / 4 := by
    have : z.im = Real.sin θ := Complex.exp_ofReal_mul_I_im θ
    rw [this, ← pow_two]
    have := Real.sin_sq_add_cos_sq θ
    rw [hc] at this
    linarith
  convert hre using 1
  · funext k
    rw [Complex.re_ofReal_mul, hzdef, re_pow_exp]
  · have h3 : z ^ 3 = 1 := by
      rw [hzdef, ← Complex.exp_nat_mul, hθ]
      have : ((3 : ℕ) : ℂ) * (((2 * Real.pi / 3 : ℝ) : ℂ) * I) = 2 * Real.pi * I := by
        push_cast; ring
      rw [this, Complex.exp_two_pi_mul_I]
    have e : (1 + 3 / 4 * z + 9 / 16 * z ^ 2 + 27 / 64 * z ^ 3 * (1 - 7 / 8 * z)⁻¹ : ℂ).re
        = 1 + 3 / 4 * z.re + 9 / 16 * (z.re * z.re - z.im * z.im)
          + 27 / 64 * ((1 - 7 / 8 * z.re) / ((1 - 7 / 8 * z.re) * (1 - 7 / 8 * z.re)
                + (7 / 8 * z.im) * (7 / 8 * z.im))) := by
      rw [h3]
      simp [Complex.inv_re, Complex.normSq_apply, pow_two]
    rw [e, ha, hb, show 7 / 8 * z.im * (7 / 8 * z.im) = 147 / 256 by linear_combination (49 / 64) * hb]
    norm_num

/-- `z* = (-7 + i√15)/8` lies on the unit circle. -/
theorem norm_zstar : ‖((-7 + Real.sqrt 15 * I) / 8 : ℂ)‖ = 1 := by
  have hs : Real.sqrt 15 * Real.sqrt 15 = 15 := Real.mul_self_sqrt (by norm_num)
  have h : Complex.normSq ((-7 + Real.sqrt 15 * I) / 8 : ℂ) = 1 := by
    simp [Complex.normSq_apply]
    nlinarith [hs]
  have h2 : ‖((-7 + Real.sqrt 15 * I) / 8 : ℂ)‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, h]
  nlinarith [norm_nonneg ((-7 + Real.sqrt 15 * I) / 8 : ℂ)]

/-- At `z* = (-7 + i√15)/8` the modulus is below `47/80`: `|f(z*)|² = (47/80)² - 57/42200`. -/
theorem cexLC_normSq :
    ∃ F : ℂ, HasSum (fun k : ℕ => (cexLC k : ℂ) * ((-7 + Real.sqrt 15 * I) / 8) ^ k) F ∧
      Complex.normSq F = (47 / 80) ^ 2 - 57 / 42200 := by
  have hs : Real.sqrt 15 * Real.sqrt 15 = 15 := Real.mul_self_sqrt (by norm_num)
  set s := Real.sqrt 15 with hsdef
  set z : ℂ := (-7 + s * I) / 8 with hzdef
  have hn : ‖z‖ = 1 := norm_zstar
  have hza : z.re = -7 / 8 := by simp [hzdef]
  have hzb : z.im = s / 8 := by simp [hzdef]
  have hw : (1 - 7 / 8 * z : ℂ) ≠ 0 := by
    intro h
    have h1 : (7 / 8 : ℂ) * z = 1 := by linear_combination -h
    have h2 := congrArg norm h1
    rw [norm_mul, hn] at h2
    norm_num at h2
  refine ⟨_, cexLC_hasSum_complex z hn.le, ?_⟩
  have hF : (1 + 3 / 4 * z + 9 / 16 * z ^ 2 + 27 / 64 * z ^ 3 * (1 - 7 / 8 * z)⁻¹ : ℂ)
      = (1 - z / 8 - 3 / 32 * z ^ 2 - 9 / 128 * z ^ 3) / (1 - 7 / 8 * z) := by
    rw [eq_div_iff hw]
    have hinv : (1 - 7 / 8 * z) * (1 - 7 / 8 * z)⁻¹ = 1 := mul_inv_cancel₀ hw
    linear_combination (27 / 64 * z ^ 3) * hinv
  rw [hF, map_div₀]
  simp [Complex.normSq_apply, pow_succ, hza, hzb]
  have s2 : s ^ 2 = 15 := by rw [pow_two]; exact hs
  have s4 : s ^ 4 = 225 := by rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, s2]; norm_num
  have s6 : s ^ 6 = 3375 := by rw [show s ^ 6 = (s ^ 2) ^ 3 by ring, s2]; norm_num
  rw [div_eq_iff (by nlinarith [sq_nonneg s])]
  ring_nf
  simp only [s2, s4, s6]
  norm_num

/-- The three times monotone example has its modulus below the value at `z = -1` too: at
`z* = (-7 + i√15)/8`, `|g(z*)|² = (14/3)² - 635/2448`. (At `cos θ = -3/4`, where its real part drops,
its modulus does not.) -/
theorem cex3_normSq :
    ∃ F : ℂ, HasSum (fun k : ℕ => (cex3 k : ℂ) * ((-7 + Real.sqrt 15 * I) / 8) ^ k) F ∧
      Complex.normSq F = (14 / 3) ^ 2 - 635 / 2448 := by
  have hs : Real.sqrt 15 * Real.sqrt 15 = 15 := Real.mul_self_sqrt (by norm_num)
  set s := Real.sqrt 15 with hsdef
  set z : ℂ := (-7 + s * I) / 8 with hzdef
  have hn : ‖z‖ = 1 := norm_zstar
  have hza : z.re = -7 / 8 := by simp [hzdef]
  have hzb : z.im = s / 8 := by simp [hzdef]
  have hw : (2 - z : ℂ) ≠ 0 := by
    intro h
    have h1 : z = 2 := by linear_combination -h
    have h2 := congrArg norm h1
    rw [hn] at h2
    norm_num at h2
  have hw' : (1 - z / 2 : ℂ) ≠ 0 := by
    intro h
    exact hw (by linear_combination 2 * h)
  refine ⟨_, cex3_hasSum_complex z (norm_half hn), ?_⟩
  have hF : (6 + 3 * z + z ^ 2 + (1 - z / 2)⁻¹ : ℂ) = (14 - z ^ 2 - z ^ 3) / (2 - z) := by
    rw [eq_div_iff hw]
    have hinv : (1 - z / 2) * (1 - z / 2)⁻¹ = 1 := mul_inv_cancel₀ hw'
    linear_combination (2 : ℂ) * hinv
  rw [hF, map_div₀]
  simp [Complex.normSq_apply, pow_succ, hza, hzb]
  have s2 : s ^ 2 = 15 := by rw [pow_two]; exact hs
  have s4 : s ^ 4 = 225 := by rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, s2]; norm_num
  have s6 : s ^ 6 = 3375 := by rw [show s ^ 6 = (s ^ 2) ^ 3 by ring, s2]; norm_num
  rw [div_eq_iff (by nlinarith [sq_nonneg s])]
  ring_nf
  simp only [s2, s4, s6]
  norm_num

end Polylog
