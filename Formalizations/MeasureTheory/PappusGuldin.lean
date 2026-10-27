/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# The Pappus–Guldin theorem for volumes of revolution

Revolving a measurable plane region `R` (coordinates `(r, z)`) about the `z`-axis gives a solid of
volume `2π ∫_R r`, i.e. the area of `R` times the length `2π r̄` of the path of its centroid; points
with `r ≤ 0` contribute nothing to either side, so no sign condition is needed. Built on Mathlib's
polar coordinates: each horizontal slice is a planar set `{√(u² + v²) ∈ A}`, whose area is
`2π ∫_A r` by `lintegral_comp_polarCoord_symm`, and Tonelli reassembles the slices.

## Main results

* `PappusGuldin.volume_revolution`: volume of the solid of revolution of R = 2 pi * integral over R of r

## References

* P. Guldin, *Centrobaryca*, Vienna, 1635–1641; Pappus of Alexandria, *Collection*, Book VII.
-/

@[expose] public section

open MeasureTheory Set

namespace PappusGuldin

/-- Radial slice: for measurable `A ⊆ ℝ`, the plane set `{w | ‖w‖ ∈ A}` has area `2π ∫_A r`. -/
private lemma volume_radial (A : Set ℝ) (hA : MeasurableSet A) :
    volume {w : ℝ × ℝ | Real.sqrt (w.1 ^ 2 + w.2 ^ 2) ∈ A}
      = ENNReal.ofReal (2 * Real.pi) * ∫⁻ r in A, ENNReal.ofReal r := by
  have hm : MeasurableSet {w : ℝ × ℝ | Real.sqrt (w.1 ^ 2 + w.2 ^ 2) ∈ A} :=
    (by fun_prop : Measurable fun w : ℝ × ℝ => Real.sqrt (w.1 ^ 2 + w.2 ^ 2)) hA
  have h := lintegral_comp_polarCoord_symm
    ({w : ℝ × ℝ | Real.sqrt (w.1 ^ 2 + w.2 ^ 2) ∈ A}.indicator (fun _ => (1 : ENNReal)))
  rw [lintegral_indicator_const hm, one_mul] at h
  rw [← h]
  have h2 : ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 •
      ({w : ℝ × ℝ | Real.sqrt (w.1 ^ 2 + w.2 ^ 2) ∈ A}.indicator (fun _ => (1 : ENNReal))
        (polarCoord.symm p))
      = ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 * A.indicator (fun _ => (1 : ENNReal)) p.1 := by
    refine setLIntegral_congr_fun polarCoord.open_target.measurableSet ?_
    intro p hp
    rw [polarCoord_target] at hp
    have hp1 : 0 < p.1 := hp.1
    have : Real.sqrt ((polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2) = p.1 := by
      rw [polarCoord_symm_apply]
      simp only
      have : (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq p.2]
      rw [this, Real.sqrt_sq hp1.le]
    have e : polarCoord.symm p ∈ {w : ℝ × ℝ | Real.sqrt (w.1 ^ 2 + w.2 ^ 2) ∈ A} ↔ p.1 ∈ A := by
      show Real.sqrt _ ∈ A ↔ _
      rw [this]
    classical
    simp only [smul_eq_mul, indicator]
    rw [if_congr e rfl rfl]
  have hmeas : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 * A.indicator (fun _ => (1 : ENNReal)) p.1 :=
    Measurable.mul (by fun_prop) ((measurable_const.indicator hA).comp measurable_fst)
  rw [h2, polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod _ hmeas.aemeasurable]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
  have hm1 : Measurable fun x : ℝ => ENNReal.ofReal x * A.indicator (fun _ => (1 : ENNReal)) x :=
    Measurable.mul (by fun_prop) (measurable_const.indicator hA)
  rw [lintegral_mul_const _ hm1]
  have e1 : ∫⁻ x in Ioi 0, ENNReal.ofReal x * A.indicator (fun _ => (1 : ENNReal)) x
      = ∫⁻ r in A, ENNReal.ofReal r := by
    rw [setLIntegral_eq_of_support_subset, ← lintegral_indicator hA]
    · congr 1
      funext x
      by_cases hx : x ∈ A <;> simp [indicator, hx]
    · intro x hx
      by_contra hx0
      have : x ≤ 0 := not_lt.mp hx0
      exact hx (by simp [ENNReal.ofReal_eq_zero.mpr this])
  rw [e1, mul_comm]
  congr 2
  ring

/-- **Pappus–Guldin (volume).** Revolving a measurable plane region `R` (coordinates `(r, z)`) about
the `z`-axis gives a solid of volume `2π ∫_R r`. -/
theorem volume_revolution (R : Set (ℝ × ℝ)) (hR : MeasurableSet R) :
    volume {q : (ℝ × ℝ) × ℝ | (Real.sqrt (q.1.1 ^ 2 + q.1.2 ^ 2), q.2) ∈ R}
      = ENNReal.ofReal (2 * Real.pi) * ∫⁻ p in R, ENNReal.ofReal p.1 := by
  have hS : MeasurableSet {q : (ℝ × ℝ) × ℝ | (Real.sqrt (q.1.1 ^ 2 + q.1.2 ^ 2), q.2) ∈ R} :=
    (by fun_prop : Measurable fun q : (ℝ × ℝ) × ℝ => (Real.sqrt (q.1.1 ^ 2 + q.1.2 ^ 2), q.2)) hR
  have hslice : ∀ z : ℝ, volume ((fun x : ℝ × ℝ => (x, z)) ⁻¹'
      {q : (ℝ × ℝ) × ℝ | (Real.sqrt (q.1.1 ^ 2 + q.1.2 ^ 2), q.2) ∈ R})
      = ENNReal.ofReal (2 * Real.pi) * ∫⁻ r in (fun r : ℝ => (r, z)) ⁻¹' R, ENNReal.ofReal r :=
    fun z => volume_radial _ (measurable_prodMk_right hR)
  have hind : Measurable fun p : ℝ × ℝ => R.indicator (fun p : ℝ × ℝ => ENNReal.ofReal p.1) p :=
    (by fun_prop : Measurable fun p : ℝ × ℝ => ENNReal.ofReal p.1).indicator hR
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hS]
  simp_rw [hslice]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  rw [← lintegral_indicator hR, Measure.volume_eq_prod, lintegral_prod_symm _ hind.aemeasurable]
  refine lintegral_congr fun z => ?_
  rw [← lintegral_indicator (measurable_prodMk_right hR)]
  rfl

end PappusGuldin
