/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.MeasureTheory.PappusGuldin
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.NonIntegrable
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum

/-!
# Torricelli's trumpet

Revolving `y = 1/x`, `x ≥ 1`, about the `x`-axis gives a solid of volume `π`; adding the cylinder of
radius 1 and height 1 gives the volume `2π` of the cylinder of radius `√2` and height 1 (Theorem of
the Day's form). The plane region under the hyperbola has infinite area and the surface integrand
`(1/x)√(1 + x⁻⁴) ≥ 1/x` is not integrable: a finite volume with an infinite cross-section and skin.
The volumes come from our Pappus–Guldin `volume_revolution`.

## Main results

* `Torricelli.volume_trumpet`: the trumpet has volume π
* `Torricelli.volume_trumpet_union_cylinder`: trumpet + unit cylinder = cylinder of radius √2 and height 1 (volume 2π)
* `Torricelli.volume_section_eq_top`: the plane section has infinite area
* `Torricelli.not_integrableOn_surface`: the surface-area integrand is not integrable on [1, ∞)

## References

* R. Whitty, Theorem of the Day, «Torricelli's Trumpet» (Analysis/Torricelli).
* E. Torricelli, Opera geometrica (1644); P. Mancosu, Philosophy of Mathematics and Mathematical Practice in the Seventeenth Century, OUP 1999, ch. 5.
-/

@[expose] public section

open MeasureTheory Set

namespace Torricelli

/-- `∫_{r ≤ a} r⁺ = a²/2` for `a ≥ 0`. -/
private lemma lintegral_Iic (a : ℝ) (ha : 0 ≤ a) :
    ∫⁻ r in Iic a, ENNReal.ofReal r = ENNReal.ofReal (a ^ 2 / 2) := by
  have h1 : ∫⁻ r in Iic a, ENNReal.ofReal r = ∫⁻ r in Icc 0 a, ENNReal.ofReal r := by
    rw [← lintegral_indicator measurableSet_Iic, ← lintegral_indicator measurableSet_Icc]
    refine lintegral_congr fun r => ?_
    by_cases h0 : 0 ≤ r
    · by_cases hr : r ≤ a
      · simp [indicator, hr, h0]
      · simp [indicator, hr]
    · have : r ≤ 0 := (not_le.mp h0).le
      simp [indicator, ENNReal.ofReal_eq_zero.mpr this, h0]
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha]
    simp
  · exact (continuous_id.integrableOn_Icc)
  · exact ae_restrict_of_forall_mem measurableSet_Icc fun r hr => hr.1

/-- Tonelli for regions `{p | p.2 ∈ S ∧ p.1 ≤ g p.2}`. -/
private lemma region_lintegral (S : Set ℝ) (hS : MeasurableSet S) (g : ℝ → ℝ)
    (hg : Measurable g) :
    ∫⁻ p in {p : ℝ × ℝ | p.2 ∈ S ∧ p.1 ≤ g p.2}, ENNReal.ofReal p.1
      = ∫⁻ z in S, ∫⁻ r in Iic (g z), ENNReal.ofReal r := by
  have hR : MeasurableSet {p : ℝ × ℝ | p.2 ∈ S ∧ p.1 ≤ g p.2} :=
    (measurable_snd hS).inter (measurableSet_le measurable_fst (hg.comp measurable_snd))
  have hind : Measurable fun p : ℝ × ℝ =>
      {p : ℝ × ℝ | p.2 ∈ S ∧ p.1 ≤ g p.2}.indicator (fun p : ℝ × ℝ => ENNReal.ofReal p.1) p :=
    (by fun_prop : Measurable fun p : ℝ × ℝ => ENNReal.ofReal p.1).indicator hR
  rw [← lintegral_indicator hR, Measure.volume_eq_prod, lintegral_prod_symm _ hind.aemeasurable,
    ← lintegral_indicator hS]
  refine lintegral_congr fun z => ?_
  have e : (fun r : ℝ => {p : ℝ × ℝ | p.2 ∈ S ∧ p.1 ≤ g p.2}.indicator
      (fun p : ℝ × ℝ => ENNReal.ofReal p.1) (r, z))
      = (S.indicator fun _ : ℝ => ((Iic (g z)).indicator (fun r : ℝ => ENNReal.ofReal r))) z := by
    funext r
    by_cases hz : z ∈ S <;> by_cases hr : r ≤ g z <;> simp [indicator, hz, hr]
  by_cases hz : z ∈ S
  · simp only [indicator, hz, ite_true]
    rw [← lintegral_indicator measurableSet_Iic]
    refine lintegral_congr fun r => ?_
    by_cases hr : r ≤ g z <;> simp [indicator, hz, hr]
  · simp [indicator, hz]

/-- Volume of a solid with `0 ≤ z ≤ 1`-type slices of constant radius bound `c`. -/
private lemma volume_cyl (c : ℝ) (hc : 0 ≤ c) :
    volume {q : (ℝ × ℝ) × ℝ | 0 ≤ q.2 ∧ q.2 ≤ 1 ∧ Real.sqrt (q.1.1 ^ 2 + q.1.2 ^ 2) ≤ c}
      = ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (c ^ 2 / 2) := by
  have hset : {q : (ℝ × ℝ) × ℝ | 0 ≤ q.2 ∧ q.2 ≤ 1 ∧ Real.sqrt (q.1.1 ^ 2 + q.1.2 ^ 2) ≤ c}
      = {q : (ℝ × ℝ) × ℝ | (Real.sqrt (q.1.1 ^ 2 + q.1.2 ^ 2), q.2) ∈
          {p : ℝ × ℝ | p.2 ∈ Icc (0 : ℝ) 1 ∧ p.1 ≤ (fun _ => c) p.2}} := by
    ext q; simp [and_assoc]
  rw [hset, PappusGuldin.volume_revolution, region_lintegral (Icc 0 1) measurableSet_Icc _
    measurable_const]
  · congr 1
    simp only [lintegral_Iic c hc]
    rw [setLIntegral_const, Real.volume_Icc]
    simp
  · exact (measurable_snd measurableSet_Icc).inter
      (measurableSet_le measurable_fst measurable_const)

/-- The trumpet has volume `π`. -/
theorem volume_trumpet :
    volume {q : (ℝ × ℝ) × ℝ | 1 ≤ q.2 ∧ Real.sqrt (q.1.1 ^ 2 + q.1.2 ^ 2) ≤ 1 / q.2}
      = ENNReal.ofReal Real.pi := by
  have hset : {q : (ℝ × ℝ) × ℝ | 1 ≤ q.2 ∧ Real.sqrt (q.1.1 ^ 2 + q.1.2 ^ 2) ≤ 1 / q.2}
      = {q : (ℝ × ℝ) × ℝ | (Real.sqrt (q.1.1 ^ 2 + q.1.2 ^ 2), q.2) ∈
          {p : ℝ × ℝ | p.2 ∈ Ici (1 : ℝ) ∧ p.1 ≤ (fun z : ℝ => 1 / z) p.2}} := by
    ext q; simp [and_comm]
  have hg : Measurable fun z : ℝ => 1 / z := by fun_prop
  rw [hset, PappusGuldin.volume_revolution, region_lintegral (Ici 1) measurableSet_Ici _ hg]
  swap
  · exact (measurable_snd measurableSet_Ici).inter
      (measurableSet_le measurable_fst (hg.comp measurable_snd))
  have h1 : ∫⁻ z in Ici (1 : ℝ), ∫⁻ r in Iic (1 / z), ENNReal.ofReal r
      = ∫⁻ z in Ioi (1 : ℝ), ENNReal.ofReal (z ^ (-2 : ℝ) / 2) := by
    calc ∫⁻ z in Ici (1 : ℝ), ∫⁻ r in Iic (1 / z), ENNReal.ofReal r
        = ∫⁻ z in Ioi (1 : ℝ), ∫⁻ r in Iic (1 / z), ENNReal.ofReal r :=
          (setLIntegral_congr Ioi_ae_eq_Ici).symm
      _ = _ := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun z hz => ?_
        have hz0 : (0 : ℝ) < z := by have := hz.out; linarith
        rw [lintegral_Iic (1 / z) (by positivity)]
        congr 1
        rw [Real.rpow_neg hz0.le, Real.rpow_two]
        field_simp
  have hint : IntegrableOn (fun z : ℝ => z ^ (-2 : ℝ) / 2) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).div_const 2
  have h2 : ∫⁻ z in Ioi (1 : ℝ), ENNReal.ofReal (z ^ (-2 : ℝ) / 2) = ENNReal.ofReal (1 / 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (ae_restrict_of_forall_mem measurableSet_Ioi fun z hz => by
        have hz0 : (0 : ℝ) < z := by have := hz.out; linarith
        show 0 ≤ z ^ (-2 : ℝ) / 2
        positivity)]
    congr 1
    rw [integral_div, integral_Ioi_rpow_of_lt (by norm_num) one_pos]
    norm_num
  rw [h1, h2, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

private lemma volume_null_slice :
    volume {q : (ℝ × ℝ) × ℝ | q.2 = 1} = 0 := by
  have : {q : (ℝ × ℝ) × ℝ | q.2 = 1} = (univ : Set (ℝ × ℝ)) ×ˢ {1} := by
    ext q; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]

/-- Trumpet plus unit cylinder has the volume `2π` of the cylinder of radius `√2`, height 1. -/
theorem volume_trumpet_union_cylinder :
    volume ({q : (ℝ × ℝ) × ℝ | 1 ≤ q.2 ∧ Real.sqrt (q.1.1 ^ 2 + q.1.2 ^ 2) ≤ 1 / q.2} ∪
        {q : (ℝ × ℝ) × ℝ | 0 ≤ q.2 ∧ q.2 ≤ 1 ∧ Real.sqrt (q.1.1 ^ 2 + q.1.2 ^ 2) ≤ 1})
      = volume {q : (ℝ × ℝ) × ℝ | 0 ≤ q.2 ∧ q.2 ≤ 1 ∧
          Real.sqrt (q.1.1 ^ 2 + q.1.2 ^ 2) ≤ Real.sqrt 2} ∧
    volume {q : (ℝ × ℝ) × ℝ | 0 ≤ q.2 ∧ q.2 ≤ 1 ∧
          Real.sqrt (q.1.1 ^ 2 + q.1.2 ^ 2) ≤ Real.sqrt 2} = ENNReal.ofReal (2 * Real.pi) := by
  have hf : Measurable fun q : (ℝ × ℝ) × ℝ => Real.sqrt (q.1.1 ^ 2 + q.1.2 ^ 2) := by fun_prop
  have hC : MeasurableSet {q : (ℝ × ℝ) × ℝ | 0 ≤ q.2 ∧ q.2 ≤ 1 ∧
      Real.sqrt (q.1.1 ^ 2 + q.1.2 ^ 2) ≤ 1} :=
    (measurableSet_le measurable_const measurable_snd).inter
      ((measurableSet_le measurable_snd measurable_const).inter
        (measurableSet_le hf measurable_const))
  have hC2 : volume {q : (ℝ × ℝ) × ℝ | 0 ≤ q.2 ∧ q.2 ≤ 1 ∧
      Real.sqrt (q.1.1 ^ 2 + q.1.2 ^ 2) ≤ Real.sqrt 2} = ENNReal.ofReal (2 * Real.pi) := by
    rw [volume_cyl _ (Real.sqrt_nonneg 2), Real.sq_sqrt (by norm_num), ← ENNReal.ofReal_mul
      (by positivity)]
    congr 1
    ring
  have hC1 := volume_cyl 1 zero_le_one
  have hcyl : volume {q : (ℝ × ℝ) × ℝ | 0 ≤ q.2 ∧ q.2 ≤ 1 ∧
      Real.sqrt (q.1.1 ^ 2 + q.1.2 ^ 2) ≤ 1} = ENNReal.ofReal Real.pi := by
    rw [hC1, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  refine ⟨?_, hC2⟩
  rw [hC2]
  have hnull : volume ({q : (ℝ × ℝ) × ℝ | 1 ≤ q.2 ∧ Real.sqrt (q.1.1 ^ 2 + q.1.2 ^ 2) ≤ 1 / q.2}
      ∩ {q : (ℝ × ℝ) × ℝ | 0 ≤ q.2 ∧ q.2 ≤ 1 ∧ Real.sqrt (q.1.1 ^ 2 + q.1.2 ^ 2) ≤ 1}) = 0 := by
    refine measure_mono_null ?_ volume_null_slice
    intro q hq
    exact le_antisymm hq.2.2.1 hq.1.1
  have := measure_union_add_inter (μ := volume)
    {q : (ℝ × ℝ) × ℝ | 1 ≤ q.2 ∧ Real.sqrt (q.1.1 ^ 2 + q.1.2 ^ 2) ≤ 1 / q.2} hC
  rw [hnull, add_zero, volume_trumpet, hcyl, ← ENNReal.ofReal_add Real.pi_pos.le Real.pi_pos.le]
    at this
  rw [this]
  congr 1
  ring

/-- The plane section of the trumpet has infinite area. -/
theorem volume_section_eq_top :
    volume {p : ℝ × ℝ | 1 ≤ p.1 ∧ |p.2| ≤ 1 / p.1} = ⊤ := by
  have hmeas : MeasurableSet {p : ℝ × ℝ | 1 ≤ p.1 ∧ |p.2| ≤ 1 / p.1} :=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le (by fun_prop : Measurable fun p : ℝ × ℝ => |p.2|)
        (by fun_prop : Measurable fun p : ℝ × ℝ => 1 / p.1))
  have hslice : ∀ x : ℝ, volume (Prod.mk x ⁻¹' {p : ℝ × ℝ | 1 ≤ p.1 ∧ |p.2| ≤ 1 / p.1})
      = (Ici (1 : ℝ)).indicator (fun x : ℝ => ENNReal.ofReal (2 / x)) x := by
    intro x
    by_cases hx : 1 ≤ x
    · have hx0 : 0 < x := by linarith
      have : Prod.mk x ⁻¹' {p : ℝ × ℝ | 1 ≤ p.1 ∧ |p.2| ≤ 1 / p.1} = Icc (-(1 / x)) (1 / x) := by
        ext y; simp [abs_le, hx]
      rw [this, Real.volume_Icc, indicator_of_mem (mem_Ici.mpr hx)]
      congr 1
      field_simp
      ring
    · have : Prod.mk x ⁻¹' {p : ℝ × ℝ | 1 ≤ p.1 ∧ |p.2| ≤ 1 / p.1} = ∅ := by
        ext y; simp [hx]
      rw [this, indicator_of_notMem (by simpa using hx)]
      simp
  rw [Measure.volume_eq_prod, Measure.prod_apply hmeas]
  simp_rw [hslice]
  rw [lintegral_indicator measurableSet_Ici]
  by_contra hne
  have hlt : ∫⁻ x in Ici (1 : ℝ), ENNReal.ofReal (2 / x) < ⊤ := lt_top_iff_ne_top.mpr hne
  have hI : IntegrableOn (fun x : ℝ => 2 / x) (Ici 1) := by
    refine ⟨(by fun_prop : Measurable fun x : ℝ => 2 / x).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal]
    · exact hlt
    · exact ae_restrict_of_forall_mem measurableSet_Ici fun x hx => by
        have : (0 : ℝ) < x := by have := hx.out; linarith
        show 0 ≤ 2 / x
        positivity
  refine not_integrableOn_Ici_inv (a := 1) ?_
  have h2 : IntegrableOn (fun x : ℝ => 2 / x / 2) (Ici 1) := hI.div_const 2
  refine IntegrableOn.congr_fun h2 (fun x _ => ?_) measurableSet_Ici
  show 2 / x / 2 = x⁻¹
  ring

/-- The surface-area integrand is not integrable on `[1, ∞)`. -/
theorem not_integrableOn_surface :
    ¬ IntegrableOn (fun x : ℝ => (1 / x) * Real.sqrt (1 + x⁻¹ ^ 4)) (Ici 1) := by
  intro h
  refine not_integrableOn_Ici_inv (a := 1) ?_
  refine Integrable.mono' h (by fun_prop : Measurable fun x : ℝ => x⁻¹).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ici fun x hx => ?_
  have hx0 : (0 : ℝ) < x := by have := hx.out; linarith
  have hs : 1 ≤ Real.sqrt (1 + x⁻¹ ^ 4) := by
    have h4 : 0 ≤ x⁻¹ ^ 4 := by positivity
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
  rw [Real.norm_of_nonneg (by positivity), one_div]
  calc x⁻¹ = x⁻¹ * 1 := (mul_one _).symm
    _ ≤ x⁻¹ * Real.sqrt (1 + x⁻¹ ^ 4) := by gcongr

/-- **Torricelli's trumpet.** -/
theorem trumpet :
    let ρ : (ℝ × ℝ) × ℝ → ℝ := fun q => Real.sqrt (q.1.1 ^ 2 + q.1.2 ^ 2)
    let T : Set ((ℝ × ℝ) × ℝ) := {q | 1 ≤ q.2 ∧ ρ q ≤ 1 / q.2}
    let Cyl : Set ((ℝ × ℝ) × ℝ) := {q | 0 ≤ q.2 ∧ q.2 ≤ 1 ∧ ρ q ≤ 1}
    let Cyl2 : Set ((ℝ × ℝ) × ℝ) := {q | 0 ≤ q.2 ∧ q.2 ≤ 1 ∧ ρ q ≤ Real.sqrt 2}
    volume (T ∪ Cyl) = volume Cyl2 ∧ volume Cyl2 = ENNReal.ofReal (2 * Real.pi) ∧
      volume T = ENNReal.ofReal Real.pi ∧
      volume {p : ℝ × ℝ | 1 ≤ p.1 ∧ |p.2| ≤ 1 / p.1} = ⊤ ∧
      ¬ IntegrableOn (fun x : ℝ => (1 / x) * Real.sqrt (1 + x⁻¹ ^ 4)) (Set.Ici 1) := by
  intro ρ T Cyl Cyl2
  exact ⟨volume_trumpet_union_cylinder.1, volume_trumpet_union_cylinder.2, volume_trumpet,
    volume_section_eq_top, not_integrableOn_surface⟩

end Torricelli

open MeasureTheory
