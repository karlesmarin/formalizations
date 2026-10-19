/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Higgs self-coupling deviations in the SMEFT: tree-level coefficient matching

Structural identities for the deviations `δκ₃, …, δκ₆` of the Higgs self-couplings in the
Standard Model Effective Field Theory (Warsaw basis, normalization `L ⊃ (c / Λ²) O`), as pure
identities in the field `ℝ`.

* The operator `O_φ = (φ†φ − v²/2)³` equals `(v h + h²/2)³` in unitary gauge; matching the `h³`
  and `h⁴` coefficients of the potential gives the `c_φ` pieces
  `δκ₃ = −2 v⁴ c_φ / (m_h² Λ²)` and `δκ₄ = −12 v⁴ c_φ / (m_h² Λ²)`, so `δκ₄ = 6 δκ₃`.
* The operators `O_{φ□}` and `O_{φD}` enter through the field redefinition of Alasfar et al.
  with `C_{H,kin} = c_{φ□} − c_{φD}/4`; their pieces `3 (v²/Λ²) C_{H,kin}` (in `δκ₃`) and
  `(50/3) (v²/Λ²) C_{H,kin}` (in `δκ₄`) are taken as input, not derived here.

## Main results

* `operator_phi_expansion`: `(v h + h²/2)³ = v³h³ + (3v²/2)h⁴ + (3v/4)h⁵ + h⁶/8`.
* `h3_matching`, `h4_matching`: the `c_φ` pieces solve the `h³` and `h⁴` matching equations
  with `λ_SM = m_h² / (2 v²)`.
* `deltaKappa4Phi_eq_six_mul`: `δκ₄ = 6 δκ₃` for the `c_φ` pieces; `deltaKappa4Phi_ne_div_six`:
  `δκ₄ ≠ δκ₃ / 6` whenever `c_φ ≠ 0`.
* `exists_ne_deltaKappa3_eq`: distinct Wilson coefficients give the same `δκ₃` (flat direction).
* `deltaKappa4_sub_six_mul_deltaKappa3`: `δκ₄ − 6 δκ₃ = −(4/3) (v²/Λ²) C_{H,kin}`;
  `deltaKappa4_eq_six_mul_iff`: `δκ₄ = 6 δκ₃ ↔ C_{H,kin} = 0` (for `v, Λ ≠ 0`).
* `deltaKappa5LO_sub_fifteen_mul`, `deltaKappa6LO_sub_fifteen_mul`: at leading order in
  `C_{H,kin}`, `δκ₅ − 15 δκ₃ = δκ₆ − 15 δκ₃ = −5 (v²/Λ²) C_{H,kin}`; the `c_φ` pieces cancel.

## Related

Mathlib has no physics. physlib (`Physlib.Particles.StandardModel`) formalizes the Higgs field
and potential but, as far as we found, not these SMEFT coefficient identities (existence check of
2026-10-19 against Mathlib, LeanSearch, the AFP and GitHub: nothing found). The leading-order
identities are consistent with the geometric SMEFT of Helset, Martin and Trott and are not
claimed as new. The all-orders closed forms in the Alasfar scheme are in the separate project
`smeft-lean` (`SmeftLean.RingIdentities`).

## References

* J. ter Hoeve, L. Mantani, J. Rojo, A. N. Rossia, E. Vryonidou, *Higgs trilinear coupling in
  SMEFT at HL-LHC and FCC-ee*, arXiv:2504.05974.
* L. Alasfar et al., arXiv:2304.01968 (field redefinition, eqs. (2.4)–(2.5)).
* A. Helset, A. Martin, M. Trott, *The geometric Standard Model Effective Field Theory*,
  arXiv:2001.01453.
* Ported from `Taf/SmeftTrilinearAudit.lean` of
  [karlesmarin/lean-taf](https://github.com/karlesmarin/lean-taf) (Lean v4.30.0-rc2).
-/

@[expose] public section

namespace SMEFT.HiggsSelfCouplings

/-! ### The operator `O_φ` in unitary gauge -/

/-- Full expansion of `O_φ = (v h + h²/2)³`. -/
theorem operator_phi_expansion (v h : ℝ) :
    (v * h + h ^ 2 / 2) ^ 3
      = v ^ 3 * h ^ 3 + (3 * v ^ 2 / 2) * h ^ 4 + (3 * v / 4) * h ^ 5 + h ^ 6 / 8 := by
  ring

/-- The `h³ + h⁴` part of `O_φ` plus the `h⁵, h⁶` tail. -/
theorem operator_phi_partial (v h : ℝ) :
    (v * h + h ^ 2 / 2) ^ 3
      = (v ^ 3 * h ^ 3 + (3 * v ^ 2 / 2) * h ^ 4) + ((3 * v / 4) * h ^ 5 + h ^ 6 / 8) := by
  ring

/-! ### The Standard Model coupling and the κ-framework -/

/-- `λ_SM = m_h² / (2 v²)`. -/
def LambdaSMRelation (lam_SM m_h v : ℝ) : Prop :=
  lam_SM = m_h ^ 2 / (2 * v ^ 2)

/-- `λ_SM v = m_h² / (2 v)`. -/
theorem lambdaSM_mul_v (lam_SM m_h v : ℝ) (hv : v ≠ 0)
    (h : LambdaSMRelation lam_SM m_h v) :
    lam_SM * v = m_h ^ 2 / (2 * v) := by
  unfold LambdaSMRelation at h
  rw [h]
  field_simp

/-- `κ₃ = 1 + δκ₃`. -/
def kappa3 (delta_kappa3 : ℝ) : ℝ := 1 + delta_kappa3

theorem kappa3_def (delta_kappa3 : ℝ) : kappa3 delta_kappa3 = 1 + delta_kappa3 := rfl

theorem kappa3_zero : kappa3 0 = 1 := by
  unfold kappa3; ring

/-- `λ_SM = m_h² / (2 v²)` at `m_h = v = 1`. -/
theorem lambdaSM_rational_check : (1 : ℝ) ^ 2 / (2 * (1 : ℝ) ^ 2) = 1 / 2 := by
  norm_num

/-! ### The `c_φ` pieces -/

/-- The `c_φ` piece of `δκ₃`. -/
noncomputable def deltaKappa3Phi (v m_h c_phi Λ : ℝ) : ℝ :=
  -2 * v ^ 4 * c_phi / (m_h ^ 2 * Λ ^ 2)

/-- The `c_φ` piece of `δκ₄`. -/
noncomputable def deltaKappa4Phi (v m_h c_phi Λ : ℝ) : ℝ :=
  -12 * v ^ 4 * c_phi / (m_h ^ 2 * Λ ^ 2)

/-- `h³` matching: `λ_SM v (1 + δκ₃) = λ_SM v − c_φ v³ / Λ²` with `λ_SM = m_h² / (2 v²)`. -/
theorem h3_matching (v m_h c_phi Λ : ℝ) (hv : v ≠ 0) (hm : m_h ≠ 0) (hΛ : Λ ≠ 0) :
    (m_h ^ 2 / (2 * v ^ 2)) * v * (1 + deltaKappa3Phi v m_h c_phi Λ)
      = (m_h ^ 2 / (2 * v ^ 2)) * v - c_phi * v ^ 3 / Λ ^ 2 := by
  unfold deltaKappa3Phi
  have h2v2 : (2 : ℝ) * v ^ 2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hv)
  have hΛ2 : Λ ^ 2 ≠ 0 := pow_ne_zero 2 hΛ
  have hm2 : m_h ^ 2 ≠ 0 := pow_ne_zero 2 hm
  field_simp
  ring

/-- `h⁴` matching: `(λ_SM / 4)(1 + δκ₄) = λ_SM / 4 − 3 c_φ v² / (2 Λ²)`. -/
theorem h4_matching (v m_h c_phi Λ : ℝ) (hv : v ≠ 0) (hm : m_h ≠ 0) (hΛ : Λ ≠ 0) :
    ((m_h ^ 2 / (2 * v ^ 2)) / 4) * (1 + deltaKappa4Phi v m_h c_phi Λ)
      = (m_h ^ 2 / (2 * v ^ 2)) / 4 - 3 * c_phi * v ^ 2 / (2 * Λ ^ 2) := by
  unfold deltaKappa4Phi
  have h2v2 : (2 : ℝ) * v ^ 2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hv)
  have hΛ2 : Λ ^ 2 ≠ 0 := pow_ne_zero 2 hΛ
  have hm2 : m_h ^ 2 ≠ 0 := pow_ne_zero 2 hm
  field_simp
  ring

/-- `δκ₄ = 6 δκ₃` for the `c_φ` pieces. -/
theorem deltaKappa4Phi_eq_six_mul (v m_h c_phi Λ : ℝ) :
    deltaKappa4Phi v m_h c_phi Λ = 6 * deltaKappa3Phi v m_h c_phi Λ := by
  unfold deltaKappa3Phi deltaKappa4Phi
  ring

/-- `δκ₄ ≠ δκ₃ / 6` for the `c_φ` pieces whenever `c_φ ≠ 0`. -/
theorem deltaKappa4Phi_ne_div_six (v m_h c_phi Λ : ℝ) (hv : v ≠ 0) (hm : m_h ≠ 0)
    (hΛ : Λ ≠ 0) (hc : c_phi ≠ 0) :
    deltaKappa4Phi v m_h c_phi Λ ≠ deltaKappa3Phi v m_h c_phi Λ / 6 := by
  unfold deltaKappa3Phi deltaKappa4Phi
  have h2v2 : (2 : ℝ) * v ^ 2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hv)
  have hΛ2 : Λ ^ 2 ≠ 0 := pow_ne_zero 2 hΛ
  have hm2 : m_h ^ 2 ≠ 0 := pow_ne_zero 2 hm
  have hv4 : v ^ 4 ≠ 0 := pow_ne_zero 4 hv
  intro habs
  apply hc
  field_simp at habs
  linarith

/-- Standard Model limit of the `c_φ` piece of `δκ₃`. -/
theorem deltaKappa3Phi_zero (v m_h Λ : ℝ) : deltaKappa3Phi v m_h 0 Λ = 0 := by
  unfold deltaKappa3Phi
  ring

/-- Standard Model limit of the `c_φ` piece of `δκ₄`. -/
theorem deltaKappa4Phi_zero (v m_h Λ : ℝ) : deltaKappa4Phi v m_h 0 Λ = 0 := by
  unfold deltaKappa4Phi
  ring

/-! ### Field-redefinition pieces and full `δκ₃`, `δκ₄` -/

/-- `C_{H,kin} = c_{φ□} − c_{φD} / 4` (Alasfar et al., eq. (2.4)). -/
noncomputable def cHKin (c_phi_box c_phi_D : ℝ) : ℝ := c_phi_box - c_phi_D / 4

/-- The field-redefinition piece of `δκ₃`, `3 (v²/Λ²) C_{H,kin}`. -/
noncomputable def deltaKappa3Redef (v c_phi_box c_phi_D Λ : ℝ) : ℝ :=
  3 * v ^ 2 / Λ ^ 2 * (cHKin c_phi_box c_phi_D)

/-- `δκ₃` = `c_φ` piece + field-redefinition piece. -/
noncomputable def deltaKappa3 (v m_h c_phi c_phi_box c_phi_D Λ : ℝ) : ℝ :=
  deltaKappa3Phi v m_h c_phi Λ + deltaKappa3Redef v c_phi_box c_phi_D Λ

theorem deltaKappa3_eq (v m_h c_phi c_phi_box c_phi_D Λ : ℝ) :
    deltaKappa3 v m_h c_phi c_phi_box c_phi_D Λ
      = deltaKappa3Phi v m_h c_phi Λ + deltaKappa3Redef v c_phi_box c_phi_D Λ := by
  rfl

theorem deltaKappa3_box_D_zero (v m_h c_phi Λ : ℝ) :
    deltaKappa3 v m_h c_phi 0 0 Λ = deltaKappa3Phi v m_h c_phi Λ := by
  unfold deltaKappa3 deltaKappa3Redef cHKin
  ring

theorem deltaKappa3_phi_zero (v m_h c_phi_box c_phi_D Λ : ℝ) :
    deltaKappa3 v m_h 0 c_phi_box c_phi_D Λ = deltaKappa3Redef v c_phi_box c_phi_D Λ := by
  unfold deltaKappa3 deltaKappa3Phi
  ring

/-- Flat direction: two distinct triples `(c_φ, c_{φ□}, c_{φD})` give the same `δκ₃`. -/
theorem exists_ne_deltaKappa3_eq (v m_h Λ : ℝ) :
    ∃ (c_phi_a c_box_a c_D_a c_phi_b c_box_b c_D_b : ℝ),
      (c_phi_a, c_box_a, c_D_a) ≠ (c_phi_b, c_box_b, c_D_b) ∧
      deltaKappa3 v m_h c_phi_a c_box_a c_D_a Λ
        = deltaKappa3 v m_h c_phi_b c_box_b c_D_b Λ := by
  refine ⟨0, 0, 0, 0, 4, 16, ?_, ?_⟩
  · intro h
    simp at h
  · unfold deltaKappa3 deltaKappa3Phi deltaKappa3Redef cHKin
    ring

/-- `δκ₄^{c_φ} − 6 δκ₃ = −18 (v²/Λ²) C_{H,kin}`. -/
theorem deltaKappa4Phi_sub_six_mul_deltaKappa3 (v m_h c_phi c_phi_box c_phi_D Λ : ℝ) :
    deltaKappa4Phi v m_h c_phi Λ - 6 * deltaKappa3 v m_h c_phi c_phi_box c_phi_D Λ
      = -18 * (v ^ 2 / Λ ^ 2) * (cHKin c_phi_box c_phi_D) := by
  unfold deltaKappa4Phi deltaKappa3 deltaKappa3Phi deltaKappa3Redef cHKin
  ring

/-- The field-redefinition piece of `δκ₄`, `(50/3) (v²/Λ²) C_{H,kin}`. -/
noncomputable def deltaKappa4Redef (v c_phi_box c_phi_D Λ : ℝ) : ℝ :=
  (50 / 3) * (v ^ 2 / Λ ^ 2) * (cHKin c_phi_box c_phi_D)

/-- `δκ₄` = `c_φ` piece + field-redefinition piece. -/
noncomputable def deltaKappa4 (v m_h c_phi c_phi_box c_phi_D Λ : ℝ) : ℝ :=
  deltaKappa4Phi v m_h c_phi Λ + deltaKappa4Redef v c_phi_box c_phi_D Λ

theorem deltaKappa4_eq (v m_h c_phi c_phi_box c_phi_D Λ : ℝ) :
    deltaKappa4 v m_h c_phi c_phi_box c_phi_D Λ
      = deltaKappa4Phi v m_h c_phi Λ + deltaKappa4Redef v c_phi_box c_phi_D Λ := by
  rfl

theorem deltaKappa4_box_D_zero (v m_h c_phi Λ : ℝ) :
    deltaKappa4 v m_h c_phi 0 0 Λ = deltaKappa4Phi v m_h c_phi Λ := by
  unfold deltaKappa4 deltaKappa4Redef cHKin
  ring

theorem deltaKappa4_phi_zero (v m_h c_phi_box c_phi_D Λ : ℝ) :
    deltaKappa4 v m_h 0 c_phi_box c_phi_D Λ = deltaKappa4Redef v c_phi_box c_phi_D Λ := by
  unfold deltaKappa4 deltaKappa4Phi
  ring

/-- `δκ₄ − 6 δκ₃ = −(4/3) (v²/Λ²) C_{H,kin}`: the `c_φ` pieces cancel. -/
theorem deltaKappa4_sub_six_mul_deltaKappa3 (v m_h c_phi c_phi_box c_phi_D Λ : ℝ) :
    deltaKappa4 v m_h c_phi c_phi_box c_phi_D Λ
      - 6 * deltaKappa3 v m_h c_phi c_phi_box c_phi_D Λ
      = -(4 / 3) * (v ^ 2 / Λ ^ 2) * (cHKin c_phi_box c_phi_D) := by
  unfold deltaKappa4 deltaKappa4Phi deltaKappa4Redef deltaKappa3 deltaKappa3Phi
    deltaKappa3Redef cHKin
  ring

/-- `9 δκ₄^{redef} = 50 δκ₃^{redef}`. -/
theorem nine_mul_deltaKappa4Redef (v c_phi_box c_phi_D Λ : ℝ) :
    9 * deltaKappa4Redef v c_phi_box c_phi_D Λ
      = 50 * deltaKappa3Redef v c_phi_box c_phi_D Λ := by
  unfold deltaKappa4Redef deltaKappa3Redef
  ring

/-! ### The ratio `δκ₄ / δκ₃ = 6` and the kinetic hyperplane

The identity `deltaKappa4_sub_six_mul_deltaKappa3` holds pointwise in the Wilson coefficients,
hence at every renormalization scale: the ratio is exactly `6` at a scale iff `C_{H,kin} = 0`
there. -/

/-- `δκ₄ = 6 δκ₃ ↔ C_{H,kin} = 0`, for `v, Λ ≠ 0`. -/
theorem deltaKappa4_eq_six_mul_iff (v m_h c_phi c_phi_box c_phi_D Λ : ℝ)
    (hv : v ≠ 0) (hΛ : Λ ≠ 0) :
    deltaKappa4 v m_h c_phi c_phi_box c_phi_D Λ
      = 6 * deltaKappa3 v m_h c_phi c_phi_box c_phi_D Λ
    ↔ cHKin c_phi_box c_phi_D = 0 := by
  have h := deltaKappa4_sub_six_mul_deltaKappa3 v m_h c_phi c_phi_box c_phi_D Λ
  have hv2 : v ^ 2 ≠ 0 := pow_ne_zero 2 hv
  have hΛ2 : Λ ^ 2 ≠ 0 := pow_ne_zero 2 hΛ
  constructor
  · intro habs
    rw [habs, sub_self] at h
    have h4_3 : (4 : ℝ) / 3 ≠ 0 := by norm_num
    have hv2Λ2 : v ^ 2 / Λ ^ 2 ≠ 0 := div_ne_zero hv2 hΛ2
    have : (4 / 3 : ℝ) * (v ^ 2 / Λ ^ 2) * (cHKin c_phi_box c_phi_D) = 0 := by linarith
    have := mul_eq_zero.mp this
    rcases this with h1 | h2
    · rcases mul_eq_zero.mp h1 with h11 | h12
      · exact absurd h11 h4_3
      · exact absurd h12 hv2Λ2
    · exact h2
  · intro h_kin
    have : deltaKappa4 v m_h c_phi c_phi_box c_phi_D Λ
        - 6 * deltaKappa3 v m_h c_phi c_phi_box c_phi_D Λ = 0 := by
      rw [h]
      rw [h_kin]
      ring
    linarith

/-- On the kinetic hyperplane `C_{H,kin} = 0` the ratio is exactly `6`, for every `c_φ`. -/
theorem deltaKappa4_eq_six_mul_of_cHKin_eq_zero (v m_h c_phi c_phi_box c_phi_D Λ : ℝ)
    (h_kin : cHKin c_phi_box c_phi_D = 0) :
    deltaKappa4 v m_h c_phi c_phi_box c_phi_D Λ
      = 6 * deltaKappa3 v m_h c_phi c_phi_box c_phi_D Λ := by
  have h := deltaKappa4_sub_six_mul_deltaKappa3 v m_h c_phi c_phi_box c_phi_D Λ
  rw [h_kin] at h
  linarith

/-- A point with `c_{φ□} ≠ 0` on the kinetic hyperplane: `(c_{φ□}, c_{φD}) = (1, 4)`. -/
theorem deltaKappa4_eq_six_mul_one_four (v m_h c_phi Λ : ℝ) :
    let c_phi_box := (1 : ℝ)
    let c_phi_D := (4 : ℝ)
    deltaKappa4 v m_h c_phi c_phi_box c_phi_D Λ
      = 6 * deltaKappa3 v m_h c_phi c_phi_box c_phi_D Λ := by
  apply deltaKappa4_eq_six_mul_of_cHKin_eq_zero
  unfold cHKin
  norm_num

/-! ### `δκ₅` and `δκ₆` at leading order in `C_{H,kin}`

The `c_φ` pieces come from the `h⁵` and `h⁶` coefficients of `O_φ` with the normalizations
`N₅ = 20`, `N₆ = 120`; both are `−30 v⁴ c_φ / (m_h² Λ²)`. The leading-order
field-redefinition pieces are both `40 (v²/Λ²) C_{H,kin}` (taken as input). -/

/-- The `c_φ` piece of `δκ₅`. -/
noncomputable def deltaKappa5Phi (v m_h c_phi Λ : ℝ) : ℝ :=
  -30 * v ^ 4 * c_phi / (m_h ^ 2 * Λ ^ 2)

/-- The `c_φ` piece of `δκ₆`. -/
noncomputable def deltaKappa6Phi (v m_h c_phi Λ : ℝ) : ℝ :=
  -30 * v ^ 4 * c_phi / (m_h ^ 2 * Λ ^ 2)

/-- The leading-order field-redefinition piece of `δκ₅`. -/
noncomputable def deltaKappa5RedefLO (v c_phi_box c_phi_D Λ : ℝ) : ℝ :=
  40 * (v ^ 2 / Λ ^ 2) * (cHKin c_phi_box c_phi_D)

/-- The leading-order field-redefinition piece of `δκ₆`. -/
noncomputable def deltaKappa6RedefLO (v c_phi_box c_phi_D Λ : ℝ) : ℝ :=
  40 * (v ^ 2 / Λ ^ 2) * (cHKin c_phi_box c_phi_D)

/-- `δκ₅` at leading order. -/
noncomputable def deltaKappa5LO (v m_h c_phi c_phi_box c_phi_D Λ : ℝ) : ℝ :=
  deltaKappa5Phi v m_h c_phi Λ + deltaKappa5RedefLO v c_phi_box c_phi_D Λ

/-- `δκ₆` at leading order. -/
noncomputable def deltaKappa6LO (v m_h c_phi c_phi_box c_phi_D Λ : ℝ) : ℝ :=
  deltaKappa6Phi v m_h c_phi Λ + deltaKappa6RedefLO v c_phi_box c_phi_D Λ

/-- `δκ₅ − 15 δκ₃ = −5 (v²/Λ²) C_{H,kin}` at leading order. -/
theorem deltaKappa5LO_sub_fifteen_mul (v m_h c_phi c_phi_box c_phi_D Λ : ℝ) :
    deltaKappa5LO v m_h c_phi c_phi_box c_phi_D Λ
      - 15 * deltaKappa3 v m_h c_phi c_phi_box c_phi_D Λ
      = -5 * (v ^ 2 / Λ ^ 2) * (cHKin c_phi_box c_phi_D) := by
  unfold deltaKappa5LO deltaKappa5Phi deltaKappa5RedefLO deltaKappa3 deltaKappa3Phi
    deltaKappa3Redef cHKin
  ring

/-- `δκ₆ − 15 δκ₃ = −5 (v²/Λ²) C_{H,kin}` at leading order. -/
theorem deltaKappa6LO_sub_fifteen_mul (v m_h c_phi c_phi_box c_phi_D Λ : ℝ) :
    deltaKappa6LO v m_h c_phi c_phi_box c_phi_D Λ
      - 15 * deltaKappa3 v m_h c_phi c_phi_box c_phi_D Λ
      = -5 * (v ^ 2 / Λ ^ 2) * (cHKin c_phi_box c_phi_D) := by
  unfold deltaKappa6LO deltaKappa6Phi deltaKappa6RedefLO deltaKappa3 deltaKappa3Phi
    deltaKappa3Redef cHKin
  ring

/-- The two leading-order identities have the same right-hand side. -/
theorem deltaKappa5LO_sub_eq_deltaKappa6LO_sub (v m_h c_phi c_phi_box c_phi_D Λ : ℝ) :
    deltaKappa5LO v m_h c_phi c_phi_box c_phi_D Λ
      - 15 * deltaKappa3 v m_h c_phi c_phi_box c_phi_D Λ
    = deltaKappa6LO v m_h c_phi c_phi_box c_phi_D Λ
        - 15 * deltaKappa3 v m_h c_phi c_phi_box c_phi_D Λ := by
  rw [deltaKappa5LO_sub_fifteen_mul, deltaKappa6LO_sub_fifteen_mul]

/-- The `c_φ` pieces cancel in `δκ₅ − 15 δκ₃`. -/
theorem deltaKappa5Phi_sub_fifteen_mul (v m_h c_phi Λ : ℝ) :
    deltaKappa5Phi v m_h c_phi Λ - 15 * deltaKappa3Phi v m_h c_phi Λ = 0 := by
  unfold deltaKappa5Phi deltaKappa3Phi
  ring

/-- The `c_φ` pieces cancel in `δκ₆ − 15 δκ₃`. -/
theorem deltaKappa6Phi_sub_fifteen_mul (v m_h c_phi Λ : ℝ) :
    deltaKappa6Phi v m_h c_phi Λ - 15 * deltaKappa3Phi v m_h c_phi Λ = 0 := by
  unfold deltaKappa6Phi deltaKappa3Phi
  ring

/-- On the kinetic hyperplane `δκ₅ = δκ₆ = 15 δκ₃` at leading order. -/
theorem deltaKappa5LO_deltaKappa6LO_of_cHKin_eq_zero (v m_h c_phi c_phi_box c_phi_D Λ : ℝ)
    (h_kin : cHKin c_phi_box c_phi_D = 0) :
    deltaKappa5LO v m_h c_phi c_phi_box c_phi_D Λ
      = 15 * deltaKappa3 v m_h c_phi c_phi_box c_phi_D Λ
    ∧ deltaKappa6LO v m_h c_phi c_phi_box c_phi_D Λ
      = 15 * deltaKappa3 v m_h c_phi c_phi_box c_phi_D Λ := by
  refine ⟨?_, ?_⟩
  · have h := deltaKappa5LO_sub_fifteen_mul v m_h c_phi c_phi_box c_phi_D Λ
    rw [h_kin] at h; linarith
  · have h := deltaKappa6LO_sub_fifteen_mul v m_h c_phi c_phi_box c_phi_D Λ
    rw [h_kin] at h; linarith

end SMEFT.HiggsSelfCouplings
