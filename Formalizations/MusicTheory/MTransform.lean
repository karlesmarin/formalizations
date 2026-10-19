/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.MusicTheory.Fourier
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.Zsqrtd.ToReal
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.IntervalCases

/-!
# The multiplication transform on the Fourier coefficients

For a unit `u` of `ℤ/12`, multiplying a pitch-class set by `u` permutes its Fourier coefficients:
`Ahat (u • A) t = Ahat A (u * t)`; with `u = 5` this exchanges the first and fifth coefficients.
The power `‖Ahat A 1‖²` lies in `½ ℤ[√3]`: `2 ‖Ahat A 1‖² = P + Q √3` with integers `P`, `Q`
read from the interval vector, and the order of these values is decided in `ℤ√3`.

## Main results

* `Ahat_mul`, `Ahat_mul_norm`, `Ahat_M5`, `Ahat_M5_norm`.
* `powerSpec_one_eq`: the `ℤ[√3]` form of the first power coefficient.
* `toR3_le_iff`, `powerSpec_one_re_le_iff`: the order of `ℤ√3` agrees with the real order.

## References

* E. Amiot, *David Lewin and maximally even sets*, J. Math. Music 1 (2007).
* I. Quinn, *General equal-tempered harmony*, Perspectives of New Music 44–45 (2006–2007).
-/

@[expose] public section

namespace MusicTheory

open Finset ZMod AddChar Complex
open scoped ZMod Real

namespace MTransform

/-- The 0/1 indicator of a pc-set (= `Fourier.ind`). -/
noncomputable def ind (A : Finset (ZMod 12)) : ZMod 12 → ℂ := fun j => if j ∈ A then 1 else 0

/-- The DFT of a pc-set (= `Fourier.Ahat`): `Â A t = Σ_{a ∈ A} exp(−2πi·a·t/12)`. -/
noncomputable def Ahat (A : Finset (ZMod 12)) : ZMod 12 → ℂ := 𝓕 (ind A)

/-- `Â A t = Σ_{a ∈ A} stdAddChar(−(a·t))` (= `Fourier.Ahat_apply`). -/
lemma Ahat_apply (A : Finset (ZMod 12)) (t : ZMod 12) :
    Ahat A t = ∑ a ∈ A, stdAddChar (-(a * t)) := by
  unfold Ahat ind
  rw [dft_apply]
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]

/-- Left multiplication by a unit is injective on `ZMod 12` (no `NoZeroDivisors` needed: cancel by
    `u⁻¹`). The witness fed to `Finset.sum_image`. -/
lemma unit_mul_injOn (u : (ZMod 12)ˣ) {s : Finset (ZMod 12)} :
    ∀ x ∈ s, ∀ y ∈ s, (u : ZMod 12) * x = (u : ZMod 12) * y → x = y := by
  intro x _ y _ h
  have h' := congrArg (fun z => (↑u⁻¹ : ZMod 12) * z) h
  simpa only [← mul_assoc, Units.inv_mul, one_mul] using h'

/-- **STAGE A — the M-transform coefficient permutation.** For a unit `u ∈ (ℤ/12)ˣ`, multiplying
    every pitch class by `u` permutes the Fourier index: `Â(u·A)(t) = Â(A)(u·t)`. Equivalently
    `a_k(M_u A) = a_{u·k}(A)` — Amiot's footnote / Quinn's Multiplication Principle. -/
theorem Ahat_mul (u : (ZMod 12)ˣ) (A : Finset (ZMod 12)) (t : ZMod 12) :
    Ahat (A.image (fun a => (u : ZMod 12) * a)) t = Ahat A ((u : ZMod 12) * t) := by
  rw [Ahat_apply, Ahat_apply, Finset.sum_image (unit_mul_injOn u)]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  ring

/-- **Magnitude corollary.** The M-transform preserves the spectrum up to the index permutation:
    `‖Â(u·A)(t)‖ = ‖Â(A)(u·t)‖`. -/
theorem Ahat_mul_norm (u : (ZMod 12)ˣ) (A : Finset (ZMod 12)) (t : ZMod 12) :
    ‖Ahat (A.image (fun a => (u : ZMod 12) * a)) t‖ = ‖Ahat A ((u : ZMod 12) * t)‖ := by
  rw [Ahat_mul]

/-- `5` is a unit of `ℤ/12` (it is its own inverse: `5·5 = 25 ≡ 1`). The M₅ "circle-of-fifths"
    multiplication used in Amiot's corollary. -/
def u5 : (ZMod 12)ˣ := ⟨5, 5, by decide, by decide⟩

@[simp] lemma u5_coe : (u5 : ZMod 12) = 5 := rfl

/-- **M-transform corollary, frequency `1 ↦ 5`.** With `u = 5`, the M-transform sends the `k = 1`
    coefficient to the `k = 5` coefficient: `Â(M₅ A)(1) = Â(A)(5)`. This is the index map that
    turns the Huddling Lemma (cluster maximizes `‖a_1‖`) into its M-corollary (the fifth-generated
    set, image of the cluster under M₅, maximizes `‖a_5‖`). -/
theorem Ahat_M5 (A : Finset (ZMod 12)) :
    Ahat (A.image (fun a => (5 : ZMod 12) * a)) 1 = Ahat A 5 := by
  have h := Ahat_mul u5 A 1
  simpa only [u5_coe, mul_one] using h

/-- **M-transform corollary (magnitudes), `‖a_1‖ ↦ ‖a_5‖`.** `‖Â(M₅ A)(1)‖ = ‖Â(A)(5)‖`. -/
theorem Ahat_M5_norm (A : Finset (ZMod 12)) :
    ‖Ahat (A.image (fun a => (5 : ZMod 12) * a)) 1‖ = ‖Ahat A 5‖ := by
  rw [Ahat_M5]

/-- The cluster `{0,1,2,3,4,5}` maps under M₅ to the fifth-generated chain `{0,5,10,3,8,1}`
    (= `{0,1,3,5,8,10}`), the diatonic-fifths skeleton — the concrete Huddling↦M₅ witness. -/
example : ({0, 1, 2, 3, 4, 5} : Finset (ZMod 12)).image (fun a => (5 : ZMod 12) * a)
    = {0, 1, 3, 5, 8, 10} := by decide

/-! ### STAGE B — Amiot's Huddling Lemma: the ℤ[√3] reformulation and the decidable order.

Amiot 2007 (Huddling Lemma) maximizes `‖Â A 1‖`, equivalently `powerSpec A 1 = ‖Â A 1‖² ∈ ℝ`.
The 12th-root cosines `cos(π d/6)` introduce `√3` at the `d = ±1, ±5` interval classes, so the
value is NOT rational: it lives in ℤ[√3] (scaled by ½). We FORMALIZE that reformulation here.
This is a Lean restatement of Amiot's analysis, NOT new mathematics.

`powerSpec`, `autocorr`, `IVraw` live in `Fourier.lean`; `IV k := IVraw A k` is the interval vector.

KEYSTONE (`powerSpec_one_eq`):
    2 · powerSpec A 1  =  P A + (Q A)·√3 ,   with the INTEGER coefficients
      P A = 2·|A| + IV 2 − IV 4 − 2·IV 6           (the ℚ-part, ×2)
      Q A = IV 1 − IV 5                            (the √3-part)
The √3 ordering BLOCKS naive `decide`; mapping `P + Q√3 ↦ (⟨P,Q⟩ : Zsqrtd 3)` exposes Mathlib's
`LinearOrder (ℤ√d)` (decidable), and `toR3_le_iff` bridges that order to the real spectrum order
(Mathlib has `Zsqrtd.toReal` as a ring hom and its injectivity, not its monotonicity, which is
proved here from `SqLe`/`nonneg_cases`). -/

/-- Bridge: `stdAddChar` of an integer residue as `cos + sin·i` (real cosines/sines). -/
lemma charZ (n : ℤ) :
    stdAddChar ((n : ℤ) : ZMod 12) =
      (Real.cos (π * n / 6) : ℂ) + (Real.sin (π * n / 6) : ℂ) * Complex.I := by
  rw [stdAddChar_coe]
  have h : Complex.exp (2 * (π : ℂ) * Complex.I * (n : ℂ) / (12 : ℕ))
      = Complex.exp (((π * n / 6 : ℝ) : ℂ) * Complex.I) := by
    congr 1; push_cast; ring
  rw [h, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

-- derived fundamental real values (the two angles outside Mathlib's named special angles)
private lemma rc4 : Real.cos (2 * π / 3) = -1 / 2 := by
  rw [show 2 * π / 3 = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]; ring
private lemma rs4 : Real.sin (2 * π / 3) = Real.sqrt 3 / 2 := by
  rw [show 2 * π / 3 = π - π / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
private lemma rc5 : Real.cos (5 * π / 6) = -Real.sqrt 3 / 2 := by
  rw [show 5 * π / 6 = π - π / 6 by ring, Real.cos_pi_sub, Real.cos_pi_div_six]; ring
private lemma rs5 : Real.sin (5 * π / 6) = 1 / 2 := by
  rw [show 5 * π / 6 = π - π / 6 by ring, Real.sin_pi_sub, Real.sin_pi_div_six]

-- the twelve 12th-root character values  stdAddChar (-(d : ZMod 12))
private lemma ch0 : stdAddChar (-(0 : ZMod 12)) = 1 := by
  rw [show (-(0 : ZMod 12)) = (((0 : ℤ)) : ZMod 12) from by decide, charZ]
  rw [show (π * ((0 : ℤ) : ℝ) / 6) = 0 from by push_cast; ring, Real.cos_zero, Real.sin_zero]
  push_cast; ring
private lemma ch1 : stdAddChar (-(1 : ZMod 12)) = (Real.sqrt 3 : ℂ) / 2 - (1 / 2) * Complex.I := by
  rw [show (-(1 : ZMod 12)) = (((-1 : ℤ)) : ZMod 12) from by decide, charZ]
  rw [show (π * ((-1 : ℤ) : ℝ) / 6) = -(π / 6) from by push_cast; ring,
      Real.cos_neg, Real.sin_neg, Real.cos_pi_div_six, Real.sin_pi_div_six]
  push_cast; ring
private lemma ch2 : stdAddChar (-(2 : ZMod 12)) = (1 / 2 : ℂ) - (Real.sqrt 3 : ℂ) / 2 * Complex.I := by
  rw [show (-(2 : ZMod 12)) = (((-2 : ℤ)) : ZMod 12) from by decide, charZ]
  rw [show (π * ((-2 : ℤ) : ℝ) / 6) = -(π / 3) from by push_cast; ring,
      Real.cos_neg, Real.sin_neg, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast; ring
private lemma ch3 : stdAddChar (-(3 : ZMod 12)) = -Complex.I := by
  rw [show (-(3 : ZMod 12)) = (((-3 : ℤ)) : ZMod 12) from by decide, charZ]
  rw [show (π * ((-3 : ℤ) : ℝ) / 6) = -(π / 2) from by push_cast; ring,
      Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast; ring
private lemma ch4 : stdAddChar (-(4 : ZMod 12)) = (-1 / 2 : ℂ) - (Real.sqrt 3 : ℂ) / 2 * Complex.I := by
  rw [show (-(4 : ZMod 12)) = (((-4 : ℤ)) : ZMod 12) from by decide, charZ]
  rw [show (π * ((-4 : ℤ) : ℝ) / 6) = -(2 * π / 3) from by push_cast; ring,
      Real.cos_neg, Real.sin_neg, rc4, rs4]
  push_cast; ring
private lemma ch5 : stdAddChar (-(5 : ZMod 12)) = -(Real.sqrt 3 : ℂ) / 2 - (1 / 2) * Complex.I := by
  rw [show (-(5 : ZMod 12)) = (((-5 : ℤ)) : ZMod 12) from by decide, charZ]
  rw [show (π * ((-5 : ℤ) : ℝ) / 6) = -(5 * π / 6) from by push_cast; ring,
      Real.cos_neg, Real.sin_neg, rc5, rs5]
  push_cast; ring
private lemma ch6 : stdAddChar (-(6 : ZMod 12)) = -1 := by
  rw [show (-(6 : ZMod 12)) = (((-6 : ℤ)) : ZMod 12) from by decide, charZ]
  rw [show (π * ((-6 : ℤ) : ℝ) / 6) = -π from by push_cast; ring,
      Real.cos_neg, Real.sin_neg, Real.cos_pi, Real.sin_pi]
  push_cast; ring
private lemma ch7 : stdAddChar (-(7 : ZMod 12)) = -(Real.sqrt 3 : ℂ) / 2 + (1 / 2) * Complex.I := by
  rw [show (-(7 : ZMod 12)) = (((5 : ℤ)) : ZMod 12) from by decide, charZ]
  rw [show (π * ((5 : ℤ) : ℝ) / 6) = 5 * π / 6 from by push_cast; ring, rc5, rs5]
  push_cast; ring
private lemma ch8 : stdAddChar (-(8 : ZMod 12)) = (-1 / 2 : ℂ) + (Real.sqrt 3 : ℂ) / 2 * Complex.I := by
  rw [show (-(8 : ZMod 12)) = (((4 : ℤ)) : ZMod 12) from by decide, charZ]
  rw [show (π * ((4 : ℤ) : ℝ) / 6) = 2 * π / 3 from by push_cast; ring, rc4, rs4]
  push_cast; ring
private lemma ch9 : stdAddChar (-(9 : ZMod 12)) = Complex.I := by
  rw [show (-(9 : ZMod 12)) = (((3 : ℤ)) : ZMod 12) from by decide, charZ]
  rw [show (π * ((3 : ℤ) : ℝ) / 6) = π / 2 from by push_cast; ring,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast; ring
private lemma ch10 : stdAddChar (-(10 : ZMod 12)) = (1 / 2 : ℂ) + (Real.sqrt 3 : ℂ) / 2 * Complex.I := by
  rw [show (-(10 : ZMod 12)) = (((2 : ℤ)) : ZMod 12) from by decide, charZ]
  rw [show (π * ((2 : ℤ) : ℝ) / 6) = π / 3 from by push_cast; ring,
      Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast; ring
private lemma ch11 : stdAddChar (-(11 : ZMod 12)) = (Real.sqrt 3 : ℂ) / 2 + (1 / 2) * Complex.I := by
  rw [show (-(11 : ZMod 12)) = (((1 : ℤ)) : ZMod 12) from by decide, charZ]
  rw [show (π * ((1 : ℤ) : ℝ) / 6) = π / 6 from by push_cast; ring,
      Real.cos_pi_div_six, Real.sin_pi_div_six]
  push_cast; ring

/-- ℚ-part (×2) of `2·powerSpec A 1`: `P A = 2·|A| + IV 2 − IV 4 − 2·IV 6`. -/
def P (A : Finset (ZMod 12)) : ℤ :=
  2 * (A.card : ℤ) + Fourier.IVraw A 2 - Fourier.IVraw A 4 - 2 * Fourier.IVraw A 6

/-- √3-part of `2·powerSpec A 1`: `Q A = IV 1 − IV 5`. -/
def Q (A : Finset (ZMod 12)) : ℤ :=
  Fourier.IVraw A 1 - Fourier.IVraw A 5

/-- **STAGE B keystone — the ℤ[√3] reformulation of Amiot's Huddling target.**
    `2 · powerSpec A 1 = P A + (Q A)·√3` with `P A, Q A : ℤ` the interval-vector combinations. -/
theorem powerSpec_one_eq (A : Finset (ZMod 12)) :
    2 * Fourier.powerSpec A 1 = (P A : ℂ) + (Q A : ℂ) * Real.sqrt 3 := by
  -- conversions IVraw → autocorr
  have hIV : ∀ k : ℕ, 1 ≤ k → k ≤ 5 →
      (Fourier.IVraw A k : ℂ) = 2 * (Fourier.autocorr A (k : ZMod 12) : ℂ) := by
    intro k h1 h5
    rw [Fourier.IVraw_eq_two_commonTones A k h1 h5, Fourier.commonTones_eq_autocorr]
    push_cast; ring
  have hIV6 : (Fourier.IVraw A 6 : ℂ) = (Fourier.autocorr A (6 : ZMod 12) : ℂ) := by
    rw [Fourier.IVraw_tritone, Fourier.commonTones_eq_autocorr]
  have hcard : (A.card : ℂ) = (Fourier.autocorr A (0 : ZMod 12) : ℂ) := by
    rw [Fourier.autocorr_zero]
  -- expand the power spectrum as a forward DFT of the autocorrelation
  rw [Fourier.powerSpec_eq_dft_autocorr,
      show (Finset.univ : Finset (ZMod 12)) = {0,1,2,3,4,5,6,7,8,9,10,11} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [mul_one]
  rw [ch0, ch1, ch2, ch3, ch4, ch5, ch6, ch7, ch8, ch9, ch10, ch11]
  -- fold the upper-half autocorrelations onto the lower half (evenness, `autocorr_neg`)
  rw [show (7 : ZMod 12) = -(5 : ZMod 12) from by decide, Fourier.autocorr_neg,
      show (8 : ZMod 12) = -(4 : ZMod 12) from by decide, Fourier.autocorr_neg,
      show (9 : ZMod 12) = -(3 : ZMod 12) from by decide, Fourier.autocorr_neg,
      show (10 : ZMod 12) = -(2 : ZMod 12) from by decide, Fourier.autocorr_neg,
      show (11 : ZMod 12) = -(1 : ZMod 12) from by decide, Fourier.autocorr_neg]
  -- expand P, Q and convert to autocorrelation; then ℂ-ring with √3 as an atom
  simp only [P, Q]
  push_cast
  rw [hcard, hIV6, hIV 1 (by norm_num) (by norm_num), hIV 2 (by norm_num) (by norm_num),
      hIV 4 (by norm_num) (by norm_num), hIV 5 (by norm_num) (by norm_num)]
  simp only [Nat.cast_ofNat, Nat.cast_one]
  ring

/-! #### The decidable ℤ[√3] order (`Zsqrtd 3`) and the bridge to the real spectrum order.

`Zsqrtd (3 : ℕ)` is used (not `Zsqrtd (3 : ℤ)`) because Mathlib's `LinearOrder (ℤ√d)` is stated
for `d : ℕ`. `Zsqrtd.toReal` is a ring hom but Mathlib does not prove it monotone, so we supply
`toR3_le_iff` from the `SqLe`/`nonneg_cases` characterisation of the order. -/

/-- The ℤ[√3] coordinate vector of `2·powerSpec A 1` (= `P A + Q A·√3`). -/
def psZ (A : Finset (ZMod 12)) : Zsqrtd (3 : ℕ) := ⟨P A, Q A⟩

/-- `ℤ[√3] ↪ ℝ`, the canonical ring hom sending `√3 ↦ Real.sqrt 3`. -/
noncomputable abbrev toR3 : Zsqrtd (3 : ℕ) →+* ℝ :=
  Zsqrtd.toReal (by norm_num : (0 : ℤ) ≤ (3 : ℕ))

/-- The image of `psZ A` in ℝ is exactly `2·Re(powerSpec A 1)`: the spectrum value lives in ℤ[√3]. -/
lemma toReal_psZ (A : Finset (ZMod 12)) :
    toR3 (psZ A) = 2 * (Fourier.powerSpec A 1).re := by
  have h := congrArg Complex.re (powerSpec_one_eq A)
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat] at h
  simp only [psZ, toR3, Zsqrtd.toReal, Zsqrtd.lift_apply_apply]
  push_cast
  linarith [h]

/-- `3` is not a perfect square in ℤ (needed for `Zsqrtd.toReal` injectivity). -/
lemma three_nonsquare : ∀ n : ℤ, ((3 : ℕ) : ℤ) ≠ n * n := by
  intro n h
  push_cast at h
  have h1 : n ≤ 1 := by nlinarith [sq_nonneg (n - 2), h]
  have h2 : -1 ≤ n := by nlinarith [sq_nonneg (n + 2), h]
  interval_cases n <;> norm_num at h

private lemma toReal_mk (p q : ℤ) :
    toR3 ⟨p, q⟩ = (p : ℝ) + (q : ℝ) * Real.sqrt 3 := by
  simp only [toR3, Zsqrtd.toReal, Zsqrtd.lift_apply_apply]
  push_cast
  ring

private lemma sqrt3_ge_iff {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    v * Real.sqrt 3 ≤ u ↔ 3 * v ^ 2 ≤ u ^ 2 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsn : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  constructor
  · intro h; nlinarith [mul_nonneg hv hsn, h]
  · intro h; nlinarith [mul_nonneg hv hsn, h, sq_nonneg (u - v * Real.sqrt 3)]

private lemma sqrt3_le_iff {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    u ≤ v * Real.sqrt 3 ↔ u ^ 2 ≤ 3 * v ^ 2 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsn : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  constructor
  · intro h; nlinarith [mul_nonneg hv hsn, h]
  · intro h; nlinarith [mul_nonneg hv hsn, h, sq_nonneg (v * Real.sqrt 3 - u)]

private lemma toR3_nonneg {a : Zsqrtd (3 : ℕ)} (ha : 0 ≤ a) : 0 ≤ toR3 a := by
  obtain ⟨x, y, h | h | h⟩ := Zsqrtd.nonneg_cases (Zsqrtd.nonneg_iff_zero_le.mpr ha)
  · subst h; rw [toReal_mk]; push_cast; positivity
  · subst h
    have hN : Zsqrtd.SqLe y 3 x 1 :=
      Zsqrtd.nonnegg_pos_neg.1 (Zsqrtd.nonneg_iff_zero_le.mpr ha)
    rw [toReal_mk]; push_cast
    have hh : (3 : ℝ) * (y : ℝ) ^ 2 ≤ (x : ℝ) ^ 2 := by
      simp only [Zsqrtd.SqLe] at hN
      have h1 : (3 : ℝ) * y * y ≤ 1 * x * x := by exact_mod_cast hN
      nlinarith [h1]
    have := (sqrt3_ge_iff (by positivity) (by positivity)).2 hh
    linarith
  · subst h
    have hN : Zsqrtd.SqLe x 1 y 3 :=
      Zsqrtd.nonnegg_neg_pos.1 (Zsqrtd.nonneg_iff_zero_le.mpr ha)
    rw [toReal_mk]; push_cast
    have hh : (x : ℝ) ^ 2 ≤ 3 * (y : ℝ) ^ 2 := by
      simp only [Zsqrtd.SqLe] at hN
      have h1 : (1 : ℝ) * x * x ≤ 3 * y * y := by exact_mod_cast hN
      nlinarith [h1]
    have := (sqrt3_le_iff (by positivity) (by positivity)).2 hh
    linarith

/-- `0 ≤ a` in `ℤ[√3]` iff `0 ≤ toR3 a` in ℝ — monotonicity of `Zsqrtd.toReal` (not in Mathlib). -/
lemma zero_le_iff_toR3 (a : Zsqrtd (3 : ℕ)) : 0 ≤ a ↔ 0 ≤ toR3 a := by
  constructor
  · exact toR3_nonneg
  · intro ht
    rcases Zsqrtd.nonneg_total a with h | h
    · exact Zsqrtd.nonneg_iff_zero_le.mp h
    · have h0 : 0 ≤ toR3 (-a) := toR3_nonneg (Zsqrtd.nonneg_iff_zero_le.mp h)
      rw [map_neg] at h0
      have hTa : toR3 a = 0 := le_antisymm (by linarith) ht
      have hinj : Function.Injective toR3 :=
        Zsqrtd.toReal_injective (by norm_num) three_nonsquare
      have ha0 : a = 0 := hinj (by rw [hTa, map_zero])
      rw [ha0]

/-- **The ℤ[√3] order IS the real spectrum order.** `a ≤ b` in `ℤ[√3]` iff `toR3 a ≤ toR3 b`. -/
lemma toR3_le_iff (a b : Zsqrtd (3 : ℕ)) : a ≤ b ↔ toR3 a ≤ toR3 b := by
  constructor
  · intro hab
    have h0 : (0 : ℝ) ≤ toR3 (b - a) := (zero_le_iff_toR3 (b - a)).mp (sub_nonneg.mpr hab)
    rw [map_sub] at h0; linarith
  · intro hab
    have h0 : (0 : ℝ) ≤ toR3 (b - a) := by rw [map_sub]; linarith
    exact sub_nonneg.mp ((zero_le_iff_toR3 (b - a)).mpr h0)

/-- **STAGE B bridge — the Huddling comparison reduced to the decidable ℤ[√3] order.**
    `Re(powerSpec A 1) ≤ Re(powerSpec B 1)` iff `psZ A ≤ psZ B` in `Zsqrtd 3` (a `DecidableLE`
    order). So Amiot's "cluster maximizes `‖a₁‖`" becomes a finite decidable comparison. -/
theorem powerSpec_one_re_le_iff (A B : Finset (ZMod 12)) :
    (Fourier.powerSpec A 1).re ≤ (Fourier.powerSpec B 1).re ↔ psZ A ≤ psZ B := by
  rw [toR3_le_iff, toReal_psZ, toReal_psZ]
  constructor <;> intro h <;> linarith

/-- The ℤ[√3] order on spectrum values is decidable — kernel-checkable comparisons. -/
example (A B : Finset (ZMod 12)) : Decidable (psZ A ≤ psZ B) := inferInstance

/-- **Concrete Huddling witness (kernel `decide`).** The contiguous cluster
    `{0,1,2,3,4,5}` dominates the whole-tone scale `{0,2,4,6,8,10}` in `‖a₁‖²` — a single
    decidable ℤ[√3] comparison via `psZ`. (The general statement over all sets is
    `Huddling.arc_maximizes_power`, proved by a structural argument.) -/
example : psZ {0, 2, 4, 6, 8, 10} ≤ psZ {0, 1, 2, 3, 4, 5} := by decide

end MTransform

end MusicTheory
