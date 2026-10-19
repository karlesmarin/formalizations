/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Higgs self-coupling deviations in the SMEFT to all orders in `α`

Closed forms of the Higgs self-coupling deviations `δκ₃, …, δκ₁₂` in the polynomial field
redefinition scheme `h → h + α P(h)`, `P(h) = h + h²/v + h³/(3v²)`, with
`α = v² (C_{H□} − C_{HD}/4) / Λ²` (Alasfar et al.). The `δκₙ` are exact rational functions of
`α`; they are inputs here (derived by computer algebra), and the file checks the identities
between them as identities in the field `ℝ`.

The catalog terminates at `n = 12`: the Standard Model potential in the old field is of degree
`12` in `h`, so `δκ₁₃ = 0`; and `δκ₁₁ = δκ₁₂`.

## Main results

* `ring_identity_four`: `δκ₄ − 6 δκ₃ = α (3α³ + 30α² + 35α − 4) / (3 (α + 1)²)`.
* `ring_identity_five`: `δκ₅ − 15 δκ₃ = 5α (12α³ + 75α² + 68α − 3) / (3 (α + 1)²)`.
* `ring_identity_six`: `δκ₆ − 15 δκ₃ = 5α (α + 3)(132α² + 99α − 1) / (3 (α + 1)²)`.
* `ring_identity_four_leading_order`: `δκ₄ − 6 δκ₃ = −(4/3) α + O(α²)`, with the remainder
  written out.
* `dim8_break_four`, `dim8_break_five`, `dim8_break_six`: at first order in `α` and in the
  dimension-8 parameter `β = v⁴ (C_{HD8} + C_{H,D2}) / Λ⁴` the three identities acquire the
  terms `−(3/2) β`, `−(125/8) β`, `−(573/8) β`.
* `dk7_factored`, …, `dk10_factored`, `dk3_factored`, …, `dk6_factored`: expanded and
  factored forms of each closed form agree; `dk11_eq_dk12`: `δκ₁₁ = δκ₁₂`.

## Related

`SMEFT.HiggsSelfCouplings` treats the leading order with the `c_φ` pieces kept separate; this
file has the all-orders closed forms in `α`, in which the `c_φ` pieces are absent. At leading
order both give `δκ₄ − 6 δκ₃ = −(4/3) α`. The leading-order identities are consistent with the
geometric SMEFT of Helset, Martin and Trott and are not claimed as new.

## References

* L. Alasfar et al., arXiv:2304.01968 (field redefinition).
* J. ter Hoeve, L. Mantani, J. Rojo, A. N. Rossia, E. Vryonidou, *Higgs trilinear coupling in
  SMEFT at HL-LHC and FCC-ee*, arXiv:2504.05974.
* A. Helset, A. Martin, M. Trott, *The geometric Standard Model Effective Field Theory*,
  arXiv:2001.01453.
* Ported from `SmeftLean/RingIdentities.lean` of the project `smeft-lean` (Lean v4.27.0).
-/

@[expose] public section

namespace SMEFT.AllOrdersSelfCouplings

/-! ### All-orders `δκₙ`, `n = 3, …, 6` -/

/-- `δκ₃(α)`, the trilinear deviation. -/
noncomputable def dk3 (a : ℝ) : ℝ := a * (a + 3) / (a + 1)

/-- `δκ₄(α)`, the quartic deviation. -/
noncomputable def dk4 (a : ℝ) : ℝ :=
  a * (3 * a ^ 3 + 48 * a ^ 2 + 107 * a + 50) / (3 * (a + 1) ^ 2)

/-- `δκ₅(α)`, the quintic deviation (Standard Model value `0`). -/
noncomputable def dk5 (a : ℝ) : ℝ :=
  20 * a * (3 * a ^ 3 + 21 * a ^ 2 + 26 * a + 6) / (3 * (a + 1) ^ 2)

/-- `δκ₆(α)`, the sextic deviation. -/
noncomputable def dk6 (a : ℝ) : ℝ :=
  20 * a * (33 * a ^ 3 + 126 * a ^ 2 + 83 * a + 6) / (3 * (a + 1) ^ 2)

/-! ### The ring identities, to all orders in `α` -/

/-- The trilinear–quartic identity `δκ₄ − 6 δκ₃ = α (3α³ + 30α² + 35α − 4) / (3 (α + 1)²)`. -/
theorem ring_identity_four (a : ℝ) (ha : a + 1 ≠ 0) :
    dk4 a - 6 * dk3 a = a * (3 * a ^ 3 + 30 * a ^ 2 + 35 * a - 4) / (3 * (a + 1) ^ 2) := by
  unfold dk4 dk3
  field_simp
  ring

/-- The trilinear–quintic identity `δκ₅ − 15 δκ₃ = 5α (12α³ + 75α² + 68α − 3) / (3 (α + 1)²)`. -/
theorem ring_identity_five (a : ℝ) (ha : a + 1 ≠ 0) :
    dk5 a - 15 * dk3 a
      = 5 * a * (12 * a ^ 3 + 75 * a ^ 2 + 68 * a - 3) / (3 * (a + 1) ^ 2) := by
  unfold dk5 dk3
  field_simp
  ring

/-- The trilinear–sextic identity `δκ₆ − 15 δκ₃ = 5α (α + 3)(132α² + 99α − 1) / (3 (α + 1)²)`. -/
theorem ring_identity_six (a : ℝ) (ha : a + 1 ≠ 0) :
    dk6 a - 15 * dk3 a
      = 5 * a * (a + 3) * (132 * a ^ 2 + 99 * a - 1) / (3 * (a + 1) ^ 2) := by
  unfold dk6 dk3
  field_simp
  ring

/-- Leading order of `ring_identity_four`: `δκ₄ − 6 δκ₃ = −(4/3) α + O(α²)`. -/
theorem ring_identity_four_leading_order (a : ℝ) (ha : a + 1 ≠ 0) :
    dk4 a - 6 * dk3 a + (4 / 3) * a
      = a ^ 2 * (3 * a ^ 2 + 34 * a + 43) / (3 * (a + 1) ^ 2) := by
  unfold dk4 dk3
  field_simp
  ring

/-! ### Dimension-8 breaking at first order

At first order in `α` and `β`, `δκ₃ = 3α − (5/8)β`, `δκ₄ = (50/3)α − (21/4)β`,
`δκ₅ = 40α − 25β`, `δκ₆ = 40α − 81β` (inputs). -/

/-- `δκ₄ − 6 δκ₃ = −(4/3) α − (3/2) β` at first order. -/
theorem dim8_break_four (a b : ℝ) :
    ((50 / 3) * a - (21 / 4) * b) - 6 * (3 * a - (5 / 8) * b) = -(4 / 3) * a - (3 / 2) * b := by
  ring

/-- `δκ₅ − 15 δκ₃ = −5 α − (125/8) β` at first order. -/
theorem dim8_break_five (a b : ℝ) :
    (40 * a - 25 * b) - 15 * (3 * a - (5 / 8) * b) = -5 * a - (125 / 8) * b := by
  ring

/-- `δκ₆ − 15 δκ₃ = −5 α − (573/8) β` at first order. -/
theorem dim8_break_six (a b : ℝ) :
    (40 * a - 81 * b) - 15 * (3 * a - (5 / 8) * b) = -5 * a - (573 / 8) * b := by
  ring

/-! ### The catalog `n = 7, …, 12` -/

/-- `δκ₇(α)`. -/
noncomputable def dk7 (a : ℝ) : ℝ := (280 * a ^ 2 * (6 * a ^ 2 + 13 * a + 4)) / (a ^ 2 + 2 * a + 1)

theorem dk7_factored (a : ℝ) :
    dk7 a = (1680 * a ^ 4 + 3640 * a ^ 3 + 1120 * a ^ 2) / (a ^ 2 + 2 * a + 1) := by
  unfold dk7; ring

/-- `δκ₈(α)`. -/
noncomputable def dk8 (a : ℝ) : ℝ := (560 * a ^ 2 * (17 * a ^ 2 + 20 * a + 2)) / (a ^ 2 + 2 * a + 1)

theorem dk8_factored (a : ℝ) :
    dk8 a = (9520 * a ^ 4 + 11200 * a ^ 3 + 1120 * a ^ 2) / (a ^ 2 + 2 * a + 1) := by
  unfold dk8; ring

/-- `δκ₉(α)`. -/
noncomputable def dk9 (a : ℝ) : ℝ := (4480 * a ^ 3 * (9 * a + 5)) / (a ^ 2 + 2 * a + 1)

theorem dk9_factored (a : ℝ) :
    dk9 a = (40320 * a ^ 4 + 22400 * a ^ 3) / (a ^ 2 + 2 * a + 1) := by
  unfold dk9; ring

/-- `δκ₁₀(α)`. -/
noncomputable def dk10 (a : ℝ) : ℝ := (11200 * a ^ 3 * (11 * a + 2)) / (a ^ 2 + 2 * a + 1)

theorem dk10_factored (a : ℝ) :
    dk10 a = (123200 * a ^ 4 + 22400 * a ^ 3) / (a ^ 2 + 2 * a + 1) := by
  unfold dk10; ring

/-- `δκ₁₁(α) = 246400 α⁴ / (α + 1)²`. -/
noncomputable def dk11 (a : ℝ) : ℝ := (246400 * a ^ 4) / (a ^ 2 + 2 * a + 1)

/-- `δκ₁₂(α) = 246400 α⁴ / (α + 1)²`. -/
noncomputable def dk12 (a : ℝ) : ℝ := (246400 * a ^ 4) / (a ^ 2 + 2 * a + 1)

/-- `δκ₁₁ = δκ₁₂`. -/
theorem dk11_eq_dk12 (a : ℝ) : dk11 a = dk12 a := rfl

/-! ### Expanded forms for `n = 3, …, 6` -/

theorem dk3_factored (a : ℝ) : dk3 a = (a ^ 2 + 3 * a) / (a + 1) := by
  unfold dk3; ring

theorem dk4_factored (a : ℝ) :
    dk4 a = (3 * a ^ 4 + 48 * a ^ 3 + 107 * a ^ 2 + 50 * a) / (3 * a ^ 2 + 6 * a + 3) := by
  unfold dk4; ring

theorem dk5_factored (a : ℝ) :
    dk5 a = (60 * a ^ 4 + 420 * a ^ 3 + 520 * a ^ 2 + 120 * a) / (3 * a ^ 2 + 6 * a + 3) := by
  unfold dk5; ring

theorem dk6_factored (a : ℝ) :
    dk6 a = (660 * a ^ 4 + 2520 * a ^ 3 + 1660 * a ^ 2 + 120 * a) / (3 * a ^ 2 + 6 * a + 3) := by
  unfold dk6; ring

end SMEFT.AllOrdersSelfCouplings
