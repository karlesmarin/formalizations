/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

-- encaje: la familia F_t = Q + t·w² sobre la forma de longitud 8 de Xu–Cui–Qi: 8 cuadrados para t ≥ 1/2.
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

/-!
# A family above the Xu–Cui–Qi form of length eight

Let `Q` be the `4 × 3` biquadratic form of Xu, Cui and Qi (arXiv:2602.21570, Theorem 4.1), which is a sum of
eight squares of bilinear forms and of no fewer, and let `w = x₂y₁ + x₃y₂ + x₄y₃`. For `t > 0` the Gram matrix
of `F_t = Q + t w²` built from the nine forms is an extreme point of rank nine of its Gram spectrahedron
(checked by computation, not here). Nevertheless `F_t` is a sum of eight squares for every `t ≥ 1/2`, and of
seven at `t = 1/2`: this file proves the polynomial identity behind it and the resulting representation.

## Main results

* `SegrePersistence.XCQFamily.scaled_identity`: `t F_t = t S + (t(h + l) + (t − 1)d)² + (2t − 1) d²`, with `S`
  a sum of six squares, for every real `t` (`d = x₂y₁`, `h = x₃y₂`, `l = x₄y₃`).
* `SegrePersistence.XCQFamily.eight_squares`: for `t ≥ 1/2`, `F_t` equals an explicit sum of eight squares of
  real bilinear forms.
* `SegrePersistence.XCQFamily.seven_squares_half`: at `t = 1/2`, seven squares.
-/

@[expose] public section

namespace SegrePersistence

namespace XCQFamily

variable (x : Fin 4 → ℝ) (y : Fin 3 → ℝ)

/-- `z i j = x_{i+1} y_{j+1}`. -/
def z (i : Fin 4) (j : Fin 3) : ℝ := x i * y j

/-- The form `Q` of Xu–Cui–Qi, Theorem 4.1: `P_{4,3,7} + (x₄y₂ + x₁y₃)²`. -/
def Q : ℝ :=
  z x y 0 0 ^ 2 + z x y 1 1 ^ 2 + z x y 2 2 ^ 2 + z x y 0 1 ^ 2 + z x y 1 2 ^ 2 + z x y 2 0 ^ 2 +
    z x y 3 0 ^ 2 + (z x y 3 1 + z x y 0 2) ^ 2

/-- `d = x₂y₁`, `h = x₃y₂`, `l = x₄y₃`. -/
def d : ℝ := z x y 1 0
def h : ℝ := z x y 2 1
def l : ℝ := z x y 3 2

/-- The family `F_t = Q + t (d + h + l)²`. -/
def F (t : ℝ) : ℝ := Q x y + t * (d x y + h x y + l x y) ^ 2

/-- Six squares. -/
def S : ℝ :=
  z x y 0 0 ^ 2 + z x y 0 1 ^ 2 + (z x y 0 2 + z x y 3 1) ^ 2 + z x y 2 2 ^ 2 +
    (z x y 1 1 + z x y 2 0) ^ 2 + (z x y 1 2 + z x y 3 0) ^ 2

/-- The scaled identity, valid for every real `t`. -/
theorem scaled_identity (t : ℝ) :
    t * F x y t = t * S x y + (t * (h x y + l x y) + (t - 1) * d x y) ^ 2 + (2 * t - 1) * d x y ^ 2 := by
  simp only [F, Q, S, d, h, l, z]
  ring

/-- For `t ≥ 1/2`, `F_t` is a sum of eight squares of bilinear forms: the six of `S`, then
`(t(h + l) + (t − 1)d)/√t` and `√((2t − 1)/t) · d`. -/
theorem eight_squares {t : ℝ} (ht : 1 / 2 ≤ t) :
    F x y t = S x y + ((t * (h x y + l x y) + (t - 1) * d x y) / Real.sqrt t) ^ 2 +
      (Real.sqrt ((2 * t - 1) / t) * d x y) ^ 2 := by
  have t0 : 0 < t := by linarith
  have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt t0.le
  have hq : Real.sqrt ((2 * t - 1) / t) ^ 2 = (2 * t - 1) / t :=
    Real.sq_sqrt (div_nonneg (by linarith) t0.le)
  have key := scaled_identity x y t
  rw [div_pow, mul_pow, hs, hq]
  field_simp
  linarith [key]

/-- At `t = 1/2` the last square vanishes: seven squares. -/
theorem seven_squares_half :
    F x y (1 / 2) = S x y + ((h x y + l x y) - d x y) ^ 2 / 2 := by
  simp only [F, Q, S, d, h, l, z]
  ring

end XCQFamily

end SegrePersistence
