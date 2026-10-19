/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Tactic.Ring

/-!
# Integrality of the `U(2)` anomaly quadratic form

Integer arithmetic for the `U(2)` example of Monnier–Moore–Park on the quantization of anomaly
coefficients in six-dimensional `𝒩 = (1, 0)` supergravity (§3, equations (3.32)–(3.34)). On the
cocharacters `(m, n)` of `U(2)` the relevant quadratic form is
`(2 b₀ (m − n)² + b₁ (m + n)²) / 8`. The translation from Lie theory to this quadratic numerator
is an input; nothing is stated about a complete supergravity spectrum.

## Main results

* `joint_criterion`: the form is integer-valued iff `2 b₀ + b₁ ≡ 0 (mod 8)`.
* `separate_sufficient`: `4 ∣ b₀` and `8 ∣ b₁` together are sufficient.
* `positive_joint`, `positive_not_separate`, `joint_does_not_imply_separate`: `(b₀, b₁) = (1, 6)`
  is integer-valued, with `(1 / 8)(2 (m − n)² + 6 (m + n)²) = m² + mn + n²`, but
  `4 ∤ b₀`; so the separate conditions are not necessary.
* `rational_joint_criterion`, `two_samples_suffice`: with rational coefficients `b₀ = p/t`,
  `b₁ = q/t`, integrality is decided by the two samples `(1, 0)` and `(1, 1)`.

## References

* S. Monnier, G. W. Moore, D. S. Park, *Quantization of anomaly coefficients in 6D
  `𝒩 = (1, 0)` supergravity*, JHEP 02 (2018) 020, arXiv:1711.04777, §3.
-/

@[expose] public section

namespace AnomalyQuantization.U2Example

/-- The numerator `2 b₀ (m − n)² + b₁ (m + n)²`. -/
def numerator (b0 b1 m n : Int) : Int :=
  2 * b0 * (m - n)^2 + b1 * (m + n)^2

/-- The quadratic form is integer-valued. -/
def jointIntegral (b0 b1 : Int) : Prop :=
  ∀ m n : Int, ∃ k : Int, numerator b0 b1 m n = 8 * k

/-- The separate conditions `4 ∣ b₀`, `8 ∣ b₁`. -/
def separateIntegral (b0 b1 : Int) : Prop :=
  (∃ k : Int, b0 = 4 * k) ∧ (∃ k : Int, b1 = 8 * k)

/-- For `(b₀, b₁) = (1, 6)` the form is `m² + mn + n²`. -/
theorem positive_identity (m n : Int) :
    numerator 1 6 m n = 8 * (m*m + m*n + n*n) := by
  unfold numerator
  grind

/-- `(1, 6)` is integer-valued. -/
theorem positive_joint : jointIntegral 1 6 := by
  intro m n
  exact ⟨m*m + m*n + n*n, positive_identity m n⟩

/-- `(1, 6)` does not satisfy the separate conditions. -/
theorem positive_not_separate : ¬ separateIntegral 1 6 := by
  intro ⟨⟨k, hk⟩, _⟩
  omega

/-- The form is integer-valued iff `2 b₀ + b₁ ≡ 0 (mod 8)`. -/
theorem joint_criterion (b0 b1 : Int) :
    jointIntegral b0 b1 ↔ ∃ d : Int, 2*b0 + b1 = 8*d := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := h 1 0
    exact ⟨d, by simpa [numerator] using hd⟩
  · rintro ⟨d, hd⟩ m n
    refine ⟨d*(m*m+n*n) + (2*d-b0)*m*n, ?_⟩
    unfold numerator
    grind

/-- The separate conditions are sufficient. -/
theorem separate_sufficient (b0 b1 : Int) :
    separateIntegral b0 b1 → jointIntegral b0 b1 := by
  rintro ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
  apply (joint_criterion b0 b1).mpr
  exact ⟨k+l, by omega⟩

/-- The separate conditions are not necessary. -/
theorem joint_does_not_imply_separate :
    ¬ (∀ b0 b1 : Int, jointIntegral b0 b1 → separateIntegral b0 b1) := by
  intro h
  exact positive_not_separate (h 1 6 positive_joint)

/-- Rational coefficients `b₀ = p/t`, `b₁ = q/t` with a common denominator `t ≠ 0`: the form is
integer-valued iff `numerator p q m n ∈ 8 t ℤ`. (Valid also for `t = 0`, which does not encode
rationals.) -/
def scaledJoint (p q t : Int) : Prop :=
  ∀ m n : Int, ∃ k : Int, numerator p q m n = 8*t*k

/-- The criterion with rational coefficients. -/
theorem rational_joint_criterion (p q t : Int) :
    scaledJoint p q t ↔
      ∃ c d : Int, p = t*c ∧ 2*p+q = 8*t*d := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := h 1 0
    obtain ⟨e, he⟩ := h 1 1
    simp [numerator] at hd he
    refine ⟨4*d-e, d, ?_, ?_⟩
    · grind
    · grind
  · rintro ⟨c, d, hc, hd⟩ m n
    refine ⟨d*(m*m+n*n) + (2*d-c)*m*n, ?_⟩
    unfold numerator
    grind

/-- Two samples, at `(1, 0)` and `(1, 1)`, decide integrality in this family. -/
theorem two_samples_suffice (p q t : Int)
    (h10 : ∃ d : Int, numerator p q 1 0 = 8*t*d)
    (h11 : ∃ e : Int, numerator p q 1 1 = 8*t*e) :
    scaledJoint p q t := by
  obtain ⟨d, hd⟩ := h10
  obtain ⟨e, he⟩ := h11
  simp [numerator] at hd he
  apply (rational_joint_criterion p q t).mpr
  refine ⟨4*d-e, d, ?_, ?_⟩ <;> grind

end AnomalyQuantization.U2Example
