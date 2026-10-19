/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Tactic.Ring

/-!
# Integrality of quadratic forms on the cocharacters of `S(U(2) × U(3))`

Conditional arithmetic certificates for `H = S(U(2) × U(3))`. A cocharacter of `H` is
`(m, n; u, v, −m − n − u − v)`, and `A = mn`, `B` (the second elementary symmetric function of
the `U(3)` entries) and `C = (m + n)²` are the three invariant quadratic forms on it. The
dictionary between cocharacters and characteristic classes and the Green–Schwarz ansatz are
inputs, not formalized.

## Main results

* `integral_basis_criterion`: `p A + q B + r C` takes values in `t ℤ` on all cocharacters iff
  `t ∣ p`, `t ∣ q`, `t ∣ r`.
* `quotient_witness`, `cover_witness`, `cover_misses_fraction`: `C` takes the value `1`, while
  `C / 36` is not integral.
* `no_standard_tensor_parent_match`, `residue_mod_three`: the transfer coefficients
  `(16 − 3p, −3q, −3r)` never satisfy the parent relation `x + y + 2z = 0`; their combination is
  `1` modulo `3`.
-/

@[expose] public section

namespace GaugeHiggsUnification.ChargeQuantization

/-- The form `A = mn`. -/
def A (m n : Int) : Int := m*n

/-- The form `B`, the second elementary symmetric function of `(u, v, −m − n − u − v)`. -/
def B (m n u v : Int) : Int := u*v + u*(-m-n-u-v) + v*(-m-n-u-v)

/-- The form `C = (m + n)²`. -/
def C (m n : Int) : Int := (m+n)^2

/-- The combination `p A + q B + r C`. -/
def form (p q r m n u v : Int) : Int := p*A m n + q*B m n u v + r*C m n

/-- `p A + q B + r C` takes values in `t ℤ` on every cocharacter. -/
def integralOnH (p q r t : Int) : Prop :=
  ∀ m n u v : Int, ∃ k : Int, form p q r m n u v = t*k

/-- The integral basis criterion. -/
theorem integral_basis_criterion (p q r t : Int) :
    integralOnH p q r t ↔
      ∃ a b c : Int, p=t*a ∧ q=t*b ∧ r=t*c := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := h 1 (-1) 0 0
    obtain ⟨b, hb⟩ := h 0 0 1 (-1)
    obtain ⟨c, hc⟩ := h 1 0 (-1) 0
    simp [form, A, B, C] at ha hb hc
    refine ⟨-a, -b, c, ?_, ?_, ?_⟩ <;> grind
  · rintro ⟨a,b,c,hp,hq,hr⟩ m n u v
    refine ⟨a*A m n + b*B m n u v + c*C m n, ?_⟩
    unfold form
    grind

/-- `C` takes the value `1`. -/
theorem quotient_witness : form 0 0 1 1 0 (-1) 0 = 1 := by decide

/-- A value `36` of `C`. -/
theorem cover_witness : form 0 0 1 (-3) (-3) 2 2 = 36 := by decide

/-- `C` does not take values in `36 ℤ`. -/
theorem cover_misses_fraction :
    ¬ integralOnH 0 0 1 36 := by
  intro h
  obtain ⟨k,hk⟩ := h 1 0 (-1) 0
  simp [form,A,B,C] at hk
  omega

/-- The parent relation `x + y + 2z = 0` annihilates `(−2s, −2t, s + t)`. -/
theorem parent_annihilator (s t : Int) :
    (-2*s) + (-2*t) + 2*(s+t) = 0 := by omega

/-- With integer doubled tensor coefficients `p, q, r`, six times the transfer coefficients are
`(16 − 3p, −3q, −3r)`; they never satisfy the parent relation. -/
theorem standard_tensor_obstruction (p q r : Int) :
    (16-3*p) + (-3*q) + 2*(-3*r) ≠ 0 := by omega

/-- No integer tensor coefficients match the parent relation. -/
theorem no_standard_tensor_parent_match :
    ¬ (∃ p q r : Int, (16-3*p) + (-3*q) + 2*(-3*r) = 0) := by
  rintro ⟨p,q,r,h⟩
  exact standard_tensor_obstruction p q r h

/-- The obstruction is the residue `1` modulo `3`. -/
theorem residue_mod_three (p q r : Int) :
    ((16-3*p) + (-3*q) + 2*(-3*r)) % 3 = 1 := by omega

end GaugeHiggsUnification.ChargeQuantization
