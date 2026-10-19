/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.Ring

/-!
# Reality of a scalar CP source

A small algebraic control: if the quartic coefficient `λ` and both Higgs-wall backgrounds
`v₁, v₂` are real, the imaginary part of the relative-phase scalar source
`λ (conj v₁ · v₂)²` vanishes. It says nothing about CP violation in the full six-dimensional
`SU(4)` model, which also depends on its fermion and boundary sectors; it is the scalar-sector
statement only.

## Main results

* `real_scalar_wall_source_vanishes`: `Im (λ (conj v₁ · v₂)²) = 0` for real `λ, v₁, v₂`.
* `real_scalar_wall_source_with_prefactor_vanishes`: the same after multiplication by any real
  radial prefactor.
-/

@[expose] public section

namespace GaugeHiggsUnification.ScalarCPSource

open ComplexConjugate

/-- If the quartic coefficient and both Higgs-wall backgrounds are real, the imaginary part of
the relative-phase scalar source vanishes. -/
theorem real_scalar_wall_source_vanishes (lambda v₁ v₂ : ℝ) :
    Complex.im ((lambda : ℂ) * ((conj (v₁ : ℂ) * (v₂ : ℂ)) ^ 2)) = 0 := by
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_im]

/-- The same conclusion after multiplication by any real radial prefactor. -/
theorem real_scalar_wall_source_with_prefactor_vanishes (prefactor lambda v₁ v₂ : ℝ) :
    prefactor * Complex.im ((lambda : ℂ) * ((conj (v₁ : ℂ) * (v₂ : ℂ)) ^ 2)) = 0 := by
  rw [real_scalar_wall_source_vanishes]
  ring

end GaugeHiggsUnification.ScalarCPSource
