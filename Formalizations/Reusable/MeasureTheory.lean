/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.MeasureTheory.Torricelli

/-!
# Reusable layer: measure theory

A stable name for Torricelli's trumpet (Gabriel's horn). The theorem is proved by the two archive
theorems it re-exposes (no proof is copied).

## Main results

* `Formalizations.Reusable.torricelli_trumpet`: the solid of revolution of `y = 1/x`, `x ≥ 1`, has
  Lebesgue volume `π`, while its plane section has infinite area (archive:
  `Torricelli.volume_trumpet`, `Torricelli.volume_section_eq_top`).
-/

@[expose] public section

open MeasureTheory

namespace Formalizations.Reusable

/-- **Torricelli's trumpet** (Gabriel's horn). The solid `{(u, v, t) : t ≥ 1, √(u² + v²) ≤ 1/t}`
in `ℝ³` (the revolution of `y = 1/x`, `x ≥ 1`, about the axis) has Lebesgue volume `π`, while its
plane section `{(x, y) : x ≥ 1, |y| ≤ 1/x}` has infinite area. (The archive also proves that the
surface integrand is not integrable, i.e. the infinite surface area.)

* Archive: `Torricelli.volume_trumpet` and `Torricelli.volume_section_eq_top`
  (`Formalizations.MeasureTheory.Torricelli`, on the archive's Pappus–Guldin
  `volume_revolution`); no research paper.
* Classical reference: E. Torricelli, *Opera geometrica* (1644); P. Mancosu, *Philosophy of
  Mathematics and Mathematical Practice in the Seventeenth Century*, OUP 1999, ch. 5.
* Example: `torricelli_trumpet.1` is the volume `π`; `torricelli_trumpet.2` the infinite area. -/
theorem torricelli_trumpet :
    volume {q : (ℝ × ℝ) × ℝ | 1 ≤ q.2 ∧ Real.sqrt (q.1.1 ^ 2 + q.1.2 ^ 2) ≤ 1 / q.2}
        = ENNReal.ofReal Real.pi ∧
      volume {p : ℝ × ℝ | 1 ≤ p.1 ∧ |p.2| ≤ 1 / p.1} = ⊤ :=
  ⟨Torricelli.volume_trumpet, Torricelli.volume_section_eq_top⟩

end Formalizations.Reusable
