/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.Geometry.Projective.Pappus
public import Formalizations.Geometry.Euclidean.WolstenholmeInequality

/-!
# Reusable layer: geometry

Stable names for two classical geometry results of the archive. Each theorem is proved by the
archive theorem it re-exposes (no proof is copied), so the provenance is the archive module.

## Main results

* `Formalizations.Reusable.pappus_hexagon`: Pappus's hexagon theorem in homogeneous coordinates
  over any commutative ring (archive: `Pappus.pappus`).
* `Formalizations.Reusable.wolstenholme_defect_eq_sq_add_sq`: the defect of Wolstenholme's
  triangle inequality is a sum of two squares (archive: `WolstenholmeInequality.sub_eq_sq_add_sq`).
-/

@[expose] public section

open Matrix

namespace Formalizations.Reusable

/-- **Pappus's hexagon theorem** (homogeneous coordinates, any commutative ring).

Points of the projective plane are vectors of `R³`; three points are collinear when their triple
product `A ⬝ᵥ (B ⨯₃ C)` vanishes, and the meet of the lines `PQ` and `RS` is
`(P ⨯₃ Q) ⨯₃ (R ⨯₃ S)`. If `A, B, C` are collinear and `a, b, c` are collinear, then the three meets
`Ab ∩ aB`, `Ac ∩ aC`, `Bc ∩ bC` are collinear. No non-degeneracy hypothesis is needed: the
conclusion is an ideal-membership identity.

* Archive: `Pappus.pappus` (`Formalizations.Geometry.Projective.Pappus`); no research paper.
* Classical reference: Pappus of Alexandria, *Collection*, Book VII (c. 320 AD); R. Whitty,
  Theorem of the Day, «Pappus' Theorem».
* Example: over `ℤ`, from `h₁ : A ⬝ᵥ (B ⨯₃ C) = 0` and `h₂ : a ⬝ᵥ (b ⨯₃ c) = 0`,
  `pappus_hexagon A B C a b c h₁ h₂` gives the collinearity of the three meets. -/
theorem pappus_hexagon {R : Type*} [CommRing R] (A B C a b c : Fin 3 → R)
    (h₁ : A ⬝ᵥ (B ⨯₃ C) = 0) (h₂ : a ⬝ᵥ (b ⨯₃ c) = 0) :
    ((A ⨯₃ b) ⨯₃ (a ⨯₃ B)) ⬝ᵥ (((A ⨯₃ c) ⨯₃ (a ⨯₃ C)) ⨯₃ ((B ⨯₃ c) ⨯₃ (b ⨯₃ C))) = 0 :=
  Pappus.pappus A B C a b c h₁ h₂

/-- **Wolstenholme's inequality, defect form.** If `A + B + C = π` then for all real `x, y, z`,
`x² + y² + z² − (2yz cos A + 2zx cos B + 2xy cos C) = (x − z cos B − y cos C)² + (z sin B − y sin C)²`.
In particular `2yz cos A + 2zx cos B + 2xy cos C ≤ x² + y² + z²` (Wolstenholme's inequality,
archive `WolstenholmeInequality.cos_le`). No sign condition on the angles is needed.

* Archive: `WolstenholmeInequality.sub_eq_sq_add_sq`
  (`Formalizations.Geometry.Euclidean.WolstenholmeInequality`); no research paper.
* Classical reference: J. Wolstenholme, *A Book of Mathematical Problems*, Macmillan, 1867.
* Example: `wolstenholme_defect_eq_sq_add_sq 1 1 1 (π/3) (π/3) (π/3) h` for the equilateral
  triangle, with `h : π/3 + π/3 + π/3 = π`. -/
theorem wolstenholme_defect_eq_sq_add_sq (x y z A B C : ℝ) (h : A + B + C = Real.pi) :
    x ^ 2 + y ^ 2 + z ^ 2 - (2 * y * z * Real.cos A + 2 * z * x * Real.cos B
        + 2 * x * y * Real.cos C) =
      (x - z * Real.cos B - y * Real.cos C) ^ 2 + (z * Real.sin B - y * Real.sin C) ^ 2 :=
  WolstenholmeInequality.sub_eq_sq_add_sq x y z A B C h

end Formalizations.Reusable
