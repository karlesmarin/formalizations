/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.AlgebraicGeometry.PlaneCurve.Cotes

/-!
# Reusable layer: algebraic geometry

A stable name for Cotes' harmonic means theorem. The theorem is proved by the archive theorem it
re-exposes (no proof is copied).

## Main results

* `Formalizations.Reusable.cotes_harmonic_mean_polar`: the harmonic-mean point of the intersections
  of a line through `p` with a real plane curve lies on the polar line of `p` (archive:
  `Cotes.harmonic_mean_polar`).
-/

@[expose] public section

namespace Formalizations.Reusable

/-- **Cotes' harmonic means theorem.** Let `f ∈ ℝ[x, y]` define a plane curve, `p` a point with
`f(p) ≠ 0` and `v` a direction, and let `g(t) = f(p + t v)`. Suppose `g` splits over `ℝ` with
`d = deg g ≥ 1` roots `tᵢ` and `Σ 1/tᵢ ≠ 0`. Then the harmonic-mean point `p + t* v`,
`t* = d / Σ 1/tᵢ`, satisfies `∇f(p) · (t* v) = −d f(p)`: it lies on the polar line
`∇f(p) · (q − p) = −d f(p)` of `p`, which does not depend on the direction `v`.

* Archive: `Cotes.harmonic_mean_polar` (`Formalizations.AlgebraicGeometry.PlaneCurve.Cotes`,
  from Mathlib's logarithmic derivative of a split polynomial); no research paper.
* Classical reference: R. Cotes, *Harmonia Mensurarum*, Cambridge, 1722; C. Maclaurin,
  *De linearum geometricarum proprietatibus generalibus*, 1748.
* Example: for the unit circle `f = x² + y² − 1`, `p = 0` and any `v`, `g = |v|² t² − 1` splits
  with `Σ 1/tᵢ = 0`, so the hypothesis `hH` fails: the theorem says nothing about lines through the
  centre, as expected (the polar of the centre is the line at infinity). -/
theorem cotes_harmonic_mean_polar (f : MvPolynomial (Fin 2) ℝ) (p v : Fin 2 → ℝ)
    (hp : MvPolynomial.eval p f ≠ 0)
    (g : Polynomial ℝ)
    (hg : g = MvPolynomial.aeval (fun i => Polynomial.C (p i) + Polynomial.C (v i) * Polynomial.X) f)
    (hsplit : g.roots.card = g.natDegree) (hd : 1 ≤ g.natDegree)
    (hH : (g.roots.map (fun r => r⁻¹)).sum ≠ 0) :
    ∑ i, MvPolynomial.eval p (MvPolynomial.pderiv i f) *
        ((g.natDegree : ℝ) / (g.roots.map (fun r => r⁻¹)).sum * v i)
      = -(g.natDegree : ℝ) * MvPolynomial.eval p f :=
  Cotes.harmonic_mean_polar f p v hp g hg hsplit hd hH

end Formalizations.Reusable
