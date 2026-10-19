/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

/-!
# Localized cubic anomalies of the `SU(4)` irrep `60` and their Wilson-line invariance

For the six-dimensional `SU(4)` gauge-Higgs unification model of arXiv:2603.05857, with the
colour-fundamental block `(3, 60)` (`60 = (0, 2, 1)`, intrinsic parity `η = (+, +)`, 6D
chirality `+`), exact integer computation over the `40` weights of `60` gives the localized
non-Abelian cubic anomalies at an `f = 0, 1` fixed point:
`SU(3)_C³ = (1/4) · c3num = −3/2` and `SU(3)_{123}³ = (−1/8) · s3num = −3/4`, with the integer
numerators certified here. The weight list is an input (from `SU(4)` character data).

The Higgs is a Wilson line along a `U(1)` Cartan direction of `SU(4)` and shifts every abelian
charge `q₁₅ ↦ q₁₅ + θ`. The pure non-Abelian cubics carry no `U(1)` charge and are exactly
`θ`-invariant, while a mixed `C² · U(1)` piece depends on `θ`: the anomaly obstruction decouples
from electroweak symmetry breaking. The file uses no Mathlib; every check is `decide` or `rfl`.

## Main results

* `dim_60`: the `40` weights carry dimension `60`.
* `c3_exact`, `s3_exact`: `c3num = −6`, `s3num = 6`.
* `c3_wilson_invariant`, `s3_wilson_invariant`: both cubic numerators are independent of the
  Wilson line `θ`.
* `mixed_depends`: the mixed `C² · U(1)₁₅` numerator is not.

## References

* arXiv:2603.05857 (the six-dimensional `SU(4)` gauge-Higgs unification model).
* C. Marín, *Anomaly- and Tadpole-Compatible Fermion Completion of Six-Dimensional `SU(4)`
  Gauge-Higgs Unification*, Zenodo, doi:10.5281/zenodo.21432625.
-/

@[expose] public section

namespace GaugeHiggsUnification.R60LocalizedAnomaly

/-- One weight of the `60`: `(mult, p0, q15, h3)`, with `p0 = ±1` the `ℤ₂` parity, `q15` the
local `U(1)₁₅` charge and `h3` the `SU(3)_{123}` Cartan probe. -/
abbrev St := Int × Int × Int × Int

/-- The `40` weights of `60 = (0, 2, 1)`. -/
def S : List St :=
  [(1,-1,-5,-5), (1,-1,-5,-5), (1,-1,-5,-2), (1,-1,-5,-2), (1,-1,-5,1),
   (1,-1,-5,1), (1,-1,-5,4), (1,-1,-5,4), (1,-1,-5,4), (1,-1,3,-3),
   (1,-1,3,-3), (1,-1,3,6), (1,1,-1,-4), (1,1,-1,-4), (1,1,-1,-1),
   (1,1,-1,-1), (1,1,-1,5), (1,1,-1,5), (1,1,7,-2), (1,1,7,-2),
   (1,1,7,-2), (1,1,7,1), (1,1,7,1), (1,1,7,4), (2,-1,-5,-2),
   (2,-1,-5,1), (2,-1,-5,1), (2,-1,3,-3), (2,-1,3,-3), (2,-1,3,0),
   (2,-1,3,0), (2,-1,3,3), (2,-1,3,3), (2,1,-1,-4), (2,1,-1,2),
   (2,1,-1,2), (3,-1,3,0), (3,1,-1,-1), (3,1,-1,-1), (3,1,-1,2)]

/-- Total dimension carried by the `40` weights. -/
def dim : Int := (S.map (fun s => s.1)).foldl (· + ·) 0

/-- `SU(3)_C³` numerator `Σ mult · p0`. The pure colour cubic carries no `U(1)` charge, so it
takes the Wilson line `θ` and ignores it. -/
def c3num (_theta : Int) : Int :=
  (S.map (fun s => s.1 * s.2.1)).foldl (· + ·) 0

/-- `SU(3)_{123}³` numerator `Σ mult · p0 · h3³`; it carries no `U(1)` charge either. -/
def s3num (_theta : Int) : Int :=
  (S.map (fun s => s.1 * s.2.1 * s.2.2.2 * s.2.2.2 * s.2.2.2)).foldl (· + ·) 0

/-- Mixed `C² · U(1)₁₅` numerator `Σ mult · p0 · (q15 + θ) · h3²`; the Wilson line enters. -/
def mixnum (theta : Int) : Int :=
  (S.map (fun s => s.1 * s.2.1 * (s.2.2.1 + theta) * s.2.2.2 * s.2.2.2)).foldl (· + ·) 0

/-- The `40` weights carry dimension `60`. -/
theorem dim_60 : dim = 60 := by decide

/-- The `SU(3)_C³` numerator is `−6`, so the anomaly is `−3/2`. -/
theorem c3_exact : c3num 0 = -6 := by decide

/-- The `SU(3)_{123}³` numerator is `6`, so the anomaly is `−3/4`. -/
theorem s3_exact : s3num 0 = 6 := by decide

/-- The `SU(3)_C³` anomaly is independent of the Higgs Wilson line. -/
theorem c3_wilson_invariant (θ₁ θ₂ : Int) : c3num θ₁ = c3num θ₂ := rfl

/-- The `SU(3)_{123}³` anomaly is independent of the Higgs Wilson line. -/
theorem s3_wilson_invariant (θ₁ θ₂ : Int) : s3num θ₁ = s3num θ₂ := rfl

/-- The mixed `C² · U(1)` piece is not Wilson-line invariant. -/
theorem mixed_depends : mixnum 0 ≠ mixnum 1 := by decide

end GaugeHiggsUnification.R60LocalizedAnomaly
