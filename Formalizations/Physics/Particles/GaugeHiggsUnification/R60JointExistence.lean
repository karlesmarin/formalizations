/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

/-!
# The localized tadpole never obstructs an anomaly-free completion of `(3, 60)`

In the six-dimensional `SU(4)` gauge-Higgs unification model with the colour-fundamental block
`(3, 60)`, each species of added matter contributes an integer `10`-vector
`[108 · (eight anomaly coefficients), Θ₀₁, Θ₂₃]`; the anomalies are scaled by their common
denominator `108`. The species data are inputs (computed with SageMath).

The file exhibits four anomaly-neutral non-negative additions (sums of species) that realize the
four signed tadpole axes `±Θ₀₁`, `±Θ₂₃`: a Farkas certificate that `0` is interior to the
achievable tadpole cone. Two of their tadpoles are linearly independent, so `Θ` has rank `2` on
the anomaly kernel and no linear invariant of `Θ` is conserved. Everything is decided by the
kernel with `decide`; the file uses no Mathlib.

## Main results

* `existence_certificate`: the four additions are anomaly-neutral, have tadpoles `(288, 0)`,
  `(−288, 0)`, `(0, 48)`, `(0, −16)`, and `288 · 48 − 0 · 0 ≠ 0`.

## References

* C. Marín, *Anomaly- and Tadpole-Compatible Fermion Completion of Six-Dimensional `SU(4)`
  Gauge-Higgs Unification*, Zenodo, doi:10.5281/zenodo.21432625.
-/

@[expose] public section

namespace GaugeHiggsUnification.R60JointExistence

/-- A species vector, of length `10`: `[a₀, …, a₇, Θ₀₁, Θ₂₃]`. -/
abbrev Vec := List Int

/-- Componentwise sum. -/
def add (u v : Vec) : Vec := List.zipWith (· + ·) u v

/-- Sum of a list of vectors. -/
def sumv (l : List Vec) : Vec := l.foldl add (List.replicate 10 (0 : Int))

-- the twelve species making up the four cone witnesses (108 · anomalies | tadpole)
def s86  : Vec := [-3780, -88128, -11340,  648, -288,  108, -21828, -1728, 144,  0]
def s87  : Vec := [ 3780,  88128,  11340, -648,  288, -108,  21828,  1728, 144,  0]
def s82  : Vec := [-3780, -88128, -11340, -324,  288, 1188,  11028,  1728,-144,  0]
def s83  : Vec := [ 3780,  88128,  11340,  324, -288,-1188, -11028, -1728,-144,  0]
def s129 : Vec := [ 2160,  -3564,   6480,  108, -126, -621,  -2253,  -756, -54, 12]
def s133 : Vec := [ 2160,  -3564,   6480, -108,   90,  378,    366,   540,  54, 12]
def s234 : Vec := [-2160,   3564,  -6480,  108,  -90, -378,   -366,  -540,  54, 12]
def s238 : Vec := [-2160,   3564,  -6480, -108,  126,  621,   2253,   756, -54, 12]
def s122 : Vec := [    0,   1188,  -2160,    0,    0,  126,    122,   180, -18, -4]
def s127 : Vec := [    0,  -1188,   2160,    0,    0,  207,    751,   252,  18, -4]
def s216 : Vec := [    0,   1188,  -2160,    0,    0, -207,   -751,  -252,  18, -4]
def s221 : Vec := [    0,  -1188,   2160,    0,    0, -126,   -122,  -180, -18, -4]

/-- Witness for `+Θ₀₁`. -/
def wP01 : Vec := sumv [s86, s87]
/-- Witness for `−Θ₀₁`. -/
def wM01 : Vec := sumv [s82, s83]
/-- Witness for `+Θ₂₃`. -/
def wP23 : Vec := sumv [s129, s133, s234, s238]
/-- Witness for `−Θ₂₃`. -/
def wM23 : Vec := sumv [s122, s127, s216, s221]

/-- All eight anomalies cancel. -/
def anomZero (v : Vec) : Bool := (v.take 8).all (· == 0)

/-- The tadpole `(Θ₀₁, Θ₂₃)`. -/
def tad (v : Vec) : Int × Int := (v.getD 8 0, v.getD 9 0)

/-- **Existence certificate.** The four additions are anomaly-neutral and realize the four
signed tadpole axes; two of their tadpoles, `(288, 0)` and `(0, 48)`, have non-zero
determinant. -/
theorem existence_certificate :
    (anomZero wP01 = true ∧ anomZero wM01 = true ∧
     anomZero wP23 = true ∧ anomZero wM23 = true)
  ∧ (tad wP01 = (288, 0)  ∧ tad wM01 = (-288, 0) ∧
     tad wP23 = (0, 48)   ∧ tad wM23 = (0, -16))
  ∧ ((288 : Int) * 48 - 0 * 0 ≠ 0) := by decide

end GaugeHiggsUnification.R60JointExistence
