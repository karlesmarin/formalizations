/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Basic

/-!
# The `x₆` parity of `SU(7)` gauge components separates colour

In the `SU(7)` gauge-Higgs unification model of Komori–Maru the parity acting in `x₆` is
`P₆ = diag(+,+,+,−,−,−,−)`: the first three indices of the fundamental are the colour triplet.
A gauge component along `E_ij` carries the product `P₆(i) P₆(j)`. This file proves the
arithmetic half of the theorem "colour lives on the small circle": `P₆(i) P₆(j) = −1` iff exactly
one of `i, j` is a colour index, and there are exactly `24` such components. The other half (the
`P₆`-odd components expand in `sin (m x₆ / R₆)`, `m ≥ 1`) is a reading of the mode expansions of
Komori–Maru and is not formalized.

## Main results

* `colourParity_neg_iff`: `P₆ i * P₆ j = −1 ↔ (IsColour i ↔ ¬ IsColour j)`.
* `colourChanging_card`: exactly `24` ordered index pairs `(i, j)` have `P₆ i * P₆ j = −1`.
* `colourChanging_parity_neg`: no colour-changing component has `P₆ = +1`.

## References

* C. Marín, *An Upper Bound on the Compactification Scale of `SU(7)` Grand Gauge-Higgs Unification,
  and the Dijet Angular Distribution That Tests It (Part VII)*, Zenodo, doi:10.5281/zenodo.22087252,
  eq. (colourparity) and Theorem (colour lives on the small circle).
* Y. Komori, N. Maru, *`SU(7)` grand gauge-Higgs unification*, arXiv:2503.04090, eq. (11).
-/

@[expose] public section

namespace GaugeHiggsUnification.SU7ColourParity

/-- The colour block: the first three indices of the fundamental `7`. -/
def IsColour (i : Fin 7) : Prop := i.val < 3

instance : DecidablePred IsColour := fun i => inferInstanceAs (Decidable (i.val < 3))

/-- The `x₆` parity `P₆ = diag(+,+,+,−,−,−,−)` on the indices of the fundamental. -/
def P6 (i : Fin 7) : ℤ := if IsColour i then 1 else -1

/-- `P₆(i) P₆(j) = −1` exactly when one and only one index is a colour index. -/
theorem colourParity_neg_iff (i j : Fin 7) :
    P6 i * P6 j = -1 ↔ (IsColour i ↔ ¬ IsColour j) := by
  revert i j
  decide

/-- There are exactly `24` gauge components `E_ij` with `P₆(i) P₆(j) = −1`. -/
theorem colourChanging_card :
    (Finset.univ.filter fun p : Fin 7 × Fin 7 => P6 p.1 * P6 p.2 = -1).card = 24 := by
  decide

/-- No colour-changing component carries `P₆ = +1`. -/
theorem colourChanging_parity_neg (i j : Fin 7) (h : IsColour i ↔ ¬ IsColour j) :
    P6 i * P6 j = -1 :=
  (colourParity_neg_iff i j).2 h

end GaugeHiggsUnification.SU7ColourParity
