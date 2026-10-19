/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# The 11- and 12-point Higgs self-couplings coincide at the top edge

In the cubic field redefinition `h → h + α P(h)` of Alasfar et al., the Standard Model potential
in the old field has degree `12` in `h`. At this top edge the 11- and 12-point contributions,
with the normalization `Nₙ = n! / 3!` (so `N₁₁ = 6652800`, `N₁₂ = 79833600`), coincide, and the
12-point one has the closed form `246400 α⁴ / (1 + α)²`. These are algebraic identities in `ℝ`;
the tree-level reparametrization is the hypothesis, not derived here.

## Main results

* `bhr_top_edge_collapse`: the normalized 11- and 12-point top-edge contributions are equal.
* `bhr_top_edge_closed_form`: the 12-point coefficient equals `246400 α⁴ / (1 + α)²`.

## Related

`SMEFT.AllOrdersSelfCouplings.dk11_eq_dk12` states the same coincidence for the all-orders
closed forms.

## References

* L. Alasfar et al., arXiv:2304.01968 (field redefinition).
-/

@[expose] public section

namespace SMEFT.TopEdgeCollapse

/-- At the degree-12 edge of the cubic reparametrization the normalized 11- and 12-point
contributions coincide; `massSq` is an arbitrary common normalization. -/
theorem bhr_top_edge_collapse (prefactor v massSq top : ℝ) :
    6652800 * (prefactor * (4 * (3 * v * top) * top ^ 3)) * (2 * v ^ 9) / massSq =
      79833600 * (prefactor * top ^ 4) * (2 * v ^ 10) / massSq := by
  ring

/-- The 12-point coefficient produced by the cubic top term is `246400 α⁴ / (1 + α)²`. -/
theorem bhr_top_edge_closed_form (alpha v massSq : ℝ) (hv : v ≠ 0) (hmassSq : massSq ≠ 0) :
    79833600 * (massSq / (8 * v ^ 2)) * (alpha / (3 * v ^ 2)) ^ 4 *
          (2 * v ^ 10) / (massSq * (1 + alpha) ^ 2) =
      246400 * alpha ^ 4 / (1 + alpha) ^ 2 := by
  field_simp [hv, hmassSq]
  ring

end SMEFT.TopEdgeCollapse
