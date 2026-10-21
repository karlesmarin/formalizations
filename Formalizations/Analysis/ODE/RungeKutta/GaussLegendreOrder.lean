/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.Analysis.ODE.RungeKutta.OrderConditions

/-!
# Gauss–Legendre with three stages does not have order 7

The three-stage Gauss–Legendre method has order 6 (`Butcher.gauss_order6`) and not order 7. The
witness is the bushy tree with seven nodes (root with six leaves), whose order condition is the
quadrature condition `∑ bᵢ cᵢ⁶ = 1/7`; a three-node Gauss rule is exact only up to degree 5.

## Main results

* `Butcher.gauss_not_ord7`: the unscaled `ℚ(√15)` tableau fails the order condition on the bushy
  tree with seven nodes.
* `Butcher.gauss_not_order7`: hence `¬ satisfiesOrderConditions gauss_A gauss_b 7`.
* `Butcher.gaussI_not_ord7`, `Butcher.gaussI_exact_order6`: the same failure for the scaled integer
  tableau of `Butcher.gauss_order6`, and with it "order 6 and not 7" for that tableau.
* `Butcher.gaussI_all_ord7_fail`: every planar tree with exactly seven nodes fails the scaled
  integer condition (132 planar trees; the paper counts the 48 abstract ones).

## References

* E. Hairer, C. Lubich, G. Wanner, *Geometric Numerical Integration*, Springer (2006).
* C. Marín, *What Order a Method Knows: certified Runge–Kutta order conditions over rooted trees,
  machine-checked in Lean 4* (2026), doi:10.5281/zenodo.20787666, Section 6.
-/

@[expose] public section

namespace Butcher

/-- The bushy tree with seven nodes: a root with six leaves. `γ = 7`. -/
def t7bushy : RTree := .node [leaf, leaf, leaf, leaf, leaf, leaf]

example : order t7bushy = 7 ∧ gamma t7bushy = 7 := by decide

/-- Gauss–Legendre `s = 3` fails the order condition on the bushy seven-node tree. -/
theorem gauss_not_ord7 : ¬ orderCond gauss_A gauss_b t7bushy := by
  simp only [orderCond, Phi, phiVec, phiForest, dot, pmul, mulMatVec, gamma, gammaF,
    order, orderF, leaf, gauss_A, gauss_b, t7bushy, Q15.natCast_eq, List.map_cons,
    List.map_nil, List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons, List.sum_nil]
  intro h
  have h1 := congrArg Q15.re h
  simp only [Q15.mul_re, Q15.mul_im, Q15.add_re, Q15.add_im, Q15.one_re, Q15.zero_re,
    Q15.zero_im] at h1
  norm_num at h1

/-- Gauss–Legendre `s = 3` does not satisfy the order conditions of order 7. -/
theorem gauss_not_order7 : ¬ satisfiesOrderConditions gauss_A gauss_b 7 :=
  fun h => gauss_not_ord7 (h t7bushy (by decide))

/-- The scaled integer tableau fails the cleared order condition on the bushy seven-node tree. -/
theorem gaussI_not_ord7 : ¬ orderCondInt gaussI_A gaussI_b Dscale t7bushy := by decide

/-- The scaled integer Gauss–Legendre tableau satisfies the cleared conditions through order 6 and
not through order 7. -/
theorem gaussI_exact_order6 :
    satisfiesOrderConditionsInt gaussI_A gaussI_b Dscale 6 ∧
      ¬ satisfiesOrderConditionsInt gaussI_A gaussI_b Dscale 7 :=
  ⟨gauss_order6, fun h => gaussI_not_ord7 (h t7bushy (by decide))⟩

set_option maxHeartbeats 4000000 in
/-- Every planar tree with exactly seven nodes fails the cleared order condition. -/
theorem gaussI_all_ord7_fail :
    ∀ t ∈ catalog 7, order t = 7 → ¬ orderCondInt gaussI_A gaussI_b Dscale t := by
  intro t ht
  fin_cases ht <;> decide

end Butcher
