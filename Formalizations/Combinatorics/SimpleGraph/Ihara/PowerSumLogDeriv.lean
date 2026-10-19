/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.Combinatorics.SimpleGraph.Ihara.PowerSumGenfun

/-!
# Power sums and the reversed logarithmic derivative

For a monic polynomial `q = ∏_{θ ∈ s} (X - θ)`, the generating function of the power sums of its
roots times the reversed polynomial `∏ (1 - θ X)` is the reverse of `q' = ∑_θ ∏_{φ ≠ θ} (X - φ)`.
The proof cancels one geometric series against one linear factor; no formal logarithm is used.

## Main results

* `PowerSeries.geomSeries_sum_mul_prod`:
  `(∑_θ geomSeries θ) · ∏_θ (1 - θ X) = ∑_θ ∏_{φ ∈ s.erase θ} (1 - φ X)`.
* `Polynomial.reverse_X_sub_C`: `reverse (X - C a) = 1 - C a * X`.
* `Polynomial.derivative_prod_X_sub_C`: `(∏ (X - θ))' = ∑_θ ∏_{φ ∈ s.erase θ} (X - φ)`.
* `Polynomial.reverse_prod_X_sub_C`: `reverse (∏ (X - θ)) = ∏ (1 - θ X)`.
-/

@[expose] public section

open PowerSeries

namespace PowerSeries

variable {R : Type*} [CommRing R] [DecidableEq R]

/-- **The geometric-series / reversed-product cancellation.**
Multiplying the multiset-sum of per-root geometric series `Σ_{θ∈s} geomSeries θ` by the reversed
factor product `∏_{θ∈s} (1 - θX)` collapses, root by root, to the sum of the "leave-one-out"
products:

  `(Σ_{θ∈s} geomSeries θ) · ∏_{θ∈s} (1 - θX)  =  Σ_{θ∈s} ∏_{φ∈s.erase θ} (1 - φX)`.

The whole product `∏_{θ}(1 - θX)` factors as `(1 - θX) · ∏_{erase θ}` (`Multiset.prod_map_erase`),
and `geomSeries θ · (1 - θX) = 1` (`geomSeries_mul_one_sub`) cancels the singled-out factor, leaving
`∏_{erase θ}`. No formal derivative is needed: the right-hand side is precisely `reverse_{n-1}[μ']`
(the reverse of `μ' = Σ_θ ∏_{φ≠θ}(X - φ)`), the numerator of the reversed logarithmic derivative. -/
theorem geomSeries_sum_mul_prod (s : Multiset R) :
    (s.map geomSeries).sum * (s.map (fun a => 1 - C a * X)).prod
      = (s.map fun a => ((s.erase a).map fun b => 1 - C b * X).prod).sum := by
  rw [← Multiset.sum_map_mul_right]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun a ha => ?_)
  rw [← Multiset.prod_map_erase (f := fun b => 1 - C b * X) ha, ← mul_assoc,
    geomSeries_mul_one_sub, one_mul]

end PowerSeries

namespace Polynomial

variable {R : Type*} [CommRing R]

@[simp] theorem reverse_one : reverse (1 : R[X]) = 1 := by rw [← C_1, reverse_C]

/-- **(B3) Reverse of a monic linear factor:** `reverse (X - a) = 1 - a·X`. The degree-1 reflection
swaps the constant `-a` and leading `1` coefficients. Used to identify the reversed factor product
`∏(1 - θX)` (right of `geomSeries_sum_mul_prod`) with `↑reverse(∏(X - θ))`. -/
theorem reverse_X_sub_C (a : R) : reverse (X - C a) = 1 - C a * X := by
  nontriviality R
  have hX : reverse (X : R[X]) = 1 := by rw [← one_mul (X : R[X]), reverse_mul_X, reverse_one]
  rw [sub_eq_add_neg, ← map_neg, reverse_add_C, hX, natDegree_X, pow_one, map_neg, neg_mul,
    ← sub_eq_add_neg]

end Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R] [DecidableEq R]

/-- **(B2) The product rule for a split polynomial — `μ' = Σ_θ ∏_{φ≠θ}(X - φ)`.** The derivative of
`∏_{θ∈s}(X - θ)` is the sum, over the multiset of roots, of the "leave-one-out" products
`∏_{φ∈s.erase θ}(X - φ)`. Immediate from `Polynomial.derivative_prod` (the multiset product rule)
with `derivative (X - C θ) = 1`. The numerator of the reversed logarithmic derivative
(`reverse_{n-1}[μ']`) is the degree-`(n-1)` reflection of this sum — and the reflection of a sum of
equal-degree terms is the sum of the reflections (`reflect` is additive at a fixed length), each
`reflect (X - φ) = 1 - φ·X`, matching the right-hand side of `geomSeries_sum_mul_prod`. -/
theorem derivative_prod_X_sub_C (s : Multiset R) :
    derivative ((s.map fun a => X - C a).prod)
      = (s.map fun a => ((s.erase a).map fun b => X - C b).prod).sum := by
  rw [derivative_prod]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun a _ => ?_)
  rw [derivative_X_sub_C, mul_one]

end Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R] [NoZeroDivisors R]

/-- **(B3) Reverse of a split product:** `reverse (∏_θ (X - θ)) = ∏_θ (1 - θX)`. Over a domain
`reverse` is multiplicative (`reverse_mul_of_domain`), so the reversal distributes over the product
of monic linear factors, each `reverse (X - θ) = 1 - θX`. This identifies the right-hand product of
`geomSeries_sum_mul_prod` with the coercion of `reverse μ` when `μ = ∏_θ (X - θ)` splits monic. -/
theorem reverse_prod_X_sub_C (s : Multiset R) :
    reverse ((s.map fun a => X - C a).prod) = (s.map fun a => 1 - C a * X).prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain, reverse_X_sub_C, ih,
      Multiset.map_cons, Multiset.prod_cons]

end Polynomial
