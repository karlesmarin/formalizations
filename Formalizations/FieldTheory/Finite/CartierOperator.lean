/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Tactic.Ring

/-!
# Iterating `X d/dX` over `ZMod p`

Over `ZMod p`, the operator `D = X · d/dX` acts on `X^m` as multiplication by `m`. Iterating it
`p − 1` times kills exactly the monomials whose exponent is divisible by `p` and fixes the others
(Fermat's little theorem): `D^[p−1]` is the identity minus the projection onto the `p`-divisible
exponents, the kernel of the Cartier operator.

## Main results

* `ConjeturaC.D_iter_X_pow`: `D^[k] (X^m) = C (m^k) * X^m`.
* `ConjeturaC.D_iter_card_sub_one`: `D^[p−1] (X^m) = if p ∣ m then 0 else X^m`.
* `ConjeturaC.D_iter_cartier`: `D^[p−1] f = f − ∑_{m ∈ supp f, p ∣ m} C (f.coeff m) * X^m`.
-/

@[expose] public section

open Polynomial Finset

namespace ConjeturaC

variable {p : ℕ} [hp : Fact p.Prime]

/-- The Euler operator `D f = X * f'` on `(ZMod p)[X]`. -/
noncomputable def D (p : ℕ) (f : Polynomial (ZMod p)) : Polynomial (ZMod p) := X * derivative f

/-- `D` as a linear endomorphism. -/
noncomputable def Dlin (p : ℕ) : Module.End (ZMod p) (Polynomial (ZMod p)) :=
  LinearMap.mulLeft (ZMod p) (X : Polynomial (ZMod p)) ∘ₗ derivative

omit hp in
theorem D_iter_eq (k : ℕ) : (D p)^[k] = ⇑(Dlin p ^ k) := by
  rw [Module.End.coe_pow]; rfl

theorem D_C_mul_X_pow (a : ZMod p) (m : ℕ) :
    D p (C a * X ^ m) = C (a * (m : ZMod p)) * X ^ m := by
  unfold D
  rw [derivative_C_mul_X_pow]
  rcases m with _ | m
  · simp
  · rw [Nat.add_sub_cancel, pow_succ]; ring

theorem D_iter_C_mul_X_pow (a : ZMod p) (k m : ℕ) :
    (D p)^[k] (C a * X ^ m) = C (a * (m : ZMod p) ^ k) * X ^ m := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, D_C_mul_X_pow, ih, pow_succ]; ring_nf

/-- (a) -/
theorem D_iter_X_pow (k m : ℕ) :
    (D p)^[k] (X ^ m) = C ((m : ZMod p) ^ k) * X ^ m := by
  simpa using D_iter_C_mul_X_pow (p := p) 1 k m

theorem pow_card_sub_one_natCast (m : ℕ) :
    (m : ZMod p) ^ (p - 1) = if p ∣ m then 0 else 1 := by
  simp only [ZMod.pow_card_sub_one, ne_eq, ZMod.natCast_eq_zero_iff, ite_not]

/-- (b) -/
theorem D_iter_card_sub_one (m : ℕ) :
    (D p)^[p - 1] (X ^ m) = if p ∣ m then 0 else X ^ m := by
  rw [D_iter_X_pow, pow_card_sub_one_natCast]
  split_ifs <;> simp

/-- (c) -/
theorem D_iter_cartier (f : Polynomial (ZMod p)) :
    (D p)^[p - 1] f =
      f - ∑ m ∈ f.support with p ∣ m, C (f.coeff m) * X ^ m := by
  conv_lhs => rw [f.as_sum_support_C_mul_X_pow]
  conv_rhs => arg 1; rw [f.as_sum_support_C_mul_X_pow]
  rw [D_iter_eq, map_sum, ← D_iter_eq]
  simp_rw [D_iter_C_mul_X_pow, pow_card_sub_one_natCast]
  rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs <;> simp

end ConjeturaC
