/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Algebra.Ring.Pointwise.Set
public import Mathlib.Algebra.Field.Basic

/-!
# Absorption lemmas for the DGH stratification

Pointwise-set lemmas behind the Dubrovin–Gräter–Hanke stratification (Jakobs 2019, Def. 1.1.4):
iterated sums `sumPow`, distributivity of a set over an `n`-term sum, absorption of a layer of
inverses, the inverse of a sum of two inverses, and Hua's identity in a division ring.

## Main results

* `mul_sumPow_subset`, `inv_mul_subset_inv`, `inv_mul_sumPow_subset`.
* `inv_add_inv_inv`, `inv_add_inv_inv'`: `(a⁻¹ + b⁻¹)⁻¹ = b (a + b)⁻¹ a = a (a + b)⁻¹ b`
  (the "parallel sum"; one line from Mathlib's `inv_add_inv'`).
* `hua_classical`: Hua's identity `a − (a⁻¹ + (b⁻¹ − a)⁻¹)⁻¹ = a b a`.

## Related

The binary distributivity step is Mathlib's `Set.mul_add_subset`; the identity
`a⁻¹ + b⁻¹ = a⁻¹ (a + b) b⁻¹` is Mathlib's `inv_add_inv'` (`invOf_add_invOf` for `Invertible`).

## References

* F. Jakobs, PhD thesis, 2019, Def. 1.1.4.
* L.-K. Hua, *On the automorphisms of a sfield*, Proc. Nat. Acad. Sci. USA 35 (1949), 386–389.
-/

@[expose] public section

open Pointwise

namespace DGH

section Ring
variable {R : Type*} [Ring R]

/-- (a) `sumPow n S = S + ⋯ + S` (n summands), `sumPow 0 S = {0}`. -/
def sumPow : ℕ → Set R → Set R
  | 0, _ => {0}
  | n + 1, S => S + sumPow n S

@[simp] lemma sumPow_zero (S : Set R) : sumPow 0 S = {0} := rfl
@[simp] lemma sumPow_succ (n : ℕ) (S : Set R) : sumPow (n + 1) S = S + sumPow n S := rfl

lemma sumPow_mono (n : ℕ) {S T : Set R} (h : S ⊆ T) : sumPow n S ⊆ sumPow n T := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact Set.add_subset_add h ih

/-- (b) `X * (D + ⋯ + D) ⊆ X*D + ⋯ + X*D` (iterating Mathlib's `Set.mul_add_subset`). -/
theorem mul_sumPow_subset (X D : Set R) (n : ℕ) : X * sumPow n D ⊆ sumPow n (X * D) := by
  induction n with
  | zero =>
    rintro _ ⟨x, _, z, hz, rfl⟩
    simp only [sumPow_zero, Set.mem_singleton_iff] at hz ⊢
    simp [hz]
  | succ n ih =>
    exact (Set.mul_add_subset _ _ _).trans (Set.add_subset_add le_rfl ih)

end Ring

section DivisionRing
variable {K : Type*} [DivisionRing K]

/-- (c) If `U⁻¹ * S ⊆ S` then `S⁻¹ * U ⊆ S⁻¹`. -/
theorem inv_mul_subset_inv {U S : Set K} (h : U⁻¹ * S ⊆ S) : S⁻¹ * U ⊆ S⁻¹ := by
  rintro _ ⟨x, hx, u, hu, rfl⟩
  rw [Set.mem_inv] at hx ⊢
  rw [mul_inv_rev]
  refine h ⟨u⁻¹, ?_, x⁻¹, hx, rfl⟩
  rw [Set.mem_inv, inv_inv]; exact hu

/-- (c) Corollary: a layer of inverses times an n-term polynomial in `U`
stays in an n-term sum of inverses. -/
theorem inv_mul_sumPow_subset {U S : Set K} (h : U⁻¹ * S ⊆ S) (n : ℕ) :
    S⁻¹ * sumPow n U ⊆ sumPow n S⁻¹ :=
  (mul_sumPow_subset _ _ n).trans (sumPow_mono n (inv_mul_subset_inv h))

/-- (d) The inverse of a sum of two inverses ("parallel sum"), noncommutative form:
`(a⁻¹ + b⁻¹)⁻¹ = b (a + b)⁻¹ a`. This is Mathlib's `inv_add_inv'` inverted with `mul_inv_rev`.
It is not Hua's identity (that is `hua_classical`). -/
theorem inv_add_inv_inv {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a⁻¹ + b⁻¹)⁻¹ = b * (a + b)⁻¹ * a := by
  rw [inv_add_inv' ha hb, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv, mul_assoc]

/-- (d) The inverse of a sum of two inverses, symmetric form: `(a⁻¹ + b⁻¹)⁻¹ = a (a + b)⁻¹ b`. -/
theorem inv_add_inv_inv' {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a⁻¹ + b⁻¹)⁻¹ = a * (a + b)⁻¹ * b := by
  rw [add_comm a⁻¹, add_comm a b]
  exact inv_add_inv_inv hb ha

@[deprecated inv_add_inv_inv (since := "2026-10-17")] alias hua_identity := inv_add_inv_inv
@[deprecated inv_add_inv_inv' (since := "2026-10-17")] alias hua_identity' := inv_add_inv_inv'

/-- **Hua's identity** in a division ring: if `a ≠ 0`, `b ≠ 0` and `a b ≠ 1`, then
`a − (a⁻¹ + (b⁻¹ − a)⁻¹)⁻¹ = a b a`. -/
theorem hua_classical {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a * b ≠ 1) :
    a - (a⁻¹ + (b⁻¹ - a)⁻¹)⁻¹ = a * b * a := by
  have hc : b⁻¹ - a ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    exact hab (by rw [← h, inv_mul_cancel₀ hb])
  rw [inv_add_inv_inv ha hc, add_sub_cancel, inv_inv, sub_mul, inv_mul_cancel₀ hb, sub_mul,
    one_mul, sub_sub_cancel]

end DivisionRing

end DGH
