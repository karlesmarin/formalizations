/-
Author: Carles Marín (with Claude as AI assistant).

DGHAbsorb: pointwise-set lemmas behind the Dubrovin–Gräter–Hanke stratification
(Jakobs 2019, Def 1.1.4): iterated sums `sumPow`, distributivity of a set over an
n-term sum, absorption of a layer of inverses, and Hua's identity in a division ring.
-/
import Mathlib.Algebra.Ring.Pointwise.Set
import Mathlib.Algebra.Field.Basic

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

/-- (b) Left distributivity of pointwise product over pointwise sum
(this is Mathlib's `Set.mul_add_subset`). -/
theorem mul_add_subset' (X A B : Set R) : X * (A + B) ⊆ X * A + X * B :=
  Set.mul_add_subset X A B

/-- (b) `X * (D + ⋯ + D) ⊆ X*D + ⋯ + X*D`. -/
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

/-- `a⁻¹ + b⁻¹ = a⁻¹ (a + b) b⁻¹`. -/
lemma inv_add_inv_eq_left {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    a⁻¹ + b⁻¹ = a⁻¹ * (a + b) * b⁻¹ := by
  rw [mul_add, add_mul, inv_mul_cancel₀ ha, one_mul, mul_assoc, mul_inv_cancel₀ hb,
    mul_one, add_comm]

/-- `a⁻¹ + b⁻¹ = b⁻¹ (a + b) a⁻¹`. -/
lemma inv_add_inv_eq_right {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    a⁻¹ + b⁻¹ = b⁻¹ * (a + b) * a⁻¹ := by
  rw [mul_add, add_mul, mul_assoc, mul_inv_cancel₀ ha, mul_one, inv_mul_cancel₀ hb, one_mul, add_comm]

/-- (d) Hua's identity (noncommutative form). -/
theorem hua_identity {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) (_hab : a + b ≠ 0) :
    (a⁻¹ + b⁻¹)⁻¹ = b * (a + b)⁻¹ * a := by
  rw [inv_add_inv_eq_left ha hb, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv, mul_assoc]

/-- (d) Hua's identity, symmetric form. -/
theorem hua_identity' {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) (_hab : a + b ≠ 0) :
    (a⁻¹ + b⁻¹)⁻¹ = a * (a + b)⁻¹ * b := by
  rw [inv_add_inv_eq_right ha hb, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv, mul_assoc]

end DivisionRing

end DGH

#print axioms DGH.mul_sumPow_subset
#print axioms DGH.inv_mul_subset_inv
#print axioms DGH.inv_mul_sumPow_subset
#print axioms DGH.hua_identity
#print axioms DGH.hua_identity'
