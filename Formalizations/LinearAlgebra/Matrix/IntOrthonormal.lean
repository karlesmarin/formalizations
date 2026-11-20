/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Tactic.Linarith

/-!
# Integer vectors of norm one and integer orthonormal columns

An integer vector v with v·v = 1 is ±e_i for some i. Consequently the columns of an integer m × n
matrix A with AᵀA = I are signed standard basis vectors with their nonzero entries in distinct rows.
This is the first step of Theorem 8.1 (integer lengths) of the paper on rational sums-of-squares
lengths of biquadratic forms, and of the sign-independence of integer lengths of signed graphs.

## Main results

* `IntOrthonormal.eq_single_of_dotProduct_self_eq_one`: v : m → ℤ, v ⬝ᵥ v = 1 ⇒ v = ±Pi.single i 1
* `IntOrthonormal.columns_of_transpose_mul_self`: Aᵀ A = 1 over ℤ ⇒ columns ±e_{f j} with f injective

## References

* Mathlib: Matrix.dotProduct, Finset.sum_eq_zero_iff_of_nonneg, Finset.add_sum_erase, sq_nonneg, Int.isUnit_iff, Int.eq_one_or_neg_one_of_mul_eq_one, Pi.single, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply.
* Nuestro repo: nada equivalente (existe-ya 21-nov, Mathlib 0 candidatos). Mathlib tiene Matrix.UnitaryGroup / signed permutation matrices sin esta caracterización de columnas enteras.
-/

@[expose] public section

namespace IntOrthonormal

open Matrix

variable {m n : Type*} [Fintype m] [DecidableEq m]

theorem eq_single_of_dotProduct_self_eq_one {v : m → ℤ} (hv : v ⬝ᵥ v = 1) :
    ∃ i, v = Pi.single i 1 ∨ v = Pi.single i (-1) := by
  have hex : ∃ i, v i ≠ 0 := by
    by_contra h
    have h' : ∀ i, v i = 0 := fun i => by
      by_contra hh
      exact h ⟨i, hh⟩
    have h0 : v ⬝ᵥ v = 0 := by simp [dotProduct, h']
    rw [h0] at hv
    exact absurd hv (by decide)
  obtain ⟨i, hi⟩ := hex
  have h1 : v i * v i + ∑ k ∈ Finset.univ.erase i, v k * v k = 1 := by
    exact (Finset.add_sum_erase Finset.univ (fun k => v k * v k) (Finset.mem_univ i)).trans hv
  have hpos : 0 < v i * v i := mul_self_pos.mpr hi
  have hrest : 0 ≤ ∑ k ∈ Finset.univ.erase i, v k * v k :=
    Finset.sum_nonneg (fun k _ => mul_self_nonneg (v k))
  have hrest0 : ∑ k ∈ Finset.univ.erase i, v k * v k = 0 := by linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ => mul_self_nonneg (v k))).1 hrest0
  have hvi : v i * v i = 1 := by linarith
  refine ⟨i, ?_⟩
  rcases mul_self_eq_one_iff.1 hvi with h | h
  · left
    funext k
    by_cases hk : k = i
    · subst hk; simp [h]
    · have := mul_self_eq_zero.1 (hz k (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩))
      simp [hk, this]
  · right
    funext k
    by_cases hk : k = i
    · subst hk; simp [h]
    · have := mul_self_eq_zero.1 (hz k (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩))
      simp [hk, this]

theorem columns_of_transpose_mul_self [Fintype n] [DecidableEq n] {A : Matrix m n ℤ}
    (hA : Aᵀ * A = 1) :
    ∃ f : n → m, Function.Injective f ∧
      ∀ j, (fun i => A i j) = Pi.single (f j) 1 ∨ (fun i => A i j) = Pi.single (f j) (-1) := by
  have hcol : ∀ j, (fun i => A i j) ⬝ᵥ (fun i => A i j) = 1 := by
    intro j
    have := congrFun (congrFun hA j) j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, dotProduct] using this
  choose f hf using fun j => eq_single_of_dotProduct_self_eq_one (hcol j)
  refine ⟨f, ?_, hf⟩
  intro j k hjk
  by_contra hne
  have h := congrFun (congrFun hA j) k
  rw [Matrix.one_apply_ne hne] at h
  simp only [Matrix.mul_apply, Matrix.transpose_apply] at h
  have key : ∀ (a b : ℤ), (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) → a * b ≠ 0 := by
    intro a b ha hb; rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide
  have hsum : ∑ i, A i j * A i k = A (f j) j * A (f j) k := by
    rw [Finset.sum_eq_single (f j)]
    · intro i _ hi
      have hj : A i j = 0 := by
        rcases hf j with e | e <;> simp [congrFun e i, hi]
      simp [hj]
    · simp
  rw [hsum] at h
  apply key (A (f j) j) (A (f j) k) _ _ h.symm.symm
  · rcases hf j with e | e <;> simp [congrFun e (f j)]
  · rw [hjk]
    rcases hf k with e | e <;> simp [congrFun e (f k)]

end IntOrthonormal
