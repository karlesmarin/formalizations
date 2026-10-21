/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.RingTheory.FreeField.ThreeAxes.ArrowMatrix
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# The witnesses of the paper as corners of arrow matrices

Each witness inverse of the paper is minus the border corner of the inverse of an arrow matrix
`[[diag d, ω], [α, 0]]` (`ArrowMatrix`), with entries in a division ring `D`:

* `s⁻¹`, `s = u⁻² + v⁻² + w⁻²` (Theorem 5.1): `d = (u², v², w²)`, `α = ω = 1`;
* `f_k⁻¹`, `f_k = u⁻² + w⁻² + Σ_{i=1}^{m} yⁱ u⁻² y⁻ⁱ`, `k = m + 2` (Theorems 7.1, 7.3);
* `e_d = q_d⁻¹`, `q_d = w⁻¹ + Σ_{i=0}^{d-1} yⁱ u⁻¹ y⁻ⁱ` (Corollary 7.10(a));
* `φ_r⁻¹`, `φ_r = Σ_τ α_τ ℓ_{τ,1}⁻¹ ⋯ ℓ_{τ,r}⁻¹ ω_τ` (equation (5.1), Remark 8.2), with
  `d_τ = ℓ_{τ,r} ⋯ ℓ_{τ,1}`; for the five chains of (5.1) the arrow matrix is `6 × 6`.

## Main results

* `inv_eq_neg_corner`: if `x = Σ α d⁻¹ ω ≠ 0`, the arrow matrix is a unit and
  `x⁻¹ = −(arrowInv d α ω) (inr ()) (inr ())`.
* `s_inv_eq_neg_corner`, `f_inv_eq_neg_corner`, `e_inv_eq_neg_corner`, `phi_inv_eq_neg_corner`:
  the four instances.

The statements hold in any division ring; in the paper `D` is the free field, where the
nonvanishing hypotheses are true.
-/

@[expose] public section

namespace ThreeAxes.ArrowInstances

open Matrix ArrowMatrix

variable {D : Type*} [DivisionRing D]

/-- `x⁻¹` is minus the border corner of the inverse of the arrow matrix, which is a unit. -/
theorem inv_eq_neg_corner {ι : Type*} [Fintype ι] [DecidableEq ι] (d α ω : ι → D)
    (hd : ∀ τ, d τ ≠ 0) (hx : arrowSum d α ω ≠ 0) :
    IsUnit (arrow d α ω) ∧ (arrowSum d α ω)⁻¹ = -arrowInv d α ω (Sum.inr ()) (Sum.inr ()) :=
  ⟨arrow_isUnit d α ω hd hx, by rw [arrowInv_corner, neg_neg]⟩

/-! ### `s = u⁻² + v⁻² + w⁻²` -/

theorem arrowSum_s (u v w : D) :
    arrowSum ![u ^ 2, v ^ 2, w ^ 2] 1 1 = (u ^ 2)⁻¹ + (v ^ 2)⁻¹ + (w ^ 2)⁻¹ := by
  simp [arrowSum, Fin.sum_univ_three]

theorem s_inv_eq_neg_corner (u v w : D) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (hs : (u ^ 2)⁻¹ + (v ^ 2)⁻¹ + (w ^ 2)⁻¹ ≠ 0) :
    IsUnit (arrow ![u ^ 2, v ^ 2, w ^ 2] 1 1) ∧
      ((u ^ 2)⁻¹ + (v ^ 2)⁻¹ + (w ^ 2)⁻¹)⁻¹ =
        -arrowInv ![u ^ 2, v ^ 2, w ^ 2] 1 1 (Sum.inr ()) (Sum.inr ()) := by
  rw [← arrowSum_s] at hs ⊢
  refine inv_eq_neg_corner _ _ _ (fun τ => ?_) hs
  fin_cases τ <;> simp [hu, hv, hw]

/-! ### `f_k = u⁻² + w⁻² + Σ_{i=1}^{m} yⁱ u⁻² y⁻ⁱ` -/

/-- Diagonal of the arrow matrix of `f_k`: `u², w²`, then `m` copies of `u²`. -/
def fDiag (u w : D) (m : ℕ) : Fin 2 ⊕ Fin m → D := Sum.elim ![u ^ 2, w ^ 2] fun _ => u ^ 2

/-- Left border: `1, 1, y, …, y^m`. -/
def fLeft (y : D) (m : ℕ) : Fin 2 ⊕ Fin m → D := Sum.elim 1 fun i => y ^ (i.val + 1)

/-- Right border: `1, 1, y⁻¹, …, y⁻ᵐ`. -/
def fRight (y : D) (m : ℕ) : Fin 2 ⊕ Fin m → D := Sum.elim 1 fun i => (y ^ (i.val + 1))⁻¹

theorem arrowSum_f (u w y : D) (m : ℕ) :
    arrowSum (fDiag u w m) (fLeft y m) (fRight y m) =
      (u ^ 2)⁻¹ + (w ^ 2)⁻¹ + ∑ i : Fin m, y ^ (i.val + 1) * (u ^ 2)⁻¹ * (y ^ (i.val + 1))⁻¹ := by
  simp [arrowSum, fDiag, fLeft, fRight, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem f_inv_eq_neg_corner (u w y : D) (m : ℕ) (hu : u ≠ 0) (hw : w ≠ 0)
    (hf : (u ^ 2)⁻¹ + (w ^ 2)⁻¹ +
      ∑ i : Fin m, y ^ (i.val + 1) * (u ^ 2)⁻¹ * (y ^ (i.val + 1))⁻¹ ≠ 0) :
    IsUnit (arrow (fDiag u w m) (fLeft y m) (fRight y m)) ∧
      ((u ^ 2)⁻¹ + (w ^ 2)⁻¹ +
        ∑ i : Fin m, y ^ (i.val + 1) * (u ^ 2)⁻¹ * (y ^ (i.val + 1))⁻¹)⁻¹ =
        -arrowInv (fDiag u w m) (fLeft y m) (fRight y m) (Sum.inr ()) (Sum.inr ()) := by
  rw [← arrowSum_f] at hf ⊢
  refine inv_eq_neg_corner _ _ _ (fun τ => ?_) hf
  rcases τ with τ | τ
  · fin_cases τ <;> simp [fDiag, hu, hw]
  · simp [fDiag, hu]

/-! ### `q_d = w⁻¹ + Σ_{i=0}^{d-1} yⁱ u⁻¹ y⁻ⁱ` -/

/-- Diagonal of the arrow matrix of `q_d`: `w`, then `d` copies of `u`. -/
def qDiag (u w : D) (d : ℕ) : Option (Fin d) → D := fun τ => τ.elim w fun _ => u

/-- Left border: `1, 1, y, …, y^{d-1}`. -/
def qLeft (y : D) (d : ℕ) : Option (Fin d) → D := fun τ => τ.elim 1 fun i => y ^ i.val

/-- Right border: `1, 1, y⁻¹, …, y^{-(d-1)}`. -/
def qRight (y : D) (d : ℕ) : Option (Fin d) → D := fun τ => τ.elim 1 fun i => (y ^ i.val)⁻¹

theorem arrowSum_q (u w y : D) (d : ℕ) :
    arrowSum (qDiag u w d) (qLeft y d) (qRight y d) =
      w⁻¹ + ∑ i : Fin d, y ^ i.val * u⁻¹ * (y ^ i.val)⁻¹ := by
  simp [arrowSum, qDiag, qLeft, qRight, Fintype.sum_option]

theorem e_inv_eq_neg_corner (u w y : D) (d : ℕ) (hu : u ≠ 0) (hw : w ≠ 0)
    (hq : w⁻¹ + ∑ i : Fin d, y ^ i.val * u⁻¹ * (y ^ i.val)⁻¹ ≠ 0) :
    IsUnit (arrow (qDiag u w d) (qLeft y d) (qRight y d)) ∧
      (w⁻¹ + ∑ i : Fin d, y ^ i.val * u⁻¹ * (y ^ i.val)⁻¹)⁻¹ =
        -arrowInv (qDiag u w d) (qLeft y d) (qRight y d) (Sum.inr ()) (Sum.inr ()) := by
  rw [← arrowSum_q] at hq ⊢
  refine inv_eq_neg_corner _ _ _ (fun τ => ?_) hq
  rcases τ with _ | τ <;> simp [qDiag, hu, hw]

/-! ### `φ_r = Σ_τ α_τ ℓ_{τ,1}⁻¹ ⋯ ℓ_{τ,r}⁻¹ ω_τ` -/

/-- `d_τ = ℓ_{τ,r} ⋯ ℓ_{τ,1}`, so that `d_τ⁻¹ = ℓ_{τ,1}⁻¹ ⋯ ℓ_{τ,r}⁻¹`. -/
def chainDiag {ι : Type*} {r : ℕ} (ℓ : ι → Fin r → D) : ι → D :=
  fun τ => (List.ofFn (ℓ τ)).reverse.prod

/-- `(a_n ⋯ a_1)⁻¹ = a_1⁻¹ ⋯ a_n⁻¹` in a division ring (`List.prod_inv_reverse` is for groups). -/
theorem prod_reverse_inv (L : List D) : L.reverse.prod⁻¹ = (L.map (·⁻¹)).prod := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.prod_append, mul_inv_rev, ih]

theorem chainDiag_inv {ι : Type*} {r : ℕ} (ℓ : ι → Fin r → D) (τ : ι) :
    (chainDiag ℓ τ)⁻¹ = (List.ofFn fun j => (ℓ τ j)⁻¹).prod := by
  rw [chainDiag, prod_reverse_inv, List.map_ofFn]
  rfl

theorem arrowSum_phi {ι : Type*} [Fintype ι] {r : ℕ} (ℓ : ι → Fin r → D) (α ω : ι → D) :
    arrowSum (chainDiag ℓ) α ω = ∑ τ, α τ * (List.ofFn fun j => (ℓ τ j)⁻¹).prod * ω τ := by
  simp only [arrowSum, chainDiag_inv]

theorem phi_inv_eq_neg_corner {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (ℓ : ι → Fin r → D) (α ω : ι → D) (hℓ : ∀ τ j, ℓ τ j ≠ 0)
    (hφ : ∑ τ, α τ * (List.ofFn fun j => (ℓ τ j)⁻¹).prod * ω τ ≠ 0) :
    IsUnit (arrow (chainDiag ℓ) α ω) ∧
      (∑ τ, α τ * (List.ofFn fun j => (ℓ τ j)⁻¹).prod * ω τ)⁻¹ =
        -arrowInv (chainDiag ℓ) α ω (Sum.inr ()) (Sum.inr ()) := by
  rw [← arrowSum_phi] at hφ ⊢
  refine inv_eq_neg_corner _ _ _ (fun τ => ?_) hφ
  refine List.prod_ne_zero fun h => ?_
  obtain ⟨j, hj⟩ := List.mem_ofFn.1 (List.mem_reverse.1 h)
  exact hℓ τ j hj

end ThreeAxes.ArrowInstances
