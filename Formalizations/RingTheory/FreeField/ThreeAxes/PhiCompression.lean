/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.RingTheory.FreeField.ThreeAxes.InverseIdentities

/-!
# Compression of `φ_r` over a division ring

For `d : ι → K` with every `d i ≠ 0`, `α ω : ι → K` and `d₂ ≠ 0`, `w`, let
`φ = Σ_i α_i d_i⁻¹ ω_i + w d₂⁻¹` (in the paper `φ_r = Σ_τ α_τ d_τ⁻¹ ω_τ + α₂ d₂⁻¹ ω₂` with
`ω₂ = 1`, `α₂ = w`). Over an arbitrary division ring `K` (no commutativity):

## Main results

* `fromBlocks_schur_mul`, `fromBlocks_schur_mul'`: two-sided block inverse of
  `fromBlocks A B C (S + C A⁻¹ B)` from two-sided inverses of the pivot `A` and of the Schur
  complement `S`, over any ring.
* `phiMatrix`, `phiMatrixInv` (Remark 8.2): `M = [[diag d, −ω d₂], [α, w]]` and its explicit
  inverse; the Schur complement of `diag d` is `φ d₂` (`phiMatrix_schur`).
  `phiMatrix_mul_inv`, `phiMatrixInv_mul`: both products are `1`; `phiMatrix_isUnit`;
  `phi_inv_eq_corner`: `φ⁻¹ = d₂ (M⁻¹)_{∞∞}`.
* `phi_inv_woodbury` (Remark 8.2, second compression): for `S = diag d + ω (d₂ w⁻¹) α` and a right
  inverse `T` of `S`, `φ⁻¹ = c − c (α T ω) c` with `c = d₂ w⁻¹`.
* `inv_mul_conj` (Corollary 7.10(c)): `m₀ ℓ⁻¹ m₁ = (m₀ ℓ m₀⁻¹)⁻¹ (m₀ m₁)`.
* `harmonic_compression_inv` (Remark 7.11(iii)): the case `r = 0` of
  `InverseIdentities.compression_inv`.

Matrix inverses are given explicitly and checked on both sides; `Matrix.inv` needs a commutative
ring.

## Related

Over a commutative ring the block inverse is Mathlib's `Matrix.invOf_fromBlocks₁₁_eq` (with
`Invertible` instances), and `phi_inv_woodbury` is a scalar reading of the Woodbury identity
`Matrix.invOf_add_mul_mul'` (over a ring, with `Invertible` instances).
-/

@[expose] public section

namespace ThreeAxes.PhiCompression

open Matrix

/-! ### Two-sided block inverse with pivot in the upper-left block -/

section Block

variable {R : Type*} [Ring R] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-- Block inverse of `fromBlocks A B C (S + C A⁻¹ B)`, right product, over any ring. -/
theorem fromBlocks_schur_mul (A Ai : Matrix m m R) (B : Matrix m n R) (C : Matrix n m R)
    (S Si : Matrix n n R) (hA : A * Ai = 1) (hS : S * Si = 1) :
    fromBlocks A B C (S + C * Ai * B) *
        fromBlocks (Ai + Ai * B * Si * C * Ai) (-(Ai * B * Si)) (-(Si * C * Ai)) Si = 1 := by
  rw [fromBlocks_multiply, ← fromBlocks_one]
  congr 1 <;>
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_neg, Matrix.mul_assoc] <;>
    simp only [← Matrix.mul_assoc A Ai, ← Matrix.mul_assoc S Si, hA, hS, Matrix.one_mul] <;> abel

/-- Block inverse of `fromBlocks A B C (S + C A⁻¹ B)`, left product, over any ring. -/
theorem fromBlocks_schur_mul' (A Ai : Matrix m m R) (B : Matrix m n R) (C : Matrix n m R)
    (S Si : Matrix n n R) (hA : Ai * A = 1) (hS : Si * S = 1) :
    fromBlocks (Ai + Ai * B * Si * C * Ai) (-(Ai * B * Si)) (-(Si * C * Ai)) Si *
        fromBlocks A B C (S + C * Ai * B) = 1 := by
  rw [fromBlocks_multiply, ← fromBlocks_one]
  congr 1 <;>
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_assoc] <;>
    simp only [hA, hS, Matrix.mul_one] <;> abel

end Block

variable {K : Type*} [DivisionRing K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Remark 8.2: first compression -/

/-- `φ = Σ_i α_i d_i⁻¹ ω_i + w d₂⁻¹`. -/
def phi (d α ω : ι → K) (d₂ w : K) : K := (∑ i, α i * (d i)⁻¹ * ω i) + w * d₂⁻¹

/-- `M = [[diag d, −ω d₂], [α, w]]`, border indexed by `Unit` (Remark 8.2). -/
def phiMatrix (d α ω : ι → K) (d₂ w : K) : Matrix (ι ⊕ Unit) (ι ⊕ Unit) K :=
  fromBlocks (diagonal d) (of fun i _ => -(ω i * d₂)) (of fun _ j => α j) (of fun _ _ => w)

/-- The explicit inverse of `phiMatrix`: block inverse through the Schur complement `φ d₂` of
`diag d`. -/
noncomputable def phiMatrixInv (d α ω : ι → K) (d₂ w : K) : Matrix (ι ⊕ Unit) (ι ⊕ Unit) K :=
  let Ai : Matrix ι ι K := diagonal fun i => (d i)⁻¹
  let B : Matrix ι Unit K := of fun i _ => -(ω i * d₂)
  let C : Matrix Unit ι K := of fun _ j => α j
  let Si : Matrix Unit Unit K := of fun _ _ => (phi d α ω d₂ w * d₂)⁻¹
  fromBlocks (Ai + Ai * B * Si * C * Ai) (-(Ai * B * Si)) (-(Si * C * Ai)) Si

/-- The Schur complement of `diag d` in `phiMatrix` is `φ d₂`. -/
theorem phiMatrix_schur (d α ω : ι → K) (d₂ w : K) (h₂ : d₂ ≠ 0) :
    (of fun _ _ => w : Matrix Unit Unit K) =
      (of fun _ _ => phi d α ω d₂ w * d₂) +
        (of fun _ j => α j : Matrix Unit ι K) * diagonal (fun i => (d i)⁻¹) *
          (of fun i _ => -(ω i * d₂) : Matrix ι Unit K) := by
  ext i j
  simp only [add_apply, of_apply, Matrix.mul_apply, diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, phi]
  simp only [mul_neg, Finset.sum_neg_distrib, add_mul, Finset.sum_mul, mul_assoc,
    inv_mul_cancel₀ h₂, mul_one]
  abel

theorem diagonal_mul_diagonal_inv (d : ι → K) (hd : ∀ i, d i ≠ 0) :
    diagonal d * diagonal (fun i => (d i)⁻¹) = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  exact congrArg diagonal (funext fun i => mul_inv_cancel₀ (hd i))

theorem diagonal_inv_mul_diagonal (d : ι → K) (hd : ∀ i, d i ≠ 0) :
    diagonal (fun i => (d i)⁻¹) * diagonal d = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  exact congrArg diagonal (funext fun i => inv_mul_cancel₀ (hd i))

theorem phiMatrix_mul_inv (d α ω : ι → K) (d₂ w : K) (hd : ∀ i, d i ≠ 0) (h₂ : d₂ ≠ 0)
    (hφ : phi d α ω d₂ w ≠ 0) : phiMatrix d α ω d₂ w * phiMatrixInv d α ω d₂ w = 1 := by
  rw [phiMatrix, phiMatrixInv, phiMatrix_schur d α ω d₂ w h₂]
  refine fromBlocks_schur_mul _ _ _ _ _ _ (diagonal_mul_diagonal_inv d hd) ?_
  ext i j
  simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton, of_apply,
    Matrix.one_apply_eq]
  exact mul_inv_cancel₀ (mul_ne_zero hφ h₂)

theorem phiMatrixInv_mul (d α ω : ι → K) (d₂ w : K) (hd : ∀ i, d i ≠ 0) (h₂ : d₂ ≠ 0)
    (hφ : phi d α ω d₂ w ≠ 0) : phiMatrixInv d α ω d₂ w * phiMatrix d α ω d₂ w = 1 := by
  rw [phiMatrix, phiMatrixInv, phiMatrix_schur d α ω d₂ w h₂]
  refine fromBlocks_schur_mul' _ _ _ _ _ _ (diagonal_inv_mul_diagonal d hd) ?_
  ext i j
  simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton, of_apply,
    Matrix.one_apply_eq]
  exact inv_mul_cancel₀ (mul_ne_zero hφ h₂)

theorem phiMatrix_isUnit (d α ω : ι → K) (d₂ w : K) (hd : ∀ i, d i ≠ 0) (h₂ : d₂ ≠ 0)
    (hφ : phi d α ω d₂ w ≠ 0) : IsUnit (phiMatrix d α ω d₂ w) :=
  ⟨⟨_, _, phiMatrix_mul_inv d α ω d₂ w hd h₂ hφ, phiMatrixInv_mul d α ω d₂ w hd h₂ hφ⟩, rfl⟩

/-- The border corner of `phiMatrixInv` is `d₂⁻¹ φ⁻¹`. -/
theorem phiMatrixInv_corner (d α ω : ι → K) (d₂ w : K) :
    phiMatrixInv d α ω d₂ w (Sum.inr ()) (Sum.inr ()) = d₂⁻¹ * (phi d α ω d₂ w)⁻¹ := by
  simp [phiMatrixInv, mul_inv_rev]

/-- **Remark 8.2.** If `φ = Σ_i α_i d_i⁻¹ ω_i + w d₂⁻¹ ≠ 0`, then `M = [[diag d, −ω d₂], [α, w]]`
has a two-sided inverse `N`, and `φ⁻¹ = d₂ N_{∞∞}`. -/
theorem phi_inv_eq_corner (d α ω : ι → K) (d₂ w : K) (hd : ∀ i, d i ≠ 0) (h₂ : d₂ ≠ 0)
    (hφ : phi d α ω d₂ w ≠ 0) :
    ∃ N : Matrix (ι ⊕ Unit) (ι ⊕ Unit) K, phiMatrix d α ω d₂ w * N = 1 ∧
      N * phiMatrix d α ω d₂ w = 1 ∧ N (Sum.inr ()) (Sum.inr ()) = d₂⁻¹ * (phi d α ω d₂ w)⁻¹ ∧
      (phi d α ω d₂ w)⁻¹ = d₂ * N (Sum.inr ()) (Sum.inr ()) := by
  refine ⟨phiMatrixInv d α ω d₂ w, phiMatrix_mul_inv d α ω d₂ w hd h₂ hφ,
    phiMatrixInv_mul d α ω d₂ w hd h₂ hφ, phiMatrixInv_corner d α ω d₂ w, ?_⟩
  rw [phiMatrixInv_corner, mul_inv_cancel_left₀ h₂]

/-! ### Remark 8.2: second compression (Woodbury) -/

/-- **Remark 8.2, second compression.** With `c = d₂ w⁻¹` and
`S = diag d + ω c α` (`S_ij = d_i δ_ij + ω_i d₂ w⁻¹ α_j`), if `S T = 1` then
`φ⁻¹ = c − c (Σ_{i,j} α_i T_ij ω_j) c`. No hypothesis `φ ≠ 0` is needed: it follows from
`S T = 1`. -/
theorem phi_inv_woodbury (d α ω : ι → K) (d₂ w : K) (hd : ∀ i, d i ≠ 0) (h₂ : d₂ ≠ 0)
    (hw : w ≠ 0) (T : Matrix ι ι K)
    (hST : (diagonal d + of fun i j => ω i * d₂ * w⁻¹ * α j) * T = 1) :
    (phi d α ω d₂ w)⁻¹ =
      d₂ * w⁻¹ - d₂ * w⁻¹ * (∑ i, ∑ j, α i * T i j * ω j) * d₂ * w⁻¹ := by
  set c := d₂ * w⁻¹ with hc
  set x := ∑ i, ∑ j, α i * T i j * ω j with hx
  set y := ∑ i, α i * (d i)⁻¹ * ω i with hy
  set z : ι → K := fun j => ∑ k, α k * T k j with hz
  -- entries of `S T = 1`: `d_i T_ij + ω_i c z_j = δ_ij`
  have hT : ∀ i j, T i j = (d i)⁻¹ * (1 : Matrix ι ι K) i j - (d i)⁻¹ * ω i * c * z j := by
    intro i j
    have h := congrFun (congrFun hST i) j
    simp only [Matrix.mul_apply, add_apply, of_apply] at h
    have h' : d i * T i j + ω i * c * z j = (1 : Matrix ι ι K) i j := by
      rw [← h, hz, hc]
      simp only [add_mul, Finset.sum_add_distrib, diagonal_apply, ite_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.mul_sum, mul_assoc]
    rw [← h', mul_add, ← mul_assoc, inv_mul_cancel₀ (hd i), one_mul]
    simp only [mul_assoc]
    abel
  -- `x = y − y c x`
  have hzx : ∑ j, z j * ω j = x := by
    rw [hx, hz]
    simp only [Finset.sum_mul]
    exact Finset.sum_comm
  have hxy : x = y - y * c * x := by
    conv_lhs => rw [hx]
    simp only [hT, mul_sub, sub_mul, Finset.sum_sub_distrib, Matrix.one_apply, mul_ite, mul_one,
      mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [hy, ← hzx]
    simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    congr 1
    exact Finset.sum_comm
  have hφ : phi d α ω d₂ w = y + c⁻¹ := by
    rw [phi, hc, mul_inv_rev, inv_inv]
  have hcc : c⁻¹ * c = 1 := inv_mul_cancel₀ (mul_ne_zero h₂ (inv_ne_zero hw))
  have hcxc : c * x * d₂ * w⁻¹ = c * x * c := by
    rw [hc]
    simp only [mul_assoc]
  rw [hφ, hcxc]
  refine inv_eq_of_mul_eq_one_right ?_
  -- `(y + c⁻¹)(c − c x c) = (y − y c x − x) c + 1 = 1` by `x = y − y c x`
  have e : (y + c⁻¹) * (c - c * x * c) = (y - y * c * x - x) * c + 1 := by
    simp only [add_mul, mul_sub, sub_mul, mul_assoc, ← mul_assoc c⁻¹ c, hcc, one_mul]
    abel
  rw [e, ← hxy, sub_self, zero_mul, zero_add]

/-! ### Corollary 7.10(c) -/

/-- **Corollary 7.10(c).** `m₀ ℓ⁻¹ m₁ = (m₀ ℓ m₀⁻¹)⁻¹ (m₀ m₁)` for `m₀ ≠ 0`. -/
theorem inv_mul_conj (m₀ ℓ m₁ : K) (h₀ : m₀ ≠ 0) :
    m₀ * ℓ⁻¹ * m₁ = (m₀ * ℓ * m₀⁻¹)⁻¹ * (m₀ * m₁) := by
  rw [mul_inv_rev, mul_inv_rev, inv_inv]
  simp only [mul_assoc, inv_mul_cancel_left₀ h₀]

/-! ### Remark 7.11(iii): the harmonic case `r = 0` -/

omit [Fintype ι] in
theorem compressionMatrix_zero (d₁ d₂ : K) (d : ι → K) :
    InverseIdentities.compressionMatrix d₁ d₂ 0 d =
      fromBlocks (of fun _ _ => d₁ + d₂) (of fun _ _ => d₁) (of fun _ _ => -d₂) (diagonal d) := by
  simp [InverseIdentities.compressionMatrix]

/-- **Remark 7.11(iii).** The case `r = 0` of `InverseIdentities.compression_inv`:
`(d₁⁻¹ + d₂⁻¹ + Σ dᵢ⁻¹)⁻¹ = d₂ (M⁻¹)₁₁ d₁` for `M = [[d₁ + d₂, d₁ 𝟙ᵀ], [−𝟙 d₂, diag d]]`
(`compressionMatrix_zero`). -/
theorem harmonic_compression_inv (d₁ d₂ : K) (d : ι → K) (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0)
    (hd : ∀ i, d i ≠ 0) (hf : d₁⁻¹ + d₂⁻¹ + ∑ i, (d i)⁻¹ ≠ 0)
    [Invertible (InverseIdentities.compressionMatrix d₁ d₂ 0 d)] :
    d₂ * (⅟(InverseIdentities.compressionMatrix d₁ d₂ 0 d)) (Sum.inl 0) (Sum.inl 0) * d₁ =
      (d₁⁻¹ + d₂⁻¹ + ∑ i, (d i)⁻¹)⁻¹ := by
  have h := InverseIdentities.compression_inv d₁ d₂ 0 d h₁ h₂ hd (by rwa [add_zero])
  rwa [add_zero] at h

end ThreeAxes.PhiCompression
