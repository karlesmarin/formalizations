/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Invertible
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Abel

/-!
# Inverse identities of the three-axes problem over a division ring

Exact versions, over an arbitrary division ring `D` (no commutativity), of the inversion identities
of the three-axes problem that were only checked numerically.

## Main results

* `three_term_inv` (Part 1, proof of Cor. 5.3, "A16"):
  `(p⁻¹ + q⁻¹ + r)⁻¹ = q (p r q + p + q)⁻¹ p`; `one_term_inv`: `(d⁻¹ + r)⁻¹ = (1 + d r)⁻¹ d`.
* `schur_two`: the `2 × 2` block inverse with a pivot `a` and Schur complement `S`, over any ring.
* `harmonicMatrix`: `H a b c = !![a + b, a; a, a + c]`. With `s = a⁻¹ + b⁻¹ + c⁻¹ ≠ 0`:
  `harmonic_isUnit`; `woodbury_corner` (Part 1, (5.1)): `s⁻¹ = b − b (H⁻¹)₁₁ b`;
  `woodbury_sum` (Part 2, Lemma 6.1(1)): `s⁻¹ = a − (a a) H⁻¹ (a a)ᵀ`.
* `intermediate_inv` (Part 2, Lemma 6.2): for `M = !![d₃, d₂; −d₁, d₁ r d₂ + d₁ + d₂]`,
  `(d₁⁻¹ + d₂⁻¹ + d₃⁻¹ + r)⁻¹ = d₂ (M⁻¹)₂₂ d₁`.
* `fromBlocks_mul_schur`: block inverse of `fromBlocks A B C E` from right inverses of `E` and of
  the Schur complement `S = A − B E⁻¹ C`, over any ring.
* `compression_schur`, `compression_inv` (Part 2, Lemma 6.6): for
  `M = [[Y, d₁ 𝟙ᵀ], [−𝟙 d₂, diag d]]` with `Y = d₁ r d₂ + d₁ + d₂` and `f = d₁⁻¹ + d₂⁻¹ + Σ dᵢ⁻¹ + r`,
  the Schur complement of `diag d` is `d₁ f d₂` and `f⁻¹ = d₂ (M⁻¹)₁₁ d₁`.
* `chain_mul_inv`, `chain_inv_corner` (Part 1, Lemma 3.2): the upper bidiagonal chain `C` with
  `ℓ 0, …, ℓ q` on the diagonal and `−a 0, …, −a (q−1)` above it has the explicit inverse
  `chainInv`, and `(C⁻¹)_{0,q} = ℓ 0⁻¹ a 0 ℓ 1⁻¹ ⋯ a (q−1) ℓ q⁻¹` (`chainProd`), for every `q`.
* `cycleMatrix_inv` (Part 2, (2.1)/(2.2)): for the cyclic `d × d` matrix `F̂_d` with `p₁, …, p_d`
  on the diagonal, `c` on the superdiagonal and in position `(d, 1)`,
  `(F̂_d⁻¹)₁₁ = [p₁ + (−1)^{d−1} c p₂⁻¹ c ⋯ p_d⁻¹ c]⁻¹`, for every `d ≥ 2`; `cycle_inv` is the
  block form `F̂_d = [[p₁, c e₁ᵀ], [c e_{d−1}, T_d]]` with the explicit block inverse (2.2).

Matrix inverses are `⅟M` for an arbitrary `Invertible M` instance; existence is proved separately
(`IsUnit`), using that matrix rings over a division ring are Dedekind-finite.

## Related

* `three_term_eq` with `r = 0` is Mathlib's `inv_add_inv'` (`invOf_add_invOf` for `Invertible`).
* `woodbury_corner` and `woodbury_sum` are scalar readings of the Woodbury identity for the
  harmonic matrix `diag(b, c) + a 𝟙 𝟙ᵀ`. Mathlib has Woodbury for matrices over a `Ring` as
  `Matrix.invOf_add_mul_mul` (`⅟` version; the `⁻¹` version `Matrix.add_mul_mul_inv_eq_sub` is
  stated over a `CommRing`).
* `schur_two` and `fromBlocks_mul_schur` are noncommutative versions, with one-sided inverses, of
  Mathlib's block inverse through a Schur complement, `Matrix.fromBlocks₂₂Invertible` and
  `Matrix.invOf_fromBlocks₂₂_eq` (also `Matrix.fromBlocks₁₁Invertible`), which are stated over a
  `CommRing`.
-/

@[expose] public section

namespace ThreeAxes.InverseIdentities

open Matrix

variable {D : Type*} [DivisionRing D]

/-! ### Scalar identities -/

theorem three_term_eq (p q r : D) (hp : p ≠ 0) (hq : q ≠ 0) :
    p⁻¹ + q⁻¹ + r = p⁻¹ * (p * r * q + p + q) * q⁻¹ := by
  simp only [mul_add, add_mul, mul_assoc, inv_mul_cancel_left₀ hp, mul_inv_cancel₀ hq, mul_one,
    inv_mul_cancel₀ hp, one_mul]
  abel

/-- **A16.** `(p⁻¹ + q⁻¹ + r)⁻¹ = q (p r q + p + q)⁻¹ p` in a division ring. -/
theorem three_term_inv (p q r : D) (hp : p ≠ 0) (hq : q ≠ 0) :
    (p⁻¹ + q⁻¹ + r)⁻¹ = q * (p * r * q + p + q)⁻¹ * p := by
  rw [three_term_eq p q r hp hq, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv, ← mul_assoc]

theorem three_term_ne_zero_iff (p q r : D) (hp : p ≠ 0) (hq : q ≠ 0) :
    p⁻¹ + q⁻¹ + r ≠ 0 ↔ p * r * q + p + q ≠ 0 := by
  rw [three_term_eq p q r hp hq]
  simp [hp, hq]

/-- One pure summand: `(d⁻¹ + r)⁻¹ = (1 + d r)⁻¹ d`. -/
theorem one_term_inv (d r : D) (hd : d ≠ 0) : (d⁻¹ + r)⁻¹ = (1 + d * r)⁻¹ * d := by
  have h : d⁻¹ + r = d⁻¹ * (1 + d * r) := by
    rw [mul_add, mul_one, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]
  rw [h, mul_inv_rev, inv_inv]

/-! ### `2 × 2` Schur complement -/

/-- The `2 × 2` block inverse with pivot `a` and Schur complement `S`, over any ring. -/
theorem schur_two {R : Type*} [Ring R] (a b c S ai Si : R) (ha : a * ai = 1) (hS : S * Si = 1) :
    !![a, b; c, S + c * ai * b] *
        !![ai + ai * b * Si * c * ai, -(ai * b * Si); -(Si * c * ai), Si] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_add, add_mul, mul_assoc, ← mul_assoc a ai,
      ha, ← mul_assoc S Si, hS]

/-! ### The harmonic matrix and the Woodbury identity -/

/-- `H a b c = !![a + b, a; a, a + c] = diag(b, c) + a 𝟙 𝟙ᵀ`. -/
def harmonicMatrix (a b c : D) : Matrix (Fin 2) (Fin 2) D := !![a + b, a; a, a + c]

/-- An explicit inverse of `harmonicMatrix a b c`, through `H = !![1, 1; 0, 1] * K` with
`K = !![b, −c; a, a + c]`, whose Schur complement is `a s c`, `s = a⁻¹ + b⁻¹ + c⁻¹`. -/
noncomputable def harmonicInv (a b c : D) : Matrix (Fin 2) (Fin 2) D :=
  let S := a * (a⁻¹ + b⁻¹ + c⁻¹) * c
  !![b⁻¹ + b⁻¹ * (-c) * S⁻¹ * a * b⁻¹, -(b⁻¹ * (-c) * S⁻¹); -(S⁻¹ * a * b⁻¹), S⁻¹] *
    !![1, -1; 0, 1]

theorem harmonic_mul_inv (a b c : D) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hs : a⁻¹ + b⁻¹ + c⁻¹ ≠ 0) : harmonicMatrix a b c * harmonicInv a b c = 1 := by
  set s := a⁻¹ + b⁻¹ + c⁻¹ with hs_def
  have hS : a * s * c ≠ 0 := mul_ne_zero (mul_ne_zero ha hs) hc
  have hK : a + c = a * s * c + a * b⁻¹ * (-c) := by
    rw [hs_def]
    simp only [mul_add, add_mul, mul_neg, mul_assoc, mul_inv_cancel_left₀ ha, inv_mul_cancel₀ hc,
      mul_one]
    abel
  have hHK : harmonicMatrix a b c =
      !![(1 : D), 1; 0, 1] * !![b, -c; a, a * s * c + a * b⁻¹ * (-c)] := by
    rw [← hK]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [harmonicMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals abel
  have hKinv := schur_two b (-c) a (a * s * c) b⁻¹ (a * s * c)⁻¹ (mul_inv_cancel₀ hb)
    (mul_inv_cancel₀ hS)
  have hE : !![(1 : D), 1; 0, 1] * !![1, -1; 0, 1] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hHK, harmonicInv, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ !![(1 : D), -1; 0, 1], hKinv,
    Matrix.one_mul, hE]

theorem harmonic_isUnit (a b c : D) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hs : a⁻¹ + b⁻¹ + c⁻¹ ≠ 0) : IsUnit (harmonicMatrix a b c) :=
  have h := harmonic_mul_inv a b c ha hb hc hs
  ⟨⟨_, _, h, mul_eq_one_comm.mp h⟩, rfl⟩

/-- **Part 1, (5.1).** `s⁻¹ = b − b (H⁻¹)₁₁ b` with `H = diag(b, c) + a 𝟙 𝟙ᵀ` and
`s = a⁻¹ + b⁻¹ + c⁻¹` (in the paper `a = u², b = v², c = w²`). -/
theorem woodbury_corner (a b c : D) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hs : a⁻¹ + b⁻¹ + c⁻¹ ≠ 0) [Invertible (harmonicMatrix a b c)] :
    b - b * (⅟(harmonicMatrix a b c)) 0 0 * b = (a⁻¹ + b⁻¹ + c⁻¹)⁻¹ := by
  rw [invOf_eq_right_inv (harmonic_mul_inv a b c ha hb hc hs)]
  set s := a⁻¹ + b⁻¹ + c⁻¹
  simp only [harmonicInv, Matrix.mul_apply, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero,
    cons_val_one, empty_val', cons_val_fin_one, mul_one, mul_zero, add_zero]
  rw [mul_inv_rev, mul_inv_rev]
  simp only [mul_add, add_mul, mul_assoc, mul_inv_cancel_left₀ hb, inv_mul_cancel₀ hb, mul_one,
    neg_mul, mul_neg, mul_inv_cancel_left₀ hc, inv_mul_cancel₀ ha]
  abel

/-- **Part 2, Lemma 6.1(1).** `s⁻¹ = a − (a a) H⁻¹ (a a)ᵀ` with `H = !![a + b, a; a, a + c]` and
`s = a⁻¹ + b⁻¹ + c⁻¹` (in the paper `a = d₁, b = d₂, c = d₃`). -/
theorem woodbury_sum (a b c : D) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hs : a⁻¹ + b⁻¹ + c⁻¹ ≠ 0) [Invertible (harmonicMatrix a b c)] :
    a - (a * (⅟(harmonicMatrix a b c)) 0 0 * a + a * (⅟(harmonicMatrix a b c)) 0 1 * a +
      a * (⅟(harmonicMatrix a b c)) 1 0 * a + a * (⅟(harmonicMatrix a b c)) 1 1 * a) =
      (a⁻¹ + b⁻¹ + c⁻¹)⁻¹ := by
  rw [invOf_eq_right_inv (harmonic_mul_inv a b c ha hb hc hs)]
  set s := a⁻¹ + b⁻¹ + c⁻¹ with hs_def
  simp only [harmonicInv, Matrix.mul_apply, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero,
    cons_val_one, empty_val', cons_val_fin_one, mul_one, mul_zero, add_zero, mul_neg]
  rw [mul_inv_rev, mul_inv_rev]
  simp only [mul_add, add_mul, mul_assoc, neg_mul, mul_neg, neg_neg]
  rw [← hs_def]
  simp only [inv_mul_cancel_left₀ ha, inv_mul_cancel₀ ha, mul_one, mul_inv_cancel_left₀ hc]
  -- `a (b⁻¹ + c⁻¹) s⁻¹ = a (s − a⁻¹) s⁻¹ = a − s⁻¹`
  have key : a * (b⁻¹ * s⁻¹) + a * (c⁻¹ * s⁻¹) = a - s⁻¹ := by
    rw [← mul_add, ← add_mul, show b⁻¹ + c⁻¹ = s - a⁻¹ by rw [hs_def]; abel, sub_mul, mul_sub,
      mul_inv_cancel₀ hs, mul_one, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  have e : s⁻¹ = a - (a * (b⁻¹ * s⁻¹) + a * (c⁻¹ * s⁻¹)) := by rw [key]; abel
  conv_rhs => rw [e]
  abel

/-! ### Lemma 6.2 of Part 2 -/

/-- The matrix `!![d₃, d₂; −d₁, d₁ r d₂ + d₁ + d₂]` of Part 2, Lemma 6.2. -/
def intermediateMatrix (d₁ d₂ d₃ r : D) : Matrix (Fin 2) (Fin 2) D :=
  !![d₃, d₂; -d₁, d₁ * r * d₂ + d₁ + d₂]

theorem intermediate_schur (d₁ d₂ d₃ r : D) (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) :
    d₁ * r * d₂ + d₁ + d₂ = d₁ * (d₁⁻¹ + d₂⁻¹ + d₃⁻¹ + r) * d₂ + (-d₁) * d₃⁻¹ * d₂ := by
  simp only [mul_add, add_mul, mul_assoc, neg_mul, mul_inv_cancel_left₀ h₁, inv_mul_cancel₀ h₂,
    mul_one]
  abel

theorem intermediate_mul_inv (d₁ d₂ d₃ r : D) (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) (h₃ : d₃ ≠ 0)
    (hf : d₁⁻¹ + d₂⁻¹ + d₃⁻¹ + r ≠ 0) :
    intermediateMatrix d₁ d₂ d₃ r *
      (let S := d₁ * (d₁⁻¹ + d₂⁻¹ + d₃⁻¹ + r) * d₂
      !![d₃⁻¹ + d₃⁻¹ * d₂ * S⁻¹ * (-d₁) * d₃⁻¹, -(d₃⁻¹ * d₂ * S⁻¹); -(S⁻¹ * (-d₁) * d₃⁻¹), S⁻¹]) =
      1 := by
  rw [intermediateMatrix, intermediate_schur d₁ d₂ d₃ r h₁ h₂]
  exact schur_two _ _ _ _ _ _ (mul_inv_cancel₀ h₃)
    (mul_inv_cancel₀ (mul_ne_zero (mul_ne_zero h₁ hf) h₂))

theorem intermediate_isUnit (d₁ d₂ d₃ r : D) (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) (h₃ : d₃ ≠ 0)
    (hf : d₁⁻¹ + d₂⁻¹ + d₃⁻¹ + r ≠ 0) : IsUnit (intermediateMatrix d₁ d₂ d₃ r) :=
  have h := intermediate_mul_inv d₁ d₂ d₃ r h₁ h₂ h₃ hf
  ⟨⟨_, _, h, mul_eq_one_comm.mp h⟩, rfl⟩

/-- **Part 2, Lemma 6.2.** `(s₃ + r)⁻¹ = d₂ (M⁻¹)₂₂ d₁` with `s₃ = d₁⁻¹ + d₂⁻¹ + d₃⁻¹` and
`M = !![d₃, d₂; −d₁, d₁ r d₂ + d₁ + d₂]`. -/
theorem intermediate_inv (d₁ d₂ d₃ r : D) (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) (h₃ : d₃ ≠ 0)
    (hf : d₁⁻¹ + d₂⁻¹ + d₃⁻¹ + r ≠ 0) [Invertible (intermediateMatrix d₁ d₂ d₃ r)] :
    d₂ * (⅟(intermediateMatrix d₁ d₂ d₃ r)) 1 1 * d₁ = (d₁⁻¹ + d₂⁻¹ + d₃⁻¹ + r)⁻¹ := by
  rw [invOf_eq_right_inv (intermediate_mul_inv d₁ d₂ d₃ r h₁ h₂ h₃ hf)]
  simp only [of_apply, cons_val', cons_val_one, empty_val', cons_val_fin_one]
  rw [mul_inv_rev, mul_inv_rev]
  simp only [mul_assoc, mul_inv_cancel_left₀ h₂, inv_mul_cancel₀ h₁, mul_one]

/-! ### Block Schur complement over a noncommutative ring -/

section Block

variable {R : Type*} [Ring R] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-- Block inverse of `fromBlocks (S + B E⁻¹ C) B C E` from right inverses `Ei` of `E` and `Si` of
the Schur complement `S`, over any ring. -/
theorem fromBlocks_mul_schur (S Si : Matrix m m R) (B : Matrix m n R) (C : Matrix n m R)
    (E Ei : Matrix n n R) (hE : E * Ei = 1) (hS : S * Si = 1) :
    fromBlocks (S + B * Ei * C) B C E *
        fromBlocks Si (-(Si * B * Ei)) (-(Ei * C * Si)) (Ei + Ei * C * Si * B * Ei) = 1 := by
  rw [fromBlocks_multiply, ← fromBlocks_one]
  congr 1 <;>
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_neg, Matrix.mul_assoc] <;>
    simp only [← Matrix.mul_assoc S Si, ← Matrix.mul_assoc E Ei, hE, hS, Matrix.one_mul] <;> abel

end Block

/-! ### Lemma 6.6 of Part 2: compression -/

section Compression

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `M = [[Y, d₁ 𝟙ᵀ], [−𝟙 d₂, diag d]]` with `Y = d₁ r d₂ + d₁ + d₂` (Part 2, Lemma 6.6). -/
def compressionMatrix (d₁ d₂ r : D) (d : ι → D) : Matrix (Fin 1 ⊕ ι) (Fin 1 ⊕ ι) D :=
  fromBlocks (of fun _ _ => d₁ * r * d₂ + d₁ + d₂) (of fun _ _ => d₁) (of fun _ _ => -d₂)
    (diagonal d)

/-- The Schur complement of `diag d` in `compressionMatrix` is `d₁ f d₂`,
`f = d₁⁻¹ + d₂⁻¹ + Σ dᵢ⁻¹ + r`. -/
theorem compression_schur (d₁ d₂ r : D) (d : ι → D) (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) :
    (of fun _ _ => d₁ * r * d₂ + d₁ + d₂ : Matrix (Fin 1) (Fin 1) D) -
        (of fun _ _ => d₁ : Matrix (Fin 1) ι D) * diagonal (fun i => (d i)⁻¹) *
          (of fun _ _ => -d₂ : Matrix ι (Fin 1) D) =
      of fun _ _ => d₁ * (d₁⁻¹ + d₂⁻¹ + ∑ i, (d i)⁻¹ + r) * d₂ := by
  ext i j
  simp only [sub_apply, of_apply, Matrix.mul_apply, diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [mul_neg, Finset.sum_neg_distrib,
    sub_neg_eq_add, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc,
    mul_inv_cancel_left₀ h₁, inv_mul_cancel₀ h₂, mul_one]
  abel

theorem compression_mul_inv (d₁ d₂ r : D) (d : ι → D) (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0)
    (hd : ∀ i, d i ≠ 0) (hf : d₁⁻¹ + d₂⁻¹ + ∑ i, (d i)⁻¹ + r ≠ 0) :
    compressionMatrix d₁ d₂ r d *
      (let Si : Matrix (Fin 1) (Fin 1) D :=
          of fun _ _ => (d₁ * (d₁⁻¹ + d₂⁻¹ + ∑ i, (d i)⁻¹ + r) * d₂)⁻¹
        let B : Matrix (Fin 1) ι D := of fun _ _ => d₁
        let C : Matrix ι (Fin 1) D := of fun _ _ => -d₂
        let Ei : Matrix ι ι D := diagonal fun i => (d i)⁻¹
        fromBlocks Si (-(Si * B * Ei)) (-(Ei * C * Si)) (Ei + Ei * C * Si * B * Ei)) = 1 := by
  have hA := compression_schur d₁ d₂ r d h₁ h₂
  rw [sub_eq_iff_eq_add] at hA
  rw [compressionMatrix, hA]
  refine fromBlocks_mul_schur _ _ _ _ _ _ ?_ ?_
  · rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext fun i => mul_inv_cancel₀ (hd i))
  · ext i j
    fin_cases i; fin_cases j
    simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton, of_apply,
      Matrix.one_apply_eq]
    exact mul_inv_cancel₀ (mul_ne_zero (mul_ne_zero h₁ hf) h₂)

theorem compression_isUnit (d₁ d₂ r : D) (d : ι → D) (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0)
    (hd : ∀ i, d i ≠ 0) (hf : d₁⁻¹ + d₂⁻¹ + ∑ i, (d i)⁻¹ + r ≠ 0) :
    IsUnit (compressionMatrix d₁ d₂ r d) :=
  have h := compression_mul_inv d₁ d₂ r d h₁ h₂ hd hf
  ⟨⟨_, _, h, mul_eq_one_comm.mp h⟩, rfl⟩

/-- **Part 2, Lemma 6.6.** `f⁻¹ = d₂ (M⁻¹)₁₁ d₁` for `f = d₁⁻¹ + d₂⁻¹ + Σ dᵢ⁻¹ + r`. -/
theorem compression_inv (d₁ d₂ r : D) (d : ι → D) (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0)
    (hd : ∀ i, d i ≠ 0) (hf : d₁⁻¹ + d₂⁻¹ + ∑ i, (d i)⁻¹ + r ≠ 0)
    [Invertible (compressionMatrix d₁ d₂ r d)] :
    d₂ * (⅟(compressionMatrix d₁ d₂ r d)) (Sum.inl 0) (Sum.inl 0) * d₁ =
      (d₁⁻¹ + d₂⁻¹ + ∑ i, (d i)⁻¹ + r)⁻¹ := by
  rw [invOf_eq_right_inv (compression_mul_inv d₁ d₂ r d h₁ h₂ hd hf)]
  simp only [fromBlocks_apply₁₁, of_apply]
  rw [mul_inv_rev, mul_inv_rev]
  simp only [mul_assoc, mul_inv_cancel_left₀ h₂, inv_mul_cancel₀ h₁, mul_one]

end Compression

/-! ### Bidiagonal chains (Part 1, Lemma 3.2) -/

section Chain

/-- `chainProd ℓ a i n = ℓ i⁻¹ a i ℓ (i+1)⁻¹ a (i+1) ⋯ a (i+n−1) ℓ (i+n)⁻¹`. -/
noncomputable def chainProd (ℓ a : ℕ → D) : ℕ → ℕ → D
  | i, 0 => (ℓ i)⁻¹
  | i, n + 1 => (ℓ i)⁻¹ * a i * chainProd ℓ a (i + 1) n

/-- The upper bidiagonal chain: `ℓ i` on the diagonal and `−a i` at `(i, i + 1)`. -/
def chain (q : ℕ) (ℓ a : ℕ → D) : Matrix (Fin q) (Fin q) D :=
  of fun i j => if (j : ℕ) = i then ℓ i else if (j : ℕ) = i + 1 then -a i else 0

/-- The explicit inverse of `chain q ℓ a`: entry `(i, j)` is `chainProd ℓ a i (j − i)` for
`i ≤ j`. -/
noncomputable def chainInv (q : ℕ) (ℓ a : ℕ → D) : Matrix (Fin q) (Fin q) D :=
  of fun i j => if (i : ℕ) ≤ j then chainProd ℓ a i (j - i) else 0

theorem chain_row (ℓ a : ℕ → D) (hℓ : ∀ i, ℓ i ≠ 0) (q I J : ℕ) (hI : I < q) (hJ : J < q) :
    ∑ k ∈ Finset.range q,
        (if k = I then ℓ I else if k = I + 1 then -a I else 0) *
          (if k ≤ J then chainProd ℓ a k (J - k) else 0) =
      if I = J then 1 else 0 := by
  have hsplit : ∀ k ∈ Finset.range q,
      (if k = I then ℓ I else if k = I + 1 then -a I else 0) *
          (if k ≤ J then chainProd ℓ a k (J - k) else 0) =
        (if I = k then ℓ I * (if I ≤ J then chainProd ℓ a I (J - I) else 0) else 0) +
          (if I + 1 = k then
            -a I * (if I + 1 ≤ J then chainProd ℓ a (I + 1) (J - (I + 1)) else 0) else 0) := by
    intro k _
    by_cases h1 : k = I
    · subst h1; simp
    · by_cases h2 : k = I + 1
      · subst h2; simp
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp only [Finset.mem_range, hI, ite_true]
  rcases lt_trichotomy I J with h | h | h
  · have hJI : J - I = (J - (I + 1)) + 1 := by omega
    rw [hJI]
    simp only [h.le, show I + 1 ≤ J by omega, show I + 1 < q by omega, h.ne, ite_true, ite_false,
      chainProd, mul_assoc, mul_inv_cancel_left₀ (hℓ I), neg_mul, add_neg_cancel]
  · subst h
    simp [chainProd, mul_inv_cancel₀ (hℓ I)]
  · have h2 : ¬ I + 1 ≤ J := by omega
    simp [show ¬ I ≤ J by omega, h2, show I ≠ J by omega]

theorem chain_mul_inv (q : ℕ) (ℓ a : ℕ → D) (hℓ : ∀ i, ℓ i ≠ 0) :
    chain q ℓ a * chainInv q ℓ a = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [chain, chainInv, of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k => (if k = (i : ℕ) then ℓ i else
      if k = (i : ℕ) + 1 then -a i else 0) *
      (if k ≤ (j : ℕ) then chainProd ℓ a k ((j : ℕ) - k) else 0)) q,
    chain_row ℓ a hℓ q i j i.isLt j.isLt]
  simp [Fin.ext_iff]

theorem chain_isUnit (q : ℕ) (ℓ a : ℕ → D) (hℓ : ∀ i, ℓ i ≠ 0) : IsUnit (chain q ℓ a) :=
  have h := chain_mul_inv q ℓ a hℓ
  ⟨⟨_, _, h, mul_eq_one_comm.mp h⟩, rfl⟩

/-- **Part 1, Lemma 3.2 (chain inverse).** For the `(q+1) × (q+1)` upper bidiagonal chain with
`ℓ 0, …, ℓ q` on the diagonal and `−a 0, …, −a (q−1)` above it,
`(C⁻¹)_{0,q} = ℓ 0⁻¹ a 0 ℓ 1⁻¹ ⋯ a (q−1) ℓ q⁻¹`. -/
theorem chain_inv_corner (q : ℕ) (ℓ a : ℕ → D) (hℓ : ∀ i, ℓ i ≠ 0)
    [Invertible (chain (q + 1) ℓ a)] :
    (⅟(chain (q + 1) ℓ a)) 0 (Fin.last q) = chainProd ℓ a 0 q := by
  rw [invOf_eq_right_inv (chain_mul_inv (q + 1) ℓ a hℓ)]
  simp [chainInv]

theorem chainProd_neg (ℓ : ℕ → D) (c : D) (i n : ℕ) :
    chainProd ℓ (fun _ => -c) i n = (-1) ^ n * chainProd ℓ (fun _ => c) i n := by
  induction n generalizing i with
  | zero => simp [chainProd]
  | succ n ih =>
    rw [chainProd, chainProd, ih, ← mul_assoc ((ℓ i)⁻¹ * -c),
      ← ((Commute.neg_one_left _).pow_left n).eq, pow_succ]
    simp [mul_assoc]

end Chain

/-! ### The cyclic witness of Part 2, (2.1)/(2.2) -/

section Cycle

/-- `F̂_d` for `d = n + 2` in the block form of the proof of Part 2, (2.1):
`F̂_d = [[p₁, c e₁ᵀ], [c e_{d−1}, T_d]]`, with `T_d` upper bidiagonal, `p₂, …, p_d` on the
diagonal and `c` above it (`chain` with `a = −c`). Here `p k` is `p_{k+1}`. Up to the reindexing
`Fin 1 ⊕ Fin (d − 1) ≃ Fin d`, this is the matrix with `p₁, …, p_d` on the diagonal, `c` on the
superdiagonal and `c` in position `(d, 1)`. -/
def cycleBlocks (n : ℕ) (p : ℕ → D) (c : D) : Matrix (Fin 1 ⊕ Fin (n + 1)) (Fin 1 ⊕ Fin (n + 1)) D :=
  fromBlocks (of fun _ _ => p 0) (of fun _ j => if j = 0 then c else 0)
    (of fun i _ => if i = Fin.last n then c else 0) (chain (n + 1) (fun k => p (k + 1)) fun _ => -c)

/-- `F̂_d` for `d = n + 2` as a `d × d` matrix (0-indexed): `p i` on the diagonal, `c` on the
superdiagonal and `c` in position `(d − 1, 0)`. -/
def cycleMatrix (n : ℕ) (p : ℕ → D) (c : D) : Matrix (Fin (n + 2)) (Fin (n + 2)) D :=
  of fun i j => if (j : ℕ) = i then p i else if (j : ℕ) = i + 1 then c else
    if (i : ℕ) = n + 1 ∧ (j : ℕ) = 0 then c else 0

/-- The reindexing `Fin 1 ⊕ Fin (n + 1) ≃ Fin (n + 2)`. -/
def cycleEquiv (n : ℕ) : Fin 1 ⊕ Fin (n + 1) ≃ Fin (n + 2) :=
  finSumFinEquiv.trans (finCongr (by omega))

theorem cycleBlocks_eq_submatrix (n : ℕ) (p : ℕ → D) (c : D) :
    cycleBlocks n p c = (cycleMatrix n p c).submatrix (cycleEquiv n) (cycleEquiv n) := by
  ext (i | i) (j | j)
  · fin_cases i; fin_cases j
    simp [cycleBlocks, cycleMatrix, cycleEquiv]
  · fin_cases i
    simp only [cycleBlocks, cycleMatrix, cycleEquiv, fromBlocks_apply₁₂, submatrix_apply,
      of_apply, Equiv.trans_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      finCongr_apply, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, Fin.ext_iff, Fin.val_zero]
    split_ifs <;> first | rfl | omega
  · fin_cases j
    simp only [cycleBlocks, cycleMatrix, cycleEquiv, fromBlocks_apply₂₁, submatrix_apply,
      of_apply, Equiv.trans_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      finCongr_apply, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, Fin.ext_iff, Fin.val_zero,
      Fin.val_last, and_true]
    split_ifs <;> first | rfl | (exfalso; omega)
  · simp only [cycleBlocks, cycleMatrix, cycleEquiv, chain, fromBlocks_apply₂₂, submatrix_apply,
      of_apply, Equiv.trans_apply, finSumFinEquiv_apply_right, finCongr_apply, Fin.val_cast,
      Fin.val_natAdd, neg_neg]
    split_ifs <;> first | rfl | omega | (congr 1; omega)

/-- The Schur complement of `T_d` in `F̂_d`: `σ = p₁ − c (T_d⁻¹)_{1,d−1} c`. -/
theorem cycle_schur (n : ℕ) (p : ℕ → D) (c : D) :
    (of fun _ _ => p 0 : Matrix (Fin 1) (Fin 1) D) -
        (of fun _ j => if j = 0 then c else 0 : Matrix (Fin 1) (Fin (n + 1)) D) *
          chainInv (n + 1) (fun k => p (k + 1)) (fun _ => -c) *
          (of fun i _ => if i = Fin.last n then c else 0 : Matrix (Fin (n + 1)) (Fin 1) D) =
      of fun _ _ => p 0 - c * chainProd (fun k => p (k + 1)) (fun _ => -c) 0 n * c := by
  ext i j
  simp [Matrix.mul_apply, chainInv, ite_mul, mul_ite, Finset.sum_ite_eq', Fin.le_last]

/-- The block inverse (2.2) of `cycleBlocks`. -/
noncomputable def cycleBlocksInv (n : ℕ) (p : ℕ → D) (c : D) :
    Matrix (Fin 1 ⊕ Fin (n + 1)) (Fin 1 ⊕ Fin (n + 1)) D :=
  let Si : Matrix (Fin 1) (Fin 1) D :=
    of fun _ _ => (p 0 - c * chainProd (fun k => p (k + 1)) (fun _ => -c) 0 n * c)⁻¹
  let B : Matrix (Fin 1) (Fin (n + 1)) D := of fun _ j => if j = 0 then c else 0
  let C : Matrix (Fin (n + 1)) (Fin 1) D := of fun i _ => if i = Fin.last n then c else 0
  let Ei := chainInv (n + 1) (fun k => p (k + 1)) (fun _ => -c)
  fromBlocks Si (-(Si * B * Ei)) (-(Ei * C * Si)) (Ei + Ei * C * Si * B * Ei)

theorem cycle_mul_inv (n : ℕ) (p : ℕ → D) (c : D) (hp : ∀ k, p (k + 1) ≠ 0)
    (hσ : p 0 - c * chainProd (fun k => p (k + 1)) (fun _ => -c) 0 n * c ≠ 0) :
    cycleBlocks n p c * cycleBlocksInv n p c = 1 := by
  have hA := cycle_schur n p c
  rw [sub_eq_iff_eq_add] at hA
  rw [cycleBlocks, cycleBlocksInv, hA]
  refine fromBlocks_mul_schur _ _ _ _ _ _ (chain_mul_inv _ _ _ hp) ?_
  ext i j
  fin_cases i; fin_cases j
  simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton, of_apply,
    Matrix.one_apply_eq]
  exact mul_inv_cancel₀ hσ

theorem cycle_isUnit (n : ℕ) (p : ℕ → D) (c : D) (hp : ∀ k, p (k + 1) ≠ 0)
    (hσ : p 0 - c * chainProd (fun k => p (k + 1)) (fun _ => -c) 0 n * c ≠ 0) :
    IsUnit (cycleBlocks n p c) :=
  have h := cycle_mul_inv n p c hp hσ
  ⟨⟨_, _, h, mul_eq_one_comm.mp h⟩, rfl⟩

/-- The sign in (2.1): `p₁ − c (T_d⁻¹)_{1,d−1} c = p₁ + (−1)^{d−1} c p₂⁻¹ c ⋯ p_d⁻¹ c`. -/
theorem cycle_schur_sign (n : ℕ) (p : ℕ → D) (c : D) :
    p 0 - c * chainProd (fun k => p (k + 1)) (fun _ => -c) 0 n * c =
      p 0 + (-1) ^ (n + 1) * (c * chainProd (fun k => p (k + 1)) (fun _ => c) 0 n * c) := by
  set Q := chainProd (fun k => p (k + 1)) (fun _ => c) 0 n
  have hc : c * ((-1) ^ n * Q) = (-1) ^ n * (c * Q) := by
    rw [← mul_assoc, ← ((Commute.neg_one_left c).pow_left n).eq, mul_assoc]
  rw [chainProd_neg, hc, pow_succ]
  simp [mul_assoc, sub_eq_add_neg]

/-- **Part 2, (2.1)/(2.2), block form.** `ρ_d = (F̂_d⁻¹)₁₁ = σ⁻¹ =
[p₁ + (−1)^{d−1} c p₂⁻¹ c p₃⁻¹ c ⋯ p_d⁻¹ c]⁻¹` (`d = n + 2`;
`chainProd _ (fun _ => c) 0 n = p₂⁻¹ c p₃⁻¹ ⋯ c p_d⁻¹`). -/
theorem cycle_inv (n : ℕ) (p : ℕ → D) (c : D) (hp : ∀ k, p (k + 1) ≠ 0)
    (hσ : p 0 - c * chainProd (fun k => p (k + 1)) (fun _ => -c) 0 n * c ≠ 0)
    [Invertible (cycleBlocks n p c)] :
    (⅟(cycleBlocks n p c)) (Sum.inl 0) (Sum.inl 0) =
      (p 0 + (-1) ^ (n + 1) * (c * chainProd (fun k => p (k + 1)) (fun _ => c) 0 n * c))⁻¹ := by
  rw [invOf_eq_right_inv (cycle_mul_inv n p c hp hσ), cycleBlocksInv]
  simp only [fromBlocks_apply₁₁, of_apply]
  rw [cycle_schur_sign]

theorem cycleMatrix_eq_submatrix (n : ℕ) (p : ℕ → D) (c : D) :
    cycleMatrix n p c = (cycleBlocks n p c).submatrix (cycleEquiv n).symm (cycleEquiv n).symm := by
  rw [cycleBlocks_eq_submatrix, submatrix_submatrix]
  simp

theorem cycleEquiv_symm_zero (n : ℕ) : (cycleEquiv n).symm 0 = Sum.inl 0 := by
  rw [Equiv.symm_apply_eq]
  rfl

theorem cycleMatrix_mul_inv (n : ℕ) (p : ℕ → D) (c : D) (hp : ∀ k, p (k + 1) ≠ 0)
    (hσ : p 0 - c * chainProd (fun k => p (k + 1)) (fun _ => -c) 0 n * c ≠ 0) :
    cycleMatrix n p c * (cycleBlocksInv n p c).submatrix (cycleEquiv n).symm (cycleEquiv n).symm =
      1 := by
  rw [cycleMatrix_eq_submatrix, submatrix_mul_equiv, cycle_mul_inv n p c hp hσ,
    submatrix_one_equiv]

theorem cycleMatrix_isUnit (n : ℕ) (p : ℕ → D) (c : D) (hp : ∀ k, p (k + 1) ≠ 0)
    (hσ : p 0 - c * chainProd (fun k => p (k + 1)) (fun _ => -c) 0 n * c ≠ 0) :
    IsUnit (cycleMatrix n p c) :=
  have h := cycleMatrix_mul_inv n p c hp hσ
  ⟨⟨_, _, h, mul_eq_one_comm.mp h⟩, rfl⟩

/-- **Part 2, (2.1).** For the cyclic `d × d` matrix `F̂_d` (`d = n + 2`) with `p₁, …, p_d` on the
diagonal, `c` on the superdiagonal and `c` in position `(d, 1)`, over a division ring:
`ρ_d = (F̂_d⁻¹)₁₁ = [p₁ + (−1)^{d−1} c p₂⁻¹ c p₃⁻¹ c ⋯ p_d⁻¹ c]⁻¹`, provided the `p_j` (`j ≥ 2`)
and the Schur complement are nonzero. -/
theorem cycleMatrix_inv (n : ℕ) (p : ℕ → D) (c : D) (hp : ∀ k, p (k + 1) ≠ 0)
    (hσ : p 0 - c * chainProd (fun k => p (k + 1)) (fun _ => -c) 0 n * c ≠ 0)
    [Invertible (cycleMatrix n p c)] :
    (⅟(cycleMatrix n p c)) 0 0 =
      (p 0 + (-1) ^ (n + 1) * (c * chainProd (fun k => p (k + 1)) (fun _ => c) 0 n * c))⁻¹ := by
  rw [invOf_eq_right_inv (cycleMatrix_mul_inv n p c hp hσ), submatrix_apply,
    cycleEquiv_symm_zero, cycleBlocksInv]
  simp only [fromBlocks_apply₁₁, of_apply]
  rw [cycle_schur_sign]

end Cycle

end ThreeAxes.InverseIdentities
