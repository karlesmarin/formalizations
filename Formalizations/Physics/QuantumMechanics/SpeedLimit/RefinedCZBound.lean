/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.Physics.QuantumMechanics.SpeedLimit.ExchangeQuadrature

/-!
# A refined controlled-Z bound for exchange-coupled qutrits: the trace lemma

Physics context. Two transmons truncated to three levels are coupled by the exchange interaction
`H_c = J (a† ⊗ a + a ⊗ a†)` (here `J = 1`). With ideal, instantaneous local control, the operator
norm `‖H_c‖` gives only the crude controlled-Z time bound `T ≥ π / (4 J ‖H_c‖)`-type estimates.
The sharper argument compares the true evolution `U(t)` with the evolution `L(t)` that has the same
local controls but no `H_c`, on the reference-extended product state `Ω₀` (a maximally entangled
state between a rank-two code in `ℂ³` and a two-level passive reference, on each side). The
Fubini–Study speed of `U†L Ω₀` is the spread of `H_c` in `L(t) Ω₀`, a state whose physical reduced
state is `(P_A ⊗ P_B) / 4` with `P_A, P_B` rank-two projectors of `ℂ³`. The key finite-dimensional
fact is then

  `(1/4) Tr[(P_A ⊗ P_B) H_c²] ≤ 97/32`,

with equality for `P = 1 - |v⟩⟨v|`, `v = √(7/8) |0⟩ + √(1/8) |2⟩`. Combined with the fact that
`L(T) Ω₀` is a product across the two sides while the CZ state is at Fubini–Study distance `≥ π/4`
from every product, this gives `T·√(97/32) ≥ π/4 - arccos(1 - e)` for CZ error `e`.

The argument was suggested by an AI reviewer (ChatGPT, OpenAI); the lemma was checked numerically
(`research/qsl-hardware/cota_cz_refinada.py` in the Curiosity workspace) and is formalized here.

## Main results (all proved here, sorry-free)

* `QSL.Exchange.exchC_sq_apply`: the entries of `H_c²` (a `9 × 9` integer matrix, block diagonal by
  total excitation number; the only off-diagonal entries are `⟨20|H_c²|02⟩ = ⟨02|H_c²|20⟩ = 2`).
* `QSL.Exchange.trace_expand`: closed form of `Tr[(P_A ⊗ P_B) H_c²]` for `P = 1 - |v⟩⟨v|`, as a
  polynomial in the populations `|v_i|², |w_i|²` plus the cross term `2 (z + z̄)`,
  `z = v₀ w₂ v̄₂ w̄₀`. No normalization is used.
* `QSL.Exchange.refined_cz_lemma`: for unit `v, w ∈ ℂ³`,
  `(1/4) Re Tr[(P_v ⊗ P_w) H_c²] ≤ 97/32`. Route: coordinate expansion, AM–GM on the cross term
  (`re_crossZ_le`), then the scalar inequality `scalar_ineq`
  (`97/8 - G = 2 (p₂ + q₂ - 1/4)² + p₁(…) + q₁(…) ≥ 0`, i.e. completing the square).
* `QSL.Exchange.refined_cz_equality`: equality at `v = w = √(7/8) |0⟩ + √(1/8) |2⟩`.

## Not formalized

The time bound itself (P2): `sAngle (U Ω₀) (L Ω₀) ≤ √(97/32) Σ τ_k` and the corollary
`T √(97/32) ≥ π/4 - arccos(1 - e)`. Plan, reusing `QSL.Qudit` and `QSL.Gate`:

1. Show `‖(H_c ⊗ 1) (U_A ⊗ U_B ⊗ 1) Ω₀‖² = (1/4) Tr[(P_A ⊗ P_B) H_c²]`, where
   `Ω₀ = Φ_{AA'} ⊗ Φ_{BB'}`, `Φ = 2^{-1/2} Σ_{a'} |c_{a'}⟩ ⊗ |a'⟩` (`c_0, c_1` an orthonormal pair
   in `ℂ³`), `U_A, U_B` unitary, and `P_A = Σ |U_A c_a'⟩⟨U_A c_a'|`.
2. Show every rank-two projector of `ℂ³` has the form `1 - |v⟩⟨v|` with `v` a unit vector (the
   conjugate cross product of the code pair), so `refined_cz_lemma` applies.
3. Duhamel step: for `s ↦ e^{-i(τ-s)(K+H)} H e^{-isK} ψ`, an estimate in the style of
   `QSL.Gate.sAngle_exp_le` gives `sAngle (e^{-iτ(K+H)} ψ) (e^{-iτK} ψ) ≤ τ · sup_s ‖H e^{-isK} ψ‖`,
   with `e^{-isK} Ω₀` of the form in step 1 by `QSL.Qudit.exp_local`; chain the steps with
   `QSL.Gate.sAngle_le_sAngle_add_sAngle` and unitary invariance.
4. Corollary: `L Ω₀` is a product across `AA' : BB'`; the Choi state of CZ has Schmidt
   coefficients `(1/√2, 1/√2)` across it, so the existing product-overlap lemma
   (`QSL.Qudit.norm_inner_bellPair_prodVec_le`) gives `π/4` and the triangle inequality with
   `fsAngle_le_of_norm_sub_le`/`arccos_one_sub_le` finishes.

## References

* P. Wocjan, M. Rötteler, D. Janzing, T. Beth, *Simulating Hamiltonians in quantum networks:
  efficient schemes and complexity bounds*, Phys. Rev. A 65 (2002) 042309.
-/

@[expose] public section

open scoped Matrix Kronecker

namespace QSL.Exchange

noncomputable section

/-- The exchange operator of two qutrits, as a complex matrix. -/
def exchC : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := (exch 3).map (fun r => (r : ℂ))

/-- Diagonal of `exchC ^ 2`. -/
def sqDiag : Fin 3 → Fin 3 → ℝ := ![![0, 1, 2], ![1, 4, 4], ![2, 4, 0]]

lemma sqrt_two_mul_self_C : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

lemma exchC_sq_apply (i k j l : Fin 3) :
    (exchC * exchC) (i, k) (j, l) =
      if (i, k) = (j, l) then (sqDiag i k : ℂ)
      else if ((i, k) = (2, 0) ∧ (j, l) = (0, 2)) ∨ ((i, k) = (0, 2) ∧ (j, l) = (2, 0)) then 2
      else 0 := by
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [exchC, exch, bd, sqDiag, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_three,
      Matrix.kroneckerMap_apply, sqrt_two_mul_self_C] <;> norm_num

/-- The rank-two projector `1 - |v⟩⟨v|`. -/
def codeProj (v : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ := 1 - Matrix.vecMulVec v (star v)

/-- Cross term `⟨v₀ w₂ , v₂ w₀⟩`-type. -/
def crossZ (v w : Fin 3 → ℂ) : ℂ := v 0 * w 2 * (star (v 2) * star (w 0))

/-- Real part of the expectation, with the `p`, `q` populations. -/
lemma trace_expand (v w : Fin 3 → ℂ) :
    Matrix.trace ((codeProj v ⊗ₖ codeProj w) * (exchC * exchC)) =
      ((18 - (3 * Complex.normSq (v 0) + 9 * Complex.normSq (v 1) + 6 * Complex.normSq (v 2))
        - (3 * Complex.normSq (w 0) + 9 * Complex.normSq (w 1) + 6 * Complex.normSq (w 2))
        + (Complex.normSq (v 1) * Complex.normSq (w 0) + 2 * Complex.normSq (v 2) * Complex.normSq (w 0)
          + Complex.normSq (v 0) * Complex.normSq (w 1) + 4 * Complex.normSq (v 1) * Complex.normSq (w 1)
          + 4 * Complex.normSq (v 2) * Complex.normSq (w 1) + 2 * Complex.normSq (v 0) * Complex.normSq (w 2)
          + 4 * Complex.normSq (v 1) * Complex.normSq (w 2)) : ℝ) : ℂ)
      + 2 * (crossZ v w + star (crossZ v w)) := by
  push_cast
  simp only [← Complex.mul_conj]
  have h := exchC_sq_apply
  generalize exchC * exchC = M at h ⊢
  simp [Matrix.trace, Matrix.mul_apply, codeProj, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Fin.sum_univ_three, h, sqDiag, Matrix.vecMulVec_apply, Matrix.one_apply, crossZ]
  ring

/-- Real part of the cross term: AM–GM. -/
lemma re_crossZ_le (v w : Fin 3 → ℂ) :
    (crossZ v w).re ≤
      (Complex.normSq (v 0) * Complex.normSq (v 2) + Complex.normSq (w 0) * Complex.normSq (w 2)) / 2 := by
  have h : crossZ v w = (v 0 * star (v 2)) * (w 2 * star (w 0)) := by unfold crossZ; ring
  have h1 : Complex.normSq (v 0 * star (v 2)) = Complex.normSq (v 0) * Complex.normSq (v 2) := by
    simp [Complex.normSq_conj]
  have h2 : Complex.normSq (w 2 * star (w 0)) = Complex.normSq (w 0) * Complex.normSq (w 2) := by
    simp [Complex.normSq_conj, mul_comm]
  rw [← h1, ← h2, h, Complex.mul_re, Complex.normSq_apply, Complex.normSq_apply]
  nlinarith [sq_nonneg ((v 0 * star (v 2)).re - (w 2 * star (w 0)).re),
    sq_nonneg ((v 0 * star (v 2)).im + (w 2 * star (w 0)).im)]

/-- The scalar inequality behind the bound. -/
lemma scalar_ineq (p1 p2 q1 q2 : ℝ) (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2) (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2)
    (hp : p1 + p2 ≤ 1) (hq : q1 + q2 ≤ 1) :
    18 - (3 * (1 - p1 - p2) + 9 * p1 + 6 * p2) - (3 * (1 - q1 - q2) + 9 * q1 + 6 * q2)
      + (p1 * (1 - q1 - q2) + 2 * p2 * (1 - q1 - q2) + (1 - p1 - p2) * q1 + 4 * p1 * q1
        + 4 * p2 * q1 + 2 * (1 - p1 - p2) * q2 + 4 * p1 * q2)
      + 2 * ((1 - p1 - p2) * p2 + (1 - q1 - q2) * q2) ≤ 97 / 8 := by
  nlinarith [sq_nonneg (p2 + q2 - 1 / 4), mul_nonneg hp1 hp2, mul_nonneg hp1 hq1,
    mul_nonneg hp1 hq2, mul_nonneg hq1 hq2, mul_nonneg hq1 hp2, mul_nonneg hp1 (sub_nonneg.2 hp),
    mul_nonneg hq1 (sub_nonneg.2 hq), mul_nonneg hp1 (sub_nonneg.2 hq), mul_nonneg hq1 (sub_nonneg.2 hp)]

/-- **Refined bound for the exchange coupling of two qutrits.** For any rank-two projectors
`1 - |v⟩⟨v|`, `1 - |w⟩⟨w|` (`v`, `w` unit vectors of `ℂ³`),
`(1/4) Re Tr[(P_A ⊗ P_B) H_c²] ≤ 97/32`, where `H_c = a† ⊗ a + a ⊗ a†`. -/
theorem refined_cz_lemma (v w : Fin 3 → ℂ) (hv : ∑ i, Complex.normSq (v i) = 1)
    (hw : ∑ i, Complex.normSq (w i) = 1) :
    (1 / 4) * (Matrix.trace ((codeProj v ⊗ₖ codeProj w) * (exchC * exchC))).re ≤ 97 / 32 := by
  rw [trace_expand]
  have hc := re_crossZ_le v w
  have hcre : (star (crossZ v w)).re = (crossZ v w).re := by simp
  simp only [Fin.sum_univ_three] at hv hw
  have n0 := Complex.normSq_nonneg (v 0)
  have n1 := Complex.normSq_nonneg (v 1)
  have n2 := Complex.normSq_nonneg (v 2)
  have m0 := Complex.normSq_nonneg (w 0)
  have m1 := Complex.normSq_nonneg (w 1)
  have m2 := Complex.normSq_nonneg (w 2)
  have key := scalar_ineq (Complex.normSq (v 1)) (Complex.normSq (v 2)) (Complex.normSq (w 1))
    (Complex.normSq (w 2)) n1 n2 m1 m2 (by linarith) (by linarith)
  have e0 : Complex.normSq (v 0) = 1 - Complex.normSq (v 1) - Complex.normSq (v 2) := by linarith
  have f0 : Complex.normSq (w 0) = 1 - Complex.normSq (w 1) - Complex.normSq (w 2) := by linarith
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, sub_zero, hcre]
  rw [e0, f0] at hc ⊢
  nlinarith [key, hc]


/-- The extremal vector `√(7/8) |0⟩ + √(1/8) |2⟩`. -/
def vEq : Fin 3 → ℂ := ![((Real.sqrt (7 / 8) : ℝ) : ℂ), 0, ((Real.sqrt (1 / 8) : ℝ) : ℂ)]

lemma vEq_zero : vEq 0 = ((Real.sqrt (7 / 8) : ℝ) : ℂ) := rfl

lemma vEq_one : vEq 1 = 0 := rfl

lemma vEq_two : vEq 2 = ((Real.sqrt (1 / 8) : ℝ) : ℂ) := rfl

lemma normSq_vEq_zero : Complex.normSq (vEq 0) = 7 / 8 := by
  rw [vEq_zero, Complex.normSq_ofReal]; exact Real.mul_self_sqrt (by norm_num)

lemma normSq_vEq_one : Complex.normSq (vEq 1) = 0 := by rw [vEq_one]; simp

lemma normSq_vEq_two : Complex.normSq (vEq 2) = 1 / 8 := by
  rw [vEq_two, Complex.normSq_ofReal]; exact Real.mul_self_sqrt (by norm_num)

lemma vEq_unit : ∑ i, Complex.normSq (vEq i) = 1 := by
  rw [Fin.sum_univ_three, normSq_vEq_zero, normSq_vEq_one, normSq_vEq_two]; norm_num

lemma crossZ_vEq : (crossZ vEq vEq).re = 7 / 64 := by
  have h7 : Real.sqrt (7 / 8) * Real.sqrt (7 / 8) = 7 / 8 := Real.mul_self_sqrt (by norm_num)
  have h1 : Real.sqrt (1 / 8) * Real.sqrt (1 / 8) = 1 / 8 := Real.mul_self_sqrt (by norm_num)
  have e : crossZ vEq vEq =
      ((Real.sqrt (7 / 8) * Real.sqrt (1 / 8) * (Real.sqrt (1 / 8) * Real.sqrt (7 / 8)) : ℝ) : ℂ) := by
    simp [crossZ, vEq_zero, vEq_two]
  rw [e, Complex.ofReal_re]
  calc _ = (Real.sqrt (7 / 8) * Real.sqrt (7 / 8)) * (Real.sqrt (1 / 8) * Real.sqrt (1 / 8)) := by ring
    _ = 7 / 64 := by rw [h7, h1]; norm_num

/-- **Equality case**: `v = w = √(7/8) |0⟩ + √(1/8) |2⟩` attains `97/32`. -/
theorem refined_cz_equality :
    (1 / 4) * (Matrix.trace ((codeProj vEq ⊗ₖ codeProj vEq) * (exchC * exchC))).re = 97 / 32 := by
  rw [trace_expand]
  have hcre : (star (crossZ vEq vEq)).re = (crossZ vEq vEq).re := by simp
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, sub_zero, hcre, crossZ_vEq, normSq_vEq_zero, normSq_vEq_one, normSq_vEq_two]
  norm_num

end

end QSL.Exchange
