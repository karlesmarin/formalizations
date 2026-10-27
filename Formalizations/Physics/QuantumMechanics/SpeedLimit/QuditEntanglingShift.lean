/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.Physics.QuantumMechanics.SpeedLimit.QuditEntangling

/-!
# The entangling time with the spectral half-width of the interaction

The interaction `H` of `QSL.Qudit.arccos_le_entangling_time` is only defined up to a multiple of the
identity: `c • 1 = (c • 1) ⊗ 1` is a local term, and can be absorbed into the local control `Aₖ`.
Hence the bound `arccos λ ≤ J · ∑ τₖ` holds with `J` any bound of the *shifted* norm `‖H − c • 1‖`,
`c` real. For `H` Hermitian with spectrum in `[m, M]` the choice `c = (m + M) / 2` gives the
spectral half-width `(M − m) / 2` (this spectral fact is taken as a hypothesis here, not proved).

For the two-qubit Heisenberg interaction `H = XX + YY + ZZ` (spectrum `{1, −3}`), `H + 1 = 2 · SWAP`,
so `‖H − (−1) • 1‖ = 2` instead of `‖H‖ = 3`. The Bell vector then needs total time `T ≥ π / 8`.
This matches the Heisenberg entangling time `π / 8` of Dür, Vidal, Cirac, Linden and Popescu; that
this time is *achievable* is their result and is **not** formalized here.

## Main results

* `QSL.Qudit.arccos_le_entangling_time_shift`: `arccos λ ≤ J · ∑ τₖ` whenever `‖H − c • 1‖ ≤ J`
* `QSL.Qudit.arccos_le_entangling_time_halfWidth`: the spectral half-width version
* `QSL.Qudit.pi_div_four_le_entangling_time_shift`: Bell vector, `π / 4 ≤ J · ∑ τₖ`
* `QSL.Qudit.heisenberg_shift_norm`: `‖heisenberg − (−1) • 1‖ = 2`
* `QSL.Qudit.pi_div_eight_le_heisenberg_time`: Bell vector under the Heisenberg interaction needs
  `∑ τₖ ≥ π / 8`

## References

* W. Dür, G. Vidal, J. I. Cirac, N. Linden, S. Popescu, *Entanglement capabilities of nonlocal
  Hamiltonians*, Phys. Rev. Lett. 87 (2001) 137901.
-/

@[expose] public section

noncomputable section

open scoped Matrix Kronecker
open scoped Matrix.Norms.L2Operator
open NormedSpace
open QSL.TwoQubit (act)

namespace QSL.Qudit

section Shift

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [Fintype κ] in
private lemma smul_one_kronecker_one (c : ℂ) :
    (c • (1 : Matrix ι ι ℂ)) ⊗ₖ (1 : Matrix κ κ ℂ) = c • (1 : Matrix (ι × κ) (ι × κ) ℂ) := by
  rw [Matrix.smul_kronecker, Matrix.one_kronecker_one]

private lemma isHermitian_real_smul_one {m : Type*} [Fintype m] [DecidableEq m] (c : ℝ) :
    ((c : ℂ) • (1 : Matrix m m ℂ)).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  simp

/-- (C, shifted) Entangling-time bound with a shifted interaction. As `arccos_le_entangling_time`,
but with `‖H − c • 1‖ ≤ J` for some real `c` in place of `‖H‖ ≤ J`. The identity part of `H` is a
local term and is absorbed into the control. -/
theorem arccos_le_entangling_time_shift (H : Matrix (ι × κ) (ι × κ) ℂ) (hH : H.IsHermitian)
    (c : ℝ) (J : ℝ) (hJ : ‖H - (c : ℂ) • (1 : Matrix (ι × κ) (ι × κ) ℂ)‖ ≤ J)
    (steps : List (ℝ × Matrix ι ι ℂ × Matrix κ κ ℂ))
    (hτ : ∀ s ∈ steps, 0 ≤ s.1) (hA : ∀ s ∈ steps, s.2.1.IsHermitian)
    (hB : ∀ s ∈ steps, s.2.2.IsHermitian) (a : EuclideanSpace ℂ ι) (b : EuclideanSpace ℂ κ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (Φ : EuclideanSpace ℂ (ι × κ))
    (hU : act (steps.map fun s => exp ((-(s.1 : ℂ) * Complex.I) •
        (s.2.1 ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ s.2.2 + H))).prod
        (prodVec a b) = Φ)
    (lam : ℝ) (hlam : ∀ (x : EuclideanSpace ℂ ι) (y : EuclideanSpace ℂ κ), ‖x‖ = 1 → ‖y‖ = 1 →
        ‖inner ℂ Φ (prodVec x y)‖ ≤ lam) :
    Real.arccos lam ≤ J * (steps.map Prod.fst).sum := by
  set steps' : List (ℝ × Matrix ι ι ℂ × Matrix κ κ ℂ) :=
    steps.map fun s => (s.1, s.2.1 + (c : ℂ) • (1 : Matrix ι ι ℂ), s.2.2) with hsteps'
  have hmap : steps'.map Prod.fst = steps.map Prod.fst := by
    simp [hsteps', Function.comp_def]
  have hexp : (steps'.map fun s => exp ((-(s.1 : ℂ) * Complex.I) •
        (s.2.1 ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ s.2.2 +
          (H - (c : ℂ) • (1 : Matrix (ι × κ) (ι × κ) ℂ))))).prod =
      (steps.map fun s => exp ((-(s.1 : ℂ) * Complex.I) •
        (s.2.1 ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ s.2.2 + H))).prod := by
    congr 1
    rw [hsteps', List.map_map]
    refine List.map_congr_left fun s _ => ?_
    simp only [Function.comp_apply]
    congr 2
    rw [Matrix.add_kronecker, smul_one_kronecker_one]
    abel
  have hA' : ∀ s ∈ steps', s.2.1.IsHermitian := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
    exact (hA t ht).add (isHermitian_real_smul_one c)
  have hB' : ∀ s ∈ steps', s.2.2.IsHermitian := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
    exact hB t ht
  have hτ' : ∀ s ∈ steps', 0 ≤ s.1 := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
    exact hτ t ht
  have := arccos_le_entangling_time (H - (c : ℂ) • (1 : Matrix (ι × κ) (ι × κ) ℂ))
    (hH.sub (isHermitian_real_smul_one c)) J hJ steps' hτ' hA' hB' a b ha hb Φ
    (by rw [hexp]; exact hU) lam hlam
  rwa [hmap] at this

/-- (C, spectral half-width) If `‖H − ((m + M)/2) • 1‖ ≤ (M − m)/2` — which holds for Hermitian `H`
with all eigenvalues in `[m, M]`; this spectral fact is taken as a hypothesis — then
`arccos λ ≤ ((M − m)/2) · ∑ τₖ`. For the Heisenberg interaction `XX + YY + ZZ` (spectrum
`{1, −3}`) the half-width is `2`, versus `‖H‖ = 3`. -/
theorem arccos_le_entangling_time_halfWidth (H : Matrix (ι × κ) (ι × κ) ℂ) (hH : H.IsHermitian)
    (m M : ℝ)
    (hspec : ‖H - (((m + M) / 2 : ℝ) : ℂ) • (1 : Matrix (ι × κ) (ι × κ) ℂ)‖ ≤ (M - m) / 2)
    (steps : List (ℝ × Matrix ι ι ℂ × Matrix κ κ ℂ))
    (hτ : ∀ s ∈ steps, 0 ≤ s.1) (hA : ∀ s ∈ steps, s.2.1.IsHermitian)
    (hB : ∀ s ∈ steps, s.2.2.IsHermitian) (a : EuclideanSpace ℂ ι) (b : EuclideanSpace ℂ κ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (Φ : EuclideanSpace ℂ (ι × κ))
    (hU : act (steps.map fun s => exp ((-(s.1 : ℂ) * Complex.I) •
        (s.2.1 ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ s.2.2 + H))).prod
        (prodVec a b) = Φ)
    (lam : ℝ) (hlam : ∀ (x : EuclideanSpace ℂ ι) (y : EuclideanSpace ℂ κ), ‖x‖ = 1 → ‖y‖ = 1 →
        ‖inner ℂ Φ (prodVec x y)‖ ≤ lam) :
    Real.arccos lam ≤ (M - m) / 2 * (steps.map Prod.fst).sum :=
  arccos_le_entangling_time_shift H hH ((m + M) / 2) _ hspec steps hτ hA hB a b ha hb Φ hU lam hlam

/-- (D, shifted) Bell vector: with `‖H − c • 1‖ ≤ J`, preparing `(e_{i₀ j₀} + e_{i₁ j₁}) / √2` from
a unit product vector takes `J · ∑ τₖ ≥ π / 4`. -/
theorem pi_div_four_le_entangling_time_shift (H : Matrix (ι × κ) (ι × κ) ℂ) (hH : H.IsHermitian)
    (c : ℝ) (J : ℝ) (hJ : ‖H - (c : ℂ) • (1 : Matrix (ι × κ) (ι × κ) ℂ)‖ ≤ J)
    (steps : List (ℝ × Matrix ι ι ℂ × Matrix κ κ ℂ))
    (hτ : ∀ s ∈ steps, 0 ≤ s.1) (hA : ∀ s ∈ steps, s.2.1.IsHermitian)
    (hB : ∀ s ∈ steps, s.2.2.IsHermitian) (a : EuclideanSpace ℂ ι) (b : EuclideanSpace ℂ κ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) {i₀ i₁ : ι} {j₀ j₁ : κ} (hi : i₀ ≠ i₁) (hj : j₀ ≠ j₁)
    (hU : act (steps.map fun s => exp ((-(s.1 : ℂ) * Complex.I) •
        (s.2.1 ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ s.2.2 + H))).prod
        (prodVec a b) = bellPair i₀ i₁ j₀ j₁) :
    Real.pi / 4 ≤ J * (steps.map Prod.fst).sum := by
  rw [← arccos_inv_sqrt_two]
  exact arccos_le_entangling_time_shift H hH c J hJ steps hτ hA hB a b ha hb _ hU _
    fun x y hx hy => norm_inner_bellPair_prodVec_le hi hj x y hx hy

end Shift

/-! ### The two-qubit Heisenberg interaction -/

section Heisenberg

/-- The Pauli matrix `X`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
/-- The Pauli matrix `Y`. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
/-- The Pauli matrix `Z`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Heisenberg interaction `X ⊗ X + Y ⊗ Y + Z ⊗ Z` on two qubits. -/
def heisenberg : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  pauliX ⊗ₖ pauliX + pauliY ⊗ₖ pauliY + pauliZ ⊗ₖ pauliZ

/-- The swap of two qubits. -/
private def swapM : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q => if p = q.swap then 1 else 0

private lemma swapM_conj : swapMᴴ = swapM := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [swapM, Matrix.conjTranspose_apply]

private lemma swapM_mul : swapM * swapM = 1 := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [swapM, Matrix.mul_apply]

private lemma swapM_mem : swapM ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, swapM_conj, swapM_mul]

private lemma heisenberg_eq : heisenberg = (2 : ℂ) • swapM - 1 := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [heisenberg, swapM, pauliX, pauliY, pauliZ, Matrix.kroneckerMap_apply] <;>
    norm_num

lemma heisenberg_isHermitian : heisenberg.IsHermitian := by
  rw [Matrix.IsHermitian, heisenberg_eq, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    swapM_conj, Matrix.conjTranspose_one]
  simp

/-- `‖XX + YY + ZZ − (−1) • 1‖ = 2` (the spectral half-width), whereas `‖XX + YY + ZZ‖ = 3`. -/
theorem heisenberg_shift_norm :
    ‖heisenberg - (((-1 : ℝ) : ℂ)) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ = 2 := by
  have : heisenberg - (((-1 : ℝ) : ℂ)) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) =
      (2 : ℂ) • swapM := by
    rw [heisenberg_eq]; push_cast; simp
  rw [this, norm_smul, CStarRing.norm_of_mem_unitary swapM_mem]
  simp

/-- Bell vector under the Heisenberg interaction with arbitrary local control (two qubits, no
ancilla): the total time is at least `π / 8`. Dür–Vidal–Cirac–Linden–Popescu (2001) show that
`π / 8` is achievable for this interaction; only the lower bound is proved here. -/
theorem pi_div_eight_le_heisenberg_time
    (steps : List (ℝ × Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ))
    (hτ : ∀ s ∈ steps, 0 ≤ s.1) (hA : ∀ s ∈ steps, s.2.1.IsHermitian)
    (hB : ∀ s ∈ steps, s.2.2.IsHermitian) (a b : EuclideanSpace ℂ (Fin 2))
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hU : act (steps.map fun s => exp ((-(s.1 : ℂ) * Complex.I) •
        (s.2.1 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) + (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ s.2.2 +
          heisenberg))).prod (prodVec a b) = bellPair 0 1 0 1) :
    Real.pi / 8 ≤ (steps.map Prod.fst).sum := by
  have h := pi_div_four_le_entangling_time_shift heisenberg heisenberg_isHermitian (-1) 2
    heisenberg_shift_norm.le steps hτ hA hB a b ha hb (i₀ := 0) (i₁ := 1) (j₀ := 0) (j₁ := 1)
    (by simp) (by simp) hU
  linarith

end Heisenberg

end QSL.Qudit
