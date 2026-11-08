/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate

/-!
# The `P`-height and the height of the coroot

For a finite crystallographic root pairing `P` over a field of characteristic `0` with a base `b`
and the canonical invariant form `P.RootForm`, write `q i = (α_i, α_i)`.  For `α = ∑ c_j α_j`:

* `RootPairing.Base.coroot_coeffs`: `α^∨ = ∑ c_j · ((α_j, α_j)/(α, α)) · α_j^∨`.
* `RootPairing.Base.pheight` is `∑ c_j (α_j, α_j)/2` and
  `RootPairing.Base.pheight_eq`: `ht_P α = ((α, α)/2) · ht(α^∨)`, the height of `α^∨` being taken
  w.r.t. the base `b.flip` of coroots.
* `RootPairing.Base.pheight_eq_rootForm`: `ht_P α = (ρ, α)` for any `ρ` with `⟨ρ, α_j^∨⟩ = 1`.
* `RootPairing.Base.obs_types`: arithmetic part of Observation 13.1 (`obs:types`) of the note
  `characters_at_aP`, under the length dichotomy `(α, α)/2 ∈ {1, r}`.

## References

* C. Marín, *Characters at a_P*, §13 (Observation 13.1).
-/

@[expose] public section

open Finset Submodule

set_option linter.unusedSectionVars false

namespace RootPairing.Base

variable {ι R M N : Type*} [Field R] [CharZero R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Fintype ι] {P : RootPairing ι R M N} (b : P.Base)

/-- Uniqueness of coordinates (over `R`) in the roots of the base. -/
lemma eq_of_sum_root_eq {a a' : ι → R}
    (h : ∑ j ∈ b.support, a j • P.root j = ∑ j ∈ b.support, a' j • P.root j) :
    ∀ j ∈ b.support, a j = a' j := by
  rw [b.support.sum_subtype (p := (· ∈ b.support)) (by simp) (F := inferInstance),
    b.support.sum_subtype (p := (· ∈ b.support)) (by simp) (F := inferInstance)] at h
  have aux (j : b.support) := Fintype.linearIndependent_iffₛ.mp
    b.linearIndepOn_root (a ∘ (↑)) (a' ∘ (↑)) (by simpa using h) j
  intro j hj
  simpa using aux ⟨j, hj⟩

lemma rootForm_self_smul_coroot' (i : ι) :
    P.RootForm (P.root i) (P.root i) • P.coroot i = (2 : R) • P.Polarization (P.root i) := by
  rw [P.rootForm_self_smul_coroot i]
  simp [ofNat_smul_eq_nsmul]

/-- **Objective 1.**  If `α = ∑ c_j α_j` then `α^∨ = ∑ c_j · ((α_j, α_j)/(α, α)) · α_j^∨`. -/
theorem coroot_coeffs [P.IsCrystallographic] {i : ι} {c : ι → ℤ}
    (hc : P.root i = ∑ j ∈ b.support, c j • P.root j) :
    P.coroot i = ∑ j ∈ b.support,
      ((c j : R) * (P.RootForm (P.root j) (P.root j) / P.RootForm (P.root i) (P.root i))) •
        P.coroot j := by
  have hne : P.RootForm (P.root i) (P.root i) ≠ 0 := IsAnisotropic.rootForm_root_ne_zero i
  have h1 : P.RootForm (P.root i) (P.root i) • P.coroot i =
      ∑ j ∈ b.support, ((c j : R) * P.RootForm (P.root j) (P.root j)) • P.coroot j := by
    rw [rootForm_self_smul_coroot', hc]
    simp only [map_sum, map_zsmul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj := rootForm_self_smul_coroot' (P := P) j
    rw [mul_smul, ← Int.cast_smul_eq_zsmul R (c j), smul_comm (2 : R), ← hj]
  apply smul_right_injective N hne
  simp only [h1, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  field_simp

/-- The `P`-height of `α_i = ∑ c_j α_j`: `∑ c_j (α_j, α_j)/2`. -/
noncomputable def pheight (i : ι) : R :=
  ∑ j ∈ b.support, ((b.exists_root_eq_sum_int i).choose j : R) *
    (P.RootForm (P.root j) (P.root j) / 2)

/-- **Objective 2.**  `ht_P(α) = ((α, α)/2) · ht(α^∨)`, `ht(α^∨)` taken w.r.t. the base `b.flip`. -/
theorem pheight_eq [P.IsCrystallographic] (i : ι) :
    b.pheight i = (P.RootForm (P.root i) (P.root i) / 2) * (b.flip.height i : R) := by
  have hne : P.RootForm (P.root i) (P.root i) ≠ 0 := IsAnisotropic.rootForm_root_ne_zero i
  obtain ⟨-, -, hc⟩ := (b.exists_root_eq_sum_int i).choose_spec
  obtain ⟨-, -, hf⟩ := (b.flip.exists_root_eq_sum_int i).choose_spec
  set c := (b.exists_root_eq_sum_int i).choose
  set f := (b.flip.exists_root_eq_sum_int i).choose
  have hcc := b.coroot_coeffs hc
  have hht : b.flip.height i = ∑ j ∈ b.support, f j := height_eq_sum hf
  have key : ∀ j ∈ b.support, (f j : R) =
      (c j : R) * (P.RootForm (P.root j) (P.root j) / P.RootForm (P.root i) (P.root i)) := by
    refine b.flip.eq_of_sum_root_eq (a := fun j => (f j : R))
      (a' := fun j => (c j : R) * (P.RootForm (P.root j) (P.root j) /
        P.RootForm (P.root i) (P.root i))) ?_
    change ∑ j ∈ b.support, (f j : R) • P.coroot j = ∑ j ∈ b.support,
      ((c j : R) * (P.RootForm (P.root j) (P.root j) /
        P.RootForm (P.root i) (P.root i))) • P.coroot j
    rw [← hcc]
    simpa [Int.cast_smul_eq_zsmul R] using hf.symm
  have hp : b.pheight i = ∑ j ∈ b.support, (c j : R) *
      (P.RootForm (P.root j) (P.root j) / 2) := rfl
  rw [hht, hp, Int.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [key j hj]
  field_simp

lemma rootForm_apply_root (ρ : M) (j : ι) :
    P.RootForm ρ (P.root j) =
      P.RootForm (P.root j) (P.root j) / 2 * P.coroot' j ρ := by
  have h := congrArg (P.toLinearMap ρ) (rootForm_self_smul_coroot' (P := P) j)
  rw [map_smul, map_smul, P.toLinearMap_apply_apply_Polarization] at h
  have hs : P.RootForm (P.root j) ρ = P.RootForm ρ (P.root j) := P.rootForm_symmetric.eq _ _
  rw [hs] at h
  have h2 : P.toLinearMap ρ (P.coroot j) = P.coroot' j ρ := rfl
  rw [h2] at h
  simp only [smul_eq_mul] at h
  linear_combination (-1 / 2 : R) * h

/-- `ht_P(α) = (ρ, α)` for any `ρ` with `⟨ρ, α_j^∨⟩ = 1` on the base. -/
theorem pheight_eq_rootForm (ρ : M) (hρ : ∀ j ∈ b.support, P.coroot' j ρ = 1) (i : ι) :
    b.pheight i = P.RootForm ρ (P.root i) := by
  obtain ⟨-, -, hc⟩ := (b.exists_root_eq_sum_int i).choose_spec
  set c := (b.exists_root_eq_sum_int i).choose
  conv_rhs => rw [hc]
  rw [map_sum, pheight]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [map_zsmul, rootForm_apply_root (P := P) ρ j, hρ j hj, mul_one, zsmul_eq_mul]

/-- Arithmetic core of Observation 13.1: `h = ht(α^∨)`, `s = (α, α)/2 ∈ {1, r}`. -/
theorem obs_types_arith {s r h q : ℤ} (hs : s = 1 ∨ s = r) :
    (q ∣ h → q ∣ s * h) ∧
    ((q ∣ s * h ∧ ¬ q ∣ h) ↔ (s = r ∧ q ∣ r * h ∧ ¬ q ∣ h)) ∧
    (Int.gcd q r = 1 → (q ∣ s * h ↔ q ∣ h)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hq
    rcases hs with rfl | rfl
    · simpa using hq
    · exact Dvd.dvd.mul_left hq _
  · constructor
    · rintro ⟨h1, h2⟩
      rcases hs with rfl | rfl
      · exact absurd (by simpa using h1) h2
      · exact ⟨rfl, h1, h2⟩
    · rintro ⟨rfl, h1, h2⟩
      exact ⟨h1, h2⟩
  · intro hg
    have hc : IsCoprime q r := Int.isCoprime_iff_gcd_eq_one.mpr hg
    rcases hs with rfl | rfl
    · simp
    · exact ⟨fun hd => hc.dvd_of_dvd_mul_left hd, fun hd => Dvd.dvd.mul_left hd _⟩

/-- **Objective 3** (`obs_types`, arithmetic part, on the system).  Hypothesis: the length
dichotomy `(α, α)/2 = s i ∈ {1, r}` for all roots (short roots normalised to `1`). -/
theorem obs_types [P.IsCrystallographic] {s : ι → ℤ} {r : ℤ}
    (hs : ∀ i, P.RootForm (P.root i) (P.root i) = 2 * (s i : R))
    (hr : ∀ i, s i = 1 ∨ s i = r) (q : ℤ) (i : ι) :
    b.pheight i = ((s i * b.flip.height i : ℤ) : R) ∧
    (q ∣ b.flip.height i → q ∣ s i * b.flip.height i) ∧
    ((q ∣ s i * b.flip.height i ∧ ¬ q ∣ b.flip.height i) ↔
      (s i = r ∧ q ∣ r * b.flip.height i ∧ ¬ q ∣ b.flip.height i)) ∧
    (Int.gcd q r = 1 → (q ∣ s i * b.flip.height i ↔ q ∣ b.flip.height i)) := by
  refine ⟨?_, obs_types_arith (hr i)⟩
  rw [pheight_eq, hs i]
  push_cast
  ring

end RootPairing.Base
