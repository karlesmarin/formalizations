/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.NumberTheory.DirichletCharacter.AbelZero
public import Formalizations.NumberTheory.WeightedCharacterSums.DigitCorollaries
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Zify
public import Mathlib.Tactic.FieldSimp

/-!
# The weighted half sum of an odd Dirichlet character

For `f` odd and `χ` an odd Dirichlet character modulo `f` with values in a field of
characteristic `0`, the weighted half sum `∑_{c=1}^{(f-1)/2} c χ(c)` is
`(f/2) B_{1,χ} (χ(2)⁻¹ − 1)` (a classical identity, found in Kanemitsu–Kuzumaki and in Kučera).
The proof reduces to the ring identities `DigitosII.diag`.

## Main results

* `DiagKK.thm_diag`: `∑_{c=1}^{(f-1)/2} c χ(c) = (f/2) B_{1,χ} (χ(2)⁻¹ − 1)`, with
  `B_{1,χ} = f⁻¹ ∑_{a ∈ ZMod f} χ(a) a.val` (`ConjeturaC.B1`).
* `DiagKK.thm_diag_half`: the unweighted sum, `∑_{c ≤ (f-1)/2} χ(c) = (χ(2)⁻¹ − 2) B_{1,χ}`.
* `DiagKK.thm_diag_iff`: if `B_{1,χ} ≠ 0`, the weighted half sum vanishes iff `χ(2) = 1`.

`B_{1,χ} ≠ 0` for primitive `χ` (it is `−L(0, χ)`) is a hypothesis here: at the pinned commit
Mathlib has no value of a Dirichlet `L`-function at `s = 0` for odd `χ` (`hurwitzZeta_neg_nat`
excludes `k = 0`).

## References

* C. Marín, *Zeros of weighted partial sums of completely multiplicative functions: Dirichlet
  characters, the Euler factor at 2 and Conrey's sine series*, Zenodo (2026),
  doi:10.5281/zenodo.22847374.
-/

@[expose] public section

open Finset

namespace DiagKK

/-! The sums `C`, `T`, `Tq` and the ring identities `DigitosII.diag` are those of
`Formalizations.NumberTheory.WeightedCharacterSums.DigitCorollaries`. -/

open DigitosII (C T Tq T_succ C_succ T_range C_range reflect sum_range_two_mul diag)

/-! ## The Dirichlet-character statement -/

section Field

variable {K : Type*} [Field K]

open ConjeturaC (B1 sum_zmod_eq_sum_range)

/-- The bridge: the hypotheses of `diag` for `n ↦ χ(n mod f)`, and `T_f = f B_{1,χ}`. -/
lemma bridge (c : ℕ) (χ : DirichletCharacter K (2 * c + 1)) (hodd : χ.Odd) :
    let χn : ℕ → K := fun n => χ (n : ZMod (2 * c + 1))
    (∀ a b, χn (a * b) = χn a * χn b) ∧
    (∀ j r, 1 ≤ r → r < 2 * c + 1 → χn (j * (2 * c + 1) + r) = χn r) ∧
    χn (2 * c) = -1 ∧
    Tq χn (2 * c + 1) = ∑ a : ZMod (2 * c + 1), χ a * (a.val : K) := by
  intro χn
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b; simp only [χn, Nat.cast_mul, map_mul]
  · intro j r _ _
    simp only [χn]
    have hz : ((2 * c + 1 : ℕ) : ZMod (2 * c + 1)) = 0 := ZMod.natCast_self _
    push_cast at hz ⊢
    rw [hz]
    simp
  · simp only [χn]
    have h : ((2 * c : ℕ) : ZMod (2 * c + 1)) = -1 := by
      rw [eq_neg_iff_add_eq_zero]
      have := ZMod.natCast_self (2 * c + 1)
      push_cast at this ⊢
      exact this
    rw [h]; exact hodd
  · rw [sum_zmod_eq_sum_range, sum_range_succ', Tq, Nat.add_sub_cancel, T_range]
    simp only [χn, Nat.cast_zero, ZMod.val_zero, mul_zero, add_zero]
    refine sum_congr rfl (fun n hn => ?_)
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by have := mem_range.1 hn; omega)]
    push_cast; ring

/-- `χ(2) ≠ 0` for `f` odd. -/
lemma chi_two_ne_zero (c : ℕ) (χ : DirichletCharacter K (2 * c + 1)) : χ 2 ≠ 0 := by
  have hcop : Nat.Coprime 2 (2 * c + 1) := by
    rw [Nat.coprime_comm, Nat.coprime_two_right]; exact ⟨c, rfl⟩
  have hu : IsUnit (2 : ZMod (2 * c + 1)) := by
    have := (ZMod.unitOfCoprime 2 hcop).isUnit
    rwa [ZMod.coe_unitOfCoprime, Nat.cast_ofNat] at this
  exact (hu.map χ).ne_zero

variable [CharZero K]

/-- The three identities of the proof, for an odd Dirichlet character modulo `f = 2c+1`. -/
lemma diag_char (c : ℕ) (χ : DirichletCharacter K (2 * c + 1)) (hχ : χ.Odd) :
    ∑ n ∈ Icc 1 c, (n : K) * χ n = ((2 * c + 1 : ℕ) : K) / 2 * B1 χ * ((χ 2)⁻¹ - 1) ∧
    ∑ n ∈ Icc 1 c, χ n = ((χ 2)⁻¹ - 2) * B1 χ := by
  obtain ⟨hm, hp, ho, hT⟩ := bridge c χ hχ
  obtain ⟨d1, d2, -⟩ := diag (c := c) (χ := fun n : ℕ => χ (n : ZMod (2 * c + 1))) hm hp ho
  have h2 : χ ((2 : ℕ) : ZMod (2 * c + 1)) = χ 2 := by rw [Nat.cast_ofNat]
  simp only [h2] at d1 d2
  rw [hT] at d1 d2
  have hχ2 := chi_two_ne_zero c χ
  have hf : ((2 * c + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hS : ∑ a : ZMod (2 * c + 1), χ a * (a.val : K) = ((2 * c + 1 : ℕ) : K) * B1 χ := by
    rw [B1, ← mul_assoc, mul_inv_cancel₀ hf, one_mul]
  rw [hS] at d1 d2
  change T _ c = _ ∧ C _ c = _
  constructor
  · apply mul_left_cancel₀ (show (4 * χ 2 : K) ≠ 0 from mul_ne_zero (by norm_num) hχ2)
    rw [d1]
    field_simp
    ring
  · apply mul_left_cancel₀ (show ((2 * c + 1 : ℕ) : K) * χ 2 ≠ 0 from mul_ne_zero hf hχ2)
    push_cast at d2 hf ⊢
    rw [d2]
    field_simp

/-- **`thm:diag` (4.2)**, the displayed formula. `f` odd, `χ` an odd Dirichlet character modulo
`f` with values in a field of characteristic `0`:
`∑_{c=1}^{(f-1)/2} c χ(c) = (f/2) B_{1,χ} (χ(2)⁻¹ - 1)`. -/
theorem thm_diag {f : ℕ} [NeZero f] (hf : Odd f) (χ : DirichletCharacter K f) (hχ : χ.Odd) :
    ∑ n ∈ Icc 1 ((f - 1) / 2), (n : K) * χ n = (f : K) / 2 * B1 χ * ((χ 2)⁻¹ - 1) := by
  obtain ⟨c, rfl⟩ := hf
  rw [show (2 * c + 1 - 1) / 2 = c by omega]
  exact (diag_char c χ hχ).1

/-- The unweighted twin from the proof of `thm:diag`:
`∑_{c=1}^{(f-1)/2} χ(c) = (χ(2)⁻¹ - 2) B_{1,χ}`. -/
theorem thm_diag_half {f : ℕ} [NeZero f] (hf : Odd f) (χ : DirichletCharacter K f)
    (hχ : χ.Odd) :
    ∑ n ∈ Icc 1 ((f - 1) / 2), χ n = ((χ 2)⁻¹ - 2) * B1 χ := by
  obtain ⟨c, rfl⟩ := hf
  rw [show (2 * c + 1 - 1) / 2 = c by omega]
  exact (diag_char c χ hχ).2

/-- **`thm:diag` (4.2)**, second sentence, with `B_{1,χ} ≠ 0` as hypothesis (the paper obtains it
from primitivity, `B_{1,χ} = -L(0,χ) ≠ 0`; not formalized): the weighted half sum vanishes iff
`χ(2) = 1`. -/
theorem thm_diag_iff {f : ℕ} [NeZero f] (hf : Odd f) (χ : DirichletCharacter K f) (hχ : χ.Odd)
    (hB : B1 χ ≠ 0) :
    ∑ n ∈ Icc 1 ((f - 1) / 2), (n : K) * χ n = 0 ↔ χ 2 = 1 := by
  rw [thm_diag hf χ hχ]
  obtain ⟨c, rfl⟩ := hf
  have hχ2 := chi_two_ne_zero c χ
  have hf0 : ((2 * c + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  constructor
  · intro h
    have h' : (χ 2)⁻¹ - 1 = 0 := by
      rcases mul_eq_zero.mp h with h | h
      · exfalso
        rcases mul_eq_zero.mp h with h | h
        · exact hf0 (by simpa using h)
        · exact hB h
      · exact h
    have : (χ 2)⁻¹ = 1 := sub_eq_zero.mp h'
    exact inv_eq_one.mp this
  · intro h; rw [h]; simp

end Field

end DiagKK

