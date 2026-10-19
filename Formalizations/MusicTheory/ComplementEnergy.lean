/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Complement transport for symmetric pair energies

For a symmetric weight `W` on a finite type, the energy `energy W A = (∑ a ∈ A, ∑ b ∈ A, W a b) / 2`
of a set and that of its complement differ by a term depending on the row sums of `W` over `A`.
When all row sums are equal, energy gaps between sets of the same size are invariant under
complementation, and minimizers among sets of a given size correspond to minimizers among their
complements; with zero diagonal, this property characterizes constant row sums.

## Main results

* `energy_compl_sub`, `energy_compl_regular`.
* `energy_gap_compl`, `minimizer_compl_iff`.
* `regular_iff_complement_gaps`, `regular_iff_complement_minimizers`.

## References

* N. Bushaw, B. Cody, C. Leffler, *Sets of vertices with extremal energy*, arXiv:2407.18785,
  Theorem 3.5.
-/

@[expose] public section

namespace MusicTheory

open Finset

namespace ComplementEnergy

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Half the ordered interaction sum. For symmetric W with zero diagonal this is
    the usual unordered all-pairs energy. -/
noncomputable def energy (W : α → α → ℝ) (A : Finset α) : ℝ :=
  (∑ a ∈ A, ∑ b ∈ A, W a b) / 2

/-- The total interaction seen from one site. -/
noncomputable def rowSum (W : α → α → ℝ) (a : α) : ℝ := ∑ b, W a b

def IsSymmetric (W : α → α → ℝ) : Prop := ∀ a b, W a b = W b a

def IsRegular (W : α → α → ℝ) : Prop := ∀ a b, rowSum W a = rowSum W b

/-- Global minimization among sets of the same cardinality. -/
def IsMinimizer (W : α → α → ℝ) (A : Finset α) : Prop :=
  ∀ B : Finset α, B.card = A.card → energy W A ≤ energy W B

omit [Fintype α] [DecidableEq α] in
theorem cross_sum_symm (W : α → α → ℝ) (hW : IsSymmetric W) (A B : Finset α) :
    (∑ a ∈ A, ∑ b ∈ B, W a b) = ∑ b ∈ B, ∑ a ∈ A, W b a := by
  rw [sum_comm]
  exact sum_congr rfl (fun b _ => sum_congr rfl (fun a _ => hW a b))

/-- The complement identity before any regularity hypothesis. -/
theorem energy_compl_sub (W : α → α → ℝ) (hW : IsSymmetric W) (A : Finset α) :
    energy W Aᶜ - energy W A = energy W univ - ∑ a ∈ A, rowSum W a := by
  have hr : (∑ a ∈ A, rowSum W a) =
      (∑ a ∈ A, ∑ b ∈ A, W a b) + ∑ a ∈ A, ∑ b ∈ Aᶜ, W a b := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun a _ => (sum_add_sum_compl A (W a)).symm)
  have hr' : (∑ a ∈ Aᶜ, rowSum W a) =
      (∑ a ∈ Aᶜ, ∑ b ∈ A, W a b) + ∑ a ∈ Aᶜ, ∑ b ∈ Aᶜ, W a b := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun a _ => (sum_add_sum_compl A (W a)).symm)
  have ht := sum_add_sum_compl A (rowSum W)
  rw [hr, hr', ← cross_sum_symm W hW A Aᶜ] at ht
  unfold energy
  change _ = (∑ a, rowSum W a) / 2 - _
  rw [← ht, hr]
  ring

/-- A constant weighted degree makes the complement correction depend only on cardinality. -/
theorem energy_compl_regular (W : α → α → ℝ) (hW : IsSymmetric W)
    (r : ℝ) (hr : ∀ a, rowSum W a = r) (A : Finset α) :
    energy W Aᶜ - energy W A = energy W univ - (A.card : ℝ) * r := by
  rw [energy_compl_sub W hW]
  simp only [hr, sum_const, nsmul_eq_mul]

omit [DecidableEq α] in
theorem regular_has_constant (W : α → α → ℝ) (hW : IsRegular W) :
    ∃ r : ℝ, ∀ a, rowSum W a = r := by
  classical
  by_cases h : Nonempty α
  · let a := Classical.choice h
    exact ⟨rowSum W a, fun b => hW b a⟩
  · exact ⟨0, fun a => False.elim (h ⟨a⟩)⟩

/-- Equal-cardinality energy differences survive complementation unchanged. -/
theorem energy_gap_compl (W : α → α → ℝ) (hW : IsSymmetric W) (hr : IsRegular W)
    (A B : Finset α) (hcard : A.card = B.card) :
    energy W Aᶜ - energy W Bᶜ = energy W A - energy W B := by
  obtain ⟨r, hr⟩ := regular_has_constant W hr
  have ha := energy_compl_regular W hW r hr A
  have hb := energy_compl_regular W hW r hr B
  rw [hcard] at ha
  linarith

theorem energy_le_compl_iff (W : α → α → ℝ) (hW : IsSymmetric W) (hr : IsRegular W)
    (A B : Finset α) (hcard : A.card = B.card) :
    energy W Aᶜ ≤ energy W Bᶜ ↔ energy W A ≤ energy W B := by
  have h := energy_gap_compl W hW hr A B hcard
  constructor <;> intro hh <;> linarith

/-- Both directions of the global minimizer correspondence. -/
theorem minimizer_compl_iff (W : α → α → ℝ) (hW : IsSymmetric W) (hr : IsRegular W)
    (A : Finset α) : IsMinimizer W Aᶜ ↔ IsMinimizer W A := by
  constructor
  · intro h B hB
    apply (energy_le_compl_iff W hW hr A B hB.symm).mp
    apply h Bᶜ
    simp only [card_compl, hB]
  · intro h B hB
    have hc : Bᶜ.card = A.card := by
      have h1 := card_add_card_compl A
      have h2 := card_add_card_compl B
      omega
    have he := (energy_le_compl_iff W hW hr A Bᶜ hc.symm).mpr (h Bᶜ hc)
    simpa only [compl_compl] using he

/-- Regularity is exactly what makes all equal-cardinality energy gaps complement-invariant. -/
theorem regular_iff_complement_gaps (W : α → α → ℝ) (hW : IsSymmetric W) :
    IsRegular W ↔ ∀ A B : Finset α, A.card = B.card →
      energy W Aᶜ - energy W Bᶜ = energy W A - energy W B := by
  constructor
  · exact energy_gap_compl W hW
  · intro h a b
    have ha := energy_compl_sub W hW {a}
    have hb := energy_compl_sub W hW {b}
    have hab := h {a} {b} (by simp)
    simp only [sum_singleton] at ha hb
    linarith

omit [Fintype α] [DecidableEq α] in
theorem energy_singleton (W : α → α → ℝ) (hdiag : ∀ a, W a a = 0) (a : α) :
    energy W {a} = 0 := by simp [energy, hdiag]

omit [Fintype α] [DecidableEq α] in
theorem singleton_minimizer (W : α → α → ℝ) (hdiag : ∀ a, W a a = 0) (a : α) :
    IsMinimizer W {a} := by
  intro B hB
  have hcard : B.card = 1 := by simpa using hB
  obtain ⟨b, rfl⟩ := card_eq_one.mp hcard
  simp only [energy_singleton W hdiag, le_refl]

/-- With zero diagonal, preserving all global minimizers forces constant weighted degree.
    The converse is witnessed already by complements of singleton sets. -/
theorem regular_iff_complement_minimizers (W : α → α → ℝ) (hW : IsSymmetric W)
    (hdiag : ∀ a, W a a = 0) :
    IsRegular W ↔ ∀ A : Finset α, IsMinimizer W A → IsMinimizer W Aᶜ := by
  constructor
  · intro hr A hA
    exact (minimizer_compl_iff W hW hr A).mpr hA
  · intro h a b
    have hca := h {a} (singleton_minimizer W hdiag a)
    have hcb := h {b} (singleton_minimizer W hdiag b)
    have hcards : ({a}ᶜ : Finset α).card = ({b}ᶜ : Finset α).card := by
      simp only [card_compl, card_singleton]
    have hab := hca {b}ᶜ hcards.symm
    have hba := hcb {a}ᶜ hcards
    have ha := energy_compl_sub W hW {a}
    have hb := energy_compl_sub W hW {b}
    simp only [energy_singleton W hdiag, sum_singleton, sub_zero] at ha hb
    linarith

end ComplementEnergy

end MusicTheory
