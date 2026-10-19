/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Formalizations.Physics.Particles.GaugeHiggsUnification.NotchCentreCharge

/-!
# The blind set of the boundary-condition sign and its count

A bulk `SU(4)` irrep is a partition `λ = (l₁, l₂, l₃, 0)` with `l₁ ≥ l₂ ≥ l₃ ≥ 0`. The
reflection-coset character is `D_λ(t) = s_λ(1, −1, t, 1/t)` and the boundary-condition sign `η`
acts by `D ↦ η D`, so `η` is unobservable on `λ` iff `D_λ = 0`. In Dynkin coordinates `(a, b, c)`
with `λ = (a+b+c, b+c, c, 0)`, `GaugeHiggsUnification.NotchCentreCharge.notch_degenerate_iff`
gives the vanishing criterion `N a b c = 0 ↔ Odd b ∧ ((Odd a ∧ Odd c) ∨ a = c)`. This file writes
that set (the blind set) in partition coordinates and counts it.

## Main results

* `Blind`: the blind set as two branches: (a) `l₁` odd, `l₂` even, `l₃` odd; (b) `l₁` odd, `l₂`
  odd, `l₃` even with `l₂ + l₃ = l₁`.
* `blind_iff_notch`: on `l₁ ≥ l₂ ≥ l₃` this is the Dynkin-coordinate criterion.
* `blind_iff_N_zero`: `Blind` holds iff the bialternant determinant `N` vanishes.
* `blind_l1_odd`: `l₁` is odd on the whole blind set.
* `card_shell`: the blind partitions with `l₁ = 2k+1` number `⌈(k+1)²/2⌉`. The parity of `l₂`
  splits them into the two branches: branch (a) is the strict pairs `q < p ≤ k` (a triangular
  number, via `Finset.sum_range_id_mul_two`) and branch (b) is the interval `m ≤ k/2`.

## References

* C. Marín, *What the Higgs Potential Cannot See: Bulk Matter That Cannot Help Select a
  Boundary Condition (Part V)*, Zenodo, doi:10.5281/zenodo.21727094.
-/

@[expose] public section

namespace GaugeHiggsUnification.BlindCount

open Finset

/-! ### The blind set in partition coordinates -/

/-- `Blind l₁ l₂ l₃`: the boundary sign `η` is unobservable on `λ = (l₁,l₂,l₃,0)`.
Branch (a) is `l₁` odd, `l₂` even, `l₃` odd; branch (b) is `l₁` odd, `l₂` odd,
`l₃` even with `l₂ + l₃ = l₁`.  Stated with `% 2` rather than `Odd`/`Even` so that
the predicate is decidable by `decide` and native to `omega`. -/
def Blind (l₁ l₂ l₃ : ℕ) : Prop :=
  (l₁ % 2 = 1 ∧ l₂ % 2 = 0 ∧ l₃ % 2 = 1) ∨
  (l₁ % 2 = 1 ∧ l₂ % 2 = 1 ∧ l₃ % 2 = 0 ∧ l₂ + l₃ = l₁)

instance (l₁ l₂ l₃ : ℕ) : Decidable (Blind l₁ l₂ l₃) := by unfold Blind; infer_instance

/-- `l₁` is odd on the whole blind set: half the bulk spectrum cannot be blind. -/
theorem blind_l1_odd {l₁ l₂ l₃ : ℕ} (h : Blind l₁ l₂ l₃) : Odd l₁ := by
  rw [Nat.odd_iff]; rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> exact h

/-- The `Odd`/`Even` restatement, for reading against the paper. -/
theorem blind_iff_parity (l₁ l₂ l₃ : ℕ) :
    Blind l₁ l₂ l₃ ↔
      (Odd l₁ ∧ Even l₂ ∧ Odd l₃) ∨ (Odd l₁ ∧ Odd l₂ ∧ Even l₃ ∧ l₂ + l₃ = l₁) := by
  simp only [Blind, Nat.odd_iff, Nat.even_iff]

/-! ### The dictionary to Dynkin coordinates -/

/-- The dictionary.  With `a = l₁ - l₂`, `b = l₂ - l₃`, `c = l₃` (the inverse of
`λ = (a+b+c, b+c, c, 0)`), the partition-coordinate description of the blind set is
the Dynkin-coordinate criterion certified in `NotchCentreCharge`. -/
theorem blind_iff_notch {l₁ l₂ l₃ : ℕ} (h₃ : l₃ ≤ l₂) (h₂ : l₂ ≤ l₁) :
    Blind l₁ l₂ l₃ ↔
      (Odd (l₂ - l₃) ∧ ((Odd (l₁ - l₂) ∧ Odd l₃) ∨ l₁ - l₂ = l₃)) := by
  simp only [Blind, Nat.odd_iff]
  omega

/-- The bridge: `η` is unobservable on `λ` exactly when the bialternant
determinant certified in `NotchCentreCharge` vanishes. -/
theorem blind_iff_N_zero {l₁ l₂ l₃ : ℕ} (h₃ : l₃ ≤ l₂) (h₂ : l₂ ≤ l₁) :
    Blind l₁ l₂ l₃ ↔ NotchCentreCharge.N (l₁ - l₂) (l₂ - l₃) l₃ = 0 := by
  rw [NotchCentreCharge.notch_degenerate_iff, blind_iff_notch h₃ h₂]

/-! ### The shell at `l₁ = 2k+1` -/

/-- The blind partitions with `λ₁ = 2k+1`, recorded as the pair `(λ₂, λ₃)`. -/
def shell (k : ℕ) : Finset (ℕ × ℕ) :=
  ((range (2 * k + 2)) ×ˢ (range (2 * k + 2))).filter
    (fun p => p.2 ≤ p.1 ∧ Blind (2 * k + 1) p.1 p.2)

/-- Membership in the shell, unfolded. -/
theorem mem_shell {k : ℕ} {p : ℕ × ℕ} :
    p ∈ shell k ↔ p.1 ≤ 2 * k + 1 ∧ p.2 ≤ p.1 ∧ Blind (2 * k + 1) p.1 p.2 := by
  rw [shell, mem_filter, mem_product, mem_range, mem_range]
  constructor
  · rintro ⟨⟨h1, -⟩, h2, h3⟩; exact ⟨by omega, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨by omega, by omega⟩, h2, h3⟩

/-- Branch (a): `λ₂` even.  Parametrised by `q < p ≤ k` via `(λ₂,λ₃) = (2p, 2q+1)`. -/
def shellA (k : ℕ) : Finset (ℕ × ℕ) :=
  (range (k + 1)).biUnion (fun p => (range p).image (fun q => (2 * p, 2 * q + 1)))

/-- Branch (b): `λ₂` odd.  Parametrised by `m ≤ k/2` via `(λ₂,λ₃) = (2k+1-2m, 2m)`. -/
def shellB (k : ℕ) : Finset (ℕ × ℕ) :=
  (range (k / 2 + 1)).image (fun m => (2 * k + 1 - 2 * m, 2 * m))

theorem mem_shellA {k : ℕ} {p : ℕ × ℕ} :
    p ∈ shellA k ↔ ∃ a b, b < a ∧ a ≤ k ∧ p = (2 * a, 2 * b + 1) := by
  simp only [shellA, mem_biUnion, mem_image, mem_range]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, b, hb, by omega, rfl⟩
  · rintro ⟨a, b, hb, ha, rfl⟩; exact ⟨a, by omega, b, hb, rfl⟩

theorem mem_shellB {k : ℕ} {p : ℕ × ℕ} :
    p ∈ shellB k ↔ ∃ m, m ≤ k / 2 ∧ p = (2 * k + 1 - 2 * m, 2 * m) := by
  simp only [shellB, mem_image, mem_range]
  constructor
  · rintro ⟨m, hm, rfl⟩; exact ⟨m, by omega, rfl⟩
  · rintro ⟨m, hm, rfl⟩; exact ⟨m, by omega, rfl⟩

/-- The parity of `λ₂` splits the shell into exactly the two branches: the even
part is branch (a). -/
theorem filter_even_shell (k : ℕ) :
    (shell k).filter (fun p => p.1 % 2 = 0) = shellA k := by
  ext p
  simp only [mem_filter, mem_shell, mem_shellA, Blind]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, hev⟩
    refine ⟨p.1 / 2, p.2 / 2, ?_, ?_, ?_⟩ <;> [omega; omega; (rcases p; simp; omega)]
  · rintro ⟨a, b, hb, ha, rfl⟩
    exact ⟨⟨by omega, by omega, by omega⟩, by omega⟩

/-- ... and the odd part is branch (b). -/
theorem filter_odd_shell (k : ℕ) :
    (shell k).filter (fun p => ¬ p.1 % 2 = 0) = shellB k := by
  ext p
  simp only [mem_filter, mem_shell, mem_shellB, Blind]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, hod⟩
    refine ⟨p.2 / 2, ?_, ?_⟩ <;> [omega; (rcases p; simp; omega)]
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨by omega, by omega, by omega⟩, by omega⟩

/-! ### The two cardinals -/

theorem card_shellA (k : ℕ) : (shellA k).card * 2 = (k + 1) * k := by
  have hdisj : ∀ x ∈ range (k + 1), ∀ y ∈ range (k + 1), x ≠ y →
      Disjoint ((range x).image (fun q => (2 * x, 2 * q + 1)))
               ((range y).image (fun q => (2 * y, 2 * q + 1))) := by
    intro x _ y _ hxy
    simp only [Finset.disjoint_left, mem_image, mem_range]
    rintro p ⟨q, -, rfl⟩ ⟨q', -, hq'⟩
    simp only [Prod.mk.injEq] at hq'
    exact hxy (by omega)
  have hinj : ∀ p : ℕ, ((range p).image (fun q => (2 * p, 2 * q + 1))).card = p := by
    intro p
    have hi : Function.Injective (fun q : ℕ => ((2 * p, 2 * q + 1) : ℕ × ℕ)) := by
      intro q q' h
      simp only [Prod.mk.injEq] at h
      omega
    rw [Finset.card_image_of_injective _ hi, card_range]
  rw [shellA, Finset.card_biUnion hdisj]
  simp only [hinj]
  rw [Finset.sum_range_id_mul_two (k + 1)]
  simp

theorem card_shellB (k : ℕ) : (shellB k).card = k / 2 + 1 := by
  rw [shellB, Finset.card_image_of_injOn, card_range]
  intro x hx y hy h
  simp only [Prod.mk.injEq] at h
  omega

/-! ### The count -/

/-- **Proposition (Part V).**  The blind partitions with `λ₁ = 2k+1` number
`⌈(k+1)²/2⌉`.  Together with `blind_l1_odd` (no even `λ₁` is ever blind) this is
the complete census of the blind set shell by shell. -/
theorem card_shell (k : ℕ) : (shell k).card = ((k + 1) ^ 2 + 1) / 2 := by
  have hsplit : ((shell k).filter (fun p => p.1 % 2 = 0)).card
      + ((shell k).filter (fun p => ¬ p.1 % 2 = 0)).card = (shell k).card :=
    Finset.card_filter_add_card_filter_not _
  rw [filter_even_shell, filter_odd_shell] at hsplit
  have hA := card_shellA k
  have hB := card_shellB k
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
  · have e1 : (2 * m + 1) ^ 2 = 4 * (m * m) + 4 * m + 1 := by ring
    have e2 : (2 * m + 1) * (2 * m) = 4 * (m * m) + 2 * m := by ring
    omega
  · have e1 : (2 * m + 1 + 1) ^ 2 = 4 * (m * m) + 8 * m + 4 := by ring
    have e2 : (2 * m + 1 + 1) * (2 * m + 1) = 4 * (m * m) + 6 * m + 2 := by ring
    omega

/-! ### Sanity checks -/

-- The first five shells: 1, 2, 5, 8, 13.
example : (shell 0).card = 1 := by decide
example : (shell 1).card = 2 := by decide
example : (shell 2).card = 5 := by decide

-- `(3,2,1)` is branch (a); `(3,3,0)` is branch (b); `(3,1,0)` is neither.
example : Blind 3 2 1 := by decide
example : Blind 3 3 0 := by decide
example : ¬ Blind 3 1 0 := by decide

-- The bridge, on a partition the Sage sweep confirmed: `λ = (3,2,1)` is `(a,b,c) = (1,1,1)`.
example : NotchCentreCharge.N 1 1 1 = 0 := (blind_iff_N_zero (l₁ := 3) (l₂ := 2) (l₃ := 1)
  (by omega) (by omega)).mp (by decide)

end GaugeHiggsUnification.BlindCount
