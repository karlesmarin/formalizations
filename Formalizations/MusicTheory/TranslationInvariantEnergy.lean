/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.MusicTheory.ComplementEnergy
public import Formalizations.MusicTheory.AllPairsEvenness
public import Formalizations.MusicTheory.ExtremalityConnections
public import Mathlib.Algebra.Group.Translate

/-!
# Translation-invariant pair energies

On a finite abelian group `G`, a pair weight `W a b = f (b - a)` has constant row sum `∑ x, f x`,
and it is symmetric iff `f` is even. So the complement correction of `ComplementEnergy` is a single
scalar. On `ℤ/12` with a potential of the circular distance, a hexachord and its complement have
the same energy for every potential, and complementation transports minimizers.

## Main results

* `kernel_symmetric_iff`, `rowSum_kernel`, `energy_univ`.
* `energy_compl`, `energy_compl_card`, `energy_gap_compl`, `minimizer_compl_iff`.
* `PitchClassEnergy.potential_sum`, `PitchClassEnergy.energy_compl_card`,
  `PitchClassEnergy.complement_difference_bridge`, `PitchClassEnergy.hexachord_energy_eq`,
  `PitchClassEnergy.minimizer_compl_iff`.

## References

* N. Bushaw, B. Cody, C. Leffler, *Sets of vertices with extremal energy*, arXiv:2407.18785.
-/

@[expose] public section

namespace MusicTheory

open Finset

namespace TranslationInvariantEnergy

variable {G : Type*} [AddCommGroup G]

/-- A pair potential determined only by the oriented difference of its sites. -/
def kernel (f : G → ℝ) (a b : G) : ℝ := f (b - a)

/-- Evenness of the potential makes its pair kernel symmetric. -/
theorem kernel_symmetric (f : G → ℝ) (heven : ∀ x, f (-x) = f x) :
    ComplementEnergy.IsSymmetric (kernel f) := by
  intro a b
  change f (b - a) = f (a - b)
  rw [← neg_sub b a, heven]

/-- Symmetry of the pair energy is exactly evenness of its difference potential. -/
theorem kernel_symmetric_iff (f : G → ℝ) :
    ComplementEnergy.IsSymmetric (kernel f) ↔ ∀ x, f (-x) = f x := by
  constructor
  · intro h x
    have hx := h 0 x
    change f (x - 0) = f (0 - x) at hx
    simpa only [zero_sub, sub_zero] using hx.symm
  · exact kernel_symmetric f

variable [Fintype G]

/-- Translation invariance gives the same weighted degree at every site. -/
theorem rowSum_kernel (f : G → ℝ) (a : G) :
    ComplementEnergy.rowSum (kernel f) a = ∑ x, f x := by
  change (∑ b, f (b - a)) = ∑ x, f x
  exact sum_translate a f

theorem kernel_regular (f : G → ℝ) : ComplementEnergy.IsRegular (kernel f) := by
  intro a b
  rw [rowSum_kernel, rowSum_kernel]

/-- The total energy is half the number of sites times their common row sum. -/
theorem energy_univ (f : G → ℝ) :
    ComplementEnergy.energy (kernel f) univ =
      (Fintype.card G : ℝ) * (∑ x, f x) / 2 := by
  change (∑ a : G, ComplementEnergy.rowSum (kernel f) a) / 2 = _
  simp_rw [rowSum_kernel]
  simp only [sum_const, card_univ, nsmul_eq_mul]

variable [DecidableEq G]

/-- The full complement correction is fixed by cardinality and the potential's total sum. -/
theorem energy_compl (f : G → ℝ) (heven : ∀ x, f (-x) = f x)
    (A : Finset G) :
    ComplementEnergy.energy (kernel f) Aᶜ - ComplementEnergy.energy (kernel f) A =
      ComplementEnergy.energy (kernel f) univ - (A.card : ℝ) * (∑ x, f x) := by
  apply ComplementEnergy.energy_compl_regular (kernel f) (kernel_symmetric f heven)
    (∑ x, f x)
  exact rowSum_kernel f

/-- Normal form: one scalar (the row sum) controls every complement correction. -/
theorem energy_compl_card (f : G → ℝ) (heven : ∀ x, f (-x) = f x)
    (A : Finset G) :
    ComplementEnergy.energy (kernel f) Aᶜ - ComplementEnergy.energy (kernel f) A =
      ((Fintype.card G : ℝ) / 2 - A.card) * (∑ x, f x) := by
  rw [energy_compl f heven A, energy_univ]
  ring

/-- Equal-cardinality energy gaps are unchanged by complementation. -/
theorem energy_gap_compl (f : G → ℝ) (heven : ∀ x, f (-x) = f x)
    (A B : Finset G) (hcard : A.card = B.card) :
    ComplementEnergy.energy (kernel f) Aᶜ - ComplementEnergy.energy (kernel f) Bᶜ =
      ComplementEnergy.energy (kernel f) A - ComplementEnergy.energy (kernel f) B :=
  ComplementEnergy.energy_gap_compl (kernel f) (kernel_symmetric f heven)
    (kernel_regular f) A B hcard

/-- Every cardinality-constrained minimizer is transported to its complement. -/
theorem minimizer_compl_iff (f : G → ℝ) (heven : ∀ x, f (-x) = f x)
    (A : Finset G) :
    ComplementEnergy.IsMinimizer (kernel f) Aᶜ ↔
      ComplementEnergy.IsMinimizer (kernel f) A :=
  ComplementEnergy.minimizer_compl_iff (kernel f) (kernel_symmetric f heven)
    (kernel_regular f) A

end TranslationInvariantEnergy

namespace PitchClassEnergy

/-- The twelve-tone circular-distance potential viewed as a difference kernel. -/
def potential (V : ℕ → ℝ) (x : ZMod 12) : ℝ := V (AllPairsEvenness.cdist 0 x)

theorem potential_even (V : ℕ → ℝ) (x : ZMod 12) :
    potential V (-x) = potential V x := by
  simp only [potential, AllPairsEvenness.cdist, zero_sub, sub_zero, neg_neg]
  rw [min_comm]

/-- Every distance-based pair weight in the pitch-class circle is translation invariant. -/
theorem kernel_eq_distance (V : ℕ → ℝ) (a b : ZMod 12) :
    TranslationInvariantEnergy.kernel (potential V) a b = V (AllPairsEvenness.cdist a b) := by
  simp only [TranslationInvariantEnergy.kernel, potential, AllPairsEvenness.cdist,
    zero_sub, sub_zero, neg_sub]

/-- The twelve sites occur at circular distances 0, 1, ..., 6 with
    multiplicities 1, 2, ..., 2, 1. -/
theorem potential_sum (V : ℕ → ℝ) :
    (∑ x : ZMod 12, potential V x) =
      V 0 + 2 * (V 1 + V 2 + V 3 + V 4 + V 5) + V 6 := by
  have hu : (univ : Finset (ZMod 12)) =
      {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} := by decide
  rw [hu]
  simp (config := { decide := true }) [potential, AllPairsEvenness.cdist,
    Finset.sum_insert, Finset.sum_singleton]
  simp only [show (1 : ZMod 12).val = 1 by decide,
    show (2 : ZMod 12).val = 2 by decide,
    show (3 : ZMod 12).val = 3 by decide,
    show (4 : ZMod 12).val = 4 by decide,
    show (5 : ZMod 12).val = 5 by decide,
    show (-6 : ZMod 12).val = 6 by decide,
    show (-7 : ZMod 12).val = 5 by decide,
    show (-8 : ZMod 12).val = 4 by decide,
    show (-9 : ZMod 12).val = 3 by decide,
    show (-10 : ZMod 12).val = 2 by decide,
    show (-11 : ZMod 12).val = 1 by decide]
  ring

/-- Twelve-tone specialization of the general complement identity. The scalar is
    the sum of all twelve distance weights, including the possible self-weight V(0). -/
theorem energy_compl_card (V : ℕ → ℝ) (A : Finset (ZMod 12)) :
    ComplementEnergy.energy (fun a b => V (AllPairsEvenness.cdist a b)) Aᶜ -
        ComplementEnergy.energy (fun a b => V (AllPairsEvenness.cdist a b)) A =
      (6 - (A.card : ℝ)) * (∑ x : ZMod 12, potential V x) := by
  have h := TranslationInvariantEnergy.energy_compl_card (potential V) (potential_even V) A
  have hk : TranslationInvariantEnergy.kernel (potential V) =
      (fun a b => V (AllPairsEvenness.cdist a b)) := by
    funext a b
    exact kernel_eq_distance V a b
  rw [hk] at h
  simpa only [ZMod.card, Nat.cast_ofNat,
    show (12 : ℝ) / 2 = 6 by norm_num] using h

/-- The abstract and pitch-class complement differences coincide when the diagonal
    weight vanishes, which is the convention used by `AllPairsEvenness.E`. -/
theorem complement_difference_bridge (V : ℕ → ℝ) (hzero : V 0 = 0)
    (A : Finset (ZMod 12)) :
    AllPairsEvenness.E V Aᶜ - AllPairsEvenness.E V A =
      ComplementEnergy.energy (fun a b => V (AllPairsEvenness.cdist a b)) Aᶜ -
        ComplementEnergy.energy (fun a b => V (AllPairsEvenness.cdist a b)) A := by
  rw [ExtremalityConnections.energy_compl V A, energy_compl_card V A,
    potential_sum, hzero]
  ring

/-- Any six-note set and its complement have equal pair energy for every
    circular-distance potential. This is the weighted-energy face of the
    complementary-hexachord interval-vector theorem. -/
theorem hexachord_energy_eq (V : ℕ → ℝ) (A : Finset (ZMod 12))
    (hcard : A.card = 6) :
    ComplementEnergy.energy (fun a b => V (AllPairsEvenness.cdist a b)) Aᶜ =
      ComplementEnergy.energy (fun a b => V (AllPairsEvenness.cdist a b)) A := by
  have h := energy_compl_card V A
  rw [hcard] at h
  norm_num at h
  exact sub_eq_zero.mp h

/-- Complementation transports minima for every circular-distance potential,
    with no convexity assumption. This is the abstract source of the 5↔7 bridge. -/
theorem minimizer_compl_iff (V : ℕ → ℝ) (A : Finset (ZMod 12)) :
    ComplementEnergy.IsMinimizer (fun a b => V (AllPairsEvenness.cdist a b)) Aᶜ ↔
      ComplementEnergy.IsMinimizer (fun a b => V (AllPairsEvenness.cdist a b)) A := by
  simpa only [← kernel_eq_distance] using
    TranslationInvariantEnergy.minimizer_compl_iff (potential V) (potential_even V) A

end PitchClassEnergy

end MusicTheory
