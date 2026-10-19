/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.SetTheory.Ordinal.Notation

/-!
# Height doubling on normal ordinal notations below `ε₀`

The ordinal layer of Gentzen's cut elimination, on Mathlib's normal ordinal notations `NONote`
(ordinals below `ε₀`): the height-doubling map `twoPow a = 2 ^ a` (computable, through
`NONote.opow`) and the inequalities L1–L5 used to bound the height of a derivation after a cut
is eliminated.

These statements go through `NONote.repr` and Mathlib's order on `NONote`, which is defined by
`repr`, so they depend on `Classical.choice` (through `Ordinal.lt_wf`). The choice-free versions,
stated with a syntactic order and normal form, are in
`Formalizations.SetTheory.Ordinal.Gentzen.Acc` and `Formalizations.SetTheory.Ordinal.Gentzen.TwoPow`.

## Main results

* `twoPow`, `repr_twoPow`: `2 ^ a` as a normal notation;
* `twoPow_lt_twoPow`, `twoPow_le_twoPow` (L3), `twoPow_max` (L4);
* `L1` (`1 ≤ a → 2^a + 1 < 2^(a+1)`) and `L1_fails_at_zero`;
* `L2` (`2 ≤ a → 2^a + 2 < 2^(a+1)`) and `L2_fails_at_one`;
* `L5` (`2^a + 2 < 2^(a+2)`), `twoPow_add_le_max` (`2^a + 2^b ≤ 2^(max a b + 1)`);
* `ti`: transfinite induction below `ε₀`, from `NONote.lt_wf`.

## References

* B. Bryce, R. Goré, arXiv:2603.00487 (2026): Gentzen's consistency proof for PA in Coq.
-/

@[expose] public section

namespace Gentzen.Ordinals

open Ordinal

/-! ## Basic notations -/

/-- `1` as a normal notation (Mathlib's `NONote` has no `One` instance). -/
instance : One NONote := ⟨NONote.ofNat 1⟩

/-- `2` as a normal notation. -/
def two : NONote := NONote.ofNat 2

@[simp] theorem repr_ofNat (n : ℕ) : NONote.repr (NONote.ofNat n) = n :=
  ONote.repr_ofNat n

@[simp] theorem repr_one : NONote.repr (1 : NONote) = 1 := by
  show NONote.repr (NONote.ofNat 1) = 1; simp

@[simp] theorem repr_two : NONote.repr two = 2 := by
  simp [two]

@[simp] theorem repr_zero : NONote.repr (0 : NONote) = 0 := rfl

theorem lt_iff (a b : NONote) : a < b ↔ NONote.repr a < NONote.repr b := Iff.rfl
theorem le_iff (a b : NONote) : a ≤ b ↔ NONote.repr a ≤ NONote.repr b := Iff.rfl

theorem ext_repr {a b : NONote} (h : NONote.repr a = NONote.repr b) : a = b :=
  Subtype.ext (ONote.repr_inj.1 h)

/-! ## The height-doubling map -/

/-- `twoPow a` is the notation of the ordinal `2 ^ a` (computable, via `ONote.opow`). -/
def twoPow (a : NONote) : NONote := NONote.opow two a

@[simp] theorem repr_twoPow (a : NONote) : NONote.repr (twoPow a) = 2 ^ NONote.repr a := by
  simp [twoPow, NONote.repr_opow]

theorem repr_add_one (a : NONote) : NONote.repr (a + 1) = Order.succ (NONote.repr a) := by
  rw [NONote.repr_add, repr_one, Order.succ_eq_add_one]

/-- `2^(a+1) = 2^a + 2^a`. -/
theorem twoPow_succ (a : NONote) :
    NONote.repr (twoPow (a + 1)) = NONote.repr (twoPow a) + NONote.repr (twoPow a) := by
  rw [repr_twoPow, NONote.repr_add, repr_one, opow_add_one, repr_twoPow,
    show (2 : Ordinal) = 1 + 1 from one_add_one_eq_two.symm, mul_add, mul_one]

theorem one_le_twoPow (a : NONote) : (1 : Ordinal) ≤ NONote.repr (twoPow a) := by
  rw [repr_twoPow]; exact Order.one_le_iff_ne_zero.2 (opow_pos _ zero_lt_two).ne'

/-! ## L3: monotonicity -/

theorem twoPow_lt_twoPow {a b : NONote} (h : a < b) : twoPow a < twoPow b := by
  rw [lt_iff, repr_twoPow, repr_twoPow]
  exact (opow_lt_opow_iff_right one_lt_two).2 h

theorem twoPow_le_twoPow {a b : NONote} (h : a ≤ b) : twoPow a ≤ twoPow b := by
  rw [le_iff, repr_twoPow, repr_twoPow]
  exact opow_le_opow_right zero_lt_two h

theorem twoPow_strictMono : StrictMono twoPow := fun _ _ h => twoPow_lt_twoPow h
theorem twoPow_monotone : Monotone twoPow := fun _ _ h => twoPow_le_twoPow h

/-! ## L4: commutes with `max` -/

theorem twoPow_max (a b : NONote) : twoPow (max a b) = max (twoPow a) (twoPow b) :=
  twoPow_monotone.map_max

/-! ## L1, L2: the tall-rule and disjunction-cut bounds -/

theorem two_le_twoPow {a : NONote} (h : 1 ≤ a) : (2 : Ordinal) ≤ NONote.repr (twoPow a) := by
  rw [repr_twoPow]
  have h' : (1 : Ordinal) ≤ NONote.repr a := by simpa [le_iff] using h
  calc (2 : Ordinal) = 2 ^ (1 : Ordinal) := (opow_one 2).symm
    _ ≤ 2 ^ NONote.repr a := opow_le_opow_right zero_lt_two h'

/-- L1. False at `a = 0` (`2^0 + 1 = 2 = 2^1`), see `L1_fails_at_zero`. -/
theorem L1 {a : NONote} (h : 1 ≤ a) : twoPow a + 1 < twoPow (a + 1) := by
  rw [lt_iff, NONote.repr_add, twoPow_succ, repr_one]
  exact (add_lt_add_iff_left _).2 (lt_of_lt_of_le one_lt_two (two_le_twoPow h))

theorem L1_fails_at_zero : ¬ (twoPow 0 + 1 < twoPow (0 + 1)) := by
  rw [lt_iff, NONote.repr_add, twoPow_succ, repr_one, repr_twoPow, repr_zero, opow_zero]
  exact lt_irrefl _

/-- L2. False at `a = 1` (`2^1 + 2 = 4 = 2^2`), see `L2_fails_at_one`. -/
theorem L2 {a : NONote} (h : two ≤ a) : twoPow a + two < twoPow (a + 1) := by
  rw [lt_iff, NONote.repr_add, twoPow_succ, repr_two]
  refine (add_lt_add_iff_left _).2 ?_
  have h' : (2 : Ordinal) ≤ NONote.repr a := by simpa [le_iff] using h
  rw [repr_twoPow]
  calc (2 : Ordinal) < 2 + 2 := lt_add_of_pos_right _ zero_lt_two
    _ = 2 ^ (2 : Ordinal) := by
        rw [show (2 : Ordinal) = 1 + 1 from one_add_one_eq_two.symm, opow_add, opow_one,
          mul_add, mul_one]
    _ ≤ 2 ^ NONote.repr a := opow_le_opow_right zero_lt_two h'

theorem L2_fails_at_one : ¬ (twoPow 1 + two < twoPow (1 + 1)) := by
  rw [lt_iff, NONote.repr_add, twoPow_succ, repr_two, repr_twoPow, repr_one, opow_one]
  exact lt_irrefl _

/-! ## L5: bounds for a cut of height `max + 2` -/

/-- L5a. `2^a + 2 < 2^(a+2)` for every `a` (no side condition). -/
theorem L5 (a : NONote) : twoPow a + two < twoPow (a + 1 + 1) := by
  rw [lt_iff, NONote.repr_add, twoPow_succ, twoPow_succ, repr_two, add_assoc]
  refine (add_lt_add_iff_left _).2 ?_
  have h1 := one_le_twoPow a
  have hx0 : (0 : Ordinal) < NONote.repr (twoPow a) := lt_of_lt_of_le zero_lt_one h1
  calc (2 : Ordinal) = 1 + 1 := one_add_one_eq_two.symm
    _ ≤ NONote.repr (twoPow a) + NONote.repr (twoPow a) := add_le_add h1 h1
    _ < NONote.repr (twoPow a) + NONote.repr (twoPow a) + NONote.repr (twoPow a) :=
        lt_add_of_pos_right _ hx0
    _ = _ := add_assoc _ _ _

/-- L5b. Premises of heights `a, b` reduce to height at most `2^(max a b + 1)`. -/
theorem twoPow_add_le_max (a b : NONote) : twoPow a + twoPow b ≤ twoPow (max a b + 1) := by
  rw [le_iff, NONote.repr_add, twoPow_succ]
  exact add_le_add (twoPow_monotone (le_max_left a b)) (twoPow_monotone (le_max_right a b))

/-! ## Transfinite induction -/

/-- Transfinite induction below `ε₀`, derived from `NONote.lt_wf`. -/
theorem ti {P : NONote → Prop} (h : ∀ a, (∀ b < a, P b) → P a) (a : NONote) : P a :=
  NONote.lt_wf.induction a h

/-- `ω` as a normal notation. -/
def omega : NONote := ⟨ONote.oadd 1 1 0, inferInstance⟩

end Gentzen.Ordinals
