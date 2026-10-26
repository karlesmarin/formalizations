/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.Combinatorics.Frieze.IntegerDominance

/-!
# Two integer frieze patterns of width 12 whose rows 6 differ with exactly two sign changes

Continuation of `Formalizations.Combinatorics.Frieze.IntegerDominance` (same conventions: `entry a k i` is
the continuant of `a_i, …, a_{i+k-1}`, indices modulo `n = a.length`). For width `w = 12` (`n = 15`), row
`6 = ⌊w/2⌋` lies inside the printed range `1 ≤ k ≤ [w/2]` of Problem 1 of S. Tabachnikov
(*A four-vertex theorem for frieze patterns?*, Math. Intelligencer 40 (2018)). We record two integer
Conway–Coxeter friezes of width `12` whose row-`6` differences have no zero and exactly two cyclic sign
changes, so the answer to the question is negative for integer friezes within the printed range too. An
exhaustive search found `480` such pairs at width `12` and none, in any row `k ≤ ⌊w/2⌋`, at smaller widths.
The verification is a finite computation checked by the kernel (`decide +kernel`).
-/

@[expose] public section

namespace Frieze

/-- The difference of row `k` of the friezes with quiddities `b` and `a`, at position `i`. -/
def rowDiff (a b : List ℤ) (k i : ℕ) : ℤ := entry b k i - entry a k i

/-- The number of cyclic positions `i < a.length` where the row-`k` difference changes sign strictly. -/
def signChanges (a b : List ℤ) (k : ℕ) : ℕ :=
  ((List.range a.length).filter fun i =>
    decide (rowDiff a b k i * rowDiff a b k ((i + 1) % a.length) < 0)).length

/-- First quiddity of width `12`. -/
def lower12 : List ℤ := [1, 2, 2, 2, 2, 3, 1, 4, 2, 1, 4, 2, 2, 1, 10]

/-- Second quiddity of width `12`. -/
def upper12 : List ℤ := [4, 3, 1, 2, 3, 3, 4, 1, 2, 2, 5, 2, 2, 1, 4]

theorem isQuiddity_lower12 : IsQuiddity lower12 := by decide +kernel

theorem isQuiddity_upper12 : IsQuiddity upper12 := by decide +kernel

/-- The row-`6` differences are `(1, 1, 2, 7, 1, 1, 1, 1, 9, -8, -9, 3, 7, 3, 2)`: no zero. -/
theorem rowDiff_six_ne_zero : ∀ i < 15, rowDiff lower12 upper12 6 i ≠ 0 := by decide +kernel

theorem signChanges_six : signChanges lower12 upper12 6 = 2 := by decide +kernel

/-- Control: the counter is not degenerate; row `5` of the same pair has five sign changes. -/
theorem signChanges_five : signChanges lower12 upper12 5 = 5 := by decide +kernel

/-- Two integer Conway–Coxeter friezes of width `12` whose rows `6 = ⌊12/2⌋` differ with no zero and
exactly two cyclic sign changes. -/
theorem exists_two_sign_changes_width_twelve :
    ∃ a b : List ℤ, IsQuiddity a ∧ IsQuiddity b ∧ a.length = 15 ∧ b.length = 15 ∧
      (∀ i < 15, rowDiff a b 6 i ≠ 0) ∧ signChanges a b 6 = 2 :=
  ⟨lower12, upper12, isQuiddity_lower12, isQuiddity_upper12, rfl, rfl, rowDiff_six_ne_zero,
    signChanges_six⟩

end Frieze
