/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Data.Int.Init

/-!
# Two integer frieze patterns whose middle rows are strictly ordered

A Conway–Coxeter frieze pattern of width `w` is determined by its quiddity `a = (a₀, …, a_{n-1})`,
`n = w + 3`: the entry of row `k` starting at position `i` is the continuant
`K(a_i, a_{i+1}, …, a_{i+k-1})` (indices modulo `n`), row `0` is all ones, and the pattern closes with
a row of ones (row `w + 1`) followed by a row of zeros (row `w + 2`). It is an integer Conway–Coxeter
frieze when, in addition, rows `1, …, w` are positive.

S. Tabachnikov (*A four-vertex theorem for frieze patterns?*, Math. Intelligencer 40 (2018), 14–18,
Problem 1) asks for which rows the cyclic sequence of differences of two such friezes of the same width
must change sign at least four times; a rational counterexample (width 5, middle row) is due to
M. Cuntz, and the question is left open for friezes of positive integers.

We record two integer Conway–Coxeter friezes of width `11` (`n = 14`) whose middle rows (row `6`, the
row of the diameters of the `14`-gon) are strictly ordered at all `14` positions, so the difference has
no sign change at all. The verification is a finite computation checked by the kernel (`decide +kernel`;
the only axiom used is `propext`). An exhaustive search found `672` such ordered pairs (`24` dihedral
orbits) with strictly ordered rows at width `11`, and none with strictly ordered rows, in any row, at
smaller widths. The middle row is row `⌈w/2⌉`; the printed range `1 ≤ k ≤ [w/2]` of the question would
exclude it, but the question's own rational example (width `5`, row `3`) is a middle row too.
-/

@[expose] public section

namespace Frieze

/-- The continuant `K(x₁, …, x_j)`: `K() = 1`, `K(x₁) = x₁`, and
`K(x₁, …, x_j) = x_j K(x₁, …, x_{j-1}) - K(x₁, …, x_{j-2})`. -/
def continuant (l : List ℤ) : ℤ :=
  (l.foldl (fun (p : ℤ × ℤ) x => (p.2, x * p.2 - p.1)) (0, 1)).2

/-- The entry of row `k` at position `i` of the frieze pattern with quiddity `a`:
the continuant of `a_i, …, a_{i+k-1}`, indices modulo the length of `a`. -/
def entry (a : List ℤ) (k i : ℕ) : ℤ :=
  continuant ((List.range k).map fun t => a.getD ((i + t) % a.length) 0)

/-- `a` is the quiddity of an integer Conway–Coxeter frieze of width `a.length - 3`: rows
`1, …, a.length - 3` are positive, row `a.length - 2` is all ones and row `a.length - 1` is all
zeros. -/
def IsQuiddity (a : List ℤ) : Prop :=
  (∀ k ∈ List.range' 1 (a.length - 3), ∀ i < a.length, 0 < entry a k i) ∧
    (∀ i < a.length, entry a (a.length - 2) i = 1) ∧ ∀ i < a.length, entry a (a.length - 1) i = 0

instance (a : List ℤ) : Decidable (IsQuiddity a) := by
  unfold IsQuiddity; infer_instance

/-- The fan of the `14`-gon from vertex `13` with its diameter `(13, 6)` flipped to `(5, 7)`. -/
def lower : List ℤ := [1, 2, 2, 2, 2, 3, 1, 3, 2, 2, 2, 2, 1, 11]

/-- A triangulation of the `14`-gon without diameters. -/
def upper : List ℤ := [1, 5, 2, 3, 1, 2, 5, 4, 1, 2, 2, 4, 2, 2]

theorem isQuiddity_lower : IsQuiddity lower := by decide +kernel

theorem isQuiddity_upper : IsQuiddity upper := by decide +kernel

/-- The middle rows: `(2, 6, 6, 6, 6, 6, 6)` and `(3, 7, 7, 8, 7, 7, 7)`, each repeated twice. -/
theorem entry_six_lower_lt_upper : ∀ i < 14, entry lower 6 i < entry upper 6 i := by
  decide +kernel

/-- Two integer Conway–Coxeter friezes of the same width `11` whose row `6` differences
`entry upper 6 i - entry lower 6 i` are positive at every position: no sign change. -/
theorem exists_strictly_ordered_middle_rows :
    ∃ a b : List ℤ, IsQuiddity a ∧ IsQuiddity b ∧ a.length = 14 ∧ b.length = 14 ∧
      ∀ i < 14, entry a 6 i < entry b 6 i :=
  ⟨lower, upper, isQuiddity_lower, isQuiddity_upper, rfl, rfl, entry_six_lower_lt_upper⟩

end Frieze
