/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Order.Basic
public import Mathlib.Tactic.Linarith

/-!
# An additively closed set containing `[a, 2a]` contains `[a, ∞)`

## Main results

* `ConjeturaC.mem_of_Icc_subset`: if `S ⊆ ℕ` is closed under addition and contains every `i` with
  `a ≤ i ≤ 2a` (`a > 0`), then it contains every `i ≥ a`.
-/

@[expose] public section

namespace ConjeturaC

theorem mem_of_Icc_subset {a : ℕ} (ha : 0 < a) {S : Set ℕ}
    (hadd : ∀ x y, x ∈ S → y ∈ S → x + y ∈ S)
    (hI : ∀ i, a ≤ i → i ≤ 2 * a → i ∈ S) : ∀ i, a ≤ i → i ∈ S := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h2 : i ≤ 2 * a
    · exact hI i hi h2
    · have hA : a ∈ S := hI a le_rfl (by omega)
      have hB : i - a ∈ S := ih (i - a) (by omega) (by omega)
      have := hadd (i - a) a hB hA
      rwa [Nat.sub_add_cancel (by omega)] at this

end ConjeturaC
