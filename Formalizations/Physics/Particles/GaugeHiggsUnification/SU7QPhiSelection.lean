/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FieldSimp

/-!
# The selection rule for the charge of the breaking scalar is a half-line

A vacuum expectation value of charge `q > 0` breaks a `U(1)` to a discrete subgroup, and an operator of
charge `A` can be dressed with insertions of it iff `A / q ∈ ℤ`: protection *fails* at `q`. For `A ≠ 0`
this happens iff `q = |A| / n` for some integer `n ≥ 1`, so over finitely many nonzero charges the
failure set has a maximum, `max_j |A_j|`, and protection holds on the half-line above it.

The hypothesis `A ≠ 0` is implicit in the paper: for `A = 0` protection fails at every `q`.

## Main results

* `GaugeHiggsUnification.SU7QPhi.fails_iff`: protection fails at `q` iff `q = |A| / n`, `n ≥ 1`.
* `GaugeHiggsUnification.SU7QPhi.isGreatest_failSet`: the failure set has maximum `max_j |A_j|`.

## References

* su7-proton-decay (Carles Marín), Proposition `prop:closed`.
-/

@[expose] public section

namespace GaugeHiggsUnification.SU7QPhi

/-- Protection fails at `q` for the charge `A`: the operator can be dressed, `A / q` is an integer. -/
def Fails (A q : ℚ) : Prop := ∃ k : ℤ, A / q = k

theorem fails_iff {A q : ℚ} (hA : A ≠ 0) (hq : 0 < q) :
    Fails A q ↔ ∃ n : ℕ, 1 ≤ n ∧ q = |A| / n := by
  constructor
  · rintro ⟨k, hk⟩
    have h1 : A = (k : ℚ) * q := (div_eq_iff hq.ne').mp hk
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hA
      rw [h1]
      simp
    have hkabs : |(k : ℚ)| ≠ 0 := abs_ne_zero.mpr (by exact_mod_cast hk0)
    have hn : ((k.natAbs : ℕ) : ℚ) = |(k : ℚ)| := by
      rcases Int.natAbs_eq k with h | h
      · conv_rhs => rw [h]
        simp
      · conv_rhs => rw [h]
        simp
    refine ⟨k.natAbs, Int.natAbs_pos.mpr hk0, ?_⟩
    rw [h1, abs_mul, abs_of_pos hq, hn]
    exact (mul_div_cancel_left₀ q hkabs).symm
  · rintro ⟨n, hn1, hqn⟩
    have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    rcases lt_or_gt_of_ne hA with hneg | hpos
    · refine ⟨-(n : ℤ), ?_⟩
      rw [hqn, abs_of_neg hneg]
      push_cast
      field_simp
    · refine ⟨(n : ℤ), ?_⟩
      rw [hqn, abs_of_pos hpos]
      push_cast
      field_simp

/-- The failure set of finitely many nonzero charges has a maximum, attained at `max_j |A_j|`. -/
theorem isGreatest_failSet {ι : Type*} [Fintype ι] [Nonempty ι] (A : ι → ℚ) (hA : ∀ j, A j ≠ 0) :
    IsGreatest {q : ℚ | 0 < q ∧ ∃ j, Fails (A j) q}
      (Finset.univ.sup' Finset.univ_nonempty fun j => |A j|) := by
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι)) (fun j => |A j|)
  have hpos : 0 < |A j₀| := abs_pos.mpr (hA j₀)
  have hM : 0 < Finset.univ.sup' Finset.univ_nonempty (fun j => |A j|) := by
    rw [hj₀]; exact hpos
  refine ⟨⟨hM, j₀, ?_⟩, ?_⟩
  · exact (fails_iff (hA j₀) hM).mpr ⟨1, le_rfl, by rw [hj₀]; simp⟩
  · rintro q ⟨hq, j, hF⟩
    obtain ⟨n, hn1, hqn⟩ := (fails_iff (hA j) hq).mp hF
    rw [hqn]
    exact (div_le_self (abs_nonneg _) (by exact_mod_cast hn1)).trans
      (Finset.le_sup' (fun j => |A j|) (Finset.mem_univ j))

end GaugeHiggsUnification.SU7QPhi
