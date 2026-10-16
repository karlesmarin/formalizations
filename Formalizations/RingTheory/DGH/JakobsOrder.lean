/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Data.Multiset.DershowitzManna
public import Mathlib.Data.Finset.Max

/-!
# Jakobs' order is the Dershowitz–Manna order

On a linear order, Mathlib's Dershowitz–Manna order on multisets (`Multiset.IsDershowitzMannaLT`)
coincides with Jakobs' order "lexicographic from the largest element".

## Main results

* `isDershowitzMannaLT_iff_jakobsLT`, `jakobsLT_total`, `jakobsLT_add_right`;
* `wellFounded_min_jakobsLE`: the `WellFounded.min` used in `DGH.Basic` is a minimum for Jakobs'
  order.

## References

* F. Jakobs, PhD thesis, 2019, Thm. 1.1.3; Dubrovin–Gräter–Hanke, Prop. 2.1.
-/

@[expose] public section

namespace DGH

open Multiset

variable {α : Type*} [LinearOrder α]

/-- Jakobs' order: `s <_J t` iff at some `x` the count in `s` is smaller than in `t`,
and the counts agree at every `y > x`. -/
def jakobsLT (s t : Multiset α) : Prop :=
  ∃ x, count x s < count x t ∧ ∀ y, x < y → count y s = count y t

/-- Reflexive closure of `jakobsLT`. -/
def jakobsLE (s t : Multiset α) : Prop := s = t ∨ jakobsLT s t

/-- If `s ≠ t`, there is a largest element where the counts differ. -/
lemma exists_max_count_ne {s t : Multiset α} (h : s ≠ t) :
    ∃ m, count m s ≠ count m t ∧ ∀ y, m < y → count y s = count y t := by
  classical
  set F := (s + t).toFinset.filter (fun x => count x s ≠ count x t) with hF
  have memF : ∀ x, count x s ≠ count x t → x ∈ F := by
    intro x hx
    rw [hF, Finset.mem_filter, Multiset.mem_toFinset]
    refine ⟨?_, hx⟩
    by_contra hn
    rw [Multiset.mem_add, not_or] at hn
    exact hx (by rw [count_eq_zero_of_notMem hn.1, count_eq_zero_of_notMem hn.2])
  obtain ⟨x, hx⟩ : ∃ x, count x s ≠ count x t := by
    by_contra hn
    push Not at hn
    exact h (Multiset.ext.2 hn)
  have hne : F.Nonempty := ⟨x, memF x hx⟩
  refine ⟨F.max' hne, (Finset.mem_filter.1 (F.max'_mem hne)).2, fun y hy => ?_⟩
  by_contra hc
  exact absurd (F.le_max' y (memF y hc)) (not_le.2 hy)

/-- Helper: under the DM hypothesis on `Y, Z`, the maximum of `Z` is not in `Y`. -/
lemma max_notMem {Y Z : Multiset α} (hZ : Z.toFinset.Nonempty)
    (hYZ : ∀ y ∈ Y, ∃ z ∈ Z, y < z) : Z.toFinset.max' hZ ∉ Y := by
  intro hm
  obtain ⟨z, hz, hlt⟩ := hYZ _ hm
  exact absurd (Z.toFinset.le_max' z (Multiset.mem_toFinset.2 hz)) (not_le.2 hlt)

/-- (1, ⇒) Dershowitz–Manna implies Jakobs. -/
theorem jakobsLT_of_isDershowitzMannaLT {s t : Multiset α}
    (h : IsDershowitzMannaLT s t) : jakobsLT s t := by
  obtain ⟨X, Y, Z, hZ, rfl, rfl, hYZ⟩ := h
  rw [Multiset.empty_eq_zero] at hZ
  have hZne : Z.toFinset.Nonempty := by
    obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hZ
    exact ⟨a, Multiset.mem_toFinset.2 ha⟩
  have hmax := max_notMem hZne hYZ
  have hmaxZ : Z.toFinset.max' hZne ∈ Z := Multiset.mem_toFinset.1 (Z.toFinset.max'_mem hZne)
  have hst : X + Y ≠ X + Z := by
    intro he
    have hYZeq : Y = Z := add_left_cancel he
    exact hmax (hYZeq ▸ hmaxZ)
  obtain ⟨m, hm, hgt⟩ := exists_max_count_ne hst
  refine ⟨m, ?_, hgt⟩
  rw [count_add, count_add] at hm ⊢
  by_contra hc
  have hY : count m Z < count m Y := by omega
  have hmY : m ∈ Y := Multiset.count_pos.1 (by omega)
  obtain ⟨z, hz, hmz⟩ := hYZ m hmY
  have hz0 : m < Z.toFinset.max' hZne :=
    lt_of_lt_of_le hmz (Z.toFinset.le_max' z (Multiset.mem_toFinset.2 hz))
  have heq := hgt _ hz0
  rw [count_add, count_add] at heq
  have hpos : 0 < count (Z.toFinset.max' hZne) Z := Multiset.count_pos.2 hmaxZ
  exact hmax (Multiset.count_pos.1 (by omega))

/-- (1, ⇐) Jakobs implies Dershowitz–Manna. -/
theorem isDershowitzMannaLT_of_jakobsLT {s t : Multiset α}
    (h : jakobsLT s t) : IsDershowitzMannaLT s t := by
  obtain ⟨x, hx, hgt⟩ := h
  refine ⟨s ∩ t, s - t, t - s, ?_, ?_, ?_, ?_⟩
  · rw [Multiset.empty_eq_zero]
    intro h0
    have := congrArg (count x) h0
    rw [count_sub, count_zero] at this
    omega
  · ext a; rw [count_add, count_inter, count_sub]; omega
  · ext a; rw [count_add, count_inter, count_sub]; omega
  · intro y hy
    refine ⟨x, ?_, ?_⟩
    · rw [← Multiset.count_pos, count_sub]; omega
    · have hy' := Multiset.count_pos.2 hy
      rw [count_sub] at hy'
      rcases lt_trichotomy y x with hlt | heq | hlt
      · exact hlt
      · subst heq; omega
      · have := hgt y hlt; omega

/-- (1) On a linear order, Dershowitz–Manna = Jakobs' lexicographic order. -/
theorem isDershowitzMannaLT_iff_jakobsLT {s t : Multiset α} :
    IsDershowitzMannaLT s t ↔ jakobsLT s t :=
  ⟨jakobsLT_of_isDershowitzMannaLT, isDershowitzMannaLT_of_jakobsLT⟩

/-- (2) Totality. -/
theorem jakobsLT_total {s t : Multiset α} (h : s ≠ t) : jakobsLT s t ∨ jakobsLT t s := by
  obtain ⟨m, hm, hgt⟩ := exists_max_count_ne h
  rcases lt_or_gt_of_ne hm with hlt | hlt
  · exact Or.inl ⟨m, hlt, hgt⟩
  · exact Or.inr ⟨m, hlt, fun y hy => (hgt y hy).symm⟩

/-- Irreflexivity. -/
theorem jakobsLT_irrefl (s : Multiset α) : ¬ jakobsLT s s := fun ⟨_, h, _⟩ => lt_irrefl _ h

/-- (3) Translation invariance: `s <_J t → s + u <_J t + u`. -/
theorem jakobsLT_add_right {s t : Multiset α} (u : Multiset α) (h : jakobsLT s t) :
    jakobsLT (s + u) (t + u) := by
  obtain ⟨x, hx, hgt⟩ := h
  refine ⟨x, ?_, fun y hy => ?_⟩
  · rw [count_add, count_add]; omega
  · rw [count_add, count_add, hgt y hy]

/-- (4) Over a well-founded linear order, the Dershowitz–Manna `WellFounded.min` of a
nonempty set `S` is `≤_J` every element of `S` (a minimum, not merely minimal). -/
theorem wellFounded_min_jakobsLE [WellFoundedLT α] (S : Set (Multiset α)) (hS : S.Nonempty)
    {t : Multiset α} (ht : t ∈ S) :
    jakobsLE (Multiset.wellFounded_isDershowitzMannaLT.min S hS) t := by
  by_cases he : Multiset.wellFounded_isDershowitzMannaLT.min S hS = t
  · exact Or.inl he
  · right
    rcases jakobsLT_total he with h | h
    · exact h
    · exact absurd (isDershowitzMannaLT_of_jakobsLT h)
        (Multiset.wellFounded_isDershowitzMannaLT.not_lt_min S ht)

end DGH
