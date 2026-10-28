/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Combinatorics.Matroid.IndepAxioms
public import Mathlib.Data.List.TFAE
public import Mathlib.Data.Fintype.Basic

/-!
# The Cameron–Fon-Der-Flaass IBIS theorem

For a permutation group `G` on a finite set `Ω`, the following are equivalent: all irredundant bases
have the same size; irredundant bases are preserved by re-ordering; the irredundant bases are the
bases of a matroid on `Ω` (Theorem of the Day; Cameron and Fon-Der-Flaass 1995). The key step: if
`P, b` is an irredundant base and adding `x` to `P` shrinks its pointwise stabilizer, it shrinks it
to `1` (otherwise `P, x, b` is an irredundant base whose re-ordering `P, b, x` is not), which gives
the matroid basis exchange.

## Main results

* `IBIS.one_point_completion`: under invariance by re-ordering, a point that shrinks the stabilizer of a near-base completes it
* `IBIS.exchange`: basis exchange for the underlying sets of irredundant bases
* `IBIS.tfae`: the IBIS theorem (Theorem of the Day)

## References

* R. Whitty, Theorem of the Day, «The Cameron–Fon-Der-Flaass IBIS Theorem» (GroupTheory/IBIS).
* P. J. Cameron, D. G. Fon-Der-Flaass, Bases for permutation groups and matroids, European J. Combin. 16 (1995) 537–544.
-/

@[expose] public section

namespace IBIS

set_option linter.unusedSectionVars false

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The pointwise stabilizer in `G` of a set of points. -/
def stab (G : Subgroup (Equiv.Perm Ω)) (A : Set Ω) : Subgroup G := fixingSubgroup G A

/-- An irredundant base of `G`: a list of points whose successive pointwise stabilizers strictly decrease and end at
the trivial subgroup. -/
def IsIrredundantBase (G : Subgroup (Equiv.Perm Ω)) (l : List Ω) : Prop :=
  (∀ i < l.length, stab G {x | x ∈ l.take (i + 1)} < stab G {x | x ∈ l.take i}) ∧ stab G {x | x ∈ l} = ⊥

/-- The strict-decrease part of irredundancy. -/
def PrefixChain (G : Subgroup (Equiv.Perm Ω)) (l : List Ω) : Prop :=
  ∀ i < l.length, stab G {x | x ∈ l.take (i + 1)} < stab G {x | x ∈ l.take i}

variable (G : Subgroup (Equiv.Perm Ω))

omit [Fintype Ω] [DecidableEq Ω] in
theorem isIrr_iff (l : List Ω) :
    IsIrredundantBase G l ↔ PrefixChain G l ∧ stab G {x | x ∈ l} = ⊥ := Iff.rfl

omit [Fintype Ω] [DecidableEq Ω] in
theorem stab_union (A B : Set Ω) : stab G (A ∪ B) = stab G A ⊓ stab G B :=
  fixingSubgroup_union _ _

omit [Fintype Ω] [DecidableEq Ω] in
theorem stab_anti {A B : Set Ω} (h : A ⊆ B) : stab G B ≤ stab G A :=
  fixingSubgroup_antitone _ _ h

omit [Fintype Ω] [DecidableEq Ω] in
theorem mem_stab {A : Set Ω} {g : G} :
    g ∈ stab G A ↔ ∀ y ∈ A, (g : Equiv.Perm Ω) y = y := by
  unfold stab
  rw [mem_fixingSubgroup_iff]
  rfl

omit [Fintype Ω] [DecidableEq Ω] in
theorem stab_univ : stab G (Set.univ : Set Ω) = ⊥ := by
  ext g
  rw [mem_stab, Subgroup.mem_bot]
  constructor
  · intro h
    apply Subtype.ext
    apply Equiv.ext
    intro y
    exact h y (Set.mem_univ y)
  · intro h y _
    rw [h]
    rfl

omit [Fintype Ω] [DecidableEq Ω] in
theorem set_append (l : List Ω) (x : Ω) :
    {y | y ∈ l ++ [x]} = {y | y ∈ l} ∪ {x} := by
  ext y; simp [or_comm]

omit [Fintype Ω] [DecidableEq Ω] in
theorem prefixChain_nil : PrefixChain G ([] : List Ω) := fun i hi => absurd hi (by simp)

omit [Fintype Ω] [DecidableEq Ω] in
theorem prefixChain_snoc (l : List Ω) (x : Ω) :
    PrefixChain G (l ++ [x]) ↔
      PrefixChain G l ∧ stab G ({y | y ∈ l} ∪ {x}) < stab G {y | y ∈ l} := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, ?_⟩
    · have := h i (by simp; omega)
      rwa [List.take_append_of_le_length (by omega),
        List.take_append_of_le_length (by omega)] at this
    · have := h l.length (by simp)
      rw [List.take_of_length_le (by simp), List.take_append_of_le_length le_rfl,
        List.take_length, set_append] at this
      exact this
  · rintro ⟨h1, h2⟩ i hi
    have hi' : i < l.length + 1 := by simpa using hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with h | h
    · rw [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega)]
      exact h1 i h
    · subst h
      rw [List.take_of_length_le (by simp), List.take_append_of_le_length le_rfl,
        List.take_length, set_append]
      exact h2

theorem prefixChain_nodup (l : List Ω) (h : PrefixChain G l) : l.Nodup := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l x ih =>
    obtain ⟨h1, h2⟩ := (prefixChain_snoc G l x).1 h
    refine List.nodup_append.2 ⟨ih h1, List.nodup_singleton _, ?_⟩
    intro a ha b hb hab
    simp only [List.mem_singleton] at hb
    subst hb
    subst hab
    have : ({y | y ∈ l} ∪ {a} : Set Ω) = {y | y ∈ l} :=
      Set.union_eq_left.2 (by simpa using ha)
    rw [this] at h2
    exact lt_irrefl _ h2

/-- Pruning: every list has an irredundant sublist with the same final stabilizer, strictly
shorter unless the list was already irredundant. -/
theorem exists_irredundant_sublist (l : List Ω) :
    ∃ k, k.Sublist l ∧ PrefixChain G k ∧ stab G {x | x ∈ k} = stab G {x | x ∈ l} ∧
      (k.length < l.length ∨ k = l) := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨[], List.Sublist.refl _, prefixChain_nil G, rfl, Or.inr rfl⟩
  | append_singleton l x ih =>
    obtain ⟨k, hk, hc, hs, hl⟩ := ih
    by_cases hlt : stab G ({y | y ∈ k} ∪ {x}) < stab G {y | y ∈ k}
    · refine ⟨k ++ [x], hk.append (List.Sublist.refl _), (prefixChain_snoc G k x).2 ⟨hc, hlt⟩,
        ?_, ?_⟩
      · rw [set_append, set_append, stab_union, stab_union, hs]
      · rcases hl with h | h
        · left; simp; omega
        · right; rw [h]
    · have hle := stab_anti G (Set.subset_union_left : ({y | y ∈ k} : Set Ω) ⊆ _ ∪ {x})
      have heq : stab G ({y | y ∈ k} ∪ {x}) = stab G {y | y ∈ k} :=
        eq_of_le_of_not_lt hle hlt
      refine ⟨k, hk.trans (List.sublist_append_left _ _), hc, ?_, Or.inl ?_⟩
      · rw [set_append, stab_union, ← hs, ← stab_union G, heq]
      · have := hk.length_le
        simp; omega

theorem exists_irredundantBase : ∃ l : List Ω, IsIrredundantBase G l := by
  obtain ⟨k, _, hc, hs, _⟩ := exists_irredundant_sublist G (Finset.univ : Finset Ω).toList
  refine ⟨k, hc, ?_⟩
  have : {x | x ∈ (Finset.univ : Finset Ω).toList} = (Set.univ : Set Ω) := by ext; simp
  rw [hs, this, stab_univ]

theorem length_eq_ncard {l : List Ω} (h : PrefixChain G l) :
    l.length = {x | x ∈ l}.ncard := by
  have hnd := prefixChain_nodup G l h
  have : {x | x ∈ l} = ((l.toFinset : Finset Ω) : Set Ω) := by ext; simp
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

/-- (1) ⇒ (2). -/
theorem equal_length_implies_reorder
    (h1 : ∀ l l' : List Ω, IsIrredundantBase G l → IsIrredundantBase G l' → l.length = l'.length)
    (l l' : List Ω) (hl : IsIrredundantBase G l) (hp : l.Perm l') : IsIrredundantBase G l' := by
  obtain ⟨k, _, hc, hs, hlt⟩ := exists_irredundant_sublist G l'
  have hset : {x | x ∈ l'} = {x | x ∈ l} := by ext x; exact (hp.mem_iff).symm
  have hk : IsIrredundantBase G k := ⟨hc, by rw [hs, hset]; exact hl.2⟩
  rcases hlt with h | h
  · exfalso
    have := h1 k l hk hl
    have := hp.length_eq
    omega
  · rw [← h]; exact hk

/-- Key lemma, under invariance by re-ordering. -/
theorem one_point_completion
    (h2 : ∀ l l' : List Ω, IsIrredundantBase G l → l.Perm l' → IsIrredundantBase G l')
    {P : List Ω} {b x : Ω} (hPb : IsIrredundantBase G (P ++ [b]))
    (hx : stab G ({y | y ∈ P} ∪ {x}) < stab G {y | y ∈ P}) :
    stab G ({y | y ∈ P} ∪ {x}) = ⊥ := by
  by_contra hne
  obtain ⟨hc, hbot⟩ := hPb
  obtain ⟨hcP, hlt⟩ := (prefixChain_snoc G P b).1 hc
  rw [set_append] at hbot
  have hbd : stab G (({y | y ∈ P} ∪ {x}) ∪ {b}) = ⊥ := by
    apply le_bot_iff.1
    rw [← hbot]
    apply stab_anti
    rintro y (hy | hy)
    · exact Or.inl (Or.inl hy)
    · exact Or.inr hy
  have hQ : IsIrredundantBase G ((P ++ [x]) ++ [b]) := by
    refine ⟨?_, ?_⟩
    · refine (prefixChain_snoc G _ b).2 ⟨(prefixChain_snoc G P x).2 ⟨hcP, hx⟩, ?_⟩
      rw [set_append, hbd]
      exact bot_lt_iff_ne_bot.2 hne
    · simp only [set_append]
      exact hbd
  have hperm : ((P ++ [x]) ++ [b]).Perm ((P ++ [b]) ++ [x]) := by
    simp only [List.append_assoc]
    exact List.Perm.append_left P List.perm_append_comm
  have h3 := h2 _ _ hQ hperm
  obtain ⟨hc3, _⟩ := h3
  obtain ⟨_, hlt3⟩ := (prefixChain_snoc G (P ++ [b]) x).1 hc3
  rw [set_append, hbot] at hlt3
  exact not_lt_bot hlt3

/-- Basis exchange for the underlying sets of irredundant bases, under re-ordering invariance. -/
theorem exchange
    (h2 : ∀ l l' : List Ω, IsIrredundantBase G l → l.Perm l' → IsIrredundantBase G l')
    {B C : Set Ω} (hB : ∃ l, IsIrredundantBase G l ∧ {x | x ∈ l} = B)
    (hC : ∃ l, IsIrredundantBase G l ∧ {x | x ∈ l} = C) :
    ∀ b ∈ B \ C, ∃ c ∈ C \ B, ∃ l, IsIrredundantBase G l ∧ {x | x ∈ l} = insert c (B \ {b}) := by
  rintro b ⟨hbB, hbC⟩
  obtain ⟨l, hl, rfl⟩ := hB
  obtain ⟨l', hl', rfl⟩ := hC
  have hbl : b ∈ l := hbB
  have hperm : l.Perm (l.erase b ++ [b]) :=
    (List.perm_cons_erase hbl).trans (List.perm_append_singleton b _).symm
  have hPb := h2 l _ hl hperm
  have hnd := prefixChain_nodup G l hl.1
  have hsetP : {y | y ∈ l.erase b} = {y | y ∈ l} \ {b} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
    rw [hnd.mem_erase_iff]
    tauto
  obtain ⟨hc, hbot⟩ := hPb
  obtain ⟨hcP, hlt⟩ := (prefixChain_snoc G _ b).1 hc
  rw [set_append] at hbot
  rw [hbot] at hlt
  obtain ⟨hh, hhP, hhn⟩ := (IsConcreteLE.lt_iff_le_and_exists.1 hlt).2
  have hhC : ¬ ∀ y ∈ {x | x ∈ l'}, (hh : Equiv.Perm Ω) y = y := by
    intro hall
    have : hh ∈ stab G {x | x ∈ l'} := (mem_stab G).2 hall
    rw [hl'.2] at this
    exact hhn this
  push Not at hhC
  obtain ⟨c, hcC, hcm⟩ := hhC
  have hcP' : c ∉ {y | y ∈ l.erase b} := fun hc' => hcm ((mem_stab G).1 hhP c hc')
  have hcb : c ≠ b := fun e => hbC (e ▸ hcC)
  have hcB : c ∉ {x | x ∈ l} := by
    intro hcl
    apply hcP'
    rw [hsetP]
    exact ⟨hcl, hcb⟩
  have hlt_c : stab G ({y | y ∈ l.erase b} ∪ {c}) < stab G {y | y ∈ l.erase b} := by
    refine IsConcreteLE.lt_iff_le_and_exists.2 ⟨stab_anti G Set.subset_union_left, hh, hhP, ?_⟩
    intro hmem
    rw [stab_union] at hmem
    exact hcm ((mem_stab G).1 hmem.2 c rfl)
  have hbot_c := one_point_completion G h2 (b := b) ⟨hc, by rw [set_append]; exact hbot⟩ hlt_c
  refine ⟨c, ⟨hcC, hcB⟩, l.erase b ++ [c], ⟨(prefixChain_snoc G _ c).2 ⟨hcP, hlt_c⟩, ?_⟩, ?_⟩
  · rw [set_append]; exact hbot_c
  · rw [set_append, hsetP]
    ext y
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_insert_iff]
    tauto

theorem matroid_exists
    (h2 : ∀ l l' : List Ω, IsIrredundantBase G l → l.Perm l' → IsIrredundantBase G l') :
    ∃ M : Matroid Ω, M.E = Set.univ ∧
      ∀ B, M.IsBase B ↔ ∃ l, IsIrredundantBase G l ∧ {x | x ∈ l} = B := by
  refine ⟨Matroid.ofIsBaseOfFinite Set.finite_univ
    (fun B => ∃ l, IsIrredundantBase G l ∧ {x | x ∈ l} = B) ?_ ?_ (fun B _ => Set.subset_univ B),
    rfl, fun B => Iff.rfl⟩
  · obtain ⟨l, hl⟩ := exists_irredundantBase G
    exact ⟨_, l, hl, rfl⟩
  · intro B C hB hC b hb
    obtain ⟨c, hc, l, hl⟩ := exchange G h2 hB hC b hb
    exact ⟨c, hc, l, hl⟩

theorem matroid_implies_equal_length (M : Matroid Ω)
    (hM : ∀ B, M.IsBase B ↔ ∃ l, IsIrredundantBase G l ∧ {x | x ∈ l} = B)
    (l l' : List Ω) (hl : IsIrredundantBase G l) (hl' : IsIrredundantBase G l') :
    l.length = l'.length := by
  have h1 := (hM _).2 ⟨l, hl, rfl⟩
  have h2 := (hM _).2 ⟨l', hl', rfl⟩
  rw [length_eq_ncard G hl.1, length_eq_ncard G hl'.1]
  exact h1.ncard_eq_ncard_of_isBase h2

/-- **The Cameron–Fon-Der-Flaass IBIS theorem.** For a permutation group `G` on a finite set `Ω` the following are
equivalent: (1) all irredundant bases have the same size; (2) every re-ordering of an irredundant base is an
irredundant base; (3) the underlying sets of the irredundant bases are exactly the bases of a matroid on `Ω`. -/
theorem tfae (G : Subgroup (Equiv.Perm Ω)) :
    List.TFAE
      [∀ l l', IsIrredundantBase G l → IsIrredundantBase G l' → l.length = l'.length,
       ∀ l l', IsIrredundantBase G l → l.Perm l' → IsIrredundantBase G l',
       ∃ M : Matroid Ω, M.E = Set.univ ∧
         ∀ B, M.IsBase B ↔ ∃ l, IsIrredundantBase G l ∧ {x | x ∈ l} = B] := by
  tfae_have 1 → 2 := fun h1 => equal_length_implies_reorder G h1
  tfae_have 2 → 3 := fun h2 => matroid_exists G h2
  tfae_have 3 → 1 := fun ⟨M, _, hM⟩ => matroid_implies_equal_length G M hM
  tfae_finish

end IBIS
