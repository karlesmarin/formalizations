/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Formalizations.RingTheory.DGH.Basic
import Formalizations.RingTheory.DGH.Hessenberg
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# The DGH stratification closes at `ε₀`

For any ring `R` and any `M ⊆ R`, the Dubrovin–Gräter–Hanke stratum `D M ε₀` is closed under
sums, products and inverses of its units of `R` (`κ ≤ ε₀`).

## Proof sketch

Three monotone potentials, one per process, each written as the minimum of a failure set:
* `iota x`   = min {c | invSet (D c) ⊄ D x}, capped at `A + 1`;
* `piHat x`  = min {h(t.map iota) | t ∈ N(Q), prodSets t ⊄ D x}, capped at `ω^(A+2)`;
* `sigHat x` = min {h(t.map mu)   | t ∈ N(S), sumSets t ⊄ D x}, capped at `ω^(B+1)`,

with `mu = iota ♯ piHat`, `h` the Hessenberg value, and `Q` / `S` the successors of inverse /
(inverse or product) steps. Substitution lemmas put the chosen multisets in `N(Q)` / `N(S)`; on
`Q` / `S` the labels `iota` / `mu` are strictly increasing, so they preserve Jakobs' order. Then
`Phi = mu ♯ sigHat` is strictly increasing on `[1, ε₀)` and bounded by some `β < ε₀`: impossible.

## Main results

* `kappa_le_epsilon0`;
* `sum_entry`, `prod_entry`, `D_stationary`, `main_contra`, `nadd_lt_epsilon_zero`, `jakobsLT_map`.
-/

open Pointwise Order Ordinal Multiset

namespace DGH

noncomputable section
open Classical

/-! ### 1. Natural sum: monotonicity and closure below `ε₀` -/

lemma lt_opow_add_one (o : Ordinal.{0}) {Λ : Ordinal.{0}} (h : o ≤ Λ) : o < ω ^ (Λ + 1) :=
  (right_le_opow o one_lt_omega0).trans_lt
    ((opow_lt_opow_iff_right one_lt_omega0).2 (Order.lt_add_one_iff.2 h))

lemma exists_hval_eq (o : Ordinal.{0}) {Λ : Ordinal.{0}} (h : o ≤ Λ) :
    ∃ s : Multiset Ordinal.{0}, (∀ x ∈ s, x ≤ Λ) ∧ hval s = o := by
  have : o ∈ Set.Iio (ω ^ (Λ + 1)) := lt_opow_add_one o h
  rw [← image_hval] at this
  exact this

theorem nadd_lt_nadd_right {a b : Ordinal.{0}} (h : a < b) (c : Ordinal.{0}) :
    a ♯ c < b ♯ c := by
  obtain ⟨sa, -, rfl⟩ := exists_hval_eq a le_rfl
  obtain ⟨sb, -, rfl⟩ := exists_hval_eq b le_rfl
  obtain ⟨sc, -, rfl⟩ := exists_hval_eq c le_rfl
  rw [← hval_add, ← hval_add, ← jakobsLT_iff_hval_lt]
  exact jakobsLT_add_right sc (jakobsLT_iff_hval_lt.2 h)

theorem nadd_lt_nadd_left {a b : Ordinal.{0}} (h : a < b) (c : Ordinal.{0}) :
    c ♯ a < c ♯ b := by
  rw [nadd_comm c a, nadd_comm c b]; exact nadd_lt_nadd_right h c

theorem nadd_le_nadd {a b c d : Ordinal.{0}} (h1 : a ≤ b) (h2 : c ≤ d) : a ♯ c ≤ b ♯ d := by
  have e1 : a ♯ c ≤ b ♯ c := by
    rcases h1.eq_or_lt with rfl | h1
    · exact le_rfl
    · exact (nadd_lt_nadd_right h1 c).le
  have e2 : b ♯ c ≤ b ♯ d := by
    rcases h2.eq_or_lt with rfl | h2
    · exact le_rfl
    · exact (nadd_lt_nadd_left h2 b).le
  exact e1.trans e2

theorem nadd_lt_of_lt_of_le {a b c d : Ordinal.{0}} (h1 : a < b) (h2 : c ≤ d) :
    a ♯ c < b ♯ d :=
  (nadd_lt_nadd_right h1 c).trans_le (nadd_le_nadd le_rfl h2)

theorem nadd_lt_of_le_of_lt {a b c d : Ordinal.{0}} (h1 : a ≤ b) (h2 : c < d) :
    a ♯ c < b ♯ d :=
  (nadd_le_nadd h1 le_rfl).trans_lt (nadd_lt_nadd_left h2 b)

/-- `ε₀` is closed under the natural sum. -/
theorem nadd_lt_epsilon_zero {a b : Ordinal.{0}} (ha : a < ε₀) (hb : b < ε₀) : a ♯ b < ε₀ := by
  obtain ⟨sa, hsa, ea⟩ := exists_hval_eq a (le_max_left a b)
  obtain ⟨sb, hsb, eb⟩ := exists_hval_eq b (le_max_right a b)
  rw [← ea, ← eb, ← hval_add]
  refine (hval_lt fun x hx => ?_).trans (omega0_opow_add_one_lt_epsilon_zero (max_lt ha hb))
  rcases Multiset.mem_add.1 hx with hx | hx
  · exact Order.lt_add_one_iff.2 (hsa x hx)
  · exact Order.lt_add_one_iff.2 (hsb x hx)

lemma succ_lt_epsilon_zero {x : Ordinal.{0}} (h : x < ε₀) : x + 1 < ε₀ :=
  (right_le_opow (x + 1) one_lt_omega0).trans_lt (omega0_opow_add_one_lt_epsilon_zero h)

/-! ### 2. Jakobs' order: relabeling and a bound -/

/-- Relabeling: a map strictly increasing on a set containing the supports preserves
Jakobs' order. -/
theorem jakobsLT_map {T : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}}
    (hf : ∀ x ∈ T, ∀ y ∈ T, x < y → f x < f y) {s t : Multiset Ordinal.{0}}
    (hs : ∀ x ∈ s, x ∈ T) (ht : ∀ x ∈ t, x ∈ T) (h : jakobsLT s t) :
    jakobsLT (s.map f) (t.map f) := by
  rw [← isDershowitzMannaLT_iff_jakobsLT] at h ⊢
  obtain ⟨X, Y, Z, hZ, rfl, rfl, hYZ⟩ := h
  refine ⟨X.map f, Y.map f, Z.map f, ?_, Multiset.map_add _ _ _, Multiset.map_add _ _ _, ?_⟩
  · rw [Multiset.empty_eq_zero] at hZ ⊢
    exact fun h0 => hZ (Multiset.map_eq_zero.1 h0)
  · intro y hy
    obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨z, hz, hlt⟩ := hYZ y' hy'
    exact ⟨f z, Multiset.mem_map_of_mem f hz,
      hf y' (hs y' (Multiset.mem_add.2 (Or.inr hy'))) z (ht z (Multiset.mem_add.2 (Or.inr hz))) hlt⟩

/-- If `t <_J s`, every entry of `t` is bounded by a bound of the entries of `s`. -/
theorem le_of_jakobsLT {s t : Multiset Ordinal.{0}} (h : jakobsLT t s) {a : Ordinal.{0}}
    (hs : ∀ x ∈ s, x ≤ a) : ∀ y ∈ t, y ≤ a := by
  rw [← isDershowitzMannaLT_iff_jakobsLT] at h
  obtain ⟨X, Y, Z, -, rfl, rfl, hYZ⟩ := h
  intro y hy
  rcases Multiset.mem_add.1 hy with hy | hy
  · exact hs y (Multiset.mem_add.2 (Or.inl hy))
  · obtain ⟨z, hz, hlt⟩ := hYZ y hy
    exact hlt.le.trans (hs z (Multiset.mem_add.2 (Or.inr hz)))

/-! ### 3. Potentials: minimum of a failure set, capped -/

/-- `pot V top = min (V ∪ {top})`. -/
def pot (V : Set Ordinal.{0}) (top : Ordinal.{0}) : Ordinal.{0} := sInf (insert top V)

lemma pot_le_top (V : Set Ordinal.{0}) (top : Ordinal.{0}) : pot V top ≤ top :=
  csInf_le' (Set.mem_insert _ _)

lemma pot_le_of_mem {V : Set Ordinal.{0}} {top v : Ordinal.{0}} (h : v ∈ V) : pot V top ≤ v :=
  csInf_le' (Set.mem_insert_of_mem _ h)

lemma pot_anti {V V' : Set Ordinal.{0}} {top : Ordinal.{0}} (h : V' ⊆ V) :
    pot V top ≤ pot V' top :=
  csInf_le_csInf' (Set.insert_nonempty _ _) (Set.insert_subset_insert h)

lemma lt_pot {V : Set Ordinal.{0}} {top v : Ordinal.{0}} (htop : v < top)
    (h : ∀ w ∈ V, v < w) : v < pot V top := by
  rcases Set.mem_insert_iff.1 (csInf_mem (Set.insert_nonempty top V)) with h1 | h1
  · rw [pot, h1]; exact htop
  · exact h _ h1

/-- A map strictly increasing on `[1, ε₀)` cannot be bounded by some `β < ε₀`. -/
theorem no_bounded_strictMono (F : Ordinal.{0} → Ordinal.{0}) {β : Ordinal.{0}} (hβ : β < ε₀)
    (hF : ∀ x y, 1 ≤ x → x < y → y < ε₀ → F x < F y) (hb : ∀ x, F x ≤ β) : False := by
  have key : ∀ x, x < ε₀ → 1 ≤ x → x ≤ F x + 1 := by
    intro x
    refine WellFoundedLT.induction (motive := fun x => x < ε₀ → 1 ≤ x → x ≤ F x + 1) x ?_
    intro x IH hx _
    refine le_of_forall_lt fun z hz => ?_
    rcases eq_or_ne z 0 with rfl | hz0
    · exact Order.lt_add_one_iff.2 _root_.zero_le
    · have hz1 : 1 ≤ z := Order.one_le_iff_ne_zero.2 hz0
      have h1 := IH z hz (hz.trans hx) hz1
      have h2 := hF z x hz1 hz hx
      exact h1.trans_lt ((Order.add_one_le_of_lt h2).trans_lt (Order.lt_add_one_iff.2 le_rfl))
  have hβ2 : β + 1 + 1 < ε₀ := succ_lt_epsilon_zero (succ_lt_epsilon_zero hβ)
  have h1 := key (β + 1 + 1) hβ2 le_add_self
  have h3 : F (β + 1 + 1) + 1 ≤ β + 1 := by
    have := hb (β + 1 + 1)
    rw [← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
    exact Order.succ_le_succ this
  exact absurd (h1.trans h3) (not_le.2 (Order.lt_add_one_iff.2 le_rfl))

/-! ### 4. Ring-level helpers -/

variable {R : Type} [Ring R] (M : Set R)

lemma zero_mem_D (x : Ordinal.{0}) : (0 : R) ∈ D M x :=
  D_mono M (_root_.zero_le (a := x)) (by rw [D_zero]; exact Set.mem_singleton _)

lemma one_mem_D {x : Ordinal.{0}} (hx : x ≠ 0) : (1 : R) ∈ D M x :=
  D_mono M (Order.one_le_iff_ne_zero.2 hx) (by rw [D_one]; simp [layer1])

lemma sumSets_cons (E : Ordinal.{0} → Set R) (a : Ordinal.{0}) (s : Multiset Ordinal.{0}) :
    sumSets E (a ::ₘ s) = E a + sumSets E s := by
  simp [sumSets]

lemma sumSets_add' (E : Ordinal.{0} → Set R) (s t : Multiset Ordinal.{0}) :
    sumSets E (s + t) = sumSets E s + sumSets E t := by
  simp [sumSets, Multiset.map_add, Multiset.sum_add]

lemma sumSets_zero (E : Ordinal.{0} → Set R) : sumSets E 0 = 0 := by
  simp [sumSets]

lemma sumSets_singleton (E : Ordinal.{0} → Set R) (a : Ordinal.{0}) : sumSets E {a} = E a := by
  simp [sumSets]

/-! ### 5. Primitivity (P2): substitution lemma for sums -/

/-- Substitution lemma (sum). -/
theorem sum_subst {x : Ordinal.{0}} {s : Multiset Ordinal.{0}} (hs : s ∈ sumCand (D M) x)
    (hmin : ∀ t ∈ sumCand (D M) x, ¬ Multiset.IsDershowitzMannaLT t s)
    {d : Ordinal.{0}} (hd : d ∈ s)
    (hsub : ∀ u ∈ D M d, ∃ r : Multiset Ordinal.{0}, (∀ y ∈ r, y < d) ∧ u ∈ sumSets (D M) r) :
    False := by
  apply hs.2.2
  have hsd : s = d ::ₘ s.erase d := (Multiset.cons_erase hd).symm
  intro z hz
  rw [hsd, sumSets_cons] at hz
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_add.1 hz
  obtain ⟨r, hr, hur⟩ := hsub u hu
  have hmem : u + v ∈ sumSets (D M) (r + s.erase d) := by
    rw [sumSets_add']; exact Set.add_mem_add hur hv
  by_cases ht0 : r + s.erase d = 0
  · rw [ht0, sumSets_zero] at hmem
    rw [Set.mem_zero.1 hmem]
    exact zero_mem_D M x
  · have hlt : Multiset.IsDershowitzMannaLT (r + s.erase d) s := by
      refine ⟨s.erase d, r, {d}, by simp, add_comm _ _, ?_,
        fun y hy => ⟨d, Multiset.mem_singleton_self d, hr y hy⟩⟩
      rw [add_comm, Multiset.singleton_add, Multiset.cons_erase hd]
    by_contra hnot
    refine hmin _ ⟨ht0, ?_, fun hsub' => hnot (hsub' hmem)⟩ hlt
    intro y hy
    rcases Multiset.mem_add.1 hy with hy | hy
    · exact (hr y hy).le.trans (hs.2.1 d hd)
    · exact hs.2.1 y (Multiset.mem_of_mem_erase hy)

/-- (P2) The entries of the chosen multiset of a sum step are `1` or successors of
product / inverse steps. -/
theorem sum_entry {x : Ordinal.{0}} {s : Multiset Ordinal.{0}} (hs : s ∈ sumCand (D M) x)
    (hmin : ∀ t ∈ sumCand (D M) x, ¬ Multiset.IsDershowitzMannaLT t s)
    {d : Ordinal.{0}} (hd : d ∈ s) :
    d = 1 ∨ ∃ a, d = succ a ∧ a ≠ 0 ∧ SumClosed (D M a) ∧
      ¬ (MulClosed (D M a) ∧ InvClosed (D M a)) := by
  by_cases h0 : d = 0
  · subst h0
    refine (sum_subst M hs hmin hd fun u hu => ⟨0, by simp, ?_⟩).elim
    rw [D_zero, Set.mem_singleton_iff] at hu
    rw [sumSets_zero, hu]; exact Set.zero_mem_zero
  by_cases hsucc : ∃ a, d = succ a
  · obtain ⟨a, rfl⟩ := hsucc
    have hsa : ∀ y ∈ ({a} : Multiset Ordinal.{0}), y < succ a := fun y hy => by
      rw [Multiset.mem_singleton.1 hy]; exact lt_succ a
    by_cases ha : a = 0
    · left; rw [ha, ord_succ_zero]
    right
    by_cases h1 : SumClosed (D M a)
    · refine ⟨a, rfl, ha, h1, fun ⟨h2, h3⟩ => ?_⟩
      refine sum_subst M hs hmin hd fun u hu => ⟨{a}, hsa, ?_⟩
      rw [sumSets_singleton, ← D_succ_case4 M ha h1 h2 h3]; exact hu
    · exfalso
      obtain ⟨sa, hsa', -, he⟩ := D_succ_case1 M ha h1
      refine sum_subst M hs hmin hd fun u hu => ?_
      rw [he] at hu
      rcases hu with hu | hu
      · exact ⟨{a}, hsa, by rw [sumSets_singleton]; exact hu⟩
      · exact ⟨sa, fun y hy => lt_succ_iff.2 (hsa'.2.1 y hy), hu⟩
  · exfalso
    refine sum_subst M hs hmin hd fun u hu => ?_
    rw [D_limit M h0 hsucc] at hu
    obtain ⟨β, hβ, hu⟩ := Set.mem_iUnion₂.1 hu
    refine ⟨{β}, fun y hy => ?_, by rw [sumSets_singleton]; exact hu⟩
    rw [Multiset.mem_singleton.1 hy]; exact hβ

/-! ### 6. Primitivity (P1): substitution lemma for products -/

/-- Core substitution (product): replacing the factor `d` by a word in strata `< d`. -/
theorem prod_core {x : Ordinal.{0}} (hx : x ≠ 0) {s : Multiset Ordinal.{0}}
    (hs : s ∈ prodCand (D M) x)
    (hmin : ∀ t ∈ prodCand (D M) x, ¬ Multiset.IsDershowitzMannaLT t s)
    {l1 l2 : List Ordinal.{0}} {d : Ordinal.{0}}
    (hl : ((l1 ++ d :: l2 : List Ordinal.{0}) : Multiset Ordinal.{0}) = s)
    {m : List Ordinal.{0}} (hm : ∀ y ∈ m, y < d) {p u q : R}
    (hp : p ∈ (l1.map (D M)).prod) (hu : u ∈ (m.map (D M)).prod)
    (hq : q ∈ (l2.map (D M)).prod) : p * (u * q) ∈ D M x := by
  have hprod : p * (u * q) ∈ ((l1 ++ m ++ l2).map (D M)).prod := by
    rw [List.map_append, List.map_append, List.prod_append, List.prod_append, ← mul_assoc]
    exact Set.mul_mem_mul (Set.mul_mem_mul hp hu) hq
  have hd : d ∈ s := by rw [← hl]; simp
  by_cases hL : l1 ++ m ++ l2 = []
  · rw [hL] at hprod
    simp only [List.map_nil, List.prod_nil] at hprod
    rw [Set.mem_one.1 hprod]; exact one_mem_D M hx
  set t : Multiset Ordinal.{0} := ((l1 ++ m ++ l2 : List Ordinal.{0}) : Multiset Ordinal.{0})
    with ht
  have hmem : p * (u * q) ∈ prodSets (D M) t := Set.mem_iUnion₂.2 ⟨l1 ++ m ++ l2, rfl, hprod⟩
  have ht0 : t ≠ 0 := fun h => hL ((Multiset.coe_eq_zero _).1 h)
  have hent : ∀ y ∈ t, y ≤ x := by
    intro y hy
    rw [ht, Multiset.mem_coe, List.mem_append, List.mem_append] at hy
    have hs1 : ∀ y, y ∈ l1 ∨ y ∈ l2 → y ≤ x := fun y hy' => hs.2.1 y (by
      rw [← hl, Multiset.mem_coe, List.mem_append, List.mem_cons]; tauto)
    rcases hy with (hy | hy) | hy
    · exact hs1 y (Or.inl hy)
    · exact (hm y hy).le.trans (hs.2.1 d hd)
    · exact hs1 y (Or.inr hy)
  have hlt : Multiset.IsDershowitzMannaLT t s := by
    refine ⟨(l1 : Multiset Ordinal.{0}) + l2, m, {d}, by simp, ?_, ?_,
      fun y hy => ⟨d, Multiset.mem_singleton_self d, hm y hy⟩⟩
    · rw [ht, ← Multiset.coe_add, ← Multiset.coe_add, add_right_comm]
    · rw [← hl, ← Multiset.coe_add, ← Multiset.cons_coe, ← Multiset.singleton_add,
        add_comm ({d} : Multiset Ordinal.{0}), ← add_assoc]
  by_contra hn
  exact hmin t ⟨ht0, hent, fun h => hn (h hmem)⟩ hlt

/-- Single-stratum version of `prod_core`. -/
theorem prod_core_single {x : Ordinal.{0}} (hx : x ≠ 0) {s : Multiset Ordinal.{0}}
    (hs : s ∈ prodCand (D M) x)
    (hmin : ∀ t ∈ prodCand (D M) x, ¬ Multiset.IsDershowitzMannaLT t s)
    {l1 l2 : List Ordinal.{0}} {d : Ordinal.{0}}
    (hl : ((l1 ++ d :: l2 : List Ordinal.{0}) : Multiset Ordinal.{0}) = s)
    {e : Ordinal.{0}} (he : e < d) {p u q : R}
    (hp : p ∈ (l1.map (D M)).prod) (hu : u ∈ D M e)
    (hq : q ∈ (l2.map (D M)).prod) : p * (u * q) ∈ D M x := by
  refine prod_core M hx hs hmin hl (m := [e]) (fun y hy => ?_) hp ?_ hq
  · rw [List.mem_singleton.1 hy]; exact he
  · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]; exact hu

/-- Distributivity: substituting a sum of strata `< d`, when `D x` is closed under sums. -/
theorem prod_sum_mem {x : Ordinal.{0}} (hx : x ≠ 0) (hsc : SumClosed (D M x))
    {s : Multiset Ordinal.{0}} (hs : s ∈ prodCand (D M) x)
    (hmin : ∀ t ∈ prodCand (D M) x, ¬ Multiset.IsDershowitzMannaLT t s)
    {l1 l2 : List Ordinal.{0}} {d : Ordinal.{0}}
    (hl : ((l1 ++ d :: l2 : List Ordinal.{0}) : Multiset Ordinal.{0}) = s) {p q : R}
    (hp : p ∈ (l1.map (D M)).prod) (hq : q ∈ (l2.map (D M)).prod) :
    ∀ r : Multiset Ordinal.{0}, (∀ y ∈ r, y < d) → ∀ u ∈ sumSets (D M) r,
      p * (u * q) ∈ D M x := by
  intro r
  induction r using Multiset.induction_on with
  | empty =>
    intro _ u hu
    rw [sumSets_zero] at hu
    rw [Set.mem_zero.1 hu, zero_mul, mul_zero]; exact zero_mem_D M x
  | cons e r ih =>
    intro hr u hu
    rw [sumSets_cons] at hu
    obtain ⟨u1, hu1, u2, hu2, rfl⟩ := Set.mem_add.1 hu
    rw [add_mul, mul_add]
    exact hsc (Set.add_mem_add
      (prod_core_single M hx hs hmin hl (hr e (Multiset.mem_cons_self e r)) hp hu1 hq)
      (ih (fun y hy => hr y (Multiset.mem_cons_of_mem hy)) u2 hu2))

/-- Reduction: if every substitution of the factor `d` lands in `D x`, `s` was no candidate. -/
theorem prod_subst {x : Ordinal.{0}} {s : Multiset Ordinal.{0}} (hs : s ∈ prodCand (D M) x)
    {d : Ordinal.{0}} (hd : d ∈ s)
    (H : ∀ l1 l2 : List Ordinal.{0},
      ((l1 ++ d :: l2 : List Ordinal.{0}) : Multiset Ordinal.{0}) = s →
      ∀ p ∈ (l1.map (D M)).prod, ∀ u ∈ D M d, ∀ q ∈ (l2.map (D M)).prod,
        p * (u * q) ∈ D M x) : False := by
  apply hs.2.2
  intro z hz
  obtain ⟨l, hl, hz⟩ := Set.mem_iUnion₂.1 hz
  have hdl : d ∈ l := by rw [← Multiset.mem_coe, hl]; exact hd
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hdl
  rw [List.map_append, List.map_cons, List.prod_append, List.prod_cons] at hz
  obtain ⟨p, hp, w, hw, rfl⟩ := Set.mem_mul.1 hz
  obtain ⟨u, hu, q, hq, rfl⟩ := Set.mem_mul.1 hw
  exact H l1 l2 hl p hp u hu q hq

/-- (P1) The entries of the chosen multiset of a product step are `1` or successors of
inverse steps. -/
theorem prod_entry {x : Ordinal.{0}} (hx : x ≠ 0) (hsc : SumClosed (D M x))
    {s : Multiset Ordinal.{0}} (hs : s ∈ prodCand (D M) x)
    (hmin : ∀ t ∈ prodCand (D M) x, ¬ Multiset.IsDershowitzMannaLT t s)
    {d : Ordinal.{0}} (hd : d ∈ s) :
    d = 1 ∨ ∃ a, d = succ a ∧ a ≠ 0 ∧ SumClosed (D M a) ∧ MulClosed (D M a) ∧
      ¬ InvClosed (D M a) := by
  by_cases h0 : d = 0
  · subst h0; exfalso
    refine prod_subst M hs hd fun l1 l2 hl p hp u hu q hq => ?_
    rw [D_zero, Set.mem_singleton_iff] at hu
    rw [hu, zero_mul, mul_zero]; exact zero_mem_D M x
  by_cases hsucc : ∃ a, d = succ a
  · obtain ⟨a, rfl⟩ := hsucc
    by_cases ha : a = 0
    · left; rw [ha, ord_succ_zero]
    right
    by_cases h1 : SumClosed (D M a)
    · by_cases h2 : MulClosed (D M a)
      · by_cases h3 : InvClosed (D M a)
        · exfalso
          refine prod_subst M hs hd fun l1 l2 hl p hp u hu q hq => ?_
          rw [D_succ_case4 M ha h1 h2 h3] at hu
          exact prod_core_single M hx hs hmin hl (lt_succ a) hp hu hq
        · exact ⟨a, rfl, ha, h1, h2, h3⟩
      · exfalso
        obtain ⟨sa, hsa, -, he⟩ := D_succ_case2 M ha h1 h2
        refine prod_subst M hs hd fun l1 l2 hl p hp u hu q hq => ?_
        rw [he] at hu
        rcases hu with hu | hu
        · exact prod_core_single M hx hs hmin hl (lt_succ a) hp hu hq
        · obtain ⟨l', hl', hu⟩ := Set.mem_iUnion₂.1 hu
          refine prod_core M hx hs hmin hl (m := l') (fun y hy => ?_) hp hu hq
          exact lt_succ_iff.2 (hsa.2.1 y (by rw [← hl']; exact Multiset.mem_coe.2 hy))
    · exfalso
      obtain ⟨sa, hsa, -, he⟩ := D_succ_case1 M ha h1
      refine prod_subst M hs hd fun l1 l2 hl p hp u hu q hq => ?_
      rw [he] at hu
      rcases hu with hu | hu
      · exact prod_core_single M hx hs hmin hl (lt_succ a) hp hu hq
      · exact prod_sum_mem M hx hsc hs hmin hl hp hq sa
          (fun y hy => lt_succ_iff.2 (hsa.2.1 y hy)) u hu
  · exfalso
    refine prod_subst M hs hd fun l1 l2 hl p hp u hu q hq => ?_
    rw [D_limit M h0 hsucc] at hu
    obtain ⟨β, hβ, hu⟩ := Set.mem_iUnion₂.1 hu
    exact prod_core_single M hx hs hmin hl hβ hp hu hq

/-! ### 7. Minimality against Jakobs' order (global form of M1-M3) -/

lemma sum_min_jakobs {x : Ordinal.{0}} {s : Multiset Ordinal.{0}} (hs : s ∈ sumCand (D M) x)
    (hmin : ∀ t ∈ sumCand (D M) x, ¬ Multiset.IsDershowitzMannaLT t s)
    {t : Multiset Ordinal.{0}} (ht0 : t ≠ 0) (ht : ¬ sumSets (D M) t ⊆ D M x)
    (hts : jakobsLT t s) : False :=
  hmin t ⟨ht0, le_of_jakobsLT hts hs.2.1, ht⟩ (isDershowitzMannaLT_of_jakobsLT hts)

lemma prod_min_jakobs {x : Ordinal.{0}} {s : Multiset Ordinal.{0}} (hs : s ∈ prodCand (D M) x)
    (hmin : ∀ t ∈ prodCand (D M) x, ¬ Multiset.IsDershowitzMannaLT t s)
    {t : Multiset Ordinal.{0}} (ht0 : t ≠ 0) (ht : ¬ prodSets (D M) t ⊆ D M x)
    (hts : jakobsLT t s) : False :=
  hmin t ⟨ht0, le_of_jakobsLT hts hs.2.1, ht⟩ (isDershowitzMannaLT_of_jakobsLT hts)

/-! ### 8. Steps, label sets, potentials -/

/-- `a` is an inverse step (case 3) in `[1, ε₀)`. -/
def InvStep (a : Ordinal.{0}) : Prop :=
  a ≠ 0 ∧ a < ε₀ ∧ SumClosed (D M a) ∧ MulClosed (D M a) ∧ ¬ InvClosed (D M a)

/-- `a` is a product step (case 2) in `[1, ε₀)`. -/
def ProdStep (a : Ordinal.{0}) : Prop :=
  a ≠ 0 ∧ a < ε₀ ∧ SumClosed (D M a) ∧ ¬ MulClosed (D M a)

/-- Labels for product steps: `1` and the successors of inverse steps. -/
def Qset : Set Ordinal.{0} := {d | d = 1 ∨ ∃ a, d = succ a ∧ InvStep M a}

/-- Labels for sum steps: `1` and the successors of inverse or product steps. -/
def Sset : Set Ordinal.{0} := {d | d = 1 ∨ ∃ a, d = succ a ∧ (InvStep M a ∨ ProdStep M a)}

/-- Hypothesis `(H_A)`: every inverse step in `[1, ε₀)` has a failing index `≤ A`. -/
def HInv (A : Ordinal.{0}) : Prop :=
  ∀ x, InvStep M x → ∃ c ≤ A, ¬ invSet (D M c) ⊆ D M x

variable (A : Ordinal.{0})

/-- Inverse potential. -/
def iota (x : Ordinal.{0}) : Ordinal.{0} := pot {c | ¬ invSet (D M c) ⊆ D M x} (A + 1)

/-- Product potential. -/
def piHat (x : Ordinal.{0}) : Ordinal.{0} :=
  pot {v | ∃ t : Multiset Ordinal.{0}, t ≠ 0 ∧ (∀ d ∈ t, d ∈ Qset M) ∧
    ¬ prodSets (D M) t ⊆ D M x ∧ hval (t.map (iota M A)) = v} (ω ^ (A + 1 + 1))

/-- Label of sum entries. -/
def mu (d : Ordinal.{0}) : Ordinal.{0} := iota M A d ♯ piHat M A d

/-- Bound of `mu`. -/
def bnd : Ordinal.{0} := (A + 1) ♯ ω ^ (A + 1 + 1)

/-- Sum potential. -/
def sigHat (x : Ordinal.{0}) : Ordinal.{0} :=
  pot {v | ∃ t : Multiset Ordinal.{0}, t ≠ 0 ∧ (∀ d ∈ t, d ∈ Sset M) ∧
    ¬ sumSets (D M) t ⊆ D M x ∧ hval (t.map (mu M A)) = v} (ω ^ (bnd A + 1))

/-- Total potential. -/
def Phi (x : Ordinal.{0}) : Ordinal.{0} := mu M A x ♯ sigHat M A x

/-! #### inverse potential -/

lemma iota_mono {x y : Ordinal.{0}} (h : x ≤ y) : iota M A x ≤ iota M A y :=
  pot_anti fun _ hc h' => hc (h'.trans (D_mono M h))

lemma iota_le (x : Ordinal.{0}) : iota M A x ≤ A + 1 := pot_le_top _ _

lemma iota_lt_succ (hA : HInv M A) {x : Ordinal.{0}} (hx : InvStep M x) :
    iota M A x < iota M A (succ x) := by
  obtain ⟨c, hcA, hc⟩ := hA x hx
  obtain ⟨hx0, -, h1, h2, h3⟩ := hx
  obtain ⟨b, hb, hbmin, he⟩ := D_succ_case3 M hx0 h1 h2 h3
  have hbA : b ≤ A := by
    by_cases hcx : c ≤ x
    · exact (not_lt.1 (hbmin c ⟨hcx, hc⟩)).trans hcA
    · exact hb.1.trans ((not_le.1 hcx).le.trans hcA)
  unfold iota
  refine (pot_le_of_mem hb.2).trans_lt (lt_pot (Order.lt_add_one_iff.2 hbA) fun w hw => ?_)
  by_contra hwb
  rcases (not_lt.1 hwb).eq_or_lt with rfl | hwb'
  · exact hw (by rw [he]; exact Set.subset_union_right)
  · exact hbmin w ⟨hwb'.le.trans hb.1, fun h => hw (h.trans (D_subset_succ M x))⟩ hwb'

lemma one_le_of_mem_succ_form {d : Ordinal.{0}} (hd : d = 1 ∨ ∃ a, d = succ a) : 1 ≤ d := by
  rcases hd with rfl | ⟨a, rfl⟩
  · exact le_rfl
  · rw [← ord_succ_zero]; exact succ_le_succ _root_.zero_le

lemma iota_strictOn (hA : HInv M A) {d d' : Ordinal.{0}} (hd : d ∈ Qset M)
    (hd' : d' ∈ Qset M) (h : d < d') : iota M A d < iota M A d' := by
  rcases hd' with rfl | ⟨a, rfl, ha⟩
  · exfalso
    have : 1 ≤ d := one_le_of_mem_succ_form (hd.imp id fun ⟨a, ha, _⟩ => ⟨a, ha⟩)
    exact absurd h (not_lt.2 this)
  · exact (iota_mono M A (lt_succ_iff.1 h)).trans_lt (iota_lt_succ M A hA ha)

/-! #### product potential -/

lemma piHat_mono {x y : Ordinal.{0}} (h : x ≤ y) : piHat M A x ≤ piHat M A y := by
  unfold piHat
  apply pot_anti
  rintro v ⟨t, ht0, htQ, ht, rfl⟩
  exact ⟨t, ht0, htQ, fun h' => ht (h'.trans (D_mono M h)), rfl⟩

lemma piHat_le (x : Ordinal.{0}) : piHat M A x ≤ ω ^ (A + 1 + 1) := pot_le_top _ _

lemma hval_map_iota_lt (t : Multiset Ordinal.{0}) :
    hval (t.map (iota M A)) < ω ^ (A + 1 + 1) := by
  refine hval_lt fun a ha => ?_
  obtain ⟨d, -, rfl⟩ := Multiset.mem_map.1 ha
  exact Order.lt_add_one_iff.2 (iota_le M A d)

lemma piHat_lt_succ (hA : HInv M A) {x : Ordinal.{0}} (hx : ProdStep M x) :
    piHat M A x < piHat M A (succ x) := by
  obtain ⟨hx0, hxe, h1, h2⟩ := hx
  obtain ⟨s, hs, hmin, he⟩ := D_succ_case2 M hx0 h1 h2
  have hsQ : ∀ d ∈ s, d ∈ Qset M := fun d hd => by
    rcases prod_entry M hx0 h1 hs hmin hd with h | ⟨a, rfl, ha, ha1, ha2, ha3⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, rfl, ha, ((lt_succ a).trans_le (hs.2.1 _ hd)).trans hxe, ha1, ha2, ha3⟩
  unfold piHat
  refine lt_of_le_of_lt (pot_le_of_mem ?_) (lt_pot (hval_map_iota_lt M A s) ?_)
  · exact ⟨s, hs.1, hsQ, hs.2.2, rfl⟩
  rintro w ⟨t, ht0, htQ, ht, rfl⟩
  have hts : t ≠ s := by
    rintro rfl; exact ht (by rw [he]; exact Set.subset_union_right)
  rcases jakobsLT_total hts with h | h
  · exact (prod_min_jakobs M hs hmin ht0 (fun h' => ht (h'.trans (D_subset_succ M x))) h).elim
  · exact jakobsLT_iff_hval_lt.1
      (jakobsLT_map (fun a ha b hb hab => iota_strictOn M A hA ha hb hab) hsQ htQ h)

/-! #### sum labels and sum potential -/

lemma mu_mono {x y : Ordinal.{0}} (h : x ≤ y) : mu M A x ≤ mu M A y :=
  nadd_le_nadd (iota_mono M A h) (piHat_mono M A h)

lemma mu_le (x : Ordinal.{0}) : mu M A x ≤ bnd A :=
  nadd_le_nadd (iota_le M A x) (piHat_le M A x)

lemma mu_lt_succ (hA : HInv M A) {a : Ordinal.{0}} (ha : InvStep M a ∨ ProdStep M a) :
    mu M A a < mu M A (succ a) := by
  rcases ha with ha | ha
  · exact nadd_lt_of_lt_of_le (iota_lt_succ M A hA ha) (piHat_mono M A (le_succ a))
  · exact nadd_lt_of_le_of_lt (iota_mono M A (le_succ a)) (piHat_lt_succ M A hA ha)

lemma mu_strictOn (hA : HInv M A) {d d' : Ordinal.{0}} (hd : d ∈ Sset M)
    (hd' : d' ∈ Sset M) (h : d < d') : mu M A d < mu M A d' := by
  rcases hd' with rfl | ⟨a, rfl, ha⟩
  · exfalso
    have : 1 ≤ d := one_le_of_mem_succ_form (hd.imp id fun ⟨a, ha, _⟩ => ⟨a, ha⟩)
    exact absurd h (not_lt.2 this)
  · exact (mu_mono M A (lt_succ_iff.1 h)).trans_lt (mu_lt_succ M A hA ha)

lemma sigHat_mono {x y : Ordinal.{0}} (h : x ≤ y) : sigHat M A x ≤ sigHat M A y := by
  unfold sigHat
  apply pot_anti
  rintro v ⟨t, ht0, htS, ht, rfl⟩
  exact ⟨t, ht0, htS, fun h' => ht (h'.trans (D_mono M h)), rfl⟩

lemma sigHat_le (x : Ordinal.{0}) : sigHat M A x ≤ ω ^ (bnd A + 1) := pot_le_top _ _

lemma hval_map_mu_lt (t : Multiset Ordinal.{0}) :
    hval (t.map (mu M A)) < ω ^ (bnd A + 1) := by
  refine hval_lt fun a ha => ?_
  obtain ⟨d, -, rfl⟩ := Multiset.mem_map.1 ha
  exact Order.lt_add_one_iff.2 (mu_le M A d)

lemma sigHat_lt_succ (hA : HInv M A) {x : Ordinal.{0}} (hx0 : x ≠ 0) (hxe : x < ε₀)
    (h1 : ¬ SumClosed (D M x)) : sigHat M A x < sigHat M A (succ x) := by
  obtain ⟨s, hs, hmin, he⟩ := D_succ_case1 M hx0 h1
  have hsS : ∀ d ∈ s, d ∈ Sset M := fun d hd => by
    rcases sum_entry M hs hmin hd with h | ⟨a, rfl, ha, ha1, ha2⟩
    · exact Or.inl h
    · have hae : a < ε₀ := ((lt_succ a).trans_le (hs.2.1 _ hd)).trans hxe
      refine Or.inr ⟨a, rfl, ?_⟩
      by_cases hm : MulClosed (D M a)
      · exact Or.inl ⟨ha, hae, ha1, hm, fun hi => ha2 ⟨hm, hi⟩⟩
      · exact Or.inr ⟨ha, hae, ha1, hm⟩
  unfold sigHat
  refine lt_of_le_of_lt (pot_le_of_mem ?_) (lt_pot (hval_map_mu_lt M A s) ?_)
  · exact ⟨s, hs.1, hsS, hs.2.2, rfl⟩
  rintro w ⟨t, ht0, htS, ht, rfl⟩
  have hts : t ≠ s := by
    rintro rfl; exact ht (by rw [he]; exact Set.subset_union_right)
  rcases jakobsLT_total hts with h | h
  · exact (sum_min_jakobs M hs hmin ht0 (fun h' => ht (h'.trans (D_subset_succ M x))) h).elim
  · exact jakobsLT_iff_hval_lt.1
      (jakobsLT_map (fun a ha b hb hab => mu_strictOn M A hA ha hb hab) hsS htS h)

/-! #### total potential -/

lemma Phi_mono {x y : Ordinal.{0}} (h : x ≤ y) : Phi M A x ≤ Phi M A y :=
  nadd_le_nadd (mu_mono M A h) (sigHat_mono M A h)

lemma Phi_le (x : Ordinal.{0}) : Phi M A x ≤ bnd A ♯ ω ^ (bnd A + 1) :=
  nadd_le_nadd (mu_le M A x) (sigHat_le M A x)

lemma Phi_lt_succ (hA : HInv M A)
    (H4 : ∀ x, x ≠ 0 → x < ε₀ → ¬ (SumClosed (D M x) ∧ MulClosed (D M x) ∧ InvClosed (D M x)))
    {x : Ordinal.{0}} (hx0 : x ≠ 0) (hxe : x < ε₀) : Phi M A x < Phi M A (succ x) := by
  by_cases h1 : SumClosed (D M x)
  · by_cases h2 : MulClosed (D M x)
    · have h3 : ¬ InvClosed (D M x) := fun h3 => H4 x hx0 hxe ⟨h1, h2, h3⟩
      exact nadd_lt_of_lt_of_le
        (nadd_lt_of_lt_of_le (iota_lt_succ M A hA ⟨hx0, hxe, h1, h2, h3⟩)
          (piHat_mono M A (le_succ x)))
        (sigHat_mono M A (le_succ x))
    · exact nadd_lt_of_lt_of_le (mu_lt_succ M A hA (Or.inr ⟨hx0, hxe, h1, h2⟩))
        (sigHat_mono M A (le_succ x))
  · exact nadd_lt_of_le_of_lt (mu_mono M A (le_succ x)) (sigHat_lt_succ M A hA hx0 hxe h1)

/-- Main lemma: `(H_A)` with `A < ε₀` (and no stationary step below `ε₀`) is impossible. -/
theorem main_contra {A : Ordinal.{0}} (hAe : A < ε₀)
    (H4 : ∀ x, x ≠ 0 → x < ε₀ → ¬ (SumClosed (D M x) ∧ MulClosed (D M x) ∧ InvClosed (D M x)))
    (hA : HInv M A) : False := by
  have hA1 : A + 1 < ε₀ := succ_lt_epsilon_zero hAe
  have hB : bnd A < ε₀ :=
    nadd_lt_epsilon_zero hA1 (omega0_opow_add_one_lt_epsilon_zero hA1)
  refine no_bounded_strictMono (Phi M A)
    (nadd_lt_epsilon_zero hB (omega0_opow_add_one_lt_epsilon_zero hB)) ?_ (Phi_le M A)
  intro x y hx hxy hy
  have hx0 : x ≠ 0 := Order.one_le_iff_ne_zero.1 hx
  exact (Phi_lt_succ M A hA H4 hx0 (hxy.trans hy)).trans_le
    (Phi_mono M A (Order.succ_le_of_lt hxy))

/-! ### 9. Stationarity and the theorem -/

/-- Case 4 at `x` makes the stratification constant from `x` on. -/
theorem D_stationary {x : Ordinal.{0}} (hx0 : x ≠ 0) (h1 : SumClosed (D M x))
    (h2 : MulClosed (D M x)) (h3 : InvClosed (D M x)) :
    ∀ y, x ≤ y → D M y = D M x := by
  intro y
  refine WellFoundedLT.induction (motive := fun y => x ≤ y → D M y = D M x) y ?_
  intro y IH hxy
  rcases hxy.eq_or_lt with rfl | hlt
  · rfl
  by_cases hs : ∃ a, y = succ a
  · obtain ⟨a, rfl⟩ := hs
    have hxa : x ≤ a := lt_succ_iff.1 hlt
    have ha := IH a (lt_succ a) hxa
    have ha0 : a ≠ 0 := by
      rintro rfl; exact hx0 (le_antisymm hxa _root_.zero_le)
    rw [D_succ_case4 M ha0 (by rw [ha]; exact h1) (by rw [ha]; exact h2)
      (by rw [ha]; exact h3), ha]
  · have hy0 : y ≠ 0 := by rintro rfl; exact not_lt.2 _root_.zero_le hlt
    rw [D_limit M hy0 hs]
    apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨b, hb, hz⟩ := Set.mem_iUnion₂.1 hz
      rcases le_total x b with hxb | hbx
      · rwa [IH b hb hxb] at hz
      · exact D_mono M hbx hz
    · exact Set.subset_iUnion₂ (s := fun c (_ : c < y) => D M c) x hlt

lemma epsilon_zero_ne_zero : (ε₀ : Ordinal.{0}) ≠ 0 := (epsilon_pos 0).ne'

lemma epsilon_zero_not_succ : ¬ ∃ a, (ε₀ : Ordinal.{0}) = succ a := by
  rintro ⟨a, ha⟩
  have h1 : a < ε₀ := by rw [ha]; exact lt_succ a
  have h2 := succ_lt_epsilon_zero h1
  rw [← Order.succ_eq_add_one, ← ha] at h2
  exact lt_irrefl _ h2

lemma mem_D_epsilon_zero {z : R} : z ∈ D M ε₀ ↔ ∃ b < ε₀, z ∈ D M b := by
  rw [D_limit M epsilon_zero_ne_zero epsilon_zero_not_succ]
  simp only [Set.mem_iUnion, exists_prop]

/-- **κ ≤ ε₀.** For every ring `R` and every `M ⊆ R`, the DGH stratum `D M ε₀` is closed
under sums, products, and inverses of those of its elements that are units of `R`. -/
theorem kappa_le_epsilon0 :
    SumClosed (D M ε₀) ∧ MulClosed (D M ε₀) ∧ InvClosed (D M ε₀) := by
  by_cases h4 : ∃ x, x ≠ 0 ∧ x < ε₀ ∧ SumClosed (D M x) ∧ MulClosed (D M x) ∧
      InvClosed (D M x)
  · obtain ⟨x, hx0, hxe, h1, h2, h3⟩ := h4
    rw [D_stationary M hx0 h1 h2 h3 ε₀ hxe.le]
    exact ⟨h1, h2, h3⟩
  have H4 : ∀ x, x ≠ 0 → x < ε₀ →
      ¬ (SumClosed (D M x) ∧ MulClosed (D M x) ∧ InvClosed (D M x)) :=
    fun x hx0 hxe h => h4 ⟨x, hx0, hxe, h⟩
  -- above any `δ < ε₀` there is a stratum closed under sums and products
  have binary : ∀ δ < ε₀, ∃ a, δ ≤ a ∧ a < ε₀ ∧ SumClosed (D M a) ∧ MulClosed (D M a) := by
    intro δ hδ
    by_contra hno
    refine main_contra M hδ H4 fun x hx => ⟨x, ?_, hx.2.2.2.2⟩
    by_contra hxδ
    exact hno ⟨x, (not_le.1 hxδ).le, hx.2.1, hx.2.2.1, hx.2.2.2.1⟩
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨z1, hz1, z2, hz2, rfl⟩ := Set.mem_add.1 hz
    obtain ⟨b1, hb1, hz1⟩ := (mem_D_epsilon_zero M).1 hz1
    obtain ⟨b2, hb2, hz2⟩ := (mem_D_epsilon_zero M).1 hz2
    obtain ⟨a, ha, hae, h1, -⟩ := binary (max b1 b2) (max_lt hb1 hb2)
    exact (mem_D_epsilon_zero M).2 ⟨a, hae, h1 (Set.add_mem_add
      (D_mono M ((le_max_left _ _).trans ha) hz1) (D_mono M ((le_max_right _ _).trans ha) hz2))⟩
  · intro z hz
    obtain ⟨z1, hz1, z2, hz2, rfl⟩ := Set.mem_mul.1 hz
    obtain ⟨b1, hb1, hz1⟩ := (mem_D_epsilon_zero M).1 hz1
    obtain ⟨b2, hb2, hz2⟩ := (mem_D_epsilon_zero M).1 hz2
    obtain ⟨a, ha, hae, -, h2⟩ := binary (max b1 b2) (max_lt hb1 hb2)
    exact (mem_D_epsilon_zero M).2 ⟨a, hae, h2 (Set.mul_mem_mul
      (D_mono M ((le_max_left _ _).trans ha) hz1) (D_mono M ((le_max_right _ _).trans ha) hz2))⟩
  · rintro z ⟨u, hu, rfl⟩
    obtain ⟨α, hα, hu⟩ := (mem_D_epsilon_zero M).1 hu
    by_contra hn
    refine main_contra M hα H4 fun x hx => ⟨α, le_rfl, fun h => hn ?_⟩
    exact (mem_D_epsilon_zero M).2 ⟨x, hx.2.1, h ⟨u, hu, rfl⟩⟩

end

end DGH
