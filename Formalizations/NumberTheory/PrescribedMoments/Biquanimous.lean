/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Multiset.Powerset
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.IntervalCases

/-!
# Biquanimous partitions and signed zero sums

A multiset of naturals is biquanimous if it splits into two parts of equal sum. For `n ≥ 3`,
every partition of `n` into exactly four parts is biquanimous iff `n ∈ {3, 4, 6}`. The number of
sign vectors `ε ∈ {±1}^l` with `∑ w_i ε_i = 0`, up to `ε ~ −ε`, is `½ #{A ⊆ [l] | 2 ∑_A w = n}`;
it is `0` iff the weights are not biquanimous, and `0` for odd `n`. The same count holds for an
abstract singular locus, with the description of that locus as an explicit hypothesis.

## Main results

* `P3c.thm_clasificacion_comb`: the classification of `n` for four-part partitions.
* `P3c.cor_cuenta_signos`: `2 · #(sign classes) = #{A | 2 ∑_A w = n}`.
* `P3c.cor_cuenta_cero_iff`, `P3c.cor_cuenta_impar`: when the count vanishes.
* `P3c.cor_cuenta_sing`: the count for an abstract singular locus.

## References

* C. Marín, *Subsets of F_p with two prescribed moments, Part I: the pair (1,3)*, Zenodo (2026),
  doi:10.5281/zenodo.22886540.
-/

@[expose] public section

open Finset

namespace P3c

/-! ## Part 1: four-part partitions (thm:clasificacion, combinatorial half) -/

/-- A multiset of naturals is *biquanimous* if some sub-multiset carries half the total. -/
def Biquanimous (s : Multiset ℕ) : Prop := ∃ A ≤ s, 2 * A.sum = s.sum

lemma biquanimous_iff_powerset (s : Multiset ℕ) :
    Biquanimous s ↔ ∃ A ∈ s.powerset, 2 * A.sum = s.sum := by
  simp [Biquanimous, Multiset.mem_powerset]

instance (s : Multiset ℕ) : Decidable (Biquanimous s) :=
  @decidable_of_iff _ _ (biquanimous_iff_powerset s).symm Multiset.decidableExistsMultiset

lemma sum_le_of_le {A B : Multiset ℕ} (h : A ≤ B) : A.sum ≤ B.sum := by
  obtain ⟨C, rfl⟩ := Multiset.le_iff_exists_add.mp h
  simp

lemma le_sum_of_mem' {a : ℕ} {A : Multiset ℕ} (h : a ∈ A) : a ≤ A.sum := by
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem h
  simp

/-- The witness `λ* = (n-3,1,1,1)` as a partition of `n` (needs `n ≥ 4`). -/
def lamStar (n : ℕ) (hn : 4 ≤ n) : Nat.Partition n where
  parts := {n - 3, 1, 1, 1}
  parts_pos := by
    intro i hi
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hi
    omega
  parts_sum := by simp; omega

lemma lamStar_card (n : ℕ) (hn : 4 ≤ n) : Multiset.card (lamStar n hn).parts = 4 := rfl

/-- `λ* = (n-3,1,1,1)` is not biquanimous for `n ≥ 5`, `n ≠ 6`
(by size for `n > 6`, by parity for `n = 5`). -/
lemma lamStar_not_biquanimous (n : ℕ) (hn : 5 ≤ n) (h6 : n ≠ 6) :
    ¬ Biquanimous (lamStar n (by omega)).parts := by
  rintro ⟨A, hA, hsum⟩
  have htot : (lamStar n (by omega)).parts.sum = n := (lamStar n _).parts_sum
  rw [htot] at hsum
  rcases Nat.lt_or_ge n 7 with h7 | h7
  · -- n = 5: parity
    omega
  · by_cases hm : n - 3 ∈ A
    · have := le_sum_of_mem' hm
      omega
    · have hA' : A ≤ {1, 1, 1} := by
        have : (lamStar n (by omega)).parts = (n - 3) ::ₘ {1, 1, 1} := rfl
        rw [this] at hA
        exact (Multiset.le_cons_of_notMem hm).mp hA
      have := sum_le_of_le hA'
      simp at this
      omega

/-- Four positive parts with total `6` (or `4`) always split evenly: finite check. -/
lemma four_parts_biq (n : ℕ) (hn : n = 4 ∨ n = 6) (a b c d : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hs : a + b + c + d = n) :
    Biquanimous {a, b, c, d} := by
  have hd' : d = n - a - b - c := by omega
  subst hd'
  rcases hn with rfl | rfl
  · have : a ≤ 3 := by omega
    have : b ≤ 3 := by omega
    have : c ≤ 3 := by omega
    interval_cases a <;> interval_cases b <;> interval_cases c <;> first | omega | decide
  · have : a ≤ 4 := by omega
    have : b ≤ 4 := by omega
    have : c ≤ 4 := by omega
    interval_cases a <;> interval_cases b <;> interval_cases c <;> first | omega | decide

/-- **thm:clasificacion, combinatorial half.** For `n ≥ 3`, every partition of `n` with exactly
four parts is biquanimous iff `n ∈ {3, 4, 6}` (`n = 3` vacuously). -/
theorem thm_clasificacion_comb (n : ℕ) (hn : 3 ≤ n) :
    (∀ p : Nat.Partition n, Multiset.card p.parts = 4 → Biquanimous p.parts) ↔
      n = 3 ∨ n = 4 ∨ n = 6 := by
  constructor
  · intro H
    by_contra hne
    have h5 : 5 ≤ n := by omega
    exact lamStar_not_biquanimous n h5 (by omega) (H _ (lamStar_card n (by omega)))
  · intro hn' p hp
    obtain ⟨a, b, c, d, habcd⟩ := Multiset.card_eq_four.mp hp
    have hpos := fun {i} (h : i ∈ p.parts) => p.parts_pos h
    rw [habcd] at hpos
    have hsum := p.parts_sum
    rw [habcd] at hsum ⊢
    simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton] at hsum
    have ha : 0 < a := hpos (by simp)
    have hb : 0 < b := hpos (by simp)
    have hc : 0 < c := hpos (by simp)
    have hd : 0 < d := hpos (by simp)
    rcases hn' with rfl | hn'
    · omega
    · exact four_parts_biq n hn' a b c d ha hb hc hd (by omega)

/-! ## Part 2: the count of cor:cuenta -/

variable {l : ℕ}

/-- The sign vector of a subset: `ε_A i = +1` on `A`, `-1` off `A`. -/
def eps (A : Finset (Fin l)) : Fin l → ℤˣ := fun i => if i ∈ A then 1 else -1

/-- The subset of a sign vector: the `+1` coordinates. -/
def plusSet (ε : Fin l → ℤˣ) : Finset (Fin l) := univ.filter fun i => ε i = 1

lemma neg_one_ne_one_units : (-1 : ℤˣ) ≠ 1 := by decide

lemma plusSet_eps (A : Finset (Fin l)) : plusSet (eps A) = A := by
  ext i; by_cases h : i ∈ A <;> simp [plusSet, eps, h, neg_one_ne_one_units]

lemma eps_plusSet (ε : Fin l → ℤˣ) : eps (plusSet ε) = ε := by
  funext i
  rcases Int.units_eq_one_or (ε i) with h | h <;>
    simp [plusSet, eps, h, neg_one_ne_one_units]

/-- `Σ wᵢ ε_A(i) = 2 Σ_A w - Σ w`. -/
lemma sum_eps (w : Fin l → ℤ) (A : Finset (Fin l)) :
    ∑ i, w i * (eps A i : ℤ) = 2 * ∑ i ∈ A, w i - ∑ i, w i := by
  have h : ∀ i, w i * (eps A i : ℤ) = 2 * (if i ∈ A then w i else 0) - w i := by
    intro i
    by_cases hi : i ∈ A
    · simp only [eps, hi, ite_true, Units.val_one, mul_one]; ring
    · simp only [eps, hi, ite_false, Units.val_neg, Units.val_one, mul_neg, mul_one]; ring
  simp_rw [h]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter]

/-- Sign vectors with `Σ wᵢ εᵢ = 0`. -/
def signZeros (w : Fin l → ℤ) : Finset (Fin l → ℤˣ) :=
  univ.filter fun ε => ∑ i, w i * (ε i : ℤ) = 0

/-- Equal-sum splittings: subsets `A` with `2 Σ_A w = n`, `n = Σ w`. -/
def halfSets (w : Fin l → ℤ) : Finset (Finset (Fin l)) :=
  univ.filter fun A => 2 * ∑ i ∈ A, w i = ∑ i, w i

/-- Sign vectors with `Σ wε = 0` ↔ subsets with `2 Σ_A w = n` (bijection `A ↦ ε_A`). -/
theorem card_signZeros (w : Fin l → ℤ) : #(signZeros w) = #(halfSets w) := by
  symm
  refine Finset.card_nbij' eps plusSet ?_ ?_ ?_ ?_
  · intro A hA
    simp only [halfSets, signZeros, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hA ⊢
    rw [sum_eps]; omega
  · intro ε hε
    simp only [halfSets, signZeros, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hε ⊢
    have := sum_eps w (plusSet ε)
    rw [eps_plusSet] at this
    omega
  · intro A _; exact plusSet_eps A
  · intro ε _; exact eps_plusSet ε

lemma neg_mem_signZeros (w : Fin l → ℤ) {ε : Fin l → ℤˣ} (h : ε ∈ signZeros w) :
    -ε ∈ signZeros w := by
  simp only [signZeros, mem_filter, mem_univ, true_and, Pi.neg_apply, Units.val_neg,
    mul_neg, Finset.sum_neg_distrib, neg_eq_zero] at h ⊢
  exact h

lemma ne_neg (hl : 0 < l) (ε : Fin l → ℤˣ) : ε ≠ -ε := by
  intro h
  have h0 := congrFun h ⟨0, hl⟩
  rw [Pi.neg_apply] at h0
  rcases Int.units_eq_one_or (ε ⟨0, hl⟩) with h1 | h1 <;> rw [h1] at h0
  · exact neg_one_ne_one_units h0.symm
  · exact neg_one_ne_one_units (by simpa using h0)

/-- Abstract fiber count: if `pt ε = pt η ↔ η = ±ε`, the image of `signZeros w` under `pt`
has exactly half as many elements. -/
theorem two_mul_card_image {P : Type*} [DecidableEq P] (hl : 0 < l) (w : Fin l → ℤ)
    (pt : (Fin l → ℤˣ) → P) (hpt : ∀ ε η, pt η = pt ε ↔ (η = ε ∨ η = -ε)) :
    2 * #((signZeros w).image pt) = #(signZeros w) := by
  rw [Finset.card_eq_sum_card_image pt (signZeros w)]
  rw [Finset.sum_const_nat (m := 2), mul_comm]
  intro b hb
  obtain ⟨ε, hε, rfl⟩ := Finset.mem_image.mp hb
  have : {a ∈ signZeros w | pt a = pt ε} = {ε, -ε} := by
    ext η
    simp only [mem_filter, hpt, mem_insert, mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro (rfl | rfl)
      · exact ⟨hε, Or.inl rfl⟩
      · exact ⟨neg_mem_signZeros w hε, Or.inr rfl⟩
  rw [this, Finset.card_pair (ne_neg hl ε)]

/-- The class of `ε` modulo `ε ~ -ε`, as the unordered pair `{ε, -ε}`. -/
def signClass (ε : Fin l → ℤˣ) : Sym2 (Fin l → ℤˣ) := s(ε, -ε)

/-- Solutions `Σ wε = 0` modulo `±`. -/
def signZerosMod (w : Fin l → ℤ) : Finset (Sym2 (Fin l → ℤˣ)) :=
  (signZeros w).image signClass

lemma signClass_eq_iff (ε η : Fin l → ℤˣ) :
    signClass η = signClass ε ↔ (η = ε ∨ η = -ε) := by
  simp only [signClass, Sym2.eq_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (rfl | rfl)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, neg_neg ε⟩

/-- **cor:cuenta, counting content.** For `l ≥ 1` weights `w` with total `n`,
`2 · #({ε ∈ {±1}^l : Σ wε = 0} / ±) = #{A ⊆ [l] : 2 Σ_A w = n}`. -/
theorem cor_cuenta_signos (hl : 0 < l) (w : Fin l → ℤ) :
    2 * #(signZerosMod w) = #(halfSets w) := by
  rw [signZerosMod, two_mul_card_image hl w signClass signClass_eq_iff, card_signZeros]

/-- **cor:cuenta, "in particular" (1).** The count vanishes iff the weights are not
biquanimous (no subset carries half the total). -/
theorem cor_cuenta_cero_iff (hl : 0 < l) (w : Fin l → ℤ) :
    #(signZerosMod w) = 0 ↔ ¬ ∃ A : Finset (Fin l), 2 * ∑ i ∈ A, w i = ∑ i, w i := by
  have h := cor_cuenta_signos hl w
  constructor
  · intro h0 ⟨A, hA⟩
    have hmem : A ∈ halfSets w := by simp [halfSets, hA]
    have : 0 < #(halfSets w) := Finset.card_pos.mpr ⟨A, hmem⟩
    omega
  · intro hno
    have : halfSets w = ∅ := by
      ext A; simp only [halfSets, mem_filter, mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      exact fun hA => hno ⟨A, hA⟩
    rw [this, Finset.card_empty] at h
    omega

/-- **cor:cuenta, "in particular" (2).** For odd total `n` the count is `0`. -/
theorem cor_cuenta_impar (hl : 0 < l) (w : Fin l → ℤ) (hodd : Odd (∑ i, w i)) :
    #(signZerosMod w) = 0 := by
  rw [cor_cuenta_cero_iff hl w]
  rintro ⟨A, hA⟩
  obtain ⟨k, hk⟩ := hodd
  omega

/-- **cor:cuenta with lem:sing as hypothesis.** `P` stands for projective space,
`pt ε = [ε]` with `[ε] = [η] ↔ η = ±ε` (true for `±1`-vectors in characteristic `≠ 2`),
and Lemma lem:sing (cited, not ours) is the hypothesis `hSing : Sing = {[ε] : Σ wε = 0}`.
Then `2 · #Sing = #{A : 2 Σ_A w = n}`. -/
theorem cor_cuenta_sing {P : Type*} [DecidableEq P] (hl : 0 < l) (w : Fin l → ℤ)
    (pt : (Fin l → ℤˣ) → P) (hpt : ∀ ε η, pt η = pt ε ↔ (η = ε ∨ η = -ε))
    (Sing : Finset P) (hSing : Sing = (signZeros w).image pt) :
    2 * #Sing = #(halfSets w) := by
  rw [hSing, two_mul_card_image hl w pt hpt, card_signZeros]

end P3c
