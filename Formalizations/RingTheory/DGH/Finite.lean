/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Formalizations.RingTheory.DGH.Absorb
import Formalizations.RingTheory.DGH.Basic
import Formalizations.RingTheory.DGH.JakobsOrder
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.Ring.Subring.Defs

/-!
# Finite strata of the DGH stratification

With `L = layer1 M` and the hypothesis that the chain of iterated sums `sumPow n L` grows
strictly for `n ≥ 1`:

## Main results

* `D_natCast_eq`: `D M n = sumPow n L` for every natural `n` (the minimal case-1 multiset at
  stratum `n ≥ 1` is `n+1` copies of `1`, via Jakobs' order);
* `D_omega_eq`, `D_omega_sumClosed`: `D M ω = ⋃ n, sumPow n L`, closed under sums;
* `D_omega_subring`: if moreover `L * L ⊆ L`, `D M ω` is the carrier of a subring of `R`;
* `A3`, `A4`: associativity and sum over a union, as set identities.
-/

open Pointwise Order

namespace DGH

noncomputable section

variable {R : Type} [Ring R]

/-! ### Iterated sums -/

lemma sumPow_one (S : Set R) : sumPow 1 S = S := by
  rw [sumPow_succ, sumPow_zero, Set.singleton_zero, add_zero]

lemma sumPow_add (a b : ℕ) (S : Set R) : sumPow (a + b) S = sumPow a S + sumPow b S := by
  induction a with
  | zero => rw [Nat.zero_add, sumPow_zero, Set.singleton_zero, zero_add]
  | succ a ih => rw [Nat.add_right_comm, sumPow_succ, ih, sumPow_succ, add_assoc]

lemma sumPow_subset_succ {S : Set R} (h0 : (0 : R) ∈ S) (n : ℕ) :
    sumPow n S ⊆ sumPow (n + 1) S := fun x hx => by
  rw [sumPow_succ]; exact Set.mem_add.2 ⟨0, h0, x, hx, zero_add x⟩

lemma sumPow_mono_le {S : Set R} (h0 : (0 : R) ∈ S) {m n : ℕ} (h : m ≤ n) :
    sumPow m S ⊆ sumPow n S := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (sumPow_subset_succ h0 _)

lemma zero_mem_layer1 (M : Set R) : (0 : R) ∈ layer1 M := by simp [layer1]

lemma one_mem_layer1 (M : Set R) : (1 : R) ∈ layer1 M := by simp [layer1]

lemma neg_layer1_subset (M : Set R) : -layer1 M ⊆ layer1 M := by
  intro x hx
  simp only [layer1, Set.mem_neg, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx ⊢
  rcases hx with ((h | h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl (neg_eq_zero.1 h)))
  · exact Or.inl (Or.inl (Or.inr (Or.inr (neg_eq_iff_eq_neg.1 h))))
  · exact Or.inl (Or.inl (Or.inr (Or.inl (neg_inj.1 h))))
  · exact Or.inr h
  · exact Or.inl (Or.inr (by simpa using h))

lemma neg_sumPow_subset {S : Set R} (hS : -S ⊆ S) (n : ℕ) : -sumPow n S ⊆ sumPow n S := by
  induction n with
  | zero =>
    intro x hx
    rw [Set.mem_neg, sumPow_zero, Set.mem_singleton_iff] at hx
    rw [sumPow_zero, Set.mem_singleton_iff, ← neg_eq_zero, hx]
  | succ n ih =>
    intro x hx
    rw [Set.mem_neg, sumPow_succ] at hx
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.1 hx
    rw [sumPow_succ]
    refine Set.mem_add.2 ⟨-a, hS (by rwa [Set.mem_neg, neg_neg]),
      -b, ih (by rwa [Set.mem_neg, neg_neg]), ?_⟩
    rw [← neg_add, hab, neg_neg]

/-! ### Lifting multisets of finite ordinals to `ℕ` -/

lemma exists_natCast_multiset (s : Multiset Ordinal.{0}) (n : ℕ)
    (h : ∀ x ∈ s, x ≤ (n : Ordinal.{0})) :
    ∃ s' : Multiset ℕ, (∀ k ∈ s', k ≤ n) ∧ s = s'.map (Nat.cast) := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, by simp, by simp⟩
  | cons a s ih =>
    obtain ⟨s', hs', rfl⟩ := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    have ha : a ≤ n := h a (Multiset.mem_cons_self a _)
    obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.1 (ha.trans_lt (Ordinal.natCast_lt_omega0 n))
    refine ⟨k ::ₘ s', ?_, by simp⟩
    intro j hj
    rcases Multiset.mem_cons.1 hj with rfl | hj
    · exact_mod_cast ha
    · exact hs' j hj

lemma sumSets_map_natCast (E : Ordinal.{0} → Set R) (S : Set R) (s' : Multiset ℕ)
    (hE : ∀ k ∈ s', E k = sumPow k S) : sumSets E (s'.map Nat.cast) = sumPow s'.sum S := by
  induction s' using Multiset.induction_on with
  | empty => simp [sumSets, Set.singleton_zero]
  | cons a s ih =>
    have h := ih (fun k hk => hE k (Multiset.mem_cons_of_mem hk))
    unfold sumSets at h ⊢
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons, h,
      hE a (Multiset.mem_cons_self a s), Multiset.sum_cons, sumPow_add]

lemma sum_le_count_one (s : Multiset ℕ) (h : ∀ k ∈ s, k ≤ 1) : s.sum ≤ Multiset.count 1 s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.sum_cons, Multiset.count_cons]
    have ha := h a (Multiset.mem_cons_self a s)
    have := ih (fun k hk => h k (Multiset.mem_cons_of_mem hk))
    split_ifs <;> omega

/-! ### (1) Finite strata -/

variable (M : Set R)

/-- Hypothesis H: the chain `sumPow n (layer1 M)` grows strictly from `n = 1` on. -/
def StrictChain : Prop := ∀ n : ℕ, 1 ≤ n → ¬ sumPow (n + 1) (layer1 M) ⊆ sumPow n (layer1 M)

/-- (1) Under H, every finite stratum `D M k` (`k ≤ n`) is `sumPow k (layer1 M)`. -/
theorem D_natCast_eq_aux (hH : StrictChain M) :
    ∀ n : ℕ, ∀ k ≤ n, D M (k : Ordinal.{0}) = sumPow k (layer1 M) := by
  set L := layer1 M with hLdef
  have h0 : (0 : R) ∈ L := zero_mem_layer1 M
  intro n
  induction n with
  | zero =>
    intro k hk
    rw [Nat.le_zero.1 hk, Nat.cast_zero, D_zero, sumPow_zero]
  | succ n ih =>
    intro k hk
    rcases Nat.lt_or_ge k (n + 1) with hk' | hk'
    · exact ih k (Nat.lt_succ_iff.1 hk')
    obtain rfl : k = n + 1 := le_antisymm hk hk'
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Nat.zero_add, Nat.cast_one, D_one, sumPow_one]
    have hDn : D M n = sumPow n L := ih n le_rfl
    have hcast : ((n + 1 : ℕ) : Ordinal.{0}) = succ (n : Ordinal.{0}) := by
      rw [Nat.cast_succ, Order.succ_eq_add_one]
    have hn0 : (n : Ordinal.{0}) ≠ 0 := by exact_mod_cast hn.ne'
    have hLn : L ⊆ sumPow n L := by
      have := sumPow_mono_le (S := L) h0 hn
      rwa [sumPow_one] at this
    have h1 : ¬ SumClosed (D M n) := by
      intro hc
      apply hH n hn
      rw [SumClosed, hDn] at hc
      refine (?_ : sumPow (n + 1) L ⊆ sumPow n L + sumPow n L).trans hc
      rw [sumPow_succ]
      exact Set.add_subset_add hLn le_rfl
    obtain ⟨s, hs, hmin, he⟩ := D_succ_case1 M hn0 h1
    set t : Multiset Ordinal.{0} := Multiset.replicate (n + 1) 1 with htdef
    have ht_eq : t = (Multiset.replicate (n + 1) (1 : ℕ)).map Nat.cast := by
      simp [t, Multiset.map_replicate]
    have hsumt : sumSets (D M) t = sumPow (n + 1) L := by
      rw [ht_eq, sumSets_map_natCast _ _ _ (fun k hk => ih k (by
        rw [Multiset.eq_of_mem_replicate hk]; exact hn))]
      have hs1 : (Multiset.replicate (n + 1) (1 : ℕ)).sum = n + 1 := by simp; omega
      rw [hs1]
    have htc : t ∈ sumCand (D M) n := by
      refine ⟨by simp [t], fun x hx => ?_, ?_⟩
      · rw [Multiset.eq_of_mem_replicate hx]; exact_mod_cast hn
      · rw [hsumt, hDn]; exact hH n hn
    have hst : s = t := by
      by_contra hne
      rcases jakobsLT_total hne with hlt | hlt
      · -- `s <_J t` forces `s` to be `0`s and at most `n` ones: not a candidate.
        obtain ⟨x, hx, hgt⟩ := hlt
        obtain ⟨s', hs'n, rfl⟩ := exists_natCast_multiset s n hs.2.1
        have hx1 : x = 1 :=
          Multiset.eq_of_mem_replicate (Multiset.count_pos.1 (lt_of_le_of_lt (Nat.zero_le _) hx))
        subst hx1
        have hle1 : ∀ k ∈ s', k ≤ 1 := by
          intro k hk
          by_contra hk1
          have hlt' : (1 : Ordinal.{0}) < k := by exact_mod_cast not_le.1 hk1
          have hk' : (k : Ordinal.{0}) ≠ 1 := ne_of_gt hlt'
          have hct : Multiset.count (k : Ordinal.{0}) t = 0 :=
            Multiset.count_eq_zero.2 fun hm => hk' (Multiset.eq_of_mem_replicate hm)
          have hcs : 0 < Multiset.count (k : Ordinal.{0}) (s'.map Nat.cast) :=
            Multiset.count_pos.2 (Multiset.mem_map_of_mem _ hk)
          have := hgt k hlt'
          omega
        have hc1 : Multiset.count (1 : ℕ) s' ≤ n := by
          have e : Multiset.count (1 : Ordinal.{0}) (s'.map Nat.cast) = Multiset.count 1 s' := by
            rw [← Nat.cast_one, Multiset.count_map_eq_count' _ _ Nat.cast_injective]
          have e2 : Multiset.count (1 : Ordinal.{0}) t = n + 1 := by
            simp [t]
          omega
        have hsum : s'.sum ≤ n := (sum_le_count_one s' hle1).trans hc1
        apply hs.2.2
        rw [sumSets_map_natCast _ _ _ (fun k hk => ih k (hs'n k hk)), hDn]
        exact sumPow_mono_le h0 hsum
      · exact hmin t htc (isDershowitzMannaLT_of_jakobsLT hlt)
    rw [hcast, he, hst, hsumt, hDn]
    exact Set.union_eq_right.2 (sumPow_subset_succ h0 n)

/-- (1) Under H, `D M n = sumPow n (layer1 M)` for every `n ≥ 1` (in fact for all `n`). -/
theorem D_natCast_eq (hH : StrictChain M) (n : ℕ) :
    D M (n : Ordinal.{0}) = sumPow n (layer1 M) :=
  D_natCast_eq_aux M hH n n le_rfl

/-! ### (2) The stratum `ω` -/

lemma omega0_not_succ : ¬ ∃ a : Ordinal.{0}, Ordinal.omega0 = succ a := by
  rintro ⟨a, ha⟩
  have : a < Ordinal.omega0 := ha ▸ lt_succ a
  obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.1 this
  have h : succ (k : Ordinal.{0}) < Ordinal.omega0 := by
    rw [Order.succ_eq_add_one]; exact_mod_cast Ordinal.natCast_lt_omega0 (k + 1)
  rw [← ha] at h
  exact lt_irrefl _ h

/-- (2) Under H, `D M ω = ⋃ n, sumPow n (layer1 M)`. -/
theorem D_omega_eq (hH : StrictChain M) :
    D M Ordinal.omega0 = ⋃ n : ℕ, sumPow n (layer1 M) := by
  rw [D_limit M Ordinal.omega0_ne_zero omega0_not_succ]
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨b, hb, hx⟩
    obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.1 hb
    exact ⟨k, D_natCast_eq M hH k ▸ hx⟩
  · rintro ⟨k, hx⟩
    exact ⟨k, Ordinal.natCast_lt_omega0 k, by rw [D_natCast_eq M hH k]; exact hx⟩

/-- (2) Under H, `D M ω` is closed under sums. -/
theorem D_omega_sumClosed (hH : StrictChain M) : SumClosed (D M Ordinal.omega0) := by
  rw [SumClosed, D_omega_eq M hH]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  simp only [Set.mem_iUnion] at hx hy ⊢
  obtain ⟨a, hx⟩ := hx
  obtain ⟨b, hy⟩ := hy
  exact ⟨a + b, by rw [sumPow_add]; exact Set.add_mem_add hx hy⟩

/-! ### (3) Products -/

omit M in
lemma sumPow_mul_subset {L : Set R} (hLL : L * L ⊆ L) (a b : ℕ) :
    sumPow a L * sumPow b L ⊆ sumPow (a * b) L := by
  induction a with
  | zero =>
    rw [sumPow_zero, Nat.zero_mul, sumPow_zero]
    rintro _ ⟨x, hx, y, -, rfl⟩
    rw [Set.mem_singleton_iff] at hx ⊢
    rw [hx]; exact zero_mul y
  | succ a ih =>
    calc (L + sumPow a L) * sumPow b L ⊆ L * sumPow b L + sumPow a L * sumPow b L :=
          Set.add_mul_subset _ _ _
      _ ⊆ sumPow b L + sumPow (a * b) L :=
          Set.add_subset_add ((mul_sumPow_subset L L b).trans (sumPow_mono b hLL)) ih
      _ = sumPow ((a + 1) * b) L := by
          rw [← sumPow_add]; congr 1; rw [Nat.succ_mul, Nat.add_comm]

/-- (3) Under H and `L * L ⊆ L`, `D M ω` is closed under products. -/
theorem D_omega_mulClosed (hH : StrictChain M) (hLL : layer1 M * layer1 M ⊆ layer1 M) :
    MulClosed (D M Ordinal.omega0) := by
  rw [MulClosed, D_omega_eq M hH]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  simp only [Set.mem_iUnion] at hx hy ⊢
  obtain ⟨a, hx⟩ := hx
  obtain ⟨b, hy⟩ := hy
  exact ⟨a * b, sumPow_mul_subset hLL a b (Set.mul_mem_mul hx hy)⟩

/-- (3) Under H and `L * L ⊆ L`, `D M ω` is a subring of `R` (contains `1`). -/
theorem D_omega_subring (hH : StrictChain M) (hLL : layer1 M * layer1 M ⊆ layer1 M) :
    ∃ S : Subring R, (S : Set R) = D M Ordinal.omega0 := by
  have hD := D_omega_eq M hH
  have h0 : (0 : R) ∈ D M Ordinal.omega0 := by
    rw [hD, Set.mem_iUnion]; exact ⟨0, rfl⟩
  have h1 : (1 : R) ∈ D M Ordinal.omega0 := by
    rw [hD, Set.mem_iUnion]; exact ⟨1, by rw [sumPow_one]; exact one_mem_layer1 M⟩
  have hneg : ∀ {x : R}, x ∈ D M Ordinal.omega0 → -x ∈ D M Ordinal.omega0 := by
    intro x hx
    simp only [hD, Set.mem_iUnion] at hx ⊢
    obtain ⟨n, hx⟩ := hx
    exact ⟨n, neg_sumPow_subset (neg_layer1_subset M) n (by rwa [Set.mem_neg, neg_neg])⟩
  exact ⟨{ carrier := D M Ordinal.omega0
           zero_mem' := h0
           one_mem' := h1
           add_mem' := fun hx hy => D_omega_sumClosed M hH (Set.add_mem_add hx hy)
           mul_mem' := fun hx hy => D_omega_mulClosed M hH hLL (Set.mul_mem_mul hx hy)
           neg_mem' := hneg }, rfl⟩

/-! ### (4) Set identities A3, A4 -/

omit M in
/-- A3: `X (A B) = (X A) B` for pointwise products of sets. -/
theorem A3 (X A B : Set R) : X * (A * B) = (X * A) * B := (mul_assoc X A B).symm

omit M in
/-- A4: if `D' = E ∪ (A + B)` then `P + D' ⊆ (P + E) ∪ (P + A + B)` (indeed equal). -/
theorem A4_eq {P D' E A B : Set R} (h : D' = E ∪ (A + B)) :
    P + D' = (P + E) ∪ (P + A + B) := by
  rw [h, Set.add_union, add_assoc]

omit M in
theorem A4 {P D' E A B : Set R} (h : D' = E ∪ (A + B)) :
    P + D' ⊆ (P + E) ∪ (P + A + B) :=
  (A4_eq h).subset

end

end DGH
