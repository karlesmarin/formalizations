/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Babbitt's common-tone theorem and the generalised hexachord theorem over ℤ_n

For `S ⊆ ℤ_n`, the tones common to `S` and its transposition `S + k` number the `k`-th entry of the
interval class vector for `2k < n`, and twice it at the tritone `2k = n` (Babbitt). For every `n`
and every `S` with `|S| = s`, the interval class vectors of `S` and its complement differ by exactly
`n − 2s` in every entry `2i < n` and by `n/2 − s` at the tritone (the generalised hexachord theorem,
with signs and for odd `n` too). Proof: the `n` ordered pairs `(a, a + d)` split into pairs inside
`S`, inside the complement and across.

## Main results

* `Hexachord.card_inter_image_add`: Babbitt: |S ∩ (S + k)| = icv_k (2k < n), = 2 icv_k (2k = n)
* `Hexachord.icv_compl`: generalised hexachord theorem with signs, every n
* `Hexachord.babbitt_and_hexachord`: both (Theorem of the Day)

## References

* R. Whitty, Theorem of the Day, «Milton Babbitt's Theorem» (MusicAndArt/Babbitt) and «The Generalised Hexachord Theorem» (MusicAndArt/Hexachord).
* M. Babbitt, D. Lewin (1950s); E. Amiot, A. Fourier-proof of the hexachord theorem (2006).
-/

@[expose] public section

namespace Hexachord

open Finset

/-- The `i`-th entry of the interval class vector of `S ⊆ ℤ_n`: the number of pairs `a < b` in `S` (by value in
`{0, …, n−1}`) with `min (b − a) (n − (b − a)) = i`. -/
def icv {n : ℕ} (S : Finset (ZMod n)) (i : ℕ) : ℕ :=
  ((S ×ˢ S).filter fun p => p.1.val < p.2.val ∧ min (p.2.val - p.1.val) (n - (p.2.val - p.1.val)) = i).card

variable {n : ℕ} [NeZero n]

/-- Number of ordered pairs `(a, a + d)` with both entries in `S`. -/
def N (S : Finset (ZMod n)) (d : ZMod n) : ℕ :=
  (univ.filter fun a => a ∈ S ∧ a + d ∈ S).card

theorem card_inter_image_eq_N (S : Finset (ZMod n)) (d : ZMod n) :
    (S ∩ S.image (· + d)).card = N S d := by
  unfold N
  have : S ∩ S.image (· + d) = (univ.filter fun a => a ∈ S ∧ a + d ∈ S).image (· + d) := by
    ext b
    simp only [mem_inter, mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hb, a, ha, rfl⟩
      exact ⟨a, ⟨ha, hb⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hb⟩, rfl⟩
      exact ⟨hb, a, ha, rfl⟩
  rw [this, card_image_of_injective _ (add_left_injective d)]

theorem N_compl (S : Finset (ZMod n)) (d : ZMod n) :
    (N Sᶜ d : ℤ) = N S d + n - 2 * S.card := by
  have hsum : ∀ T : Finset (ZMod n), (N T d : ℤ) =
      ∑ a : ZMod n, (if a ∈ T then (1 : ℤ) else 0) * (if a + d ∈ T then 1 else 0) := by
    intro T
    unfold N
    rw [Finset.natCast_card_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h1 : a ∈ T <;> by_cases h2 : a + d ∈ T <;> simp [h1, h2]
  have hcard : ∀ T : Finset (ZMod n), (T.card : ℤ) = ∑ a : ZMod n, (if a ∈ T then (1 : ℤ) else 0) := by
    intro T
    simp
  have hshift : ∑ a : ZMod n, (if a + d ∈ S then (1 : ℤ) else 0) = S.card := by
    rw [hcard S]
    exact Equiv.sum_comp (Equiv.addRight d) (fun a => if a ∈ S then (1 : ℤ) else 0)
  have hn : (n : ℤ) = ∑ _a : ZMod n, (1 : ℤ) := by simp [ZMod.card]
  have key : ∀ a : ZMod n, (if a ∈ Sᶜ then (1 : ℤ) else 0) * (if a + d ∈ Sᶜ then 1 else 0) =
      1 - (if a ∈ S then 1 else 0) - (if a + d ∈ S then 1 else 0) +
        (if a ∈ S then (1 : ℤ) else 0) * (if a + d ∈ S then 1 else 0) := by
    intro a
    by_cases h1 : a ∈ S <;> by_cases h2 : a + d ∈ S <;> simp [h1, h2]
  rw [hsum Sᶜ, hsum S]
  simp_rw [key]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hshift, ← hcard S, ← hn]
  ring

theorem val_add_lt (a : ZMod n) {k : ℕ} (hk : k < n) (h : a.val + k < n) :
    (a + (k : ZMod n)).val = a.val + k := by
  have h' := ZMod.val_add a (k : ZMod n)
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk] at h'
  rw [h', Nat.mod_eq_of_lt h]

theorem val_add_ge (a : ZMod n) {k : ℕ} (hk : k < n) (h : n ≤ a.val + k) :
    (a + (k : ZMod n)).val = a.val + k - n := by
  have h' := ZMod.val_add a (k : ZMod n)
  have hl := ZMod.val_lt a
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk] at h'
  rw [h', Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]

/-- Non-tritone case: `icv S k` counts the ordered pairs `(a, a + k)` in `S`. -/
theorem icv_eq_N (S : Finset (ZMod n)) {k : ℕ} (hk1 : 1 ≤ k) (hk : 2 * k < n) :
    icv S k = N S (k : ZMod n) := by
  unfold icv N
  symm
  have hk' : k < n := by omega
  refine Finset.card_bij
    (fun a _ => if a.val + k < n then (a, a + (k : ZMod n)) else (a + (k : ZMod n), a)) ?_ ?_ ?_
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    have hl := ZMod.val_lt a
    by_cases h : a.val + k < n
    · have hv := val_add_lt a hk' h
      simp only [h, ite_true, mem_filter, mem_product]
      refine ⟨⟨ha.1, ha.2⟩, ?_, ?_⟩ <;> omega
    · have hv := val_add_ge a hk' (by omega)
      simp only [h, ite_false, mem_filter, mem_product]
      refine ⟨⟨ha.2, ha.1⟩, ?_, ?_⟩ <;> omega
  · intro a ha b hb hab
    have hla := ZMod.val_lt a
    have hlb := ZMod.val_lt b
    apply ZMod.val_injective n
    by_cases h1 : a.val + k < n <;> by_cases h2 : b.val + k < n
    · simp only [h1, h2, ite_true, Prod.mk.injEq] at hab
      rw [hab.1]
    · have va := val_add_lt a hk' h1
      have vb := val_add_ge b hk' (by omega)
      simp only [h1, h2, ite_true, ite_false, Prod.mk.injEq] at hab
      have c1 := congrArg ZMod.val hab.1
      have c2 := congrArg ZMod.val hab.2
      omega
    · have va := val_add_ge a hk' (by omega)
      have vb := val_add_lt b hk' h2
      simp only [h1, h2, ite_true, ite_false, Prod.mk.injEq] at hab
      have c1 := congrArg ZMod.val hab.1
      have c2 := congrArg ZMod.val hab.2
      omega
    · simp only [h1, h2, ite_false, Prod.mk.injEq] at hab
      rw [hab.2]
  · rintro ⟨x, y⟩ hp
    simp only [mem_filter, mem_product] at hp
    obtain ⟨⟨hx, hy⟩, hlt, hmin⟩ := hp
    have hly := ZMod.val_lt y
    have hlx := ZMod.val_lt x
    by_cases hc : y.val = x.val + k
    · have hxy : x + (k : ZMod n) = y := by
        apply ZMod.val_injective n
        rw [val_add_lt x hk' (by omega)]
        omega
      have hlt' : x.val + k < n := by omega
      refine ⟨x, ?_, ?_⟩
      · simp only [mem_filter, mem_univ, true_and]
        exact ⟨hx, by rw [hxy]; exact hy⟩
      · simp only [hlt', ite_true, hxy]
    · have hyx : y + (k : ZMod n) = x := by
        apply ZMod.val_injective n
        rw [val_add_ge y hk' (by omega)]
        omega
      have hlt' : ¬ y.val + k < n := by omega
      refine ⟨y, ?_, ?_⟩
      · simp only [mem_filter, mem_univ, true_and]
        exact ⟨hy, by rw [hyx]; exact hx⟩
      · simp only [hlt', ite_false, hyx]

/-- Tritone case: every unordered pair gives two ordered pairs. -/
theorem N_eq_two_icv (S : Finset (ZMod n)) {k : ℕ} (hk1 : 1 ≤ k) (hk : 2 * k = n) :
    N S (k : ZMod n) = 2 * icv S k := by
  have hk' : k < n := by omega
  unfold N
  rw [← card_filter_add_card_filter_not (s := univ.filter fun a => a ∈ S ∧ a + (k : ZMod n) ∈ S)
    (fun a : ZMod n => a.val < k)]
  unfold icv
  have e1 : ((univ.filter fun a => a ∈ S ∧ a + (k : ZMod n) ∈ S).filter
      (fun a : ZMod n => a.val < k)).card =
      ((S ×ˢ S).filter fun p => p.1.val < p.2.val ∧
        min (p.2.val - p.1.val) (n - (p.2.val - p.1.val)) = k).card := by
    symm
    refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
    · rintro ⟨x, y⟩ hp
      simp only [mem_filter, mem_product] at hp
      obtain ⟨⟨hx, hy⟩, hlt, hmin⟩ := hp
      have hly := ZMod.val_lt y
      have hxy : x + (k : ZMod n) = y := by
        apply ZMod.val_injective n
        rw [val_add_lt x hk' (by omega)]
        omega
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨⟨hx, by rw [hxy]; exact hy⟩, by omega⟩
    · rintro ⟨x, y⟩ hp ⟨x', y'⟩ hq h
      simp only [mem_filter, mem_product] at hp hq
      have hly := ZMod.val_lt y
      have hly' := ZMod.val_lt y'
      simp only at h
      subst h
      have : y.val = y'.val := by omega
      rw [ZMod.val_injective n this]
    · intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha
      have hl := ZMod.val_lt a
      have hv := val_add_lt a hk' (by omega)
      refine ⟨(a, a + (k : ZMod n)), ?_, rfl⟩
      simp only [mem_filter, mem_product]
      refine ⟨⟨ha.1.1, ha.1.2⟩, ?_, ?_⟩ <;> omega
  have e2 : ((univ.filter fun a => a ∈ S ∧ a + (k : ZMod n) ∈ S).filter
      (fun a : ZMod n => ¬ a.val < k)).card =
      ((S ×ˢ S).filter fun p => p.1.val < p.2.val ∧
        min (p.2.val - p.1.val) (n - (p.2.val - p.1.val)) = k).card := by
    symm
    refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
    · rintro ⟨x, y⟩ hp
      simp only [mem_filter, mem_product] at hp
      obtain ⟨⟨hx, hy⟩, hlt, hmin⟩ := hp
      have hly := ZMod.val_lt y
      have hyx : y + (k : ZMod n) = x := by
        apply ZMod.val_injective n
        rw [val_add_ge y hk' (by omega)]
        omega
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨⟨hy, by rw [hyx]; exact hx⟩, by omega⟩
    · rintro ⟨x, y⟩ hp ⟨x', y'⟩ hq h
      simp only [mem_filter, mem_product] at hp hq
      have hly := ZMod.val_lt y
      have hly' := ZMod.val_lt y'
      have hlx := ZMod.val_lt x
      have hlx' := ZMod.val_lt x'
      simp only at h
      subst h
      have : x.val = x'.val := by omega
      rw [ZMod.val_injective n this]
    · intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha
      have hl := ZMod.val_lt a
      have hv := val_add_ge a hk' (by omega)
      refine ⟨(a + (k : ZMod n), a), ?_, rfl⟩
      simp only [mem_filter, mem_product]
      refine ⟨⟨ha.1.2, ha.1.1⟩, ?_, ?_⟩ <;> omega
  rw [e1, e2]
  ring

/-- **Babbitt's common-tone theorem**, both parts. -/
theorem card_inter_image_add (S : Finset (ZMod n)) :
    (∀ k : ℕ, 1 ≤ k → 2 * k < n → (S ∩ S.image (· + (k : ZMod n))).card = icv S k) ∧
    (∀ k : ℕ, 1 ≤ k → 2 * k = n → (S ∩ S.image (· + (k : ZMod n))).card = 2 * icv S k) :=
  ⟨fun _ h1 h2 => by rw [card_inter_image_eq_N, icv_eq_N S h1 h2],
   fun _ h1 h2 => by rw [card_inter_image_eq_N, N_eq_two_icv S h1 h2]⟩

/-- **Generalised hexachord theorem** (with signs, every `n`), both parts. -/
theorem icv_compl (S : Finset (ZMod n)) :
    (∀ i : ℕ, 1 ≤ i → 2 * i < n → (icv Sᶜ i : ℤ) = icv S i + (n - 2 * S.card)) ∧
    (∀ i : ℕ, 1 ≤ i → 2 * i = n → (icv Sᶜ i : ℤ) = icv S i + (i - S.card)) := by
  refine ⟨fun i h1 h2 => ?_, fun i h1 h2 => ?_⟩
  · have h := N_compl S (i : ZMod n)
    rw [← icv_eq_N S h1 h2, ← icv_eq_N Sᶜ h1 h2] at h
    linarith
  · have h := N_compl S (i : ZMod n)
    have a1 := N_eq_two_icv S h1 h2
    have a2 := N_eq_two_icv Sᶜ h1 h2
    rw [a1, a2] at h
    have : (n : ℤ) = 2 * i := by exact_mod_cast h2.symm
    push_cast at h
    linarith

theorem babbitt_and_hexachord (n : ℕ) [NeZero n] (S : Finset (ZMod n)) :
    (∀ k : ℕ, 1 ≤ k → 2 * k < n → (S ∩ S.image (· + (k : ZMod n))).card = icv S k) ∧
    (∀ k : ℕ, 1 ≤ k → 2 * k = n → (S ∩ S.image (· + (k : ZMod n))).card = 2 * icv S k) ∧
    (∀ i : ℕ, 1 ≤ i → 2 * i < n → (icv Sᶜ i : ℤ) = icv S i + (n - 2 * S.card)) ∧
    (∀ i : ℕ, 1 ≤ i → 2 * i = n → (icv Sᶜ i : ℤ) = icv S i + (i - S.card)) :=
  ⟨(card_inter_image_add S).1, (card_inter_image_add S).2, (icv_compl S).1, (icv_compl S).2⟩


end Hexachord
