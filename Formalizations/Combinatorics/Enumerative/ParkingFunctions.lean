/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Prod
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
# The number of parking functions

A parking function of length `n` is `f : Fin n → Fin n` such that, for every `j`, at least `j + 1`
cars prefer a spot `≤ j`. There are `(n + 1)^(n - 1)` of them (Konheim–Weiss, 1966). The proof is
Pollak's circular argument: with `n` cars on `n + 1` spots in a circle, adding a constant to all
preferences rotates the configuration; exactly one rotation leaves spot `n` empty, and those are the
parking functions, so `(n + 1) · #parking = (n + 1)^n`.

## Main results

* `Parking.card_isParking`: there are (n + 1)^(n - 1) parking functions of length n >= 1

## References

* A. G. Konheim and B. Weiss, *An occupancy discipline and applications*, SIAM J. Appl. Math. 14 (1966), 1266–1274. Pollak's circular argument as in R. Stanley, *Enumerative Combinatorics*, Vol. 2.
-/

@[expose] public section

namespace Parking

/-- `f : Fin n → Fin n` is a **parking function** (spots `0, …, n-1`; car `i` prefers spot `f i`)
when every car parks: for every `j`, at least `j + 1` cars prefer a spot `≤ j`. -/
def IsParking {n : ℕ} (f : Fin n → Fin n) : Prop :=
  ∀ j : Fin n, j.val + 1 ≤ (Finset.univ.filter fun i => (f i).val ≤ j.val).card

instance {n : ℕ} : DecidablePred (@IsParking n) := fun _ => by
  unfold IsParking; infer_instance

open Fin.CommRing

/-- Circular version: `n` cars, `n+1` spots, spot `n` stays empty. -/
def Q {n : ℕ} (g : Fin n → Fin (n + 1)) : Prop :=
  ∀ j : ℕ, j < n → j + 1 ≤ (Finset.univ.filter fun i => (g i).val ≤ j).card

/-- Uniqueness of the rotation. -/
lemma uniq {n : ℕ} (h : Fin n → Fin (n + 1)) (d : Fin (n + 1)) (h1 : Q h)
    (h2 : Q (fun i => h i + d)) : d = 0 := by
  by_contra hd
  have hd1 : 1 ≤ d.val := by
    by_contra hc
    apply hd
    have h0 : d.val = 0 := by omega
    exact Fin.ext (by simpa using h0)
  have hdn : d.val ≤ n := Nat.lt_succ_iff.1 d.isLt
  have hA := h1 (n - d.val) (by omega)
  have hB := h2 (d.val - 1) (by omega)
  have hdis : Disjoint (Finset.univ.filter fun i => (h i).val ≤ n - d.val)
      (Finset.univ.filter fun i => ((fun i => h i + d) i).val ≤ d.val - 1) := by
    rw [Finset.disjoint_filter]
    intro i _ h3 h4
    have hh := (h i).isLt
    simp only [Fin.val_add] at h4
    rw [Nat.mod_eq_of_lt (by omega)] at h4
    omega
  have := (Finset.card_union_of_disjoint hdis).symm.le.trans (Finset.card_le_univ _)
  rw [Fintype.card_fin] at this
  beta_reduce at hB this
  omega

lemma exists_shift {n : ℕ} (g : Fin n → Fin (n + 1)) : ∃ c : Fin (n + 1), Q (fun i => g i + c) := by
  classical
  let cnt : ℕ → ℕ := fun x => (Finset.univ.filter fun i => (g i).val < x).card
  let key : ℕ → ℤ := fun x => ((cnt x : ℤ) - x) * (n + 1) + x
  obtain ⟨t, ht, hmin⟩ := Finset.exists_min_image (Finset.range (n + 1)) key ⟨0, by simp⟩
  have htn : t ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)
  have hcnt0 : cnt 0 = 0 := by simp [cnt]
  have hcntm : cnt (n + 1) = n := by
    simp only [cnt]
    rw [Finset.filter_true_of_mem (fun i _ => (g i).isLt)]
    simp
  have hsplit : ∀ x, cnt x + (Finset.univ.filter fun i => x ≤ (g i).val).card = n := by
    intro x
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i => (g i).val < x)
    simpa [cnt, not_lt] using this
  have hge : ∀ x, x ≤ n → t ≤ x → (cnt t : ℤ) - t ≤ cnt x - x := by
    intro x hx htx
    have h1 := hmin x (Finset.mem_range.2 (by omega))
    simp only [key] at h1
    by_contra hc
    have h2 : (cnt x : ℤ) - x ≤ cnt t - t - 1 := by omega
    nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ ((cnt t : ℤ) - t) - ((cnt x : ℤ) - x) - 1)
      (by omega : (0:ℤ) ≤ (n:ℤ) + 1)]
  have hgt : ∀ x, x < t → (cnt t : ℤ) - t < cnt x - x := by
    intro x hx
    have h1 := hmin x (Finset.mem_range.2 (by omega))
    simp only [key] at h1
    by_contra hc
    have h2 : (cnt x : ℤ) - x ≤ cnt t - t := by omega
    nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ ((cnt t : ℤ) - t) - ((cnt x : ℤ) - x))
      (by omega : (0:ℤ) ≤ (n:ℤ) + 1)]
  have hneg : 1 ≤ t → (cnt t : ℤ) - t ≤ -1 := by
    intro ht1
    have h1 := hmin 0 (Finset.mem_range.2 (by omega))
    simp only [key, hcnt0] at h1
    push_cast at h1
    by_contra hc
    have h2 : (0:ℤ) ≤ (cnt t : ℤ) - t := by omega
    nlinarith [mul_nonneg h2 (by omega : (0:ℤ) ≤ (n:ℤ) + 1)]
  obtain ⟨c, hcv⟩ : ∃ c : Fin (n + 1), c.val = (n + 1 - t) % (n + 1) :=
    ⟨⟨_, Nat.mod_lt _ (Nat.succ_pos n)⟩, rfl⟩
  refine ⟨c, ?_⟩
  have hv : ∀ i, (g i + c).val =
      if t ≤ (g i).val then (g i).val - t else (g i).val + (n + 1) - t := by
    intro i
    have hgi := (g i).isLt
    rw [Fin.val_add, hcv, Nat.add_mod_mod]
    split_ifs with h
    · have : (g i).val + (n + 1 - t) = ((g i).val - t) + (n + 1) := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
  intro j hj
  show j + 1 ≤ (Finset.univ.filter fun i => (g i + c).val ≤ j).card
  by_cases hA : t + (j + 1) ≤ n + 1
  · have hU : (Finset.univ.filter fun i => (g i).val < t + (j + 1)) =
        (Finset.univ.filter fun i => (g i).val < t) ∪
        (Finset.univ.filter fun i => (g i + c).val ≤ j) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and, hv]
      have := (g i).isLt
      split_ifs <;> omega
    have hD : Disjoint (Finset.univ.filter fun i => (g i).val < t)
        (Finset.univ.filter fun i => (g i + c).val ≤ j) := by
      rw [Finset.disjoint_filter]
      intro i _ h1 h2
      rw [hv] at h2
      split_ifs at h2 <;> omega
    have hc := congrArg Finset.card hU
    rw [Finset.card_union_of_disjoint hD] at hc
    change cnt (t + (j + 1)) = cnt t + _ at hc
    by_cases hB : t + (j + 1) ≤ n
    · have := hge (t + (j + 1)) hB (by omega)
      push_cast at this
      omega
    · have h1 : t + (j + 1) = n + 1 := by omega
      have ht1 : 1 ≤ t := by omega
      have := hneg ht1
      rw [h1, hcntm] at hc
      omega
  · have hU : (Finset.univ.filter fun i => (g i + c).val ≤ j) =
        (Finset.univ.filter fun i => t ≤ (g i).val) ∪
        (Finset.univ.filter fun i => (g i).val < t + (j + 1) - (n + 1)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and, hv]
      have := (g i).isLt
      split_ifs <;> omega
    have hD : Disjoint (Finset.univ.filter fun i => t ≤ (g i).val)
        (Finset.univ.filter fun i => (g i).val < t + (j + 1) - (n + 1)) := by
      rw [Finset.disjoint_filter]
      intro i _ h1 h2
      omega
    rw [hU, Finset.card_union_of_disjoint hD]
    have h3 := hgt (t + (j + 1) - (n + 1)) (by omega)
    have h4 := hsplit t
    change (Finset.univ.filter fun i => t ≤ (g i).val).card +
      cnt (t + (j + 1) - (n + 1)) ≥ _
    omega

lemma card_Q (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {g : Fin n → Fin (n + 1) // Q g} = (n + 1) ^ (n - 1) := by
  have hbij : Function.Bijective
      (fun p : Fin (n + 1) × {g : Fin n → Fin (n + 1) // Q g} =>
        (fun i => p.2.1 i - p.1 : Fin n → Fin (n + 1))) := by
    constructor
    · rintro ⟨c, h, hh⟩ ⟨c', h', hh'⟩ e
      have e1 : ∀ i, h' i = h i + (c' - c) := by
        intro i
        have := congrFun e i
        simp only at this
        linear_combination -this
      have hq : Q (fun i => h i + (c' - c)) := by
        have : h' = fun i => h i + (c' - c) := funext e1
        rw [← this]; exact hh'
      have h0 := uniq h (c' - c) hh hq
      have hcc : c = c' := (sub_eq_zero.1 h0).symm
      subst hcc
      have : h = h' := funext fun i => by rw [e1 i]; simp
      subst this
      rfl
    · intro g
      obtain ⟨c, hc⟩ := exists_shift g
      refine ⟨(c, ⟨fun i => g i + c, hc⟩), ?_⟩
      funext i
      simp
  have h1 := Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin n → Fin (n + 1))] at h1
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin] at h1
  have h2 : (n + 1) * Nat.card {g : Fin n → Fin (n + 1) // Q g} = (n + 1) * (n + 1) ^ (n - 1) := by
    rw [h1.trans (by rfl)]
    · rw [← pow_succ']; congr 1; omega
  exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n) h2

lemma card_park (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {f : Fin n → Fin n // IsParking f} = Nat.card {g : Fin n → Fin (n + 1) // Q g} := by
  classical
  have hmap : ∀ f : {f : Fin n → Fin n // IsParking f}, Q (fun i => Fin.castSucc (f.1 i)) := by
    intro f j hj
    have := f.2 ⟨j, hj⟩
    simpa using this
  apply Nat.card_congr
  refine Equiv.ofBijective (fun f => ⟨fun i => Fin.castSucc (f.1 i), hmap f⟩) ⟨?_, ?_⟩
  · intro f f' e
    apply Subtype.ext
    funext i
    have := congrFun (congrArg Subtype.val e) i
    exact Fin.castSucc_injective _ this
  · rintro ⟨g, hg⟩
    have hall : ∀ i, (g i).val < n := by
      by_contra hc
      push Not at hc
      obtain ⟨i, hi⟩ := hc
      have h1 := hg (n - 1) (by omega)
      have h2 : (Finset.univ.filter fun i => (g i).val ≤ n - 1) ⊂ Finset.univ := by
        rw [Finset.filter_ssubset]
        exact ⟨i, Finset.mem_univ _, by omega⟩
      have h3 := Finset.card_lt_card h2
      simp at h3
      omega
    refine ⟨⟨fun i => ⟨(g i).val, hall i⟩, ?_⟩, ?_⟩
    · intro j
      have := hg j.val j.isLt
      simpa using this
    · apply Subtype.ext
      funext i
      exact Fin.ext rfl

/-- **Konheim–Weiss (1966).** There are `(n + 1)^(n - 1)` parking functions of length `n ≥ 1`. -/
theorem card_isParking (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card {f : Fin n → Fin n // IsParking f} = (n + 1) ^ (n - 1) := by
  rw [← Nat.card_eq_fintype_card, card_park n hn, card_Q n hn]

end Parking
