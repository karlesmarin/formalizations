/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# A product of `X^d - 1` determines the multiset of exponents

If `∏_{d ∈ D} (X^d - 1) = ∏_{e ∈ E} (X^e - 1)` in `ℤ[X]` for multisets `D`, `E` of positive
integers, then `D = E`. Proof: map to `ℂ[X]`, compare the multiplicity of a primitive `m`-th root
of unity (which counts the elements of the multiset divisible by `m`), then recover the
multiplicities downward from the largest element.

## Main results

* `CyclotomicMultiset.multiset_eq_of_prod_X_pow_sub_one_eq`: the statement above.

## References

* C. Marín, *Schur polynomials twisted by roots of unity and reciprocal pairs: exactly three
  factors, and where they vanish*, arXiv:2608.09619 (2026), Proposition `prop:minimal`.
-/

@[expose] public section

open Polynomial

namespace CyclotomicMultiset

lemma countP_split {p : ℕ → Prop} [DecidablePred p] {n : ℕ} (hn : p n) (D : Multiset ℕ) :
    D.countP p = D.count n + D.countP (fun x => p x ∧ ¬ x = n) := by
  induction D using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.countP_cons, Multiset.count_cons, Multiset.countP_cons, ih]
    by_cases ha : a = n
    · subst ha; simp [hn]; omega
    · have ha' : ¬ n = a := fun e => ha e.symm
      by_cases hp : p a <;> simp [ha, ha', hp]; omega

lemma eq_of_countP_dvd {D E : Multiset ℕ} (hD : ∀ d ∈ D, 0 < d) (hE : ∀ e ∈ E, 0 < e)
    (h : ∀ m, 0 < m → D.countP (m ∣ ·) = E.countP (m ∣ ·)) : D = E := by
  classical
  set N := (D + E).sum with hN
  have outside : ∀ a, (a = 0 ∨ N < a) → D.count a = 0 ∧ E.count a = 0 := by
    intro a ha
    constructor
    · refine Multiset.count_eq_zero.2 fun hm => ?_
      have h1 := hD a hm
      have h2 : a ≤ N := Multiset.le_sum_of_mem (Multiset.mem_add.2 (Or.inl hm))
      omega
    · refine Multiset.count_eq_zero.2 fun hm => ?_
      have h1 := hE a hm
      have h2 : a ≤ N := Multiset.le_sum_of_mem (Multiset.mem_add.2 (Or.inr hm))
      omega
  have key : ∀ k n, N - n = k → D.count n = E.count n := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro n hk
      by_cases hn : n = 0 ∨ N < n
      · rw [(outside n hn).1, (outside n hn).2]
      · push Not at hn
        have hpos : 0 < n := Nat.pos_of_ne_zero hn.1
        have h1 := h n hpos
        rw [countP_split (p := (n ∣ ·)) (dvd_refl n) D,
          countP_split (p := (n ∣ ·)) (dvd_refl n) E] at h1
        have hf : D.filter (fun x => n ∣ x ∧ ¬ x = n) = E.filter (fun x => n ∣ x ∧ ¬ x = n) := by
          refine Multiset.ext' fun a => ?_
          rw [Multiset.count_filter, Multiset.count_filter]
          split_ifs with hq
          · by_cases ha : a = 0 ∨ N < a
            · rw [(outside a ha).1, (outside a ha).2]
            · push Not at ha
              have hle : n ≤ a := Nat.le_of_dvd (Nat.pos_of_ne_zero ha.1) hq.1
              have hlt : n < a := lt_of_le_of_ne hle (Ne.symm hq.2)
              exact ih (N - a) (by omega) a rfl
          · rfl
        have := congrArg Multiset.card hf
        rw [← Multiset.countP_eq_card_filter, ← Multiset.countP_eq_card_filter] at this
        omega
  exact Multiset.ext' fun n => key _ n rfl

lemma count_nthRoots (d m : ℕ) (hd : 0 < d) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) :
    (nthRoots d (1 : ℂ)).count ζ = if m ∣ d then 1 else 0 := by
  classical
  have hnd : (nthRoots d (1 : ℂ)).Nodup :=
    (Complex.isPrimitiveRoot_exp d hd.ne').nthRoots_one_nodup
  split_ifs with hdv
  · exact Multiset.count_eq_one_of_mem hnd
      ((mem_nthRoots hd).2 ((hζ.pow_eq_one_iff_dvd d).2 hdv))
  · refine Multiset.count_eq_zero.2 fun hm => hdv ?_
    exact (hζ.pow_eq_one_iff_dvd d).1 ((mem_nthRoots hd).1 hm)

lemma sum_ite_eq_countP (m : ℕ) (D : Multiset ℕ) :
    (D.map fun d => if m ∣ d then 1 else 0).sum = D.countP (m ∣ ·) := by
  classical
  induction D using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.countP_cons]
    by_cases ha : m ∣ a <;> simp [ha, add_comm]

lemma count_roots_prod (D : Multiset ℕ) (hD : ∀ d ∈ D, 0 < d) {m : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ m) :
    ((D.map fun d => (X : ℂ[X]) ^ d - 1).prod.roots).count ζ = D.countP (m ∣ ·) := by
  classical
  have h0 : (0 : ℂ[X]) ∉ D.map fun d => (X : ℂ[X]) ^ d - 1 := by
    intro hm
    obtain ⟨d, hd, hd0⟩ := Multiset.mem_map.1 hm
    have : (X ^ d - C 1 : ℂ[X]).Monic := monic_X_pow_sub_C 1 (hD d hd).ne'
    have h := this.ne_zero
    simp only [map_one] at h
    exact h (by simpa using hd0)
  rw [roots_multiset_prod _ h0, Multiset.count_bind, Multiset.map_map, ← sum_ite_eq_countP]
  congr 1
  refine Multiset.map_congr rfl fun d hd => ?_
  have : (X ^ d - 1 : ℂ[X]) = X ^ d - C 1 := by simp
  simp only [Function.comp, this]
  exact count_nthRoots d m (hD d hd) hζ

theorem multiset_eq_of_prod_X_pow_sub_one_eq {D E : Multiset ℕ} (hD : ∀ d ∈ D, 0 < d)
    (hE : ∀ e ∈ E, 0 < e)
    (h : (D.map fun d => (X : ℤ[X]) ^ d - 1).prod = (E.map fun e => (X : ℤ[X]) ^ e - 1).prod) :
    D = E := by
  have h' := congrArg (Polynomial.map (Int.castRingHom ℂ)) h
  simp only [Polynomial.map_multiset_prod, Multiset.map_map, Function.comp, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one] at h'
  refine eq_of_countP_dvd hD hE fun m hm => ?_
  have hζ := Complex.isPrimitiveRoot_exp m hm.ne'
  rw [← count_roots_prod D hD hζ, ← count_roots_prod E hE hζ, h']

end CyclotomicMultiset
