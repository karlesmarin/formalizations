/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

/-!
# Dedekind sums through the sawtooth function

`DedekindSum.saw k n = ((n/k))` for `n : ℤ`, `0 < k` (`0` when `k ∣ n`, otherwise
`(n mod k)/k − 1/2`), and `DedekindSum.ded h k = s(h, k) = ∑_{r mod k} ((r/k)) ((hr/k))`. Mathlib
has neither (checked at the pinned commit).

## Main results

* `DedekindSum.ded_congr`: `s(h, k)` depends only on `h mod k`.
* `DedekindSum.ded_neg`: `s(−h, k) = −s(h, k)`.
* `DedekindSum.ded_reciprocity`: `s(h, k) + s(k, h) = (h² + k² + 1)/(12hk) − 1/4` for coprime
  `h, k ≥ 1` (elementary proof: the permutation `r ↦ hr mod k` and a lattice-point count of
  `∑ ⌊hr/k⌋²`).
* `DedekindSum.ded_inv`: `s(h⁻¹, k) = s(h, k)`.
* `DedekindSum.saw_dist`: the distribution relation `∑_{j<q} (((n + jm)/(qm))) = ((n/m))`.
* `DedekindSum.ded_scale`: `s(qy, qm) = s(y, m)`.
* `DedekindSum.petersson_knopp_prime`: for `q` prime,
  `∑_{l<q} s(x + lm, qm) = (q + 1) s(x, m) − s(qx, m)`.
* `DedekindSum.petersson_knopp_coprime_lifts`: the version for `q ∤ m`, `qy ≡ x (mod m)`.

## References

* S. R. Louboutin and M. Munsch, Canad. J. Math. 75 (2023), 1711–1743, arXiv:2205.01024 (its
  Conjecture 5.7 is the motivation).
-/

@[expose] public section

namespace DedekindSum

open Finset

/-- The sawtooth `((n/k))`. -/
def saw (k : ℕ) (n : ℤ) : ℚ :=
  if n % (k : ℤ) = 0 then 0 else ((n % (k : ℤ) : ℤ) : ℚ) / k - 1 / 2

/-- The Dedekind sum `s(h,k) = Σ_{r=0}^{k-1} ((r/k)) ((hr/k))`. -/
def ded (h : ℤ) (k : ℕ) : ℚ := ∑ r ∈ range k, saw k r * saw k (h * r)

lemma saw_emod (k : ℕ) (n : ℤ) : saw k (n % k) = saw k n := by
  unfold saw; rw [Int.emod_emod]

lemma saw_congr {k : ℕ} {n n' : ℤ} (h : n ≡ n' [ZMOD k]) : saw k n = saw k n' := by
  have e : n % k = n' % k := h
  rw [← saw_emod k n, e, saw_emod]

/-- (a) `s(h,k)` depends only on `h mod k`. -/
theorem ded_congr {h h' : ℤ} {k : ℕ} (hh : h ≡ h' [ZMOD k]) : ded h k = ded h' k := by
  unfold ded
  refine sum_congr rfl fun r _ => ?_
  rw [saw_congr (hh.mul_right (r : ℤ))]

lemma saw_neg {k : ℕ} (hk : 0 < k) (n : ℤ) : saw k (-n) = -saw k n := by
  unfold saw
  rw [Int.neg_emod]
  by_cases hd : (k : ℤ) ∣ n
  · have : n % k = 0 := Int.emod_eq_zero_of_dvd hd
    simp [hd, this]
  · have h1 : n % (k : ℤ) ≠ 0 := fun h0 => hd (Int.dvd_of_emod_eq_zero h0)
    have hk' : (0 : ℤ) < k := by exact_mod_cast hk
    have hlt : n % (k : ℤ) < k := Int.emod_lt_of_pos n hk'
    have h2 : ((k : ℤ).natAbs : ℤ) - n % (k : ℤ) ≠ 0 := by
      rw [Int.natAbs_natCast]; omega
    simp only [hd, ite_false, h1, h2]
    rw [Int.natAbs_natCast]
    have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
    push_cast
    field_simp
    ring

/-- (b) `s(−h,k) = −s(h,k)`. -/
theorem ded_neg (h : ℤ) (k : ℕ) : ded (-h) k = -ded h k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [ded]
  unfold ded
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun r _ => ?_
  rw [neg_mul, saw_neg hk, mul_neg]

/-! ### Two-term reciprocity (and the inverse symmetry of (F2)) -/

/-- Multiplication by a unit permutes the residues `0, …, k-1`. -/
lemma perm_sum {h k : ℕ} (hc : Nat.Coprime h k) (F : ℕ → ℚ) :
    ∑ r ∈ range k, F (h * r % k) = ∑ r ∈ range k, F r := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hinj : Set.InjOn (fun r => h * r % k) (range k) := by
    intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    have h1 : h * a ≡ h * b [MOD k] := hab
    have h2 := Nat.ModEq.cancel_left_of_coprime (Nat.Coprime.symm hc) h1
    unfold Nat.ModEq at h2
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2
  have himg : (range k).image (fun r => h * r % k) = range k := by
    apply eq_of_subset_of_card_le
    · intro x hx
      simp only [mem_image, mem_range] at hx ⊢
      obtain ⟨r, _, rfl⟩ := hx
      exact Nat.mod_lt _ hk
    · rw [card_image_of_injOn hinj]
  calc ∑ r ∈ range k, F (h * r % k) = ∑ x ∈ (range k).image (fun r => h * r % k), F x :=
        (sum_image hinj).symm
    _ = _ := by rw [himg]

/-- **(F2)** `s(h⁻¹,k) = s(h,k)`: if `h h' ≡ 1 (mod k)` then `s(h',k) = s(h,k)`. -/
theorem ded_inv {h h' k : ℕ} (hinv : h * h' ≡ 1 [MOD k]) : ded h' k = ded h k := by
  have hc : Nat.Coprime h k := Nat.coprime_of_mul_modEq_one h' hinv
  have hmod : ∀ n : ℕ, saw k ((n % k : ℕ) : ℤ) = saw k (n : ℤ) := fun n => by
    rw [Int.natCast_mod, saw_emod]
  unfold ded
  rw [← perm_sum hc (fun r => saw k (r : ℤ) * saw k ((h' : ℤ) * (r : ℤ)))]
  refine sum_congr rfl fun r _ => ?_
  have e1 : saw k ((h * r % k : ℕ) : ℤ) = saw k ((h : ℤ) * r) := by rw [hmod, Nat.cast_mul]
  have e2 : saw k ((h' : ℤ) * ((h * r % k : ℕ) : ℤ)) = saw k (r : ℤ) := by
    apply saw_congr
    rw [← Nat.cast_mul, Int.natCast_modEq_iff]
    calc h' * (h * r % k) ≡ h' * (h * r) [MOD k] := Nat.ModEq.mul_left _ (Nat.mod_modEq _ _)
      _ = (h * h') * r := by ring
      _ ≡ 1 * r [MOD k] := Nat.ModEq.mul_right _ hinv
      _ = r := one_mul r
  rw [e1, e2, mul_comm]

lemma sum_id (k : ℕ) : ∑ r ∈ range k, (r : ℚ) = k * (k - 1) / 2 := by
  induction k with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

lemma sum_sq (k : ℕ) : ∑ r ∈ range k, (r : ℚ) ^ 2 = (k - 1) * k * (2 * k - 1) / 6 := by
  induction k with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

lemma sum_odd (n : ℕ) : ∑ i ∈ Ico 1 (n + 1), (2 * (i : ℚ) - 1) = (n : ℚ) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_Ico_succ_top (by omega), ih]; push_cast; ring

lemma rho_cast (h k r : ℕ) : ((h * r % k : ℕ) : ℚ) = h * r - k * ((h * r / k : ℕ) : ℚ) := by
  have := congrArg (Nat.cast : ℕ → ℚ) (Nat.div_add_mod (h * r) k)
  push_cast at this
  linarith

/-- `P h k = Σ r ⌊hr/k⌋`, `Q h k = Σ ⌊hr/k⌋²`, `M h k = Σ ⌊hr/k⌋` (r over `range k`). -/
def P (h k : ℕ) : ℚ := ∑ r ∈ range k, (r : ℚ) * ((h * r / k : ℕ) : ℚ)
def Q (h k : ℕ) : ℚ := ∑ r ∈ range k, ((h * r / k : ℕ) : ℚ) ^ 2
def M (h k : ℕ) : ℚ := ∑ r ∈ range k, ((h * r / k : ℕ) : ℚ)

/-- Σ (hr mod k) = Σ r. -/
lemma eqn1 {h k : ℕ} (hc : Nat.Coprime h k) :
    (h : ℚ) * (k * (k - 1) / 2) - k * M h k = k * (k - 1) / 2 := by
  have := perm_sum hc (fun x => (x : ℚ))
  simp only [rho_cast] at this
  rw [sum_sub_distrib, ← mul_sum, sum_id, ← mul_sum] at this
  unfold M
  linarith

/-- Σ (hr mod k)² = Σ r². -/
lemma eqn2 {h k : ℕ} (hc : Nat.Coprime h k) :
    (h : ℚ) ^ 2 * ((k - 1) * k * (2 * k - 1) / 6) - 2 * h * k * P h k + k ^ 2 * Q h k
      = (k - 1) * k * (2 * k - 1) / 6 := by
  have := perm_sum hc (fun x => (x : ℚ) ^ 2)
  simp only [rho_cast] at this
  have e : ∀ r ∈ range k, ((h : ℚ) * r - k * ((h * r / k : ℕ) : ℚ)) ^ 2
      = (h : ℚ) ^ 2 * (r : ℚ) ^ 2 - 2 * h * k * ((r : ℚ) * ((h * r / k : ℕ) : ℚ))
        + (k : ℚ) ^ 2 * ((h * r / k : ℕ) : ℚ) ^ 2 := fun r _ => by ring
  rw [sum_congr rfl e, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum,
    sum_sq] at this
  unfold P Q
  linarith

/-- `s(h,k)` through `P` and `M`. -/
lemma ded_formula {h k : ℕ} (hc : Nat.Coprime h k) (hk : 0 < k) :
    ded h k = (h : ℚ) * ((k - 1) * k * (2 * k - 1) / 6) / k ^ 2 - P h k / k
      - (k * (k - 1) / 2) / (2 * k) - h * (k * (k - 1) / 2) / (2 * k) + M h k / 2
      + k / 4 - 1 / 4 := by
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  -- termwise
  have term : ∀ r ∈ range k, saw k (r : ℤ) * saw k ((h : ℤ) * (r : ℤ))
      = ((r : ℚ) / k - 1 / 2) * (((h * r % k : ℕ) : ℚ) / k - 1 / 2)
        - (if r = 0 then 1 / 4 else 0) := by
    intro r hr
    rw [mem_range] at hr
    have e : ((h : ℤ) * (r : ℤ)) % (k : ℤ) = ((h * r % k : ℕ) : ℤ) := by
      rw [Int.natCast_mod, Nat.cast_mul]
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · simp [saw]; norm_num
    · have er : (r : ℤ) % (k : ℤ) = (r : ℤ) := by
        rw [← Int.natCast_mod, Nat.mod_eq_of_lt hr]
      have hne : h * r % k ≠ 0 := by
        intro h0
        have hd : k ∣ h * r := Nat.dvd_of_mod_eq_zero h0
        have := Nat.eq_zero_of_dvd_of_lt ((Nat.Coprime.symm hc).dvd_of_dvd_mul_left hd) hr
        omega
      have hr0' : r ≠ 0 := by omega
      unfold saw
      rw [e, er]
      simp only [Nat.cast_eq_zero, hr0', hne, ite_false, Int.cast_natCast]
      ring
  unfold ded
  rw [sum_congr rfl term, sum_sub_distrib, sum_ite_eq' (range k) 0, ite_eq_left (mem_range.2 hk)]
  simp only [rho_cast]
  have e2 : ∀ r ∈ range k, ((r : ℚ) / k - 1 / 2) * (((h : ℚ) * r - k * ((h * r / k : ℕ) : ℚ)) / k - 1 / 2)
      = (h : ℚ) / k ^ 2 * (r : ℚ) ^ 2 - 1 / k * ((r : ℚ) * ((h * r / k : ℕ) : ℚ))
        - (1 / (2 * k) + h / (2 * k)) * (r : ℚ) + 1 / 2 * ((h * r / k : ℕ) : ℚ) + 1 / 4 := by
    intro r _; field_simp; ring
  rw [sum_congr rfl e2, sum_add_distrib, sum_add_distrib, sum_sub_distrib, sum_sub_distrib,
    ← mul_sum, ← mul_sum, ← mul_sum, ← mul_sum, sum_id, sum_sq, sum_const, card_range]
  unfold P M
  simp only [nsmul_eq_mul]
  field_simp
  ring

/-- For `r < k`: `⌊hr/k⌋² = Σ_{1 ≤ i < h, ki ≤ hr} (2i − 1)`. -/
lemma sq_as_sum {h k r : ℕ} (hh : 0 < h) (hk : 0 < k) (hr : r < k) :
    ((h * r / k : ℕ) : ℚ) ^ 2 = ∑ i ∈ Ico 1 h, if k * i ≤ h * r then (2 * (i : ℚ) - 1) else 0 := by
  rw [← sum_filter]
  have hμ : h * r / k < h := by
    rw [Nat.div_lt_iff_lt_mul hk]
    nlinarith
  have hf : (Ico 1 h).filter (fun i => k * i ≤ h * r) = Ico 1 (h * r / k + 1) := by
    ext i
    simp only [mem_filter, mem_Ico]
    have hiff : k * i ≤ h * r ↔ i ≤ h * r / k := by
      rw [Nat.le_div_iff_mul_le hk, Nat.mul_comm i k]
    rw [hiff]
    omega
  rw [hf, sum_odd]

/-- For `1 ≤ i < h`: `#{r < k : hr ≤ ki} = ⌊ki/h⌋ + 1`. -/
lemma count_as_sum {h k i : ℕ} (hh : 0 < h) (hk : 0 < k) (hi : i < h) :
    ((k * i / h : ℕ) : ℚ) + 1 = ∑ r ∈ range k, if h * r ≤ k * i then (1 : ℚ) else 0 := by
  rw [sum_boole]
  have hν : k * i / h < k := by
    rw [Nat.div_lt_iff_lt_mul hh]
    nlinarith
  have hf : (range k).filter (fun r => h * r ≤ k * i) = range (k * i / h + 1) := by
    ext r
    simp only [mem_filter, mem_range]
    have hiff : h * r ≤ k * i ↔ r ≤ k * i / h := by
      rw [Nat.le_div_iff_mul_le hh, Nat.mul_comm r h]
    rw [hiff]
    omega
  rw [hf, card_range]
  push_cast
  ring

/-- Lattice-point double count: `Q h k + 2 P k h − M k h + (h−1)² = k (h−1)²`. -/
lemma eqn3 {h k : ℕ} (hc : Nat.Coprime h k) (hh : 0 < h) (hk : 0 < k) :
    Q h k + 2 * P k h - M k h + ((h : ℚ) - 1) ^ 2 = k * ((h : ℚ) - 1) ^ 2 := by
  -- left block
  have hQ : Q h k = ∑ r ∈ range k, ∑ i ∈ Ico 1 h,
      (if k * i ≤ h * r then (2 * (i : ℚ) - 1) else 0) := by
    unfold Q
    exact sum_congr rfl fun r hr => sq_as_sum hh hk (mem_range.1 hr)
  -- right block
  have hR : 2 * P k h - M k h + ((h : ℚ) - 1) ^ 2 = ∑ i ∈ Ico 1 h, ∑ r ∈ range k,
      (if h * r ≤ k * i then (2 * (i : ℚ) - 1) else 0) := by
    have e1 : ∀ i ∈ Ico 1 h, ∑ r ∈ range k, (if h * r ≤ k * i then (2 * (i : ℚ) - 1) else 0)
        = (2 * (i : ℚ) - 1) * (((k * i / h : ℕ) : ℚ) + 1) := by
      intro i hi
      rw [count_as_sum hh hk (mem_Ico.1 hi).2, mul_sum]
      refine sum_congr rfl fun r _ => ?_
      split_ifs <;> ring
    rw [sum_congr rfl e1]
    have e2 : ∀ i ∈ Ico 1 h, (2 * (i : ℚ) - 1) * (((k * i / h : ℕ) : ℚ) + 1)
        = (2 * ((i : ℚ) * ((k * i / h : ℕ) : ℚ)) - ((k * i / h : ℕ) : ℚ)) + (2 * (i : ℚ) - 1) :=
      fun i _ => by ring
    rw [sum_congr rfl e2, sum_add_distrib]
    have hodd : ∑ i ∈ Ico 1 h, (2 * (i : ℚ) - 1) = ((h : ℚ) - 1) ^ 2 := by
      obtain ⟨n, rfl⟩ : ∃ n, h = n + 1 := ⟨h - 1, by omega⟩
      rw [sum_odd]; push_cast; ring
    rw [hodd]
    have hshift : ∑ i ∈ range h, (2 * ((i : ℚ) * ((k * i / h : ℕ) : ℚ)) - ((k * i / h : ℕ) : ℚ))
        = ∑ i ∈ Ico 1 h, (2 * ((i : ℚ) * ((k * i / h : ℕ) : ℚ)) - ((k * i / h : ℕ) : ℚ)) := by
      rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hh]
      simp
    rw [← hshift, sum_sub_distrib, ← mul_sum]
    unfold P M
    ring
  -- each pair (r,i) lies in exactly one triangle
  have hpair : ∀ r ∈ range k, ∀ i ∈ Ico 1 h,
      (if k * i ≤ h * r then (2 * (i : ℚ) - 1) else 0)
        + (if h * r ≤ k * i then (2 * (i : ℚ) - 1) else 0) = 2 * (i : ℚ) - 1 := by
    intro r hr i hi
    rw [mem_range] at hr
    rw [mem_Ico] at hi
    have hne : k * i ≠ h * r := by
      intro heq
      have hd : k ∣ h * r := ⟨i, heq.symm⟩
      have h0 := Nat.eq_zero_of_dvd_of_lt ((Nat.Coprime.symm hc).dvd_of_dvd_mul_left hd) hr
      subst h0
      have : 0 < k * i := Nat.mul_pos hk (by omega)
      omega
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [ite_eq_left (by omega), ite_eq_right (by omega)]; ring
    · rw [ite_eq_right (by omega), ite_eq_left (by omega)]; ring
  have htot : ∑ r ∈ range k, ∑ i ∈ Ico 1 h, (2 * (i : ℚ) - 1) = k * ((h : ℚ) - 1) ^ 2 := by
    obtain ⟨n, rfl⟩ : ∃ n, h = n + 1 := ⟨h - 1, by omega⟩
    rw [sum_const, card_range, sum_odd, nsmul_eq_mul]
    push_cast; ring
  rw [add_sub_assoc, add_assoc, hR, hQ, sum_comm (s := Ico 1 h), ← sum_add_distrib, ← htot]
  refine sum_congr rfl fun r hr => ?_
  rw [← sum_add_distrib]
  exact sum_congr rfl fun i hi => hpair r hr i hi

/-- (c) **Dedekind reciprocity.** For coprime positive integers `h, k`,
`s(h,k) + s(k,h) = (h² + k² + 1)/(12hk) − 1/4`. -/
theorem ded_reciprocity {h k : ℕ} (hc : Nat.Coprime h k) (hh : 0 < h) (hk : 0 < k) :
    ded h k + ded k h = ((h : ℚ) ^ 2 + k ^ 2 + 1) / (12 * h * k) - 1 / 4 := by
  have hhq : (h : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have E1 := eqn1 hc
  have E2 := eqn2 hc
  have E1p := eqn1 (Nat.Coprime.symm hc)
  have E3 := eqn3 hc hh hk
  rw [ded_formula hc hk, ded_formula (Nat.Coprime.symm hc) hh]
  linear_combination (norm := skip) (-1 / (2 * (k : ℚ))) * E1
    + (1 / (2 * (h : ℚ) * (k : ℚ) ^ 2)) * E2 + (-1 / (2 * (h : ℚ))) * E3
    + ((1 - (h : ℚ)) / (2 * (h : ℚ) ^ 2)) * E1p
  field_simp
  ring

/-! ### (d) Distribution relation (F3) -/

/-- `((qn/(qm))) = ((n/m))`. -/
lemma saw_scale {q m : ℕ} (hq : 0 < q) (hm : 0 < m) (n : ℤ) :
    saw (q * m) ((q : ℤ) * n) = saw m n := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have hqq : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold saw
  rw [Nat.cast_mul, Int.mul_emod_mul_of_pos _ _ hq']
  by_cases h0 : n % (m : ℤ) = 0
  · simp [h0]
  · have : (q : ℤ) * (n % m) ≠ 0 := mul_ne_zero hq'.ne' h0
    rw [ite_eq_right this, ite_eq_right h0]
    push_cast
    field_simp

lemma saw_of_lt {k : ℕ} {n : ℤ} (h0 : 0 ≤ n) (hlt : n < k) :
    saw k n = (n : ℚ) / k - 1 / 2 + (if n = 0 then 1 / 2 else 0) := by
  unfold saw
  rw [Int.emod_eq_of_lt h0 hlt]
  by_cases h : n = 0
  · subst h; simp
  · rw [ite_eq_right h, ite_eq_right h]; simp

/-- A `q`-periodic function has the same sum over any `q` consecutive integers. -/
lemma shift_sum (q : ℕ) (H : ℤ → ℚ) (hH : ∀ t, H (t + q) = H t) (a : ℤ) :
    ∑ j ∈ range q, H (a + j) = ∑ j ∈ range q, H j := by
  have step : ∀ b : ℤ, ∑ j ∈ range q, H (b + 1 + j) = ∑ j ∈ range q, H (b + j) := by
    intro b
    have h1 := sum_range_succ (fun j : ℕ => H (b + j)) q
    have h2 := sum_range_succ' (fun j : ℕ => H (b + j)) q
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero] at h1 h2
    have e : ∀ j : ℕ, b + 1 + (j : ℤ) = b + ((j : ℤ) + 1) := fun j => by ring
    simp only [e]
    rw [hH b] at h1
    linarith
  induction a using Int.induction_on with
  | zero => simp
  | succ i ih => rw [step, ih]
  | pred i ih => rw [← step (-(i : ℤ) - 1), sub_add_cancel, ih]

/-- **(F3)** Discrete distribution relation: `Σ_{j<q} (((n + jm)/(qm))) = ((n/m))`. -/
theorem saw_dist {q m : ℕ} (hq : 0 < q) (hm : 0 < m) (n : ℤ) :
    ∑ j ∈ range q, saw (q * m) (n + j * m) = saw m n := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hqq : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hb0 : 0 ≤ n % (m : ℤ) := Int.emod_nonneg _ hm'.ne'
  have hbm : n % (m : ℤ) < m := Int.emod_lt_of_pos _ hm'
  have hn : ∀ j : ℤ, n + j * m = n % m + (n / m + j) * m := fun j => by
    have := Int.emod_add_mul_ediv n m
    linear_combination -this
  let H : ℤ → ℚ := fun t => saw (q * m) (n % m + t * m)
  have hH : ∀ t, H (t + q) = H t := fun t => saw_congr (by
    rw [Int.modEq_iff_dvd]; push_cast; exact ⟨-1, by ring⟩)
  have hterm : ∀ t ∈ range q, H t = (((n % m : ℤ) : ℚ) / (q * m) - 1 / 2) + 1 / q * (t : ℚ)
      + (if n % (m : ℤ) = 0 ∧ t = 0 then 1 / 2 else 0) := by
    intro t ht
    rw [mem_range] at ht
    have htq : (t : ℤ) + 1 ≤ q := by exact_mod_cast ht
    have ht0 : (0 : ℤ) ≤ t := by positivity
    simp only [H]
    have hpos : 0 ≤ n % (m : ℤ) + (t : ℤ) * m := by nlinarith
    have hlt : n % (m : ℤ) + (t : ℤ) * m < ((q * m : ℕ) : ℤ) := by push_cast; nlinarith
    rw [saw_of_lt hpos hlt]
    by_cases hc : n % (m : ℤ) = 0 ∧ t = 0
    · obtain ⟨h1, rfl⟩ := hc
      simp [h1]
    · have hz : n % (m : ℤ) + (t : ℤ) * m ≠ 0 := by
        intro h
        apply hc
        have htm : (t : ℤ) * m = 0 := by nlinarith
        have : (t : ℤ) = 0 := by
          rcases mul_eq_zero.1 htm with h' | h'
          · exact h'
          · omega
        exact ⟨by nlinarith, by exact_mod_cast this⟩
      rw [ite_eq_right hz, ite_eq_right hc]
      push_cast
      field_simp
      ring
  calc ∑ j ∈ range q, saw (q * m) (n + j * m) = ∑ j ∈ range q, H (n / m + j) := by
        refine sum_congr rfl fun j _ => ?_
        simp only [H]
        rw [hn]
    _ = ∑ j ∈ range q, H j := shift_sum q H hH _
    _ = saw m n := by
        rw [sum_congr rfl hterm, sum_add_distrib, sum_add_distrib, ← mul_sum, sum_id, sum_const,
          card_range, nsmul_eq_mul]
        by_cases hb : n % (m : ℤ) = 0
        · simp only [hb, true_and]
          rw [sum_ite_eq' (range q) 0, ite_eq_left (mem_range.2 hq)]
          unfold saw
          rw [ite_eq_left hb]
          push_cast
          field_simp
          ring
        · simp only [hb, false_and, ite_false, sum_const_zero]
          unfold saw
          rw [ite_eq_right hb]
          field_simp
          ring

/-! ### (d) Lemma 1: the prime case of the Petersson–Knopp identity -/

lemma sum_range_mul (q m : ℕ) (f : ℕ → ℚ) :
    ∑ r ∈ range (q * m), f r = ∑ j ∈ range q, ∑ i ∈ range m, f (j * m + i) := by
  induction q with
  | zero => simp
  | succ q ih => rw [add_mul, one_mul, sum_range_add, ih, sum_range_succ]

/-- The inner sum over `l` in Lemma 1. -/
lemma inner_value {q m : ℕ} (hq : q.Prime) (hm : 0 < m) (x : ℤ) (r : ℕ) :
    ∑ l ∈ range q, saw (q * m) ((x + l * m) * r)
      = saw m (x * r) + (if q ∣ r then (q : ℚ) * saw m (x * (r / q : ℕ)) - saw m (x * r) else 0) := by
  have hq0 := hq.pos
  by_cases hd : q ∣ r
  · rw [ite_eq_left hd]
    obtain ⟨r', rfl⟩ := hd
    rw [Nat.mul_div_cancel_left r' hq0]
    have e : ∀ l ∈ range q,
        saw (q * m) ((x + l * m) * ((q * r' : ℕ) : ℤ)) = saw m (x * r') := by
      intro l _
      have : (x + l * m) * ((q * r' : ℕ) : ℤ) = (q : ℤ) * (x * r' + ((l : ℤ) * r') * m) := by
        push_cast; ring
      rw [this, saw_scale hq0 hm]
      apply saw_congr
      rw [Int.modEq_iff_dvd]
      exact ⟨-((l : ℤ) * r'), by ring⟩
    rw [sum_congr rfl e, sum_const, card_range, nsmul_eq_mul]
    ring
  · rw [ite_eq_right hd, add_zero]
    have hc : Nat.Coprime r q := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).2 hd)
    have e : ∀ l ∈ range q, saw (q * m) ((x + l * m) * r)
        = saw (q * m) (x * r + ((r * l % q : ℕ) : ℤ) * m) := by
      intro l _
      apply saw_congr
      rw [Int.modEq_iff_dvd]
      have h0 := Nat.mod_add_div (r * l) q
      have h' : ((r * l % q : ℕ) : ℤ) = (r : ℤ) * l - q * ((r * l / q : ℕ) : ℤ) := by
        have := congrArg (Nat.cast : ℕ → ℤ) h0
        simp only [Nat.cast_add, Nat.cast_mul] at this
        linarith
      refine ⟨-((r * l / q : ℕ) : ℤ), ?_⟩
      rw [h', Nat.cast_mul]
      ring
    rw [sum_congr rfl e, perm_sum hc (fun j => saw (q * m) (x * r + (j : ℤ) * m))]
    exact saw_dist hq0 hm (x * r)

/-- `Σ_{r<qm} ((r/(qm))) ((xr/m)) = s(x,m)` (split `r = jm + i`, then (F3)). -/
lemma lift_sum {q m : ℕ} (hq0 : 0 < q) (hm : 0 < m) (x : ℤ) :
    ∑ r ∈ range (q * m), saw (q * m) r * saw m (x * r)
      = ∑ r ∈ range m, saw m r * saw m (x * r) := by
  rw [sum_range_mul, sum_comm]
  refine sum_congr rfl fun i _ => ?_
  have e : ∀ j ∈ range q, saw (q * m) ((j * m + i : ℕ) : ℤ) * saw m (x * ((j * m + i : ℕ) : ℤ))
      = saw (q * m) ((i : ℤ) + (j : ℤ) * m) * saw m (x * i) := by
    intro j _
    rw [show ((j * m + i : ℕ) : ℤ) = (i : ℤ) + (j : ℤ) * m by push_cast; ring]
    congr 1
    apply saw_congr
    rw [Int.modEq_iff_dvd]
    exact ⟨-(x * j), by ring⟩
  rw [sum_congr rfl e, ← sum_mul, saw_dist hq0 hm]

/-- **(F4)**, the instance used in Corollary 1′: `s(qy, qm) = s(y, m)`. -/
theorem ded_scale {q m : ℕ} (hq0 : 0 < q) (hm : 0 < m) (y : ℤ) :
    ded (q * y) (q * m) = ded y m := by
  unfold ded
  rw [← lift_sum hq0 hm y]
  refine sum_congr rfl fun r _ => ?_
  rw [mul_assoc, saw_scale hq0 hm]

/-- **Lemma 1** (prime case of Petersson–Knopp): for a prime `q`, `m ≥ 1`, `x ∈ ℤ`,
`Σ_{l<q} s(x + lm, qm) = (q+1) s(x,m) − s(qx,m)`. -/
theorem petersson_knopp_prime {q m : ℕ} (hq : q.Prime) (hm : 0 < m) (x : ℤ) :
    ∑ l ∈ range q, ded (x + l * m) (q * m) = (q + 1) * ded x m - ded (q * x) m := by
  have hq0 := hq.pos
  have h1 := lift_sum hq0 hm x
  have h2 : ∑ r ∈ range (q * m), saw (q * m) r
        * (if q ∣ r then (q : ℚ) * saw m (x * (r / q : ℕ)) - saw m (x * r) else 0)
      = q * ∑ r ∈ range m, saw m r * saw m (x * r)
        - ∑ r ∈ range m, saw m r * saw m (q * x * r) := by
    rw [show range (q * m) = range (m * q) by rw [Nat.mul_comm], sum_range_mul, mul_sum,
      ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_eq_single 0]
    · rw [add_zero, ite_eq_left (dvd_mul_left q j), Nat.mul_div_cancel j hq0,
        show ((j * q : ℕ) : ℤ) = (q : ℤ) * j by push_cast; ring, saw_scale hq0 hm,
        show x * ((q : ℤ) * j) = q * x * j by ring]
      ring
    · intro i hi hi0
      have hnd : ¬ q ∣ j * q + i := by
        intro hdv
        have := (Nat.dvd_add_right (dvd_mul_left q j)).1 hdv
        exact hi0 (Nat.eq_zero_of_dvd_of_lt this (mem_range.1 hi))
      rw [ite_eq_right hnd, mul_zero]
    · intro h; exact absurd (mem_range.2 hq0) h
  unfold ded
  rw [sum_comm]
  simp_rw [← mul_sum]
  simp_rw [inner_value hq hm x, mul_add, sum_add_distrib]
  rw [h1, h2]
  ring

/-- **Corollary 1′** (coprime lifts). For a prime `q ∤ m` and `y` with `q y ≡ x (mod m)`
(i.e. `y = q⁻¹x mod m`): the sum over the `l < q` with `q ∤ x + lm` equals
`(q+1) s(x,m) − s(qx,m) − s(q⁻¹x,m)`. -/
theorem petersson_knopp_coprime_lifts {q m : ℕ} (hq : q.Prime) (hm : 0 < m) (hqm : ¬ q ∣ m)
    (x y : ℤ) (hy : (q : ℤ) * y ≡ x [ZMOD m]) :
    ∑ l ∈ range q, (if (q : ℤ) ∣ x + l * m then 0 else ded (x + l * m) (q * m))
      = (q + 1) * ded x m - ded (q * x) m - ded y m := by
  have hq0 := hq.pos
  have := Fact.mk hq
  have hmq : ((m : ℤ) : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun h => hqm (Int.natCast_dvd_natCast.1 h)
  -- the unique excluded `l`
  set l0 := (-(x : ZMod q) * ((m : ℤ) : ZMod q)⁻¹).val with hl0def
  have hl0 : l0 < q := ZMod.val_lt _
  have hdl0 : (q : ℤ) ∣ x + l0 * m := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hl0def, ZMod.natCast_zmod_val]
    have hmq' : ((m : ℕ) : ZMod q) ≠ 0 := by exact_mod_cast hmq
    rw [mul_assoc, Int.cast_natCast, mul_comm _ ((m : ℕ) : ZMod q), ZMod.coe_mul_inv_eq_one m
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).2 hqm))]
    ring
  have huniq : ∀ l ∈ range q, l ≠ l0 → ¬ (q : ℤ) ∣ x + l * m := by
    intro l hl hne hdl
    have hd : (q : ℤ) ∣ ((l : ℤ) - l0) * m := by
      have := dvd_sub hdl hdl0
      convert this using 1
      ring
    rcases (Nat.prime_iff_prime_int.mp hq).dvd_or_dvd hd with h | h
    · obtain ⟨c, hc⟩ := h
      have hl' : l < q := mem_range.1 hl
      have hcz : c = 0 := by
        rcases lt_trichotomy c 0 with h' | h' | h'
        · have : (q : ℤ) * c ≤ -(q : ℤ) := by nlinarith
          omega
        · exact h'
        · have : (q : ℤ) * c ≥ (q : ℤ) := by nlinarith
          omega
      subst hcz
      omega
    · exact hqm (Int.natCast_dvd_natCast.1 h)
  have hsplit : ∀ l ∈ range q, ded (x + l * m) (q * m)
      = (if (q : ℤ) ∣ x + l * m then 0 else ded (x + l * m) (q * m))
        + (if (q : ℤ) ∣ x + l * m then ded (x + l * m) (q * m) else 0) := by
    intro l _
    split_ifs <;> simp
  have hkey : ∑ l ∈ range q, (if (q : ℤ) ∣ x + l * m then ded (x + l * m) (q * m) else 0)
      = ded y m := by
    rw [sum_eq_single l0 (fun l hl hne => ite_eq_right (huniq l hl hne))
      (fun h => absurd (mem_range.2 hl0) h), ite_eq_left hdl0]
    obtain ⟨z, hz⟩ := hdl0
    rw [hz, ded_scale hq0 hm]
    apply ded_congr
    have h1 : (q : ℤ) * z ≡ (q : ℤ) * y [ZMOD m] := by
      rw [← hz]
      refine Int.ModEq.trans ?_ hy.symm
      rw [Int.modEq_iff_dvd]
      exact ⟨-(l0 : ℤ), by ring⟩
    have hcop : Nat.Coprime m q := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).2 hqm))
    have h2 := Int.ModEq.cancel_left_div_gcd (by exact_mod_cast hm) h1
    rwa [Int.gcd_natCast_natCast, hcop, Nat.cast_one, Int.ediv_one] at h2
  have hPK := petersson_knopp_prime hq hm x
  rw [sum_congr rfl hsplit, sum_add_distrib, hkey] at hPK
  linarith

end DedekindSum

-- axiom audit
