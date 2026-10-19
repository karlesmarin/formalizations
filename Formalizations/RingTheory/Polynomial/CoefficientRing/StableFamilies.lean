/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# Stable families of segments

If `r` divides `n − 1`, `n` or `n + 1`, the `SU(n)` segment is stable at `q'`: the multiset of its
exponents modulo `q'` is invariant under multiplication by every unit of `ZMod q'`.

Model: the exponents are integers `a_j` (`j < n`) cast into `ZMod q'`; the count is
`cnt f n c = #{j < n | f j = c}` and `Stable f n` means `cnt f n (u c) = cnt f n c` for every unit
`u` and every `c`. The three cases are
* `n = 2m + 1`: `a_j = j − m` (segment `−m..m`), `q' = r`;
* `n = 2m`, `p = 2`: `a_j = n − 1 − 2j`, `q' = r` with `r` odd;
* `n = 2m`, `p` odd: `a_j = n − 1 − 2j`, `q' = 2r`.
All three follow from one abstract statement (`stable_of_period`): `f` periodic of period `P`,
injective on `[0, P)`, with image stable under units; the exceptional class `c₀` satisfies
`2 c₀ = 0`, hence is fixed by every unit (`unit_mul_fixed`).

## Main results

* `NotaPuente.Families.stable_of_period`: the abstract counting statement.
* `NotaPuente.Families.prop_4_2_odd`, `NotaPuente.Families.prop_4_2_even_r`,
  `NotaPuente.Families.prop_4_2_even_2r`: the three cases.

## References

* C. Marín, *Non-real orders of character values of `GL(n)`*, preprint (2026).
* C. Marín, *The ring of character values depends only on the segment: SU(n), Sp(2m) and GL(n) at
  a torsion element*, Zenodo (2026), doi:10.5281/zenodo.22847476.
-/

@[expose] public section

namespace NotaPuente.Families

open Finset

variable {M : ℕ}

/-- `cnt f n c = #{j < n : f j = c}`. -/
def cnt (f : ℕ → ZMod M) (n : ℕ) (c : ZMod M) : ℕ := #((range n).filter (fun j => f j = c))

/-- Stability at `M = q'`: the counting function is invariant under multiplication by units. -/
def Stable (f : ℕ → ZMod M) (n : ℕ) : Prop := ∀ (u : (ZMod M)ˣ) (c : ZMod M), cnt f n (u * c) = cnt f n c

lemma cnt_sum (f : ℕ → ZMod M) (n : ℕ) (c : ZMod M) :
    cnt f n c = ∑ j ∈ range n, if f j = c then 1 else 0 := card_filter _ _

lemma cnt_zero (f : ℕ → ZMod M) (c : ZMod M) : cnt f 0 c = 0 := by simp [cnt]

lemma cnt_succ (f : ℕ → ZMod M) (n : ℕ) (c : ZMod M) :
    cnt f (n + 1) c = cnt f n c + if f n = c then 1 else 0 := by
  rw [cnt_sum, cnt_sum, sum_range_succ]

lemma cnt_periodic (f : ℕ → ZMod M) {P : ℕ} (hper : ∀ j, f (P + j) = f j) (c : ZMod M) (s : ℕ) :
    ∀ k, cnt f (k * P + s) c = k * cnt f P c + cnt f s c := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * P + s = P + (k * P + s) by ring, cnt_sum, sum_range_add]
    simp_rw [hper]
    rw [← cnt_sum, ← cnt_sum, ih]; ring

lemma cnt_period (f : ℕ → ZMod M) {P : ℕ} (hinj : ∀ i < P, ∀ j < P, f i = f j → i = j)
    (c : ZMod M) : cnt f P c = if c ∈ (range P).image f then 1 else 0 := by
  unfold cnt
  split_ifs with h
  · obtain ⟨j0, hj0, rfl⟩ := mem_image.mp h
    rw [card_eq_one]
    refine ⟨j0, ?_⟩
    ext j
    simp only [mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨hj, hfj⟩; exact hinj j hj j0 (mem_range.mp hj0) hfj
    · rintro rfl; exact ⟨mem_range.mp hj0, rfl⟩
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro j hj hfj
    exact h (mem_image.mpr ⟨j, hj, hfj⟩)

/-- If `2 c0 = 0` in `ZMod M`, every unit fixes `c0`. -/
lemma unit_mul_fixed [NeZero M] (u : (ZMod M)ˣ) {c0 : ZMod M} (h : 2 * c0 = 0) :
    (u : ZMod M) * c0 = c0 := by
  have hcop : Nat.gcd (u : ZMod M).val M = 1 := ZMod.val_coe_unit_coprime u
  rcases Nat.even_or_odd (u : ZMod M).val with ⟨w, hw⟩ | ⟨w, hw⟩
  · have hM : ¬ 2 ∣ M := fun h2 => by
      have : 2 ∣ Nat.gcd (u : ZMod M).val M := Nat.dvd_gcd ⟨w, by omega⟩ h2
      rw [hcop] at this; omega
    obtain ⟨h', hh⟩ : ∃ h', M = 2 * h' + 1 := ⟨M / 2, by omega⟩
    have hM0 : ((2 * h' + 1 : ℕ) : ZMod M) = 0 := by rw [← hh]; exact ZMod.natCast_self M
    push_cast at hM0
    have hc : c0 = 0 := by linear_combination c0 * hM0 - (h' : ZMod M) * h
    rw [hc, mul_zero]
  · have hu : (u : ZMod M) = 2 * (w : ZMod M) + 1 := by
      rw [← ZMod.natCast_zmod_val (u : ZMod M), hw]; push_cast; ring
    rw [hu]; linear_combination (w : ZMod M) * h

lemma unit_mul_eq_iff [NeZero M] (u : (ZMod M)ˣ) {c0 : ZMod M} (h : 2 * c0 = 0) (c : ZMod M) :
    c0 = (u : ZMod M) * c ↔ c0 = c := by
  constructor
  · intro hc
    have := unit_mul_fixed u⁻¹ h
    rw [← this, hc, ← mul_assoc, Units.inv_mul, one_mul]
  · rintro rfl; exact (unit_mul_fixed u h).symm

/-- **Abstract stability.** `f` of period `P`, injective on `[0, P)`, with image `T` stable under
units. If `P | n`, or `n = kP + 1` with `2 f 0 = 0`, or `n + 1 = kP` with `2 f n = 0`, then the
counting function is invariant under units. -/
theorem stable_of_period [NeZero M] (f : ℕ → ZMod M) {P : ℕ} (hper : ∀ j, f (P + j) = f j)
    (hinj : ∀ i < P, ∀ j < P, f i = f j → i = j)
    (hT : ∀ (u : (ZMod M)ˣ) (c : ZMod M),
      ((u : ZMod M) * c ∈ (range P).image f ↔ c ∈ (range P).image f))
    {n : ℕ} (hn : (∃ k, n = k * P) ∨ ((∃ k, n = k * P + 1) ∧ 2 * f 0 = 0) ∨
      ((∃ k, n + 1 = k * P) ∧ 2 * f n = 0)) :
    Stable f n := by
  intro u c
  have hP := cnt_period f hinj
  rcases hn with ⟨k, rfl⟩ | ⟨⟨k, rfl⟩, h0⟩ | ⟨⟨k, hk⟩, h0⟩
  · have e := fun c => cnt_periodic f hper c 0 k
    simp only [add_zero, cnt_zero] at e
    rw [e, e, hP, hP]
    simp only [hT u c]
  · have e := fun c => cnt_periodic f hper c 1 k
    have e1 := fun c => cnt_succ f 0 c
    simp only [zero_add, cnt_zero] at e1
    rw [e, e, hP, hP, e1, e1]
    simp only [hT u c, unit_mul_eq_iff u h0 c]
  · have e := fun c => cnt_periodic f hper c 0 k
    simp only [add_zero, cnt_zero] at e
    have s1 := cnt_succ f n (u * c)
    have s2 := cnt_succ f n c
    rw [hk, e, hP] at s1 s2
    simp only [hT u c, unit_mul_eq_iff u h0 c] at s1
    omega

/-! ### The three cases of Proposition 4.2 -/

lemma image_eq_univ [NeZero M] (f : ℕ → ZMod M) (hinj : ∀ i < M, ∀ j < M, f i = f j → i = j) :
    (range M).image f = univ := by
  refine eq_univ_of_card _ ?_
  rw [card_image_of_injOn, card_range, ZMod.card]
  intro i hi j hj hij
  exact hinj i (mem_range.mp hi) j (mem_range.mp hj) hij

lemma natCast_inj_of_lt {i j : ℕ} (hi : i < M) (hj : j < M) (h : (i : ZMod M) = j) : i = j := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h
  exact h

/-- **Proposition 4.2, n = 2m + 1 odd** (segment `-m..m`, `q' = r`). -/
theorem prop_4_2_odd {r : ℕ} (hr : 0 < r) (m : ℕ) (h : r ∣ 2 * m ∨ r ∣ 2 * m + 1 ∨ r ∣ 2 * m + 2) :
    Stable (M := r) (fun j => (((j : ℤ) - m : ℤ) : ZMod r)) (2 * m + 1) := by
  have : NeZero r := ⟨by omega⟩
  set f : ℕ → ZMod r := fun j => (((j : ℤ) - m : ℤ) : ZMod r) with hf
  have hinj : ∀ i < r, ∀ j < r, f i = f j → i = j := by
    intro i hi j hj hij
    simp only [hf] at hij
    push_cast at hij
    exact natCast_inj_of_lt hi hj (sub_left_injective hij)
  have hrr : (r : ZMod r) = 0 := ZMod.natCast_self r
  refine stable_of_period f (P := r) (fun j => by simp only [hf]; push_cast; rw [hrr, zero_add])
    hinj (fun u c => by rw [image_eq_univ f hinj]; simp) ?_
  rcases h with ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩
  · right; left
    refine ⟨⟨k, by rw [hk]; ring⟩, ?_⟩
    have : ((2 * m : ℕ) : ZMod r) = 0 := by rw [hk]; push_cast; rw [hrr, zero_mul]
    simp only [hf]; push_cast at this ⊢; linear_combination -this
  · left; exact ⟨k, by rw [hk]; ring⟩
  · right; right
    refine ⟨⟨k, by rw [show 2 * m + 1 + 1 = 2 * m + 2 by ring, hk]; ring⟩, ?_⟩
    have : ((2 * m + 2 : ℕ) : ZMod r) = 0 := by rw [hk]; push_cast; rw [hrr, zero_mul]
    simp only [hf]; push_cast at this ⊢; linear_combination this

/-- The even-case exponent map `j ↦ n - 1 - 2j`, `n = 2m`. -/
def fe (M m : ℕ) : ℕ → ZMod M := fun j => ((2 * (m : ℤ) - 1 - 2 * (j : ℤ) : ℤ) : ZMod M)

/-- The divisibility hypothesis in the even case, for any `M` with `2 r = 0` in `ZMod M`. -/
lemma even_hn {r : ℕ} (m : ℕ) (h2r : (2 * r : ZMod M) = 0)
    (h : r ∣ 2 * m - 1 ∨ r ∣ 2 * m ∨ r ∣ 2 * m + 1) (hm : 1 ≤ m) :
    (∃ k, 2 * m = k * r) ∨ ((∃ k, 2 * m = k * r + 1) ∧ 2 * fe M m 0 = 0) ∨
      ((∃ k, 2 * m + 1 = k * r) ∧ 2 * fe M m (2 * m) = 0) := by
  rcases h with ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩
  · right; left
    refine ⟨⟨k, by rw [mul_comm k r, ← hk]; omega⟩, ?_⟩
    have hk' : ((2 * m - 1 : ℕ) : ZMod M) = r * k := by rw [hk]; push_cast; ring
    rw [Nat.cast_sub (by omega)] at hk'
    simp only [fe]; push_cast at hk' ⊢
    linear_combination 2 * hk' + (k : ZMod M) * h2r
  · left; exact ⟨k, by rw [hk]; ring⟩
  · right; right
    refine ⟨⟨k, by rw [hk]; ring⟩, ?_⟩
    have hk' : ((2 * m + 1 : ℕ) : ZMod M) = r * k := by rw [hk]; push_cast; ring
    simp only [fe]; push_cast at hk' ⊢
    linear_combination -2 * hk' - (k : ZMod M) * h2r

lemma fe_per {r : ℕ} (m : ℕ) (h2r : (2 * r : ZMod M) = 0) (j : ℕ) : fe M m (r + j) = fe M m j := by
  simp only [fe]; push_cast; linear_combination -h2r

/-- **Proposition 4.2, n = 2m even, p = 2** (`q' = r`, `r` odd). -/
theorem prop_4_2_even_r {r : ℕ} (hr : Odd r) (m : ℕ)
    (h : r ∣ 2 * m - 1 ∨ r ∣ 2 * m ∨ r ∣ 2 * m + 1) :
    Stable (fe r m) (2 * m) := by
  obtain ⟨h', hh⟩ := hr
  have : NeZero r := ⟨by omega⟩
  have hrr : (r : ZMod r) = 0 := ZMod.natCast_self r
  have h2r : (2 * r : ZMod r) = 0 := by rw [hrr, mul_zero]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · intro u c; simp [cnt]
  have hinj : ∀ i < r, ∀ j < r, fe r m i = fe r m j → i = j := by
    intro i hi j hj hij
    simp only [fe] at hij
    push_cast at hij
    have h2 : 2 * (i : ZMod r) = 2 * j := by linear_combination -hij
    have hM0 : ((2 * h' + 1 : ℕ) : ZMod r) = 0 := by rw [← hh]; exact hrr
    push_cast at hM0
    refine natCast_inj_of_lt hi hj ?_
    linear_combination -(h' : ZMod r) * h2 + ((i : ZMod r) - j) * hM0
  exact stable_of_period (fe r m) (P := r) (fe_per m h2r) hinj
    (fun u c => by rw [image_eq_univ _ hinj]; simp) (even_hn m h2r h hm)

/-- Units of `ZMod (2 r)` are odd. -/
lemma odd_unit {r : ℕ} [NeZero (2 * r)] (u : (ZMod (2 * r))ˣ) : Odd (u : ZMod (2 * r)) := by
  have hcop : Nat.gcd (u : ZMod (2 * r)).val (2 * r) = 1 := ZMod.val_coe_unit_coprime u
  rcases Nat.even_or_odd (u : ZMod (2 * r)).val with ⟨w, hw⟩ | ⟨w, hw⟩
  · exfalso
    have : 2 ∣ Nat.gcd (u : ZMod (2 * r)).val (2 * r) := Nat.dvd_gcd ⟨w, by omega⟩ ⟨r, rfl⟩
    rw [hcop] at this; omega
  · exact ⟨w, by rw [← ZMod.natCast_zmod_val (u : ZMod (2 * r)), hw]; push_cast; ring⟩

/-- **Proposition 4.2, n = 2m even, p odd** (`q' = 2r`; the segment runs through the odd classes). -/
theorem prop_4_2_even_2r {r : ℕ} (hr : 0 < r) (m : ℕ)
    (h : r ∣ 2 * m - 1 ∨ r ∣ 2 * m ∨ r ∣ 2 * m + 1) :
    Stable (fe (2 * r) m) (2 * m) := by
  have : NeZero (2 * r) := ⟨by omega⟩
  have h2r0 : ((2 * r : ℕ) : ZMod (2 * r)) = 0 := ZMod.natCast_self _
  have h2r : (2 * r : ZMod (2 * r)) = 0 := by exact_mod_cast h2r0
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · intro u c; simp [cnt]
  have hinj : ∀ i < r, ∀ j < r, fe (2 * r) m i = fe (2 * r) m j → i = j := by
    intro i hi j hj hij
    simp only [fe] at hij
    push_cast at hij
    have h2 : ((2 * i : ℕ) : ZMod (2 * r)) = ((2 * j : ℕ) : ZMod (2 * r)) := by
      push_cast; linear_combination -hij
    have := natCast_inj_of_lt (by omega) (by omega) h2
    omega
  -- the image is the set of odd classes
  have himg : ∀ c, c ∈ (range r).image (fe (2 * r) m) ↔ Odd c := by
    intro c
    constructor
    · intro hc
      obtain ⟨j, -, rfl⟩ := mem_image.mp hc
      exact ⟨(m : ZMod (2 * r)) - 1 - j, by simp only [fe]; push_cast; ring⟩
    · rintro ⟨y, rfl⟩
      set w := ((m : ZMod (2 * r)) - 1 - y).val with hw
      have hwv : (w : ZMod (2 * r)) = (m : ZMod (2 * r)) - 1 - y := ZMod.natCast_zmod_val _
      obtain ⟨j0, hj0⟩ : ∃ j0, j0 = w % r := ⟨_, rfl⟩
      obtain ⟨t, ht⟩ : ∃ t, t = w / r := ⟨_, rfl⟩
      have hdiv : ((w : ℕ) : ZMod (2 * r)) = (j0 : ZMod (2 * r)) + r * (t : ZMod (2 * r)) := by
        rw [hj0, ht, ← Nat.cast_mul (r : ℕ), ← Nat.cast_add, Nat.mod_add_div]
      refine mem_image.mpr ⟨j0, mem_range.mpr (hj0 ▸ Nat.mod_lt _ hr), ?_⟩
      simp only [fe]; push_cast
      linear_combination 2 * hdiv - 2 * hwv + (t : ZMod (2 * r)) * h2r
  have hT : ∀ (u : (ZMod (2 * r))ˣ) (c : ZMod (2 * r)),
      ((u : ZMod (2 * r)) * c ∈ (range r).image (fe (2 * r) m) ↔ c ∈ (range r).image (fe (2 * r) m)) := by
    intro u c
    rw [himg, himg]
    constructor
    · intro hc
      have := (odd_unit u⁻¹).mul hc
      rwa [← mul_assoc, Units.inv_mul, one_mul] at this
    · exact (odd_unit u).mul
  exact stable_of_period (fe (2 * r) m) (P := r) (fe_per m h2r) hinj hT
    (even_hn m h2r h hm)


end NotaPuente.Families
