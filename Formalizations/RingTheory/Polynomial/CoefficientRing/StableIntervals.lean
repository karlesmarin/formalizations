/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# Stable intervals in `ZMod n` and two Laurent identities

An affine bijection `x ↦ u x + b` of `ZMod n` (`u` a unit) that maps a block of `k` consecutive
residues onto itself, with `2 ≤ k ≤ n − 2`, has `u = ±1`. The second part proves two identities
for the elementary symmetric functions `a1`, `a2` of the spectrum `t^(L−1−2j)`, `j < L`.

## Main results

* `NotaPuente.C_interval_eq_iff`: for the block `{0, …, k − 1}`, the number of `x` with `x` and
  `x + t` in the block is `k − 1` iff `t = ±1`.
* `NotaPuente.lemma_4_1`: an affine bijection fixing a block of `k` consecutive residues,
  `2 ≤ k ≤ n − 2`, has `u = 1 ∨ u = −1`.
* `NotaPuente.lemma_5_5`: for `t ≠ 0` and `L ≥ 2`, with `τ₊ = t^(L−1) + t^(−(L−1))` and
  `τ₋ = t^(L+1) + t^(−(L+1))`: `(a1² − a2) τ₊ = a1 (1 + a1² − 2 a2)` and
  `a2 τ₋ = a1 (a1² − 2 a2 − 1)` (division-free, through a Chebyshev recurrence and Cassini's
  identity).

## References

* C. Marín, *Non-real orders of character values of `GL(n)`*, preprint (2026).
* C. Marín, *The ring of character values depends only on the segment: SU(n), Sp(2m) and GL(n) at
  a torsion element*, Zenodo (2026), doi:10.5281/zenodo.22847476.
-/

@[expose] public section

namespace NotaPuente

open Finset

/-! ## Lemma 5.5 -/

section Laurent

variable {K : Type*} [Field K]

/-- `a1 t L = Σ_{j<L} t^(L-1-2j)` (first elementary symmetric function of the spectrum). -/
def a1 (t : K) (L : ℕ) : K := ∑ j ∈ range L, t ^ ((L : ℤ) - 1 - 2 * j)

/-- `a2 t L = Σ_{i<j<L} s_i s_j`, `s_j = t^(L-1-2j)` (second elementary symmetric function). -/
def a2 (t : K) (L : ℕ) : K :=
  ∑ j ∈ range L, ∑ i ∈ range j, t ^ ((L : ℤ) - 1 - 2 * i) * t ^ ((L : ℤ) - 1 - 2 * j)

variable {t : K}

lemma s_succ (ht : t ≠ 0) (L i : ℕ) :
    t ^ (((L + 1 : ℕ) : ℤ) - 1 - 2 * i) = t * t ^ ((L : ℤ) - 1 - 2 * i) := by
  rw [show ((L + 1 : ℕ) : ℤ) - 1 - 2 * i = ((L : ℤ) - 1 - 2 * i) + 1 by push_cast; ring,
    zpow_add_one₀ ht, mul_comm]

lemma s_last (L : ℕ) : t ^ (((L + 1 : ℕ) : ℤ) - 1 - 2 * (L : ℕ)) = (t ^ L)⁻¹ := by
  rw [show ((L + 1 : ℕ) : ℤ) - 1 - 2 * (L : ℕ) = -(L : ℤ) by push_cast; ring, zpow_neg,
    zpow_natCast]

lemma s_pred (ht : t ≠ 0) (L j : ℕ) :
    t ^ (((L + 1 : ℕ) : ℤ) - 1 - 2 * ((j + 1 : ℕ) : ℤ)) = t⁻¹ * t ^ ((L : ℤ) - 1 - 2 * j) := by
  rw [show ((L + 1 : ℕ) : ℤ) - 1 - 2 * ((j + 1 : ℕ) : ℤ) = ((L : ℤ) - 1 - 2 * j) + (-1) by
    push_cast; ring, zpow_add₀ ht, zpow_neg_one, mul_comm]

/-- `x_{L+1} = t x_L + t^(-L)`. -/
lemma a1_succ (ht : t ≠ 0) (L : ℕ) : a1 t (L + 1) = t * a1 t L + (t ^ L)⁻¹ := by
  unfold a1
  rw [sum_range_succ, s_last, mul_sum]
  congr 1
  exact sum_congr rfl fun i _ => s_succ ht L i

/-- `x_{L+1} = t⁻¹ x_L + t^L`. -/
lemma a1_succ' (ht : t ≠ 0) (L : ℕ) : a1 t (L + 1) = t⁻¹ * a1 t L + t ^ L := by
  unfold a1
  rw [sum_range_succ', mul_sum]
  congr 1
  · exact sum_congr rfl fun j _ => s_pred ht L j
  · rw [show ((L + 1 : ℕ) : ℤ) - 1 - 2 * ((0 : ℕ) : ℤ) = (L : ℤ) by push_cast; ring, zpow_natCast]

lemma a1_zero : a1 t 0 = 0 := by simp [a1]

/-- `x_{L+2} = t^(L+1) + x_L + t^(-(L+1))`. -/
lemma a1_two (ht : t ≠ 0) (L : ℕ) : a1 t (L + 2) = t ^ (L + 1) + a1 t L + (t ^ (L + 1))⁻¹ := by
  have h1 := a1_succ ht (L + 1)
  have h2 := a1_succ' ht L
  have htt : t * t⁻¹ = 1 := mul_inv_cancel₀ ht
  rw [h1, h2]
  linear_combination (a1 t L) * htt

/-- Chebyshev recurrence: `x_{L+2} + x_L = (t + t⁻¹) x_{L+1}`. -/
lemma a1_cheb (ht : t ≠ 0) (L : ℕ) : a1 t (L + 2) + a1 t L = (t + t⁻¹) * a1 t (L + 1) := by
  have h1 := a1_succ ht (L + 1)
  have h2 := a1_succ' ht (L + 1)
  have h3 := a1_two ht L
  linear_combination h1 + h2 - h3

/-- Cassini: `x_{L+1}² - x_L x_{L+2} = 1`. -/
lemma a1_cassini (ht : t ≠ 0) (L : ℕ) : a1 t (L + 1) ^ 2 - a1 t L * a1 t (L + 2) = 1 := by
  induction L with
  | zero =>
    have h := a1_succ ht 0
    rw [a1_zero] at h ⊢
    rw [h]; simp
  | succ n ih =>
    have c0 := a1_cheb ht n
    have c1 := a1_cheb ht (n + 1)
    simp only [show n + 1 + 1 = n + 2 from rfl, show n + 1 + 2 = n + 3 from rfl] at c1 ⊢
    linear_combination ih - a1 t (n + 1) * c1 + a1 t (n + 2) * c0

/-- `a2_{L+1} = t² a2_L + t · t^(-L) · x_L` (spectrum of `L+1` = `t ·` spectrum of `L`, plus `t^(-L)`). -/
lemma a2_succ (ht : t ≠ 0) (L : ℕ) : a2 t (L + 1) = t ^ 2 * a2 t L + t * (t ^ L)⁻¹ * a1 t L := by
  unfold a2 a1
  rw [sum_range_succ, mul_sum, mul_sum]
  congr 1
  · refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [s_succ ht L i, s_succ ht L j]; ring
  · refine sum_congr rfl fun i _ => ?_
    rw [s_succ ht L i, s_last L]; ring

lemma a2_zero : a2 t 0 = 0 := by simp [a2]

lemma a2_one : a2 t 1 = 0 := by simp [a2]

/-- `[2] · a2_{L+1} = x_{L+1} x_L` with `[2] = t + t⁻¹`. -/
lemma a2_mul (ht : t ≠ 0) (L : ℕ) : (t + t⁻¹) * a2 t (L + 1) = a1 t (L + 1) * a1 t L := by
  induction L with
  | zero => rw [a2_one, a1_zero]; ring
  | succ n ih =>
    have hb := a2_succ ht (n + 1)
    have hx := a1_succ ht (n + 1)
    have hx0 := a1_succ ht n
    have htt : t * t⁻¹ = 1 := mul_inv_cancel₀ ht
    rw [hb]
    linear_combination t ^ 2 * ih - a1 t (n + 1) * hx - t * a1 t (n + 1) * hx0
      + t⁻¹ ^ n * a1 t (n + 1) * (t⁻¹ + t) * htt

/-- **Lemma 5.5** of the note. For `L ≥ 2`, `t ≠ 0` in a field, spectrum `s_j = t^(L-1-2j)`
(`j < L`), `a1 = Σ s_j`, `a2 = Σ_{i<j} s_i s_j`, `τ₊ = t^(L-1) + t^(-(L-1))`,
`τ₋ = t^(L+1) + t^(-(L+1))`:
`(a1² - a2) τ₊ = a1 (1 + a1² - 2 a2)` and `a2 τ₋ = a1 (a1² - 2 a2 - 1)`.
Valid for every `t ≠ 0` (no `t² ≠ 1` hypothesis): the proof is division-free, via the recurrences
`x_{L+2} + x_L = [2] x_{L+1}`, Cassini `x_{L+1}² - x_L x_{L+2} = 1`, and `[2] a2_{L+1} = x_{L+1} x_L`. -/
theorem lemma_5_5 (ht : t ≠ 0) {L : ℕ} (hL : 2 ≤ L) :
    (a1 t L ^ 2 - a2 t L) * (t ^ ((L : ℤ) - 1) + t ^ (-((L : ℤ) - 1)))
        = a1 t L * (1 + a1 t L ^ 2 - 2 * a2 t L) ∧
    a2 t L * (t ^ ((L : ℤ) + 1) + t ^ (-((L : ℤ) + 1)))
        = a1 t L * (a1 t L ^ 2 - 2 * a2 t L - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 2 := ⟨L - 2, by omega⟩
  have hτp : t ^ (((n + 2 : ℕ) : ℤ) - 1) + t ^ (-(((n + 2 : ℕ) : ℤ) - 1))
      = a1 t (n + 2) - a1 t n := by
    rw [a1_two ht n, show ((n + 2 : ℕ) : ℤ) - 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast]
    ring
  have hτm : t ^ (((n + 2 : ℕ) : ℤ) + 1) + t ^ (-(((n + 2 : ℕ) : ℤ) + 1))
      = a1 t (n + 4) - a1 t (n + 2) := by
    rw [show n + 4 = (n + 2) + 2 from rfl, a1_two ht (n + 2),
      show ((n + 2 : ℕ) : ℤ) + 1 = ((n + 2 + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
    ring
  have F5 := a2_mul ht (n + 1)
  have F1n := a1_cheb ht n
  have F1 := a1_cheb ht (n + 1)
  have F1' := a1_cheb ht (n + 2)
  have C := a1_cassini ht (n + 1)
  simp only [show n + 1 + 1 = n + 2 from rfl, show n + 1 + 2 = n + 3 from rfl,
    show n + 2 + 2 = n + 4 from rfl] at F5 F1n F1 F1' C
  rw [hτp, hτm]
  constructor
  · linear_combination -(a1 t (n + 2) ^ 2 - a2 t (n + 2)) * F1n + a1 t (n + 1) * F5
      + a1 t (n + 2) * C + a1 t (n + 2) * a1 t (n + 1) * F1
  · linear_combination a2 t (n + 2) * F1' + a1 t (n + 3) * F5 - a1 t (n + 2) * C

end Laurent

/-! ## Lemma 4.1 -/

section Stable

variable {n : ℕ}

/-- Autocorrelation `C I t = #{x ∈ I : x + t ∈ I} = |I ∩ (I - t)|` (same cardinality as the
paper's `|I ∩ (I + t)|`, by the translation `x ↦ x + t`). -/
def C (I : Finset (ZMod n)) (t : ZMod n) : ℕ := #(I.filter (fun x => x + t ∈ I))

/-- Affine invariance: for `α x = u x + b` (`u` a unit), `C (α J) (u t) = C J t`. -/
lemma C_affine (u : (ZMod n)ˣ) (b : ZMod n) (J : Finset (ZMod n)) (t : ZMod n) :
    C (J.image (fun x => (u : ZMod n) * x + b)) ((u : ZMod n) * t) = C J t := by
  have hinj : Function.Injective (fun x : ZMod n => (u : ZMod n) * x + b) := by
    intro x y hxy
    have h' : (u : ZMod n) * x = u * y := add_right_cancel hxy
    simpa using congrArg (fun z => ((u⁻¹ : (ZMod n)ˣ) : ZMod n) * z) h'
  unfold C
  rw [filter_image, card_image_of_injective _ hinj]
  congr 1
  refine filter_congr fun x _ => ?_
  show (u : ZMod n) * x + b + u * t ∈ _ ↔ _
  rw [show (u : ZMod n) * x + b + u * t = u * (x + t) + b by ring]
  exact hinj.mem_finset_image

lemma arith {a m k : ℕ} (ha : a < n) (hm : m < n) (hk : k ≤ n) :
    a < k ∧ (a + m) % n < k ↔ a < k - m ∨ (n - m ≤ a ∧ a < k) := by
  by_cases h : a + m < n
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

lemma mem_J [NeZero n] {k : ℕ} (hk : k ≤ n) (x : ZMod n) :
    x ∈ (range k).image (Nat.cast : ℕ → ZMod n) ↔ x.val < k := by
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := mem_image.mp h
    rw [mem_range] at hi
    rw [ZMod.val_cast_of_lt (by omega)]; exact hi
  · intro h
    exact mem_image.mpr ⟨x.val, mem_range.mpr h, ZMod.natCast_zmod_val x⟩

/-- Exact count for the block `{0, …, k-1}`: `C = (k - m) + (k - (n - m))`, `m = t.val`
(truncated subtraction, i.e. `max(0, k-m) + max(0, k-n+m)`). -/
lemma C_J [NeZero n] {k : ℕ} (hk : k ≤ n) (t : ZMod n) :
    C ((range k).image (Nat.cast : ℕ → ZMod n)) t = (k - t.val) + (k - (n - t.val)) := by
  have htv := ZMod.val_lt t
  have hS : ((range k).image (Nat.cast : ℕ → ZMod n)).filter
        (fun x => x + t ∈ (range k).image (Nat.cast : ℕ → ZMod n))
      = (range (k - t.val) ∪ Ico (n - t.val) k).image (Nat.cast : ℕ → ZMod n) := by
    ext x
    rw [mem_filter, mem_J hk, mem_J hk, ZMod.val_add, arith (ZMod.val_lt x) htv hk, mem_image]
    constructor
    · intro hx
      exact ⟨x.val, by rw [mem_union, mem_range, mem_Ico]; exact hx, ZMod.natCast_zmod_val x⟩
    · rintro ⟨i, hi, rfl⟩
      rw [mem_union, mem_range, mem_Ico] at hi
      rw [ZMod.val_cast_of_lt (by omega)]; exact hi
  unfold C
  rw [hS, card_image_of_injOn, card_union_of_disjoint, card_range, Nat.card_Ico]
  · exact disjoint_left.mpr fun a ha hb => by
      rw [mem_range] at ha; rw [mem_Ico] at hb; omega
  · intro i hi j hj hij
    simp only [coe_union, coe_range, coe_Ico, Set.mem_union, Set.mem_Iio, Set.mem_Ico] at hi hj
    have := congrArg ZMod.val hij
    rwa [ZMod.val_cast_of_lt (by omega), ZMod.val_cast_of_lt (by omega)] at this

/-- **Counting fact.** For the block `{0,…,k-1} ⊆ ZMod n`, `2 ≤ k ≤ n - 2`:
`C t = k - 1 ↔ t = 1 ∨ t = -1`. -/
theorem C_interval_eq_iff [NeZero n] {k : ℕ} (hk2 : 2 ≤ k) (hkn : k + 2 ≤ n) (t : ZMod n) :
    C ((range k).image (Nat.cast : ℕ → ZMod n)) t = k - 1 ↔ t = 1 ∨ t = -1 := by
  have : Fact (1 < n) := ⟨by omega⟩
  rw [C_J (by omega)]
  have htv := ZMod.val_lt t
  constructor
  · intro h
    have : t.val = 1 ∨ t.val = n - 1 := by omega
    rcases this with h1 | h1
    · left; rw [← ZMod.natCast_zmod_val t, h1, Nat.cast_one]
    · right
      rw [← ZMod.natCast_zmod_val t, h1, Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one,
        zero_sub]
  · rintro (rfl | rfl)
    · rw [ZMod.val_one]; omega
    · rw [ZMod.neg_val', ZMod.val_one, Nat.mod_eq_of_lt (by omega)]; omega

/-- **Lemma 4.1** of the note (stable intervals). Let `n ≥ 3` (`n = q'`),
`I = {b0, b0+1, …, b0+k-1} ⊆ ZMod n` with `2 ≤ k ≤ n - 2`, and `α x = u x + b` with `u` a unit.
If `α(I) = I` then `u = 1 ∨ u = -1`. -/
theorem lemma_4_1 (hn : 3 ≤ n) {k : ℕ} (hk2 : 2 ≤ k) (hkn : k + 2 ≤ n) (b0 : ZMod n)
    (u : (ZMod n)ˣ) (b : ZMod n)
    (h : ((range k).image (fun i : ℕ => b0 + (i : ZMod n))).image
          (fun x => (u : ZMod n) * x + b)
        = (range k).image (fun i : ℕ => b0 + (i : ZMod n))) :
    u = 1 ∨ u = -1 := by
  have : NeZero n := ⟨by omega⟩
  set I := (range k).image (fun i : ℕ => b0 + (i : ZMod n)) with hIdef
  set J := (range k).image (Nat.cast : ℕ → ZMod n) with hJdef
  have hI : I = J.image (fun x => ((1 : (ZMod n)ˣ) : ZMod n) * x + b0) := by
    rw [hIdef, hJdef, image_image]
    congr 1
    funext i
    simp [add_comm]
  have h1 : ∀ t, C I t = C J t := fun t => by
    have := C_affine 1 b0 J t
    rw [Units.val_one, one_mul] at this
    rw [hI, ← this, Units.val_one]
  have hinv : ∀ t, C I ((u : ZMod n) * t) = C I t := fun t => by
    have := C_affine u b I t
    rwa [h] at this
  have key : C J (u : ZMod n) = k - 1 := by
    rw [← h1, ← mul_one (u : ZMod n), hinv, h1, C_interval_eq_iff hk2 hkn]
    left; rfl
  rcases (C_interval_eq_iff hk2 hkn _).mp key with h' | h'
  · left; exact Units.ext (by simpa using h')
  · right; exact Units.ext (by simpa using h')

end Stable


end NotaPuente
