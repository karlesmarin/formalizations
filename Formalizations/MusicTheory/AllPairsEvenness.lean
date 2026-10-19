/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination

/-!
# Maximally even sets minimize every convex all-pairs energy

For `A ⊆ ℤ/12` and a potential `V : ℕ → ℝ`, the all-pairs energy is
`E V A = ∑ k ∈ 1..6, iv A k * V k`, with `iv` the interval vector. A double summation by parts
(`abel_bridge`) writes `E V A - E V R` as a combination of the second differences of `V` and of
`V 5 - V 6` with coefficients the double cumulative sums `DD` of `iv A - iv R`. A finite
check over all subsets of a given size shows these coefficients are nonnegative, and positive off
the `T/I`-orbit of `R`. Hence, for every convex `V` decreasing at the top, the maximally even set
`R` minimizes the energy, uniquely up to `T/I` when the inequalities are strict, for the
pentatonic (`k = 5`), whole-tone (`6`), diatonic (`7`) and octatonic (`8`) collections.

## Main results

* `abel_bridge`, `abel_nonneg`, `abel_pos`: the summation by parts and its sign.
* `groundStateG`, `uniqueG`: the reduction to the finite check.
* `diatonic_ground_state`, `diatonic_unique` and the pentatonic, whole-tone and octatonic
  versions.

## Implementation notes

The finite checks over the `k`-subsets of `ℤ/12` are proved by `decide` in the kernel on a
bitmask encoding of the subsets (`ofBits`, `exists_ofBits`, `iv_ofBits`, `census_iv`); no
`native_decide` is used.

## References

* J. Douthett, R. Krantz, papers in J. Math. Phys. (1996, 1998) on one-dimensional Ising
  models with arbitrary-range convex interactions.
* J. Douthett, R. Krantz, *Maximally even sets and configurations: common threads in mathematics,
  physics, and music*, J. Comb. Optim. 14 (2007).
* C. Marín, *One transform and one duality: a machine-checked core of music theory in Lean 4*,
  Zenodo (2026), doi:10.5281/zenodo.20953767.
-/

@[expose] public section

namespace MusicTheory

open Finset

namespace AllPairsEvenness

/-! ### Definitions -/

/-- Circular distance in `ℤ/12`: `min(|a−b|, 12−|a−b|)`, a value in `0..6`. -/
def cdist (a b : ZMod 12) : ℕ := min (a - b).val (b - a).val

/-- Interval vector entry at distance `k` (textbook convention): the number of UNORDERED pairs
    `{a,b} ⊆ A` with circular distance `k`. Each unordered pair is counted twice in `A ×ˢ A`
    (as `(a,b)` and `(b,a)`, since `cdist` is symmetric), so we divide by 2. -/
def iv (A : Finset (ZMod 12)) (k : ℕ) : ℕ :=
  ((A ×ˢ A).filter (fun p => cdist p.1 p.2 = k)).card / 2

/-- The diatonic collection `{0,2,4,5,7,9,11} ⊂ ℤ/12`. Its interval vector is the classic
    `⟨2,5,4,3,6,1⟩` (verified by `decide`, see `iv_D`). -/
def D : Finset (ZMod 12) := {0, 2, 4, 5, 7, 9, 11}

/-- Transposition `Tₙ : a ↦ a + n`. -/
def tpose (n : ZMod 12) (A : Finset (ZMod 12)) : Finset (ZMod 12) :=
  A.map ⟨(· + n), add_left_injective n⟩

/-- Inversion `I_j : a ↦ j − a` (axis `j/2`). -/
def inv (j : ZMod 12) (A : Finset (ZMod 12)) : Finset (ZMod 12) :=
  A.map ⟨(j - ·), sub_right_injective⟩

/-- The T/I-orbit of the diatonic: all 12 transposes ∪ all inversions (= 12 distinct sets,
    the diatonic being inversionally symmetric). -/
def orbitTI : Finset (Finset (ZMod 12)) :=
  ((univ : Finset (ZMod 12)).image (fun k => tpose k D))
    ∪ ((univ : Finset (ZMod 12)).image (fun j => inv j D))

/-- The T/I-orbit of an arbitrary reference set `R`: all 12 transposes ∪ all 12 inversions. -/
def orbitOf (R : Finset (ZMod 12)) : Finset (Finset (ZMod 12)) :=
  ((univ : Finset (ZMod 12)).image (fun k => tpose k R))
    ∪ ((univ : Finset (ZMod 12)).image (fun j => inv j R))

/-- The pentatonic collection `{0,2,4,7,9} ⊂ ℤ/12` (`iv = ⟨0,3,2,1,4,0⟩`, T/I-orbit size 12). -/
def P : Finset (ZMod 12) := {0, 2, 4, 7, 9}

/-- The whole-tone collection `{0,2,4,6,8,10} ⊂ ℤ/12` (`iv = ⟨0,6,0,6,0,3⟩`, T/I-orbit size 2). -/
def W : Finset (ZMod 12) := {0, 2, 4, 6, 8, 10}

/-- The octatonic collection `{0,1,3,4,6,7,9,10} ⊂ ℤ/12` (`iv = ⟨4,4,8,4,4,4⟩`, orbit size 3). -/
def O : Finset (ZMod 12) := {0, 1, 3, 4, 6, 7, 9, 10}

/-- Integer interval-vector difference from the diatonic: `d_j = iv A (j+1) − iv D (j+1)`. -/
def dvec (A : Finset (ZMod 12)) : ℕ → ℤ := fun j => (iv A (j + 1) : ℤ) - (iv D (j + 1) : ℤ)

/-- Double-cumulative sum `DD_j = Σ_{l≤j} (j+1−l)·d_l = Σ_{l≤j} Σ_{i≤l} d_i` (single-sum closed
    form of the double Abel cumulative). -/
def DD (d : ℕ → ℤ) (j : ℕ) : ℤ := ∑ l ∈ Finset.range (j + 1), ((j + 1 : ℤ) - l) * d l

/-- All-pairs energy of `A` for a real potential `V : ℕ → ℝ` (distance → energy):
    `E V A = Σ_{k=1..6} iv A k · V k`. -/
noncomputable def E (V : ℕ → ℝ) (A : Finset (ZMod 12)) : ℝ :=
  ∑ j ∈ Finset.range 6, (iv A (j + 1) : ℝ) * V (j + 1)

/-! ### The Abel bridge (general, `V`-independent) -/

/-- **Double summation-by-parts (the engine).** For any `d : ℕ → ℤ` with `d₀+⋯+d₅ = 0` and any
    `V : ℕ → ℝ`,
    `Σ_{j<6} d_j·V(j+1) = Σ_{j<4} DD_j·(V(j+1) − 2V(j+2) + V(j+3)) + DD₄·(V 5 − V 6)`.
    Both boundary terms of the first Abel pass vanish because `∑ d = 0`; the residual `DD₄·(V5−V6)`
    is the surviving (decreasing) boundary of the second pass. Pure algebra. -/
theorem abel_bridge (d : ℕ → ℤ) (V : ℕ → ℝ)
    (hsum : d 0 + d 1 + d 2 + d 3 + d 4 + d 5 = 0) :
    ∑ j ∈ Finset.range 6, (d j : ℝ) * V (j + 1)
      = (∑ j ∈ Finset.range 4, (DD d j : ℝ) * (V (j + 1) - 2 * V (j + 2) + V (j + 3)))
        + (DD d 4 : ℝ) * (V 5 - V 6) := by
  have hsumR : (d 0 : ℝ) + d 1 + d 2 + d 3 + d 4 + d 5 = 0 := by exact_mod_cast hsum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, DD]
  push_cast
  linear_combination (V 6) * hsumR

/-- The four convexity windows expanded out of the range-4 sum (helper for the bounds). -/
private lemma bridge_sum_expand (d : ℕ → ℤ) (V : ℕ → ℝ) :
    (∑ j ∈ Finset.range 4, (DD d j : ℝ) * (V (j + 1) - 2 * V (j + 2) + V (j + 3)))
      = (DD d 0 : ℝ) * (V 1 - 2 * V 2 + V 3) + (DD d 1 : ℝ) * (V 2 - 2 * V 3 + V 4)
        + (DD d 2 : ℝ) * (V 3 - 2 * V 4 + V 5) + (DD d 3 : ℝ) * (V 4 - 2 * V 5 + V 6) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- **Nonnegativity (V-independent ≥).** With `DD_j ≥ 0` (j=0..4), the four second differences
    `≥ 0` (convexity) and `V 6 ≤ V 5` (decreasing top), the energy gap is `≥ 0`. -/
theorem abel_nonneg (d : ℕ → ℤ) (V : ℕ → ℝ)
    (hsum : d 0 + d 1 + d 2 + d 3 + d 4 + d 5 = 0)
    (h0 : 0 ≤ DD d 0) (h1 : 0 ≤ DD d 1) (h2 : 0 ≤ DD d 2) (h3 : 0 ≤ DD d 3) (h4 : 0 ≤ DD d 4)
    (hc0 : 0 ≤ V 1 - 2 * V 2 + V 3) (hc1 : 0 ≤ V 2 - 2 * V 3 + V 4)
    (hc2 : 0 ≤ V 3 - 2 * V 4 + V 5) (hc3 : 0 ≤ V 4 - 2 * V 5 + V 6)
    (hdec : V 6 ≤ V 5) :
    0 ≤ ∑ j ∈ Finset.range 6, (d j : ℝ) * V (j + 1) := by
  rw [abel_bridge d V hsum, bridge_sum_expand d V]
  have t0 := mul_nonneg (show (0 : ℝ) ≤ (DD d 0 : ℝ) by exact_mod_cast h0) hc0
  have t1 := mul_nonneg (show (0 : ℝ) ≤ (DD d 1 : ℝ) by exact_mod_cast h1) hc1
  have t2 := mul_nonneg (show (0 : ℝ) ≤ (DD d 2 : ℝ) by exact_mod_cast h2) hc2
  have t3 := mul_nonneg (show (0 : ℝ) ≤ (DD d 3 : ℝ) by exact_mod_cast h3) hc3
  have t4 := mul_nonneg (show (0 : ℝ) ≤ (DD d 4 : ℝ) by exact_mod_cast h4)
    (show (0 : ℝ) ≤ V 5 - V 6 by linarith)
  linarith [t0, t1, t2, t3, t4]

/-- **Strict positivity (V-independent >).** Strictly convex (`> 0` second differences), strictly
    decreasing top (`V 6 < V 5`), `DD_j ≥ 0`, and SOME `DD_j > 0` ⟹ strictly positive gap. -/
theorem abel_pos (d : ℕ → ℤ) (V : ℕ → ℝ)
    (hsum : d 0 + d 1 + d 2 + d 3 + d 4 + d 5 = 0)
    (h0 : 0 ≤ DD d 0) (h1 : 0 ≤ DD d 1) (h2 : 0 ≤ DD d 2) (h3 : 0 ≤ DD d 3) (h4 : 0 ≤ DD d 4)
    (hc0 : 0 < V 1 - 2 * V 2 + V 3) (hc1 : 0 < V 2 - 2 * V 3 + V 4)
    (hc2 : 0 < V 3 - 2 * V 4 + V 5) (hc3 : 0 < V 4 - 2 * V 5 + V 6)
    (hdec : V 6 < V 5)
    (hex : 0 < DD d 0 ∨ 0 < DD d 1 ∨ 0 < DD d 2 ∨ 0 < DD d 3 ∨ 0 < DD d 4) :
    0 < ∑ j ∈ Finset.range 6, (d j : ℝ) * V (j + 1) := by
  rw [abel_bridge d V hsum, bridge_sum_expand d V]
  -- all five products are ≥ 0
  have t0 := mul_nonneg (show (0 : ℝ) ≤ (DD d 0 : ℝ) by exact_mod_cast h0) hc0.le
  have t1 := mul_nonneg (show (0 : ℝ) ≤ (DD d 1 : ℝ) by exact_mod_cast h1) hc1.le
  have t2 := mul_nonneg (show (0 : ℝ) ≤ (DD d 2 : ℝ) by exact_mod_cast h2) hc2.le
  have t3 := mul_nonneg (show (0 : ℝ) ≤ (DD d 3 : ℝ) by exact_mod_cast h3) hc3.le
  have t4 := mul_nonneg (show (0 : ℝ) ≤ (DD d 4 : ℝ) by exact_mod_cast h4)
    (show (0 : ℝ) ≤ V 5 - V 6 by linarith)
  -- one of them is > 0
  rcases hex with h | h | h | h | h
  · have := mul_pos (show (0 : ℝ) < (DD d 0 : ℝ) by exact_mod_cast h) hc0; linarith
  · have := mul_pos (show (0 : ℝ) < (DD d 1 : ℝ) by exact_mod_cast h) hc1; linarith
  · have := mul_pos (show (0 : ℝ) < (DD d 2 : ℝ) by exact_mod_cast h) hc2; linarith
  · have := mul_pos (show (0 : ℝ) < (DD d 3 : ℝ) by exact_mod_cast h) hc3; linarith
  · have := mul_pos (show (0 : ℝ) < (DD d 4 : ℝ) by exact_mod_cast h)
      (show (0 : ℝ) < V 5 - V 6 by linarith); linarith

/-! ### The finite censuses

A census ranges over all `k`-subsets of `ℤ/12`. A subset is encoded by a bitmask `m < 4096`
(`ofBits`, onto by `exists_ofBits`); its interval vector is computed on the bits (`ivN`, equal to
`iv (ofBits m)` by `iv_ofBits`), and the resulting statement about the masks is checked by
`decide` in the kernel. Off the orbit, the masks of the orbit are listed explicitly and shown to
lie in it by `decide`. -/

/-- Circular distance between the residues with values `a b < 12`. -/
def cdN (a b : ℕ) : ℕ := min ((a + 12 - b) % 12) ((b + 12 - a) % 12)

/-- The subset of `ℤ/12` whose elements are the set bits of `m`. -/
def ofBits (m : ℕ) : Finset (ZMod 12) := univ.filter (fun a => m.testBit a.val)

/-- The number of elements of `ofBits m`, computed on the bits. -/
def popN (m : ℕ) : ℕ := ∑ a : ZMod 12, if m.testBit a.val then 1 else 0

/-- The interval vector of `ofBits m`, computed on the bits. -/
def ivN (m k : ℕ) : ℕ :=
  (∑ a : ZMod 12, if m.testBit a.val then
    ∑ b : ZMod 12, (if m.testBit b.val then (if cdN a.val b.val = k then 1 else 0) else 0)
    else 0) / 2

theorem cdist_eq_cdN : ∀ a b : ZMod 12, cdist a b = cdN a.val b.val := by decide

theorem card_ofBits (m : ℕ) : (ofBits m).card = popN m := by
  rw [ofBits, card_filter]
  rfl

theorem iv_ofBits (m : ℕ) : iv (ofBits m) = ivN m := by
  funext k
  rw [iv, ivN, card_filter, sum_product, ofBits, sum_filter]
  congr 1
  refine sum_congr rfl fun a _ => ?_
  split_ifs with ha
  · rw [sum_filter]
    refine sum_congr rfl fun b _ => ?_
    rw [cdist_eq_cdN]
  · rfl

/-- Every subset of `ℤ/12` is `ofBits m` for some `m < 4096`. -/
theorem exists_ofBits (A : Finset (ZMod 12)) : ∃ m < 4096, ofBits m = A := by
  induction A using Finset.induction_on with
  | empty => exact ⟨0, by decide, by ext a; simp [ofBits]⟩
  | insert a s ha ih =>
    obtain ⟨m, hm, rfl⟩ := ih
    refine ⟨m ||| 2 ^ a.val, ?_, ?_⟩
    · have h1 : m < 2 ^ 12 := hm
      have h2 : 2 ^ a.val < 2 ^ 12 := Nat.pow_lt_pow_right (by decide) (ZMod.val_lt a)
      exact Nat.or_lt_two_pow h1 h2
    · ext x
      simp only [ofBits, mem_filter, mem_univ, true_and, mem_insert, Nat.testBit_or,
        Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl (ZMod.val_injective _ h.symm)
      · rintro (h | h)
        · exact Or.inr (by rw [h])
        · exact Or.inl h

/-- A statement about the interval vectors of all `k`-subsets follows from the same statement
    about the bitmasks with `k` set bits. -/
theorem census_iv (k : ℕ) (Q : (ℕ → ℕ) → Prop)
    (h : ∀ m < 4096, popN m = k → Q (ivN m)) :
    ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard k, Q (iv A) := by
  intro A hA
  obtain ⟨m, hm, rfl⟩ := exists_ofBits A
  rw [iv_ofBits]
  exact h m hm (by rw [← card_ofBits]; exact (mem_powersetCard.1 hA).2)

/-- Off-orbit version of `census_iv`: the masks for which the statement fails are listed in `L`,
    and they encode members of `orb`. -/
theorem census_iv_off (k : ℕ) (orb : Finset (Finset (ZMod 12))) (L : List ℕ)
    (hL : ∀ m ∈ L, ofBits m ∈ orb) (Q : (ℕ → ℕ) → Prop)
    (h : ∀ m < 4096, popN m = k → m ∈ L ∨ Q (ivN m)) :
    ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard k, A ∉ orb → Q (iv A) := by
  intro A hA hoff
  obtain ⟨m, hm, rfl⟩ := exists_ofBits A
  rcases h m hm (by rw [← card_ofBits]; exact (mem_powersetCard.1 hA).2) with hm' | hQ
  · exact absurd (hL m hm') hoff
  · rw [iv_ofBits]
    exact hQ

/-- `dg R A` as a function of the interval vector `v` of `A`. -/
abbrev dgv (R : Finset (ZMod 12)) (v : ℕ → ℕ) : ℕ → ℤ :=
  fun j => (v (j + 1) : ℤ) - (iv R (j + 1) : ℤ)

/-- The census predicates, as functions of the interval vector. -/
abbrev SumZeroQ (R : Finset (ZMod 12)) (v : ℕ → ℕ) : Prop :=
  dgv R v 0 + dgv R v 1 + dgv R v 2 + dgv R v 3 + dgv R v 4 + dgv R v 5 = 0

abbrev DDNonnegQ (R : Finset (ZMod 12)) (v : ℕ → ℕ) : Prop :=
  0 ≤ DD (dgv R v) 0 ∧ 0 ≤ DD (dgv R v) 1 ∧ 0 ≤ DD (dgv R v) 2 ∧ 0 ≤ DD (dgv R v) 3
    ∧ 0 ≤ DD (dgv R v) 4

abbrev DDPosQ (R : Finset (ZMod 12)) (v : ℕ → ℕ) : Prop :=
  0 < DD (dgv R v) 0 ∨ 0 < DD (dgv R v) 1 ∨ 0 < DD (dgv R v) 2 ∨ 0 < DD (dgv R v) 3
    ∨ 0 < DD (dgv R v) 4

/-- `E0` as a function of the interval vector. -/
abbrev E0v (v : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range 6, v (j + 1) * (7 - (j + 1)) ^ 2

/-- The bitmasks of the twelve sets of `orbitTI`. -/
def orbitMasksD : List ℕ := [1387, 1451, 1453, 1709, 1717, 2741, 2773, 2774, 2902, 2906, 3418, 3434]

/-- The bitmasks of the twelve sets of `orbitOf P`. -/
def orbitMasksP : List ℕ := [661, 677, 1189, 1193, 1321, 1322, 1354, 2378, 2386, 2642, 2644, 2708]

/-- The bitmasks of the two sets of `orbitOf W`. -/
def orbitMasksW : List ℕ := [1365, 2730]

/-- The bitmasks of the three sets of `orbitOf O`. -/
def orbitMasksO : List ℕ := [1755, 2925, 3510]

set_option maxRecDepth 100000 in
theorem orbitMasksD_mem : ∀ m ∈ orbitMasksD, ofBits m ∈ orbitTI := by decide +kernel

set_option maxRecDepth 100000 in
theorem orbitMasksP_mem : ∀ m ∈ orbitMasksP, ofBits m ∈ orbitOf P := by decide +kernel

set_option maxRecDepth 100000 in
theorem orbitMasksW_mem : ∀ m ∈ orbitMasksW, ofBits m ∈ orbitOf W := by decide +kernel

set_option maxRecDepth 100000 in
theorem orbitMasksO_mem : ∀ m ∈ orbitMasksO, ofBits m ∈ orbitOf O := by decide +kernel

/-- `iv D = ⟨2,5,4,3,6,1⟩` — the classic diatonic interval vector. -/
theorem iv_D : iv D 1 = 2 ∧ iv D 2 = 5 ∧ iv D 3 = 4 ∧ iv D 4 = 3 ∧ iv D 5 = 6 ∧ iv D 6 = 1 := by
  decide

set_option maxRecDepth 100000 in
theorem census_hsum_bits : ∀ m < 4096, popN m = 7 → SumZeroQ D (ivN m) := by decide +kernel

/-- Every 7-subset has `C(7,2)=21` unordered pairs, so `∑ d = 0`. (Census.) -/
theorem census_hsum (A : Finset (ZMod 12)) (hA : A ∈ (univ : Finset (ZMod 12)).powersetCard 7) :
    dvec A 0 + dvec A 1 + dvec A 2 + dvec A 3 + dvec A 4 + dvec A 5 = 0 := by
  simpa only [SumZeroQ, dgv, dvec] using census_iv 7 (SumZeroQ D) census_hsum_bits A hA

set_option maxRecDepth 100000 in
theorem census_DD_bits : ∀ m < 4096, popN m = 7 → DDNonnegQ D (ivN m) := by decide +kernel

/-- The double-cumulative sums are nonnegative for EVERY 7-subset. (Census — the Abel engine.) -/
theorem census_DD (A : Finset (ZMod 12)) (hA : A ∈ (univ : Finset (ZMod 12)).powersetCard 7) :
    0 ≤ DD (dvec A) 0 ∧ 0 ≤ DD (dvec A) 1 ∧ 0 ≤ DD (dvec A) 2 ∧ 0 ≤ DD (dvec A) 3
      ∧ 0 ≤ DD (dvec A) 4 := by
  have e : dgv D (iv A) = dvec A := rfl
  simpa only [DDNonnegQ, e] using census_iv 7 (DDNonnegQ D) census_DD_bits A hA

set_option maxRecDepth 100000 in
/-- OFF the T/I-orbit of the diatonic, some double-cumulative sum is strictly positive. (Census —
    this is what makes the diatonic the UNIQUE minimizer.) -/
theorem census_offorbit (A : Finset (ZMod 12)) (hA : A ∈ (univ : Finset (ZMod 12)).powersetCard 7)
    (hoff : A ∉ orbitTI) :
    0 < DD (dvec A) 0 ∨ 0 < DD (dvec A) 1 ∨ 0 < DD (dvec A) 2 ∨ 0 < DD (dvec A) 3
      ∨ 0 < DD (dvec A) 4 := by
  exact census_iv_off 7 orbitTI orbitMasksD orbitMasksD_mem (DDPosQ D)
    (by decide +kernel) A hA hoff

set_option maxRecDepth 100000 in
/-- ON the orbit, the interval vector equals the diatonic's, so `dvec = 0`. (Census.) -/
theorem census_onorbit (A : Finset (ZMod 12)) (hA : A ∈ orbitTI) :
    iv A 1 = iv D 1 ∧ iv A 2 = iv D 2 ∧ iv A 3 = iv D 3 ∧ iv A 4 = iv D 4 ∧ iv A 5 = iv D 5
      ∧ iv A 6 = iv D 6 := by
  revert A hA
  decide +kernel

/-! ### Item 1 — single-V uniqueness via finite census (anchor) -/

/-- The integer admissible potential `V₀(k) = (7−k)²` (strictly convex, decreasing: 36,25,16,9,4,1)
    and its all-pairs energy over ℕ: `E₀ A = Σ_{k=1..6} iv A k · (7−k)²`. -/
def E0 (A : Finset (ZMod 12)) : ℕ := ∑ j ∈ Finset.range 6, iv A (j + 1) * (7 - (j + 1)) ^ 2

/-- `E₀ D = 313` (= 2·36+5·25+4·16+3·9+6·4+1·1). -/
theorem E0_D : E0 D = 313 := by decide

/-- `E0 A = c` exactly on an orbit, from the bitmask census off the orbit and a check on it. -/
theorem census_E0_unique (k c : ℕ) (orb : Finset (Finset (ZMod 12))) (L : List ℕ)
    (hL : ∀ m ∈ L, ofBits m ∈ orb)
    (h : ∀ m < 4096, popN m = k → m ∈ L ∨ E0v (ivN m) ≠ c)
    (hon : ∀ A ∈ orb, E0 A = c) :
    ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard k, (E0 A = c ↔ A ∈ orb) := by
  intro A hA
  refine ⟨fun hE => ?_, hon A⟩
  by_contra hoff
  exact census_iv_off k orb L hL (fun v => E0v v ≠ c) h A hA hoff hE

set_option maxRecDepth 100000 in
theorem item1_min_bits : ∀ m < 4096, popN m = 7 → 313 ≤ E0v (ivN m) := by decide +kernel

/-- **Item 1a (anchor).** Among all 7-subsets of `ℤ/12`, the all-pairs energy `E₀` is `≥ 313`.
    (Census.) -/
theorem item1_min (A : Finset (ZMod 12)) (hA : A ∈ (univ : Finset (ZMod 12)).powersetCard 7) :
    313 ≤ E0 A := by
  simpa only [E0v, E0] using census_iv 7 (fun v => 313 ≤ E0v v) item1_min_bits A hA

set_option maxRecDepth 100000 in
theorem item1_unique_bits : ∀ m < 4096, popN m = 7 → m ∈ orbitMasksD ∨ E0v (ivN m) ≠ 313 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem E0_orbitTI : ∀ A ∈ orbitTI, E0 A = 313 := by decide +kernel

/-- **Item 1b (anchor).** The minimum `313` is attained EXACTLY on the 12 T/I-transposes of the
    diatonic: `E₀ A = 313 ⟺ A ∈ orbitTI`. (Census.) -/
theorem item1_unique (A : Finset (ZMod 12)) (hA : A ∈ (univ : Finset (ZMod 12)).powersetCard 7) :
    E0 A = 313 ↔ A ∈ orbitTI :=
  census_E0_unique 7 313 orbitTI orbitMasksD orbitMasksD_mem item1_unique_bits E0_orbitTI A hA

/-! ### Item 3 — V-independent uniqueness at (7,12) (capstone) -/

/-- Energy gap as an interval-vector sum: `E V A − E V D = Σ_{j<6} dvec_j · V(j+1)`. -/
lemma E_sub (V : ℕ → ℝ) (A : Finset (ZMod 12)) :
    E V A - E V D = ∑ j ∈ Finset.range 6, (dvec A j : ℝ) * V (j + 1) := by
  unfold E
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold dvec
  push_cast
  ring

/-- On the orbit, the energy gap vanishes for any `V` (the interval vector is T/I-invariant). -/
lemma E_eq_of_mem_orbit (V : ℕ → ℝ) (A : Finset (ZMod 12)) (hA : A ∈ orbitTI) : E V A = E V D := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := census_onorbit A hA
  unfold E
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e1, e2, e3, e4, e5, e6]

/-- **Item 3, the ≥ half (V-INDEPENDENT ground state).** For EVERY decreasing-convex potential `V`,
    the diatonic minimizes the all-pairs energy: `E V D ≤ E V A` for every 7-subset `A`. The single
    inequality holds simultaneously for all admissible `V` — this is the V-independence. -/
theorem diatonic_ground_state (V : ℕ → ℝ)
    (hc0 : 0 ≤ V 1 - 2 * V 2 + V 3) (hc1 : 0 ≤ V 2 - 2 * V 3 + V 4)
    (hc2 : 0 ≤ V 3 - 2 * V 4 + V 5) (hc3 : 0 ≤ V 4 - 2 * V 5 + V 6)
    (hdec : V 6 ≤ V 5)
    (A : Finset (ZMod 12)) (hA : A ∈ (univ : Finset (ZMod 12)).powersetCard 7) :
    E V D ≤ E V A := by
  have hsum := census_hsum A hA
  obtain ⟨h0, h1, h2, h3, h4⟩ := census_DD A hA
  have key : 0 ≤ ∑ j ∈ Finset.range 6, (dvec A j : ℝ) * V (j + 1) :=
    abel_nonneg (dvec A) V hsum h0 h1 h2 h3 h4 hc0 hc1 hc2 hc3 hdec
  have := E_sub V A
  linarith

/-- **Item 3, the capstone (V-INDEPENDENT UNIQUENESS).** For EVERY STRICTLY convex, strictly
    decreasing potential `V`, the diatonic is the UNIQUE all-pairs ground state: `E V D = E V A`
    holds iff `A` is a transposition or inversion of the diatonic. One statement, all admissible
    `V` at once — the headline of Douthett–Krantz maximal evenness. -/
theorem diatonic_unique (V : ℕ → ℝ)
    (hc0 : 0 < V 1 - 2 * V 2 + V 3) (hc1 : 0 < V 2 - 2 * V 3 + V 4)
    (hc2 : 0 < V 3 - 2 * V 4 + V 5) (hc3 : 0 < V 4 - 2 * V 5 + V 6)
    (hdec : V 6 < V 5)
    (A : Finset (ZMod 12)) (hA : A ∈ (univ : Finset (ZMod 12)).powersetCard 7) :
    E V D = E V A ↔ A ∈ orbitTI := by
  constructor
  · -- equality ⟹ in orbit (else strict, contradiction)
    intro heq
    by_contra hoff
    have hsum := census_hsum A hA
    obtain ⟨h0, h1, h2, h3, h4⟩ := census_DD A hA
    have hex := census_offorbit A hA hoff
    have key : 0 < ∑ j ∈ Finset.range 6, (dvec A j : ℝ) * V (j + 1) :=
      abel_pos (dvec A) V hsum h0 h1 h2 h3 h4 hc0 hc1 hc2 hc3 hdec hex
    have := E_sub V A
    linarith
  · -- in orbit ⟹ equality
    intro hmem
    exact (E_eq_of_mem_orbit V A hmem).symm

/-! ### Generic reference-set engine (k-independent) -/

/-- Integer interval-vector difference from an arbitrary reference set `R`:
    `dg R A j = iv A (j+1) − iv R (j+1)`. (The diatonic-specific `dvec` is `dg D`.) -/
def dg (R A : Finset (ZMod 12)) : ℕ → ℤ :=
  fun j => (iv A (j + 1) : ℤ) - (iv R (j + 1) : ℤ)

/-- Energy gap against an arbitrary reference: `E V A − E V R = Σ_{j<6} dg R A j · V(j+1)`. -/
lemma E_sub_g (V : ℕ → ℝ) (R A : Finset (ZMod 12)) :
    E V A - E V R = ∑ j ∈ Finset.range 6, (dg R A j : ℝ) * V (j + 1) := by
  unfold E
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold dg
  push_cast
  ring

/-- When `iv A` agrees with `iv R` on all six classes, the energy is equal for any `V`. -/
lemma E_eq_g (V : ℕ → ℝ) (R A : Finset (ZMod 12))
    (e1 : iv A 1 = iv R 1) (e2 : iv A 2 = iv R 2) (e3 : iv A 3 = iv R 3)
    (e4 : iv A 4 = iv R 4) (e5 : iv A 5 = iv R 5) (e6 : iv A 6 = iv R 6) :
    E V A = E V R := by
  unfold E
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e1, e2, e3, e4, e5, e6]

/-- **Generic V-independent ground state.** Given the `∑dg=0` and `DD ≥ 0` censuses over a family
    `S`, the reference `R` minimizes the all-pairs energy over `S` for every decreasing-convex `V`. -/
theorem groundStateG (R : Finset (ZMod 12)) (V : ℕ → ℝ)
    (hc0 : 0 ≤ V 1 - 2 * V 2 + V 3) (hc1 : 0 ≤ V 2 - 2 * V 3 + V 4)
    (hc2 : 0 ≤ V 3 - 2 * V 4 + V 5) (hc3 : 0 ≤ V 4 - 2 * V 5 + V 6)
    (hdec : V 6 ≤ V 5)
    (S : Finset (Finset (ZMod 12)))
    (hsum : ∀ A ∈ S, dg R A 0 + dg R A 1 + dg R A 2 + dg R A 3 + dg R A 4 + dg R A 5 = 0)
    (hDD : ∀ A ∈ S, 0 ≤ DD (dg R A) 0 ∧ 0 ≤ DD (dg R A) 1 ∧ 0 ≤ DD (dg R A) 2
      ∧ 0 ≤ DD (dg R A) 3 ∧ 0 ≤ DD (dg R A) 4)
    (A : Finset (ZMod 12)) (hA : A ∈ S) :
    E V R ≤ E V A := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hDD A hA
  have key := abel_nonneg (dg R A) V (hsum A hA) h0 h1 h2 h3 h4 hc0 hc1 hc2 hc3 hdec
  have := E_sub_g V R A
  linarith

/-- **Generic V-independent uniqueness.** Given the `∑dg=0`, `DD ≥ 0`, off-orbit `DD>0` and
    on-orbit `iv`-agreement censuses, `R` is the unique all-pairs ground state over `S` for every
    strictly convex, strictly decreasing `V`. -/
theorem uniqueG (R : Finset (ZMod 12)) (V : ℕ → ℝ)
    (hc0 : 0 < V 1 - 2 * V 2 + V 3) (hc1 : 0 < V 2 - 2 * V 3 + V 4)
    (hc2 : 0 < V 3 - 2 * V 4 + V 5) (hc3 : 0 < V 4 - 2 * V 5 + V 6)
    (hdec : V 6 < V 5)
    (S orb : Finset (Finset (ZMod 12)))
    (hsum : ∀ A ∈ S, dg R A 0 + dg R A 1 + dg R A 2 + dg R A 3 + dg R A 4 + dg R A 5 = 0)
    (hDD : ∀ A ∈ S, 0 ≤ DD (dg R A) 0 ∧ 0 ≤ DD (dg R A) 1 ∧ 0 ≤ DD (dg R A) 2
      ∧ 0 ≤ DD (dg R A) 3 ∧ 0 ≤ DD (dg R A) 4)
    (hoff : ∀ A ∈ S, A ∉ orb → 0 < DD (dg R A) 0 ∨ 0 < DD (dg R A) 1 ∨ 0 < DD (dg R A) 2
      ∨ 0 < DD (dg R A) 3 ∨ 0 < DD (dg R A) 4)
    (hon : ∀ A ∈ orb, iv A 1 = iv R 1 ∧ iv A 2 = iv R 2 ∧ iv A 3 = iv R 3
      ∧ iv A 4 = iv R 4 ∧ iv A 5 = iv R 5 ∧ iv A 6 = iv R 6)
    (A : Finset (ZMod 12)) (hA : A ∈ S) :
    E V R = E V A ↔ A ∈ orb := by
  constructor
  · intro heq
    by_contra hoffA
    obtain ⟨h0, h1, h2, h3, h4⟩ := hDD A hA
    have hex := hoff A hA hoffA
    have key := abel_pos (dg R A) V (hsum A hA) h0 h1 h2 h3 h4 hc0 hc1 hc2 hc3 hdec hex
    have := E_sub_g V R A
    linarith
  · intro hmem
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hon A hmem
    exact (E_eq_g V R A e1 e2 e3 e4 e5 e6).symm

/-! ### k = 5 — pentatonic `{0,2,4,7,9}` (orbit size 12) -/

/-- `iv P = ⟨0,3,2,1,4,0⟩`. -/
theorem iv_P : iv P 1 = 0 ∧ iv P 2 = 3 ∧ iv P 3 = 2 ∧ iv P 4 = 1 ∧ iv P 5 = 4 ∧ iv P 6 = 0 := by
  decide

set_option maxRecDepth 100000 in
theorem census_hsum_P : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 5,
    dg P A 0 + dg P A 1 + dg P A 2 + dg P A 3 + dg P A 4 + dg P A 5 = 0 :=
  census_iv 5 (SumZeroQ P) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem census_DD_P : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 5,
    0 ≤ DD (dg P A) 0 ∧ 0 ≤ DD (dg P A) 1 ∧ 0 ≤ DD (dg P A) 2 ∧ 0 ≤ DD (dg P A) 3
      ∧ 0 ≤ DD (dg P A) 4 :=
  census_iv 5 (DDNonnegQ P) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem census_offorbit_P : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 5, A ∉ orbitOf P →
    0 < DD (dg P A) 0 ∨ 0 < DD (dg P A) 1 ∨ 0 < DD (dg P A) 2 ∨ 0 < DD (dg P A) 3
      ∨ 0 < DD (dg P A) 4 :=
  census_iv_off 5 (orbitOf P) orbitMasksP orbitMasksP_mem (DDPosQ P)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem census_onorbit_P : ∀ A ∈ orbitOf P,
    iv A 1 = iv P 1 ∧ iv A 2 = iv P 2 ∧ iv A 3 = iv P 3 ∧ iv A 4 = iv P 4 ∧ iv A 5 = iv P 5
      ∧ iv A 6 = iv P 6 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Single-V anchor: `E₀ P = 132` and `E₀ A = 132 ⟺ A ∈ orbit` over all 5-subsets. -/
theorem item1_min_P : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 5, 132 ≤ E0 A :=
  census_iv 5 (fun v => 132 ≤ E0v v) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem item1_unique_P_bits :
    ∀ m < 4096, popN m = 5 → m ∈ orbitMasksP ∨ E0v (ivN m) ≠ 132 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem E0_orbitP : ∀ A ∈ orbitOf P, E0 A = 132 := by decide +kernel

theorem item1_unique_P : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 5,
    E0 A = 132 ↔ A ∈ orbitOf P :=
  census_E0_unique 5 132 (orbitOf P) orbitMasksP orbitMasksP_mem item1_unique_P_bits E0_orbitP

/-- **Pentatonic ground state (V-INDEPENDENT).** For every decreasing-convex `V`, the pentatonic
    minimizes the all-pairs energy over all 5-subsets of `ℤ/12`. -/
theorem pentatonic_ground_state (V : ℕ → ℝ)
    (hc0 : 0 ≤ V 1 - 2 * V 2 + V 3) (hc1 : 0 ≤ V 2 - 2 * V 3 + V 4)
    (hc2 : 0 ≤ V 3 - 2 * V 4 + V 5) (hc3 : 0 ≤ V 4 - 2 * V 5 + V 6)
    (hdec : V 6 ≤ V 5)
    (A : Finset (ZMod 12)) (hA : A ∈ (univ : Finset (ZMod 12)).powersetCard 5) :
    E V P ≤ E V A :=
  groundStateG P V hc0 hc1 hc2 hc3 hdec _ census_hsum_P census_DD_P A hA

/-- **Pentatonic uniqueness (V-INDEPENDENT).** For every strictly convex, strictly decreasing `V`,
    the pentatonic is the unique all-pairs ground state up to T/I. -/
theorem pentatonic_unique (V : ℕ → ℝ)
    (hc0 : 0 < V 1 - 2 * V 2 + V 3) (hc1 : 0 < V 2 - 2 * V 3 + V 4)
    (hc2 : 0 < V 3 - 2 * V 4 + V 5) (hc3 : 0 < V 4 - 2 * V 5 + V 6)
    (hdec : V 6 < V 5)
    (A : Finset (ZMod 12)) (hA : A ∈ (univ : Finset (ZMod 12)).powersetCard 5) :
    E V P = E V A ↔ A ∈ orbitOf P :=
  uniqueG P V hc0 hc1 hc2 hc3 hdec _ _ census_hsum_P census_DD_P census_offorbit_P
    census_onorbit_P A hA

/-! ### k = 8 — octatonic `{0,1,3,4,6,7,9,10}` (orbit size 3) -/

/-- `iv O = ⟨4,4,8,4,4,4⟩`. -/
theorem iv_O : iv O 1 = 4 ∧ iv O 2 = 4 ∧ iv O 3 = 8 ∧ iv O 4 = 4 ∧ iv O 5 = 4 ∧ iv O 6 = 4 := by
  decide

set_option maxRecDepth 100000 in
theorem census_hsum_O : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 8,
    dg O A 0 + dg O A 1 + dg O A 2 + dg O A 3 + dg O A 4 + dg O A 5 = 0 :=
  census_iv 8 (SumZeroQ O) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem census_DD_O : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 8,
    0 ≤ DD (dg O A) 0 ∧ 0 ≤ DD (dg O A) 1 ∧ 0 ≤ DD (dg O A) 2 ∧ 0 ≤ DD (dg O A) 3
      ∧ 0 ≤ DD (dg O A) 4 :=
  census_iv 8 (DDNonnegQ O) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem census_offorbit_O : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 8, A ∉ orbitOf O →
    0 < DD (dg O A) 0 ∨ 0 < DD (dg O A) 1 ∨ 0 < DD (dg O A) 2 ∨ 0 < DD (dg O A) 3
      ∨ 0 < DD (dg O A) 4 :=
  census_iv_off 8 (orbitOf O) orbitMasksO orbitMasksO_mem (DDPosQ O)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem census_onorbit_O : ∀ A ∈ orbitOf O,
    iv A 1 = iv O 1 ∧ iv A 2 = iv O 2 ∧ iv A 3 = iv O 3 ∧ iv A 4 = iv O 4 ∧ iv A 5 = iv O 5
      ∧ iv A 6 = iv O 6 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Single-V anchor: `E₀ O = 428` and `E₀ A = 428 ⟺ A ∈ orbit` over all 8-subsets. -/
theorem item1_min_O : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 8, 428 ≤ E0 A :=
  census_iv 8 (fun v => 428 ≤ E0v v) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem item1_unique_O_bits :
    ∀ m < 4096, popN m = 8 → m ∈ orbitMasksO ∨ E0v (ivN m) ≠ 428 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem E0_orbitO : ∀ A ∈ orbitOf O, E0 A = 428 := by decide +kernel

theorem item1_unique_O : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 8,
    E0 A = 428 ↔ A ∈ orbitOf O :=
  census_E0_unique 8 428 (orbitOf O) orbitMasksO orbitMasksO_mem item1_unique_O_bits E0_orbitO

/-- **Octatonic ground state (V-INDEPENDENT).** -/
theorem octatonic_ground_state (V : ℕ → ℝ)
    (hc0 : 0 ≤ V 1 - 2 * V 2 + V 3) (hc1 : 0 ≤ V 2 - 2 * V 3 + V 4)
    (hc2 : 0 ≤ V 3 - 2 * V 4 + V 5) (hc3 : 0 ≤ V 4 - 2 * V 5 + V 6)
    (hdec : V 6 ≤ V 5)
    (A : Finset (ZMod 12)) (hA : A ∈ (univ : Finset (ZMod 12)).powersetCard 8) :
    E V O ≤ E V A :=
  groundStateG O V hc0 hc1 hc2 hc3 hdec _ census_hsum_O census_DD_O A hA

/-- **Octatonic uniqueness (V-INDEPENDENT).** -/
theorem octatonic_unique (V : ℕ → ℝ)
    (hc0 : 0 < V 1 - 2 * V 2 + V 3) (hc1 : 0 < V 2 - 2 * V 3 + V 4)
    (hc2 : 0 < V 3 - 2 * V 4 + V 5) (hc3 : 0 < V 4 - 2 * V 5 + V 6)
    (hdec : V 6 < V 5)
    (A : Finset (ZMod 12)) (hA : A ∈ (univ : Finset (ZMod 12)).powersetCard 8) :
    E V O = E V A ↔ A ∈ orbitOf O :=
  uniqueG O V hc0 hc1 hc2 hc3 hdec _ _ census_hsum_O census_DD_O census_offorbit_O
    census_onorbit_O A hA

/-! ### k = 6 — whole-tone `{0,2,4,6,8,10}` (orbit size 2, degenerate IV with zeros) -/

/-- `iv W = ⟨0,6,0,6,0,3⟩`. -/
theorem iv_W : iv W 1 = 0 ∧ iv W 2 = 6 ∧ iv W 3 = 0 ∧ iv W 4 = 6 ∧ iv W 5 = 0 ∧ iv W 6 = 3 := by
  decide

set_option maxRecDepth 100000 in
theorem census_hsum_W : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 6,
    dg W A 0 + dg W A 1 + dg W A 2 + dg W A 3 + dg W A 4 + dg W A 5 = 0 :=
  census_iv 6 (SumZeroQ W) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem census_DD_W : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 6,
    0 ≤ DD (dg W A) 0 ∧ 0 ≤ DD (dg W A) 1 ∧ 0 ≤ DD (dg W A) 2 ∧ 0 ≤ DD (dg W A) 3
      ∧ 0 ≤ DD (dg W A) 4 :=
  census_iv 6 (DDNonnegQ W) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem census_offorbit_W : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 6, A ∉ orbitOf W →
    0 < DD (dg W A) 0 ∨ 0 < DD (dg W A) 1 ∨ 0 < DD (dg W A) 2 ∨ 0 < DD (dg W A) 3
      ∨ 0 < DD (dg W A) 4 :=
  census_iv_off 6 (orbitOf W) orbitMasksW orbitMasksW_mem (DDPosQ W)
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem census_onorbit_W : ∀ A ∈ orbitOf W,
    iv A 1 = iv W 1 ∧ iv A 2 = iv W 2 ∧ iv A 3 = iv W 3 ∧ iv A 4 = iv W 4 ∧ iv A 5 = iv W 5
      ∧ iv A 6 = iv W 6 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Single-V anchor: `E₀ W = 207` and `E₀ A = 207 ⟺ A ∈ orbit` over all 6-subsets. -/
theorem item1_min_W : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 6, 207 ≤ E0 A :=
  census_iv 6 (fun v => 207 ≤ E0v v) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem item1_unique_W_bits :
    ∀ m < 4096, popN m = 6 → m ∈ orbitMasksW ∨ E0v (ivN m) ≠ 207 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem E0_orbitW : ∀ A ∈ orbitOf W, E0 A = 207 := by decide +kernel

theorem item1_unique_W : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 6,
    E0 A = 207 ↔ A ∈ orbitOf W :=
  census_E0_unique 6 207 (orbitOf W) orbitMasksW orbitMasksW_mem item1_unique_W_bits E0_orbitW

/-- **Whole-tone ground state (V-INDEPENDENT).** -/
theorem wholetone_ground_state (V : ℕ → ℝ)
    (hc0 : 0 ≤ V 1 - 2 * V 2 + V 3) (hc1 : 0 ≤ V 2 - 2 * V 3 + V 4)
    (hc2 : 0 ≤ V 3 - 2 * V 4 + V 5) (hc3 : 0 ≤ V 4 - 2 * V 5 + V 6)
    (hdec : V 6 ≤ V 5)
    (A : Finset (ZMod 12)) (hA : A ∈ (univ : Finset (ZMod 12)).powersetCard 6) :
    E V W ≤ E V A :=
  groundStateG W V hc0 hc1 hc2 hc3 hdec _ census_hsum_W census_DD_W A hA

/-- **Whole-tone uniqueness (V-INDEPENDENT).** Despite the degenerate IV (three zero classes), the
    off-orbit census still yields a strictly positive double-cumulative, so strict uniqueness holds
    for every strictly convex, strictly decreasing `V`. -/
theorem wholetone_unique (V : ℕ → ℝ)
    (hc0 : 0 < V 1 - 2 * V 2 + V 3) (hc1 : 0 < V 2 - 2 * V 3 + V 4)
    (hc2 : 0 < V 3 - 2 * V 4 + V 5) (hc3 : 0 < V 4 - 2 * V 5 + V 6)
    (hdec : V 6 < V 5)
    (A : Finset (ZMod 12)) (hA : A ∈ (univ : Finset (ZMod 12)).powersetCard 6) :
    E V W = E V A ↔ A ∈ orbitOf W :=
  uniqueG W V hc0 hc1 hc2 hc3 hdec _ _ census_hsum_W census_DD_W census_offorbit_W
    census_onorbit_W A hA

end AllPairsEvenness

end MusicTheory
