/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp

/-!
# Suffix-prefix avoidance: |A|·|B| ≤ q^(2n)/(e n) (Zakharov 2026)

If `A` and `B` are sets of words of length `n` over `q` letters and no nonempty suffix of a word in
`A` equals a prefix of a word in `B`, then `|A| · |B| ≤ q^(2n)/(e n)`; more precisely
`n · |A| · |B| ≤ q^(2n) (n/(n+1))^(n+1)` (D. Zakharov, arXiv:2602.20143, Theorem 1.1). The statement
and definitions are those of google-deepmind/formal-conjectures (`suffix_prefix_avoidance_bound`,
stated there with `sorry`). Proof: the overlap sets of all lengths decompose into disjoint pieces,
giving the renewal-type inequality `γ_j ≤ Σ γ_i δ_{j−i}`; weighting by `ρ^{j−1}` with
`Σ δ_i ρ^i = 1` gives `α γ_n ≤ (ρ−1)/ρ^(n+1)`, and AM-GM bounds the right side.

## Main results

* `SuffixPrefixAvoidance.zakharov_sharp`: sharp form: n·|A|·|B| ≤ q^(2n)·(n/(n+1))^(n+1)
* `SuffixPrefixAvoidance.zakharov_bound`: |A|·|B| ≤ q^(2n)/(e n) (the formal-conjectures statement)

## References

* D. Zakharov, «An isoperimetric inequality for word overlap», arXiv:2602.20143 v2 (2026), Thm 1.1.
* google-deepmind/formal-conjectures, FormalConjectures/Other/SuffixPrefixAvoidance.lean (Apache-2.0).
-/

@[expose] public section

open Finset Real

namespace SuffixPrefixAvoidance

variable {n q : ℕ}

/-- The suffix of a word `w : Fin n → Fin q` of length `k + 1` (the last `k + 1` characters). -/
def wordSuffix (w : Fin n → Fin q) (k : Fin n) : Fin (k + 1) → Fin q :=
  fun i => w ⟨n - k - 1 + i, by omega⟩

/-- The prefix of a word `w : Fin n → Fin q` of length `k + 1` (the first `k + 1` characters). -/
def wordPrefix (w : Fin n → Fin q) (k : Fin n) : Fin (k + 1) → Fin q :=
  fun i => w ⟨i, by omega⟩

/-- Two sets of words $A, B$ over `Fin q` of length `n` are suffix-prefix avoiding if no
nonempty suffix of any word in $A$ equals any prefix of any word in $B$ of the same length. -/
def IsSuffixPrefixAvoiding (A B : Finset (Fin n → Fin q)) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ k : Fin n, wordSuffix a k ≠ wordPrefix b k

/-! ### Real-analysis lemmas -/

/-- `Qs ρ δ k = ∑_{i<k} ρ^i δ(i+1)`. -/
noncomputable def Qs (ρ : ℝ) (δ : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ range k, ρ ^ i * δ (i + 1)

lemma Qs_succ (ρ : ℝ) (δ : ℕ → ℝ) (k : ℕ) : Qs ρ δ (k + 1) = Qs ρ δ k + ρ ^ k * δ (k + 1) := by
  simp [Qs, sum_range_succ]

lemma Qs_zero (ρ : ℝ) (δ : ℕ → ℝ) : Qs ρ δ 0 = 0 := by simp [Qs]

/-- Abel summation. -/
lemma abel_sum (g f : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ range m, g i * (f (i + 1) - f i) =
      g m * f m - g 0 * f 0 - ∑ i ∈ range m, (g (i + 1) - g i) * f (i + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, sum_range_succ, ih]; ring

/-- identity (3a) of Zakharov, section 2. -/
lemma weighted_identity (ρ : ℝ) (γ δ : ℕ → ℝ) (N : ℕ) :
    ∑ j ∈ range N, ρ ^ j * (δ (j + 1) + ∑ i ∈ range j, γ (i + 1) * δ (j - i) - γ (j + 1))
      = Qs ρ δ N - ∑ j ∈ range N, ρ ^ j * γ (j + 1) * (1 - ρ * Qs ρ δ (N - 1 - j)) := by
  induction N with
  | zero => simp [Qs]
  | succ N ih =>
    have hT : ∑ j ∈ range (N + 1), ρ ^ j * γ (j + 1) * (1 - ρ * Qs ρ δ (N + 1 - 1 - j))
        = ∑ j ∈ range N, ρ ^ j * γ (j + 1) * (1 - ρ * Qs ρ δ (N - 1 - j)) + ρ ^ N * γ (N + 1)
          - ρ ^ N * ∑ j ∈ range N, γ (j + 1) * δ (N - j) := by
      rw [sum_range_succ]
      have h1 : ∀ j ∈ range N, ρ ^ j * γ (j + 1) * (1 - ρ * Qs ρ δ (N + 1 - 1 - j))
          = ρ ^ j * γ (j + 1) * (1 - ρ * Qs ρ δ (N - 1 - j)) - ρ ^ N * (γ (j + 1) * δ (N - j)) := by
        intro j hj
        have hj' : j < N := mem_range.mp hj
        have e1 : N + 1 - 1 - j = (N - 1 - j) + 1 := by omega
        have e2 : N - 1 - j + 1 = N - j := by omega
        have e3 : ρ ^ N = ρ ^ j * ρ * ρ ^ (N - 1 - j) := by
          rw [← pow_succ, ← pow_add]; congr 1; omega
        rw [e1, Qs_succ, e2, e3]; ring
      rw [sum_congr rfl h1, sum_sub_distrib, ← mul_sum]
      have h2 : N + 1 - 1 - N = 0 := by omega
      rw [h2, Qs_zero]; ring
    rw [sum_range_succ, ih, hT, Qs_succ]
    ring

/-- identity (3b) of Zakharov, section 2. -/
lemma geometric_weight (ρ : ℝ) (δ : ℕ → ℝ) (N : ℕ) :
    (ρ - 1) * ∑ j ∈ range N, ρ ^ j * (1 - ρ * Qs ρ δ (N - 1 - j))
      = (1 - ∑ i ∈ range N, δ (i + 1)) * ρ ^ N + ρ * Qs ρ δ N - 1 := by
  induction N with
  | zero => simp [Qs]
  | succ N ih =>
    have hV : ∑ j ∈ range (N + 1), ρ ^ j * (1 - ρ * Qs ρ δ (N + 1 - 1 - j))
        = ρ * ∑ j ∈ range N, ρ ^ j * (1 - ρ * Qs ρ δ (N - 1 - j)) + (1 - ρ * Qs ρ δ N) := by
      rw [sum_range_succ', mul_sum]
      congr 1
      · apply sum_congr rfl
        intro j _
        have : N + 1 - 1 - (j + 1) = N - 1 - j := by omega
        rw [this]; ring
      · simp
    rw [hV, sum_range_succ, Qs_succ]
    linear_combination ρ * ih

lemma Qs_mono {ρ : ℝ} (hρ : 0 ≤ ρ) {δ : ℕ → ℝ} {n : ℕ} (hδ : ∀ i < n, 0 ≤ δ (i + 1))
    {k : ℕ} (hk : k ≤ n) : Qs ρ δ k ≤ Qs ρ δ n := by
  unfold Qs
  apply sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hk)
  intro i hi _
  exact mul_nonneg (pow_nonneg hρ i) (hδ i (mem_range.mp hi))

/-- Existence of `ρ > 1` with `F(ρ) = 1`. -/
lemma exists_root (n : ℕ) (δ : ℕ → ℝ) (hδ : ∀ i < n, 0 ≤ δ (i + 1))
    (hS : ∑ i ∈ range n, δ (i + 1) < 1) (hpos : ∃ k < n, 0 < δ (k + 1)) :
    ∃ ρ : ℝ, 1 < ρ ∧ ρ * Qs ρ δ n = 1 := by
  obtain ⟨k, hk, hδk⟩ := hpos
  set F : ℝ → ℝ := fun ρ => ∑ i ∈ range n, δ (i + 1) * ρ ^ (i + 1) with hF
  have hFq : ∀ ρ, ρ * Qs ρ δ n = F ρ := by
    intro ρ
    simp only [Qs, hF, mul_sum]
    apply sum_congr rfl; intro i _; ring
  have hcont : Continuous F := by
    simp only [hF]; fun_prop
  have hF1 : F 1 < 1 := by simpa [hF] using hS
  set ρb : ℝ := 1 + 1 / δ (k + 1) with hρb
  have hρb1 : 1 ≤ ρb := by
    have : 0 < 1 / δ (k + 1) := by positivity
    linarith
  have hFb : 1 ≤ F ρb := by
    have h1 : δ (k + 1) * ρb ^ (k + 1) ≤ F ρb := by
      apply single_le_sum (f := fun i => δ (i + 1) * ρb ^ (i + 1)) _ (mem_range.mpr hk)
      intro i hi
      exact mul_nonneg (hδ i (mem_range.mp hi)) (pow_nonneg (by linarith) _)
    have h2 : ρb ≤ ρb ^ (k + 1) := le_self_pow₀ hρb1 (by omega)
    have h3 : δ (k + 1) * ρb = δ (k + 1) + 1 := by
      rw [hρb]; field_simp
    nlinarith
  obtain ⟨ρ, hρ, hρF⟩ := intermediate_value_Icc hρb1 hcont.continuousOn
    (show (1 : ℝ) ∈ Set.Icc (F 1) (F ρb) from ⟨hF1.le, hFb⟩)
  have hne : ρ ≠ 1 := by
    rintro rfl; linarith
  exact ⟨ρ, lt_of_le_of_ne hρ.1 (Ne.symm hne), by rw [hFq]; exact hρF⟩

/-- Final one-variable inequality: from `t ρ^(n+1) ≤ ρ - 1` conclude `n t ≤ (n/(n+1))^(n+1)`. -/
lemma amgm_final (n : ℕ) (hn : 0 < n) (ρ t : ℝ) (hρ : 1 < ρ)
    (ht : t * ρ ^ (n + 1) ≤ ρ - 1) : (n : ℝ) * t ≤ ((n : ℝ) / (n + 1)) ^ (n + 1) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set s : ℝ := n * ρ / (n + 1) with hs
  have hs0 : -1 ≤ s := by
    have : 0 ≤ s := by positivity
    linarith
  have hB := one_add_mul_sub_le_pow hs0 (n + 1)
  have hB2 : (n : ℝ) * (ρ - 1) ≤ s ^ (n + 1) := by
    have : (1 : ℝ) + ((n + 1 : ℕ) : ℝ) * (s - 1) = n * (ρ - 1) := by
      rw [hs]; push_cast; field_simp; ring
    linarith
  have hs2 : s ^ (n + 1) = ((n : ℝ) / (n + 1)) ^ (n + 1) * ρ ^ (n + 1) := by
    rw [hs, ← mul_pow]; congr 1; ring
  have hρp : 0 < ρ ^ (n + 1) := by positivity
  have : ((n : ℝ) * t) * ρ ^ (n + 1) ≤ ((n : ℝ) / (n + 1)) ^ (n + 1) * ρ ^ (n + 1) := by
    nlinarith
  exact le_of_mul_le_mul_right this hρp

/-! ### Words as lists -/

/-- All words of length `j`, as lists. -/
def Wd (q j : ℕ) : Finset (List (Fin q)) := (Finset.univ : Finset (Fin j → Fin q)).image List.ofFn

lemma mem_Wd {l : List (Fin q)} {j : ℕ} : l ∈ Wd q j ↔ l.length = j := by
  constructor
  · intro h
    obtain ⟨f, _, rfl⟩ := mem_image.mp h
    simp
  · intro h
    subst h
    exact mem_image.mpr ⟨l.get, mem_univ _, List.ofFn_get l⟩

lemma card_Wd (j : ℕ) : (Wd q j).card = q ^ j := by
  rw [Wd, card_image_of_injective _ List.ofFn_injective, card_univ, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin]

/-- Suffixes of length `j` of the words of `A` (all of length `n`). -/
def sfx (n : ℕ) (A : Finset (List (Fin q))) (j : ℕ) : Finset (List (Fin q)) :=
  A.image (fun l => l.drop (n - j))

lemma sfx_length {A : Finset (List (Fin q))} (hA : ∀ l ∈ A, l.length = n) {j : ℕ} (hj : j ≤ n)
    {x : List (Fin q)} (hx : x ∈ sfx n A j) : x.length = j := by
  obtain ⟨l, hl, rfl⟩ := mem_image.mp hx
  simp [hA l hl]
  omega

lemma sfx_drop {A : Finset (List (Fin q))} {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n)
    {x : List (Fin q)} (hx : x ∈ sfx n A j) : x.drop i ∈ sfx n A (j - i) := by
  obtain ⟨l, hl, rfl⟩ := mem_image.mp hx
  refine mem_image.mpr ⟨l, hl, ?_⟩
  rw [List.drop_drop]
  congr 1
  omega

lemma sfx_zero {A : Finset (List (Fin q))} (hA : ∀ l ∈ A, l.length = n) (hne : A.Nonempty) :
    (sfx n A 0).card = 1 := by
  rw [card_eq_one]
  refine ⟨[], eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
  · obtain ⟨l, hl⟩ := hne
    refine mem_image.mpr ⟨l, hl, ?_⟩
    simp [hA l hl]
  · intro x hx
    have := sfx_length hA (Nat.zero_le n) hx
    exact List.length_eq_zero_iff.mp this

lemma card_sfx_succ_le {A : Finset (List (Fin q))} (hA : ∀ l ∈ A, l.length = n) {j : ℕ}
    (hj1 : 1 ≤ j) (hjn : j ≤ n) : (sfx n A j).card ≤ q * (sfx n A (j - 1)).card := by
  have hsub : sfx n A j ⊆
      ((Finset.univ : Finset (Fin q)) ×ˢ sfx n A (j - 1)).image (fun p => p.1 :: p.2) := by
    intro x hx
    have hl := sfx_length hA hjn hx
    cases x with
    | nil => simp at hl; omega
    | cons c tl =>
      refine mem_image.mpr ⟨(c, tl), mem_product.mpr ⟨mem_univ _, ?_⟩, rfl⟩
      have := sfx_drop (i := 1) hj1 hjn hx
      simpa using this
  calc (sfx n A j).card ≤ _ := card_le_card hsub
    _ ≤ _ := card_image_le
    _ = q * (sfx n A (j - 1)).card := by simp [card_product]

open scoped Classical in
/-- Suffixes none of whose proper nonempty prefixes is again a suffix of that length. -/
noncomputable def Dd (n : ℕ) (A : Finset (List (Fin q))) (i : ℕ) : Finset (List (Fin q)) :=
  (sfx n A i).filter (fun u => ∀ k, 1 ≤ k → k < i → u.take k ∉ sfx n A k)

lemma mem_Dd {A : Finset (List (Fin q))} {i : ℕ} {u : List (Fin q)} :
    u ∈ Dd n A i ↔ u ∈ sfx n A i ∧ ∀ k, 1 ≤ k → k < i → u.take k ∉ sfx n A k := by
  simp [Dd]

/-- The renewal inequality (R): `a_j ≤ ∑_{i=1}^{j} d_i a_{j-i}`. -/
theorem card_sfx_le_sum {A : Finset (List (Fin q))} (hA : ∀ l ∈ A, l.length = n) {j : ℕ}
    (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    (sfx n A j).card ≤ ∑ i ∈ range j, (Dd n A (i + 1)).card * (sfx n A (j - 1 - i)).card := by
  classical
  have hcov : sfx n A j ⊆ (range j).biUnion
      (fun i => (sfx n A j).filter (fun u => u.take (i + 1) ∈ Dd n A (i + 1))) := by
    intro u hu
    have hlen := sfx_length hA hjn hu
    have hex : ∃ k, 1 ≤ k ∧ k ≤ j ∧ u.take k ∈ sfx n A k :=
      ⟨j, hj1, le_rfl, by rwa [List.take_of_length_le hlen.le]⟩
    have hk0 := Nat.find_spec hex
    have hmin := fun k (hk : k < Nat.find hex) => Nat.find_min hex hk
    refine mem_biUnion.mpr ⟨Nat.find hex - 1, mem_range.mpr (by omega), mem_filter.mpr ⟨hu, ?_⟩⟩
    have e : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [e]
    refine mem_Dd.mpr ⟨hk0.2.2, fun k hk1 hk2 => ?_⟩
    rw [List.take_take, min_eq_left hk2.le]
    intro hmem
    exact hmin k hk2 ⟨hk1, by omega, hmem⟩
  calc (sfx n A j).card ≤ _ := card_le_card hcov
    _ ≤ _ := card_biUnion_le
    _ ≤ _ := sum_le_sum ?_
  intro i hi
  have hi' := mem_range.mp hi
  rw [← card_product]
  apply card_le_card_of_injOn (fun u => (u.take (i + 1), u.drop (i + 1)))
  · intro u hu
    rw [mem_coe, mem_filter] at hu
    rw [mem_coe, mem_product]
    refine ⟨hu.2, ?_⟩
    have := sfx_drop (i := i + 1) (by omega) hjn hu.1
    rwa [show j - (i + 1) = j - 1 - i by omega] at this
  · intro u _ v _ h
    simp only [Prod.mk.injEq] at h
    rw [← List.take_append_drop (i + 1) u, ← List.take_append_drop (i + 1) v, h.1, h.2]

open scoped Classical in
/-- Words of length `n` with no prefix `u.take k` (`1 ≤ k ≤ n`) among the suffixes of length `k`. -/
noncomputable def Ufin (n : ℕ) (A : Finset (List (Fin q))) : Finset (List (Fin q)) :=
  (Wd q n).filter (fun u => ∀ k, 1 ≤ k → k ≤ n → u.take k ∉ sfx n A k)

lemma mem_Ufin {A : Finset (List (Fin q))} {u : List (Fin q)} :
    u ∈ Ufin n A ↔ u.length = n ∧ ∀ k, 1 ≤ k → k ≤ n → u.take k ∉ sfx n A k := by
  simp [Ufin, mem_Wd]

/-- Words of length `n` whose prefix of length `i+1` is in `D_{i+1}`. -/
noncomputable def Xs (n : ℕ) (A : Finset (List (Fin q))) (i : ℕ) : Finset (List (Fin q)) :=
  (Dd n A (i + 1) ×ˢ Wd q (n - 1 - i)).image (fun p => p.1 ++ p.2)

lemma mem_Xs {A : Finset (List (Fin q))} {i : ℕ} {u : List (Fin q)} :
    u ∈ Xs n A i ↔ ∃ a ∈ Dd n A (i + 1), ∃ b, b.length = n - 1 - i ∧ u = a ++ b := by
  simp only [Xs, mem_image, mem_product, mem_Wd, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨h1, h2⟩, rfl⟩
    exact ⟨a, h1, b, h2, rfl⟩
  · rintro ⟨a, h1, b, h2, rfl⟩
    exact ⟨a, b, ⟨h1, h2⟩, rfl⟩

theorem card_Ufin_add_sum_le {A : Finset (List (Fin q))} (hA : ∀ l ∈ A, l.length = n) :
    (Ufin n A).card + ∑ i ∈ range n, (Dd n A (i + 1)).card * q ^ (n - 1 - i) ≤ q ^ n := by
  classical
  have hlenD : ∀ i, i < n → ∀ a ∈ Dd n A (i + 1), a.length = i + 1 := by
    intro i hi a ha
    exact sfx_length hA (by omega) (mem_Dd.mp ha).1
  have hXlen : ∀ i, i < n → ∀ u ∈ Xs n A i, u.length = n := by
    intro i hi u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_Xs.mp hu
    simp [hlenD i hi a ha, hb]
    omega
  have htake : ∀ i, i < n → ∀ u ∈ Xs n A i, u.take (i + 1) ∈ Dd n A (i + 1) := by
    intro i hi u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_Xs.mp hu
    rw [List.take_left' (hlenD i hi a ha)]
    exact ha
  have hcardX : ∀ i, i < n → (Xs n A i).card = (Dd n A (i + 1)).card * q ^ (n - 1 - i) := by
    intro i hi
    rw [Xs, card_image_of_injOn, card_product, card_Wd]
    intro p hp r hr h
    rw [mem_coe, mem_product] at hp hr
    have hl : p.1.length = r.1.length := by
      rw [hlenD i hi _ hp.1, hlenD i hi _ hr.1]
    obtain ⟨h1, h2⟩ := List.append_inj h hl
    exact Prod.ext h1 h2
  have hdisjU : Disjoint (Ufin n A) ((range n).biUnion (Xs n A)) := by
    rw [disjoint_left]
    intro u hu hu'
    obtain ⟨i, hi, hx⟩ := mem_biUnion.mp hu'
    have hi' := mem_range.mp hi
    have := (mem_Ufin.mp hu).2 (i + 1) (by omega) (by omega)
    exact this (mem_Dd.mp (htake i hi' u hx)).1
  have hpair : ((range n : Finset ℕ) : Set ℕ).PairwiseDisjoint (Xs n A) := by
    have aux : ∀ i i', i < i' → i' < n → Disjoint (Xs n A i) (Xs n A i') := by
      intro i i' hlt hi'
      rw [disjoint_left]
      intro u hu hu'
      have e1 := htake i (by omega) u hu
      have e2 := htake i' hi' u hu'
      have hmem := (mem_Dd.mp e2).2 (i + 1) (by omega) (by omega)
      apply hmem
      rw [List.take_take, min_eq_left (by omega)]
      exact (mem_Dd.mp e1).1
    intro i hi i' hi' hne
    rw [mem_coe, mem_range] at hi hi'
    rcases lt_or_gt_of_ne hne with h | h
    · exact aux i i' h hi'
    · exact (aux i' i h hi).symm
  have hsub : Ufin n A ∪ (range n).biUnion (Xs n A) ⊆ Wd q n := by
    intro u hu
    rcases mem_union.mp hu with h | h
    · exact mem_Wd.mpr (mem_Ufin.mp h).1
    · obtain ⟨i, hi, hx⟩ := mem_biUnion.mp h
      exact mem_Wd.mpr (hXlen i (mem_range.mp hi) u hx)
  calc (Ufin n A).card + ∑ i ∈ range n, (Dd n A (i + 1)).card * q ^ (n - 1 - i)
      = (Ufin n A).card + ∑ i ∈ range n, (Xs n A i).card := by
        congr 1
        apply sum_congr rfl
        intro i hi
        rw [hcardX i (mem_range.mp hi)]
    _ = (Ufin n A).card + ((range n).biUnion (Xs n A)).card := by
        rw [card_biUnion hpair]
    _ = (Ufin n A ∪ (range n).biUnion (Xs n A)).card := (card_union_of_disjoint hdisjU).symm
    _ ≤ (Wd q n).card := card_le_card hsub
    _ = q ^ n := card_Wd n

/-! ### Bridge from functions to lists -/

lemma ofFn_wordSuffix (w : Fin n → Fin q) (k : Fin n) :
    List.ofFn (wordSuffix w k) = (List.ofFn w).drop (n - (k + 1)) := by
  apply List.ext_getElem
  · simp [wordSuffix]
    omega
  · intro i h1 h2
    simp only [wordSuffix, List.getElem_ofFn, List.getElem_drop]
    congr 1

lemma ofFn_wordPrefix (w : Fin n → Fin q) (k : Fin n) :
    List.ofFn (wordPrefix w k) = (List.ofFn w).take (k + 1) := by
  apply List.ext_getElem
  · simp [wordPrefix]
  · intro i h1 h2
    simp only [wordPrefix, List.getElem_ofFn, List.getElem_take]

/-- The combinatorial facts. -/
theorem comb_facts (A B : Finset (Fin n → Fin q)) (h : IsSuffixPrefixAvoiding A B)
    (hne : A.Nonempty) :
    ∃ (a d : ℕ → ℕ) (u : ℕ), a 0 = 1 ∧ a n = A.card ∧ B.card ≤ u ∧
      (∀ j, 1 ≤ j → j ≤ n → a j ≤ q * a (j - 1)) ∧
      (∀ j, 1 ≤ j → j ≤ n → a j ≤ ∑ i ∈ range j, d (i + 1) * a (j - 1 - i)) ∧
      u + ∑ i ∈ range n, d (i + 1) * q ^ (n - 1 - i) ≤ q ^ n := by
  classical
  set A' : Finset (List (Fin q)) := A.image List.ofFn with hA'
  have hA : ∀ l ∈ A', l.length = n := by
    intro l hl
    obtain ⟨w, _, rfl⟩ := mem_image.mp hl
    simp
  have hne' : A'.Nonempty := hne.image _
  refine ⟨fun j => (sfx n A' j).card, fun i => (Dd n A' i).card, (Ufin n A').card, sfx_zero hA hne',
    ?_, ?_, fun j h1 h2 => card_sfx_succ_le hA h1 h2, fun j h1 h2 => card_sfx_le_sum hA h1 h2,
    card_Ufin_add_sum_le hA⟩
  · have : sfx n A' n = A' := by
      simp [sfx]
    show (sfx n A' n).card = A.card
    rw [this]
    exact card_image_of_injective A (List.ofFn_injective (α := Fin q) (n := n))
  · have hsub : B.image List.ofFn ⊆ Ufin n A' := by
      intro u hu
      obtain ⟨b, hb, rfl⟩ := mem_image.mp hu
      rw [mem_Ufin]
      refine ⟨by simp, fun k hk1 hk2 hmem => ?_⟩
      obtain ⟨l, hl, hlk⟩ := mem_image.mp hmem
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hl
      obtain ⟨κ, rfl⟩ : ∃ κ, k = κ + 1 := ⟨k - 1, by omega⟩
      apply h a ha b hb ⟨κ, by omega⟩
      apply List.ofFn_injective
      rw [ofFn_wordSuffix, ofFn_wordPrefix]
      exact hlk
    calc B.card = (B.image List.ofFn).card := (card_image_of_injective _ List.ofFn_injective).symm
      _ ≤ _ := card_le_card hsub

/-! ### The analytic core -/

/-- Zakharov's argument, section 2, on real sequences:
`α_j` (suffix densities), `e_j = |D_j| / q^j`, `u` the density of the avoiding set. -/
theorem analytic_core (n : ℕ) (hn : 0 < n) (α e : ℕ → ℝ) (u : ℝ)
    (h0 : α 0 = 1) (hα0 : ∀ j ≤ n, 0 ≤ α j) (hmono : ∀ j < n, α (j + 1) ≤ α j)
    (he : ∀ j < n, 0 ≤ e (j + 1))
    (hR : ∀ j < n, α (j + 1) ≤ ∑ i ∈ range (j + 1), e (i + 1) * α (j - i))
    (hu : u + ∑ i ∈ range n, e (i + 1) ≤ 1) :
    (n : ℝ) * (α n * u) ≤ ((n : ℝ) / (n + 1)) ^ (n + 1) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : 0 ≤ ((n : ℝ) / (n + 1)) ^ (n + 1) := by positivity
  rcases (hα0 n le_rfl).eq_or_lt with hz | hpos
  · rw [← hz]; simpa using hK
  obtain ⟨γ, hγ⟩ : ∃ γ : ℕ → ℝ, ∀ k, γ k = 1 - ∑ i ∈ range k, e (i + 1) := ⟨_, fun _ => rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℕ → ℝ, ∀ m, δ m = α (m - 1) - α m := ⟨_, fun _ => rfl⟩
  have hδ0 : ∀ i < n, 0 ≤ δ (i + 1) := by
    intro i hi
    rw [hδ, Nat.add_sub_cancel]
    linarith [hmono i hi]
  have hSδ : ∑ i ∈ range n, δ (i + 1) = 1 - α n := by
    have : ∀ i ∈ range n, δ (i + 1) = α i - α (i + 1) := by
      intro i _
      rw [hδ, Nat.add_sub_cancel]
    rw [sum_congr rfl this, sum_range_sub', h0]
  have hγ0 : γ 0 = 1 := by rw [hγ]; simp
  have hdiff : ∀ i, γ (i + 1) - γ i = - e (i + 1) := by
    intro i
    rw [hγ, hγ, sum_range_succ]
    ring
  have hγanti : ∀ j, j < n → γ n ≤ γ (j + 1) := by
    intro j hj
    rw [hγ, hγ]
    have : ∑ i ∈ range (j + 1), e (i + 1) ≤ ∑ i ∈ range n, e (i + 1) := by
      apply sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega))
      intro i hi _
      exact he i (mem_range.mp hi)
    linarith
  have huγ : u ≤ γ n := by rw [hγ]; linarith
  -- inequality (2)
  have h2 : ∀ j < n, γ (j + 1) ≤ δ (j + 1) + ∑ i ∈ range j, γ (i + 1) * δ (j - i) := by
    intro j hj
    have hab := abel_sum γ (fun i => α (j + 1 - i)) (j + 1)
    beta_reduce at hab
    have hδrw : ∀ i ∈ range (j + 1),
        γ i * (α (j + 1 - (i + 1)) - α (j + 1 - i)) = γ i * δ (j + 1 - i) := by
      intro i hi
      have hi' := mem_range.mp hi
      have e1 : j + 1 - (i + 1) = j + 1 - i - 1 := by omega
      rw [hδ, e1]
    have e1 : ∑ i ∈ range (j + 1), γ i * δ (j + 1 - i)
        = δ (j + 1) + ∑ i ∈ range j, γ (i + 1) * δ (j - i) := by
      rw [sum_range_succ']
      simp only [hγ0, Nat.add_sub_add_right, Nat.sub_zero, one_mul]
      ring
    have key : ∑ i ∈ range (j + 1), (γ (i + 1) - γ i) * α (j + 1 - (i + 1))
        = - ∑ i ∈ range (j + 1), e (i + 1) * α (j - i) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro i _
      rw [hdiff i, Nat.add_sub_add_right]
      ring
    rw [sum_congr rfl hδrw] at hab
    rw [key, Nat.sub_self, Nat.sub_zero, h0, hγ0] at hab
    have := hR j hj
    linarith
  have hSlt : ∑ i ∈ range n, δ (i + 1) < 1 := by rw [hSδ]; linarith
  by_cases hex : ∃ k < n, 0 < δ (k + 1)
  · obtain ⟨ρ, hρ1, hρF⟩ := exists_root n δ hδ0 hSlt hex
    have hρ0 : 0 < ρ := by linarith
    have h3a := weighted_identity ρ γ δ n
    have hnn : 0 ≤ ∑ j ∈ range n,
        ρ ^ j * (δ (j + 1) + ∑ i ∈ range j, γ (i + 1) * δ (j - i) - γ (j + 1)) := by
      apply sum_nonneg
      intro j hj
      have := h2 j (mem_range.mp hj)
      exact mul_nonneg (pow_nonneg hρ0.le _) (by linarith)
    obtain ⟨W, hWd⟩ : ∃ W : ℝ, W = ∑ j ∈ range n,
        ρ ^ j * γ (j + 1) * (1 - ρ * Qs ρ δ (n - 1 - j)) := ⟨_, rfl⟩
    obtain ⟨V, hVd⟩ : ∃ V : ℝ, V = ∑ j ∈ range n,
        ρ ^ j * (1 - ρ * Qs ρ δ (n - 1 - j)) := ⟨_, rfl⟩
    rw [← hWd] at h3a
    have hW : W ≤ Qs ρ δ n := by linarith
    have hb : ∀ j ∈ range n, 0 ≤ 1 - ρ * Qs ρ δ (n - 1 - j) := by
      intro j _
      have h1 := Qs_mono hρ0.le hδ0 (k := n - 1 - j) (by omega)
      have h2' := mul_le_mul_of_nonneg_left h1 hρ0.le
      linarith
    have hWV : γ n * V ≤ W := by
      rw [hWd, hVd, mul_sum]
      apply sum_le_sum
      intro j hj
      have h1 := hγanti j (mem_range.mp hj)
      have h' : 0 ≤ ρ ^ j * (1 - ρ * Qs ρ δ (n - 1 - j)) :=
        mul_nonneg (pow_nonneg hρ0.le _) (hb j hj)
      nlinarith
    have h3b := geometric_weight ρ δ n
    rw [← hVd, hSδ, hρF] at h3b
    have hV : (ρ - 1) * V = α n * ρ ^ n := by rw [h3b]; ring
    have hx : ρ * (γ n * V) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left (hWV.trans hW) hρ0.le
      linarith
    have hy : (ρ - 1) * (ρ * (γ n * V)) ≤ (ρ - 1) * 1 :=
      mul_le_mul_of_nonneg_left hx (by linarith)
    have hz2 : (ρ - 1) * (ρ * (γ n * V)) = α n * γ n * ρ ^ (n + 1) := by
      rw [pow_succ]
      linear_combination (ρ * γ n) * hV
    have hfin : (α n * u) * ρ ^ (n + 1) ≤ ρ - 1 := by
      have h1 : α n * u ≤ α n * γ n := mul_le_mul_of_nonneg_left huγ (hα0 n le_rfl)
      have h2'' := mul_le_mul_of_nonneg_right h1 (pow_nonneg hρ0.le (n + 1))
      linarith
    exact amgm_final n hn ρ (α n * u) hρ1 hfin
  · have hall : ∀ k < n, δ (k + 1) = 0 := fun k hk =>
      le_antisymm (not_lt.mp (fun h => hex ⟨k, hk, h⟩)) (hδ0 k hk)
    have h1 : α 1 = 1 := by
      have := hall 0 hn
      rw [hδ] at this
      simp [h0] at this
      linarith
    have hR0 := hR 0 hn
    simp [h0, h1] at hR0
    have hγ1 := hγanti 0 hn
    rw [hγ, hγ] at hγ1
    simp at hγ1
    have hαn : α n = 1 := by
      have : ∑ i ∈ range n, δ (i + 1) = 0 := sum_eq_zero (fun i hi => hall i (mem_range.mp hi))
      linarith
    have hu1 : u ≤ 0 := by
      have := huγ
      rw [hγ] at this
      linarith
    rw [hαn]
    nlinarith

/-! ### The sharp inequality -/

theorem zakharov_sharp {n q : ℕ} (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n)
    (h : IsSuffixPrefixAvoiding A B) :
    (n : ℝ) * A.card * B.card ≤ (q : ℝ) ^ (2 * n) * ((n : ℝ) / (n + 1)) ^ (n + 1) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hK : 0 ≤ ((n : ℝ) / (n + 1)) ^ (n + 1) := by positivity
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty, Nat.cast_zero, mul_zero, zero_mul]
    positivity
  obtain ⟨a, d, u, ha0, han, hBu, hmono, hRn, hUn⟩ := comb_facts A B h hne
  obtain ⟨α, hα⟩ : ∃ α : ℕ → ℝ, ∀ j, α j = (a j : ℝ) / (q : ℝ) ^ j := ⟨_, fun _ => rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℝ, ∀ j, e j = (d j : ℝ) / (q : ℝ) ^ j := ⟨_, fun _ => rfl⟩
  have key := analytic_core n hn α e ((u : ℝ) / (q : ℝ) ^ n)
    (by rw [hα, ha0]; simp)
    (fun j _ => by rw [hα]; positivity)
    (fun j hj => by
      rw [hα, hα, div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 := hmono (j + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at h1
      have h' : (a (j + 1) : ℝ) ≤ q * a j := by exact_mod_cast h1
      calc (a (j + 1) : ℝ) * (q : ℝ) ^ j ≤ (q * a j) * (q : ℝ) ^ j := by gcongr
        _ = a j * (q : ℝ) ^ (j + 1) := by ring)
    (fun j _ => by rw [he]; positivity)
    (fun j hj => by
      have hr := hRn (j + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at hr
      have hr' : (a (j + 1) : ℝ) ≤ ∑ i ∈ range (j + 1), (d (i + 1) : ℝ) * a (j - i) := by
        exact_mod_cast hr
      have hs : ∑ i ∈ range (j + 1), e (i + 1) * α (j - i)
          = (∑ i ∈ range (j + 1), (d (i + 1) : ℝ) * a (j - i)) / (q : ℝ) ^ (j + 1) := by
        rw [sum_div]
        apply sum_congr rfl
        intro i hi
        have hi' := mem_range.mp hi
        rw [he, hα, div_mul_div_comm, ← pow_add]
        have : i + 1 + (j - i) = j + 1 := by omega
        rw [this]
      rw [hs, hα]
      exact div_le_div_of_nonneg_right hr' (by positivity))
    (by
      have hs : ∑ i ∈ range n, e (i + 1)
          = (∑ i ∈ range n, (d (i + 1) : ℝ) * (q : ℝ) ^ (n - 1 - i)) / (q : ℝ) ^ n := by
        rw [sum_div]
        apply sum_congr rfl
        intro i hi
        have hi' := mem_range.mp hi
        rw [he, div_eq_div_iff (by positivity) (by positivity)]
        have : (q : ℝ) ^ n = (q : ℝ) ^ (i + 1) * (q : ℝ) ^ (n - 1 - i) := by
          rw [← pow_add]; congr 1; omega
        rw [this]; ring
      have hU' : (u : ℝ) + ∑ i ∈ range n, (d (i + 1) : ℝ) * (q : ℝ) ^ (n - 1 - i) ≤ (q : ℝ) ^ n := by
        exact_mod_cast hUn
      rw [hs, ← add_div]
      exact (div_le_one (by positivity)).mpr hU')
  rw [hα, han] at key
  have hAnn : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  have hBu' : (B.card : ℝ) ≤ u := by exact_mod_cast hBu
  have hq2 : (q : ℝ) ^ (2 * n) = (q : ℝ) ^ n * (q : ℝ) ^ n := by rw [two_mul, pow_add]
  have hid : (n : ℝ) * A.card * u
      = ((n : ℝ) * ((A.card : ℝ) / (q : ℝ) ^ n * ((u : ℝ) / (q : ℝ) ^ n))) * (q : ℝ) ^ (2 * n) := by
    rw [hq2]; field_simp
  calc (n : ℝ) * A.card * B.card ≤ (n : ℝ) * A.card * u :=
        mul_le_mul_of_nonneg_left hBu' (by positivity)
    _ = _ := hid
    _ ≤ ((n : ℝ) / (n + 1)) ^ (n + 1) * (q : ℝ) ^ (2 * n) :=
        mul_le_mul_of_nonneg_right key (by positivity)
    _ = _ := by ring

/-- `(n/(n+1))^(n+1) ≤ exp (-1)`. -/
lemma pow_div_le_exp_neg_one (n : ℕ) (hn : 0 < n) :
    ((n : ℝ) / (n + 1)) ^ (n + 1) ≤ Real.exp (-1) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : (0 : ℝ) < 1 + 1 / n := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos hx
  have hinv : (1 + 1 / (n : ℝ))⁻¹ = n / (n + 1) := by field_simp
  have hy : (0 : ℝ) < (n : ℝ) / (n + 1) := by positivity
  have h1 : 1 - (n : ℝ) / (n + 1) = 1 / (n + 1) := by field_simp; ring
  rw [hinv, h1] at hlog
  have hlogy : Real.log ((n : ℝ) / (n + 1)) = - Real.log (1 + 1 / n) := by
    rw [← hinv, Real.log_inv]
  have h2 : ((n : ℝ) + 1) * Real.log (1 + 1 / n) ≥ 1 := by
    have := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ n + 1 by positivity)
    rw [mul_one_div_cancel (by positivity)] at this
    exact this
  calc ((n : ℝ) / (n + 1)) ^ (n + 1)
      = Real.exp (Real.log ((n : ℝ) / (n + 1))) ^ (n + 1) := by rw [Real.exp_log hy]
    _ = Real.exp (((n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) / (n + 1))) := by
        rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (-1) := by
        apply Real.exp_le_exp.mpr
        rw [hlogy]
        push_cast
        nlinarith

/-- **Zakharov (2026)**, formal-conjectures form. -/
theorem zakharov_bound {n q : ℕ} (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n)
    (h : IsSuffixPrefixAvoiding A B) :
    (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := zakharov_sharp A B hq hn h
  have he := pow_div_le_exp_neg_one n hn
  have hq' : (0 : ℝ) ≤ (q : ℝ) ^ (2 * n) := by positivity
  have h1 : (n : ℝ) * A.card * B.card ≤ (q : ℝ) ^ (2 * n) * Real.exp (-1) :=
    hs.trans (mul_le_mul_of_nonneg_left he hq')
  rw [le_div_iff₀ (by positivity)]
  have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos 1).le
  have h3 : (q : ℝ) ^ (2 * n) * Real.exp (-1) * Real.exp 1 = (q : ℝ) ^ (2 * n) := by
    rw [mul_assoc, ← Real.exp_add]; simp
  nlinarith

end SuffixPrefixAvoidance


end
