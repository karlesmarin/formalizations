/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.LinearAlgebra.Matrix.Permanent
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp

/-!
# Brégman's theorem on permanents of (0,1)-matrices

For an `n × n` `(0,1)`-matrix with non-zero row sums `rᵢ`, `per A ≤ ∏ᵢ (rᵢ!)^(1/rᵢ)` (Brégman 1973,
conjectured by Minc; Theorem of the Day). Proof: Schrijver's induction in logarithmic form,
`P log P ≤ P Σᵢ log(rᵢ!)/rᵢ` for `P = per A` (zero rows allowed), from a single Jensen inequality
for `x log x`, the fibres of `σ ↦ σ(i)` (permanents of minors), the counts `r_k − 1` and `n − r_k`
over a fixed permutation, and `log r + (n − r)F(r) + (r − 1)F(r − 1) = nF(r)`.

## Main results

* `Bregman.log_bound`: P log P ≤ P Σᵢ log(rᵢ!)/rᵢ for every (0,1)-matrix (zero rows allowed)
* `Bregman.permanent_le`: Brégman: per A ≤ ∏ᵢ (rᵢ!)^(1/rᵢ)

## References

* R. Whitty, Theorem of the Day, «Bregman's Theorem» (CombinatorialTheory/Bregman).
* L. M. Brégman, Some properties of nonnegative matrices and their permanents, Soviet Math. Dokl. 14 (1973); A. Schrijver, A short proof of Minc's conjecture, J. Combin. Theory Ser. A 25 (1978) 80–83.
-/

@[expose] public section

namespace Bregman

open Finset

/-! ### Fibres of `σ ↦ σ i` and minors -/

section Fibre

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- The admissible bijections of a `(0,1)`-matrix. -/
def adm (A : I → J → ℕ) : Finset (I ≃ J) := univ.filter fun σ => ∀ i, A i (σ i) = 1

/-- The minor of `A` obtained by deleting row `i` and column `j`. -/
def minor (A : I → J → ℕ) (i : I) (j : J) : {k // k ≠ i} → {l // l ≠ j} → ℕ := fun k l => A k l

omit [Fintype I] [Fintype J] in
/-- Extend a bijection of the minors to a bijection sending `i` to `j`. -/
def extendEquiv (i : I) (j : J) (τ : {k // k ≠ i} ≃ {l // l ≠ j}) : I ≃ J :=
  (Equiv.optionSubtypeNe i).symm.trans ((Equiv.optionCongr τ).trans (Equiv.optionSubtypeNe j))

omit [Fintype I] [Fintype J] in
lemma extendEquiv_self (i : I) (j : J) (τ : {k // k ≠ i} ≃ {l // l ≠ j}) :
    extendEquiv i j τ i = j := by
  simp [extendEquiv]

omit [Fintype I] [Fintype J] in
lemma extendEquiv_of_ne (i : I) (j : J) (τ : {k // k ≠ i} ≃ {l // l ≠ j}) (k : I) (hk : k ≠ i) :
    extendEquiv i j τ k = (τ ⟨k, hk⟩).1 := by
  simp [extendEquiv, Equiv.optionSubtypeNe_symm_of_ne hk]

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- Restrict a bijection with `σ i = j` to the minors. -/
def restrictEquiv (σ : I ≃ J) (i : I) (j : J) (h : σ i = j) : {k // k ≠ i} ≃ {l // l ≠ j} :=
  σ.subtypeEquiv (fun k => by rw [← h]; simp)

/-- (F1) The fibre `{σ admissible | σ i = j}` has `a_{ij} * per(minor)` elements. -/
lemma fiber_card (A : I → J → ℕ) (hA : ∀ i j, A i j ≤ 1) (i : I) (j : J) :
    ((adm A).filter fun σ => σ i = j).card = A i j * (adm (minor A i j)).card := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hA i j) with h0 | h1
  · rw [h0, zero_mul, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro σ hσ hσi
    have := (mem_filter.1 hσ).2 i
    rw [hσi, h0] at this
    omega
  · rw [h1, one_mul]
    refine Finset.card_bij (fun σ hσ => restrictEquiv σ i j (mem_filter.1 hσ).2) ?_ ?_ ?_
    · intro σ hσ
      have h := (mem_filter.1 (mem_filter.1 hσ).1).2
      simp only [adm, mem_filter, mem_univ, true_and]
      intro k
      exact h k.1
    · intro σ hσ σ' hσ' he
      have h1 := (mem_filter.1 hσ).2
      have h2 := (mem_filter.1 hσ').2
      ext k
      by_cases hk : k = i
      · subst hk; rw [h1, h2]
      · have := congrArg (fun e => (e ⟨k, hk⟩).1) he
        exact this
    · intro τ hτ
      have hex : extendEquiv i j τ ∈ (adm A).filter fun σ => σ i = j := by
        simp only [adm, mem_filter, mem_univ, true_and] at hτ ⊢
        refine ⟨fun k => ?_, extendEquiv_self i j τ⟩
        by_cases hk : k = i
        · subst hk; rw [extendEquiv_self]; exact h1
        · rw [extendEquiv_of_ne i j τ k hk]; exact hτ ⟨k, hk⟩
      refine ⟨extendEquiv i j τ, hex, ?_⟩
      ext k
      exact extendEquiv_of_ne i j τ k.1 k.2

/-- (F3) Summing over admissible `σ` a function of `σ i`: group by the fibres. -/
lemma sum_adm_eq (A : I → J → ℕ) (hA : ∀ i j, A i j ≤ 1) (i : I) (G : J → ℝ) :
    ∑ σ ∈ adm A, G (σ i) = ∑ j, ((A i j : ℝ) * ((adm (minor A i j)).card : ℝ)) * G j := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := adm A) (t := univ) (g := fun σ => σ i)
    (fun _ _ => mem_univ _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => G j) (fun σ hσ => by rw [(mem_filter.1 hσ).2]),
    Finset.sum_const, nsmul_eq_mul, fiber_card A hA i j]
  push_cast
  ring

/-- (F2) The number of admissible bijections splits along row `i`. -/
lemma card_adm_eq (A : I → J → ℕ) (hA : ∀ i j, A i j ≤ 1) (i : I) :
    ((adm A).card : ℝ) = ∑ j, (A i j : ℝ) * ((adm (minor A i j)).card : ℝ) := by
  have := sum_adm_eq A hA i (fun _ => 1)
  simpa using this

omit [Fintype J] [DecidableEq J] in
lemma card_subtype_ne (i : I) : Fintype.card {k // k ≠ i} = Fintype.card I - 1 := by
  rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (mem_univ i),
    Finset.card_univ]

end Fibre

/-! ### Analytic lemmas -/

/-- `Φ(x) = x log x`. -/
noncomputable def Phi (x : ℝ) : ℝ := x * Real.log x

/-- `F(m) = log(m!) / m`. -/
noncomputable def F (m : ℕ) : ℝ := Real.log (m.factorial : ℝ) / m

lemma mul_F (m : ℕ) : (m : ℝ) * F m = Real.log (m.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [F]
  · unfold F
    have : (m : ℝ) ≠ 0 := by positivity
    field_simp

/-- (L2) `log r + (N - r) F(r) + (r - 1) F(r - 1) = N F(r)`. -/
lemma L2 (r : ℕ) (hr : 1 ≤ r) (N : ℝ) :
    Real.log r + (N - r) * F r + ((r : ℝ) - 1) * F (r - 1) = N * F r := by
  have h1 : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by rw [Nat.cast_sub hr]; simp
  have h2 : (r : ℝ) * F r = Real.log r + ((r : ℝ) - 1) * F (r - 1) := by
    rw [← h1, mul_F, mul_F]
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity)]
  linear_combination (-1 : ℝ) * h2

/-- (J) Jensen for `x log x` with weights `a_j / r`. -/
lemma jensen {ι : Type*} (t : Finset ι) (a c : ι → ℝ) (ha : ∀ j ∈ t, 0 ≤ a j)
    (hc : ∀ j ∈ t, 0 ≤ c j) (r : ℝ) (hr : 0 < r) (hsum : ∑ j ∈ t, a j = r)
    (hP : 0 < ∑ j ∈ t, a j * c j) :
    Phi (∑ j ∈ t, a j * c j) ≤ (∑ j ∈ t, a j * c j) * Real.log r + ∑ j ∈ t, a j * Phi (c j) := by
  set P := ∑ j ∈ t, a j * c j with hPdef
  set S := ∑ j ∈ t, a j * Phi (c j) with hSdef
  have hJ := Real.convexOn_mul_log.map_sum_le (t := t) (w := fun j => a j / r) (p := c)
    (fun j hj => div_nonneg (ha j hj) hr.le)
    (by rw [← Finset.sum_div, hsum, div_self hr.ne'])
    (fun j hj => Set.mem_Ici.2 (hc j hj))
  simp only [smul_eq_mul] at hJ
  have e1 : ∑ j ∈ t, a j / r * c j = P / r := by
    rw [hPdef, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ j ∈ t, a j / r * (c j * Real.log (c j)) = S / r := by
    rw [hSdef, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by unfold Phi; ring
  rw [e1, e2, Real.log_div hP.ne' hr.ne'] at hJ
  have h3 : P * Real.log P - P * Real.log r ≤ S := by
    calc P * Real.log P - P * Real.log r
        = r * (P / r * (Real.log P - Real.log r)) := by field_simp
      _ ≤ r * (S / r) := mul_le_mul_of_nonneg_left hJ hr.le
      _ = S := by field_simp
  unfold Phi
  linarith

/-! ### Row counts -/

section Rows

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [DecidableEq J] in
/-- (C2) For an admissible `σ` and a row `k`:
`Σ_{i ≠ k} F(r_k - a_{k,σ i}) = (N - r_k) F(r_k) + (r_k - 1) F(r_k - 1)`. -/
lemma row_count (A : I → J → ℕ) (hA : ∀ i j, A i j ≤ 1) (σ : I ≃ J)
    (hσ : ∀ i, A i (σ i) = 1) (k : I) :
    ∑ i ∈ univ.erase k, F (∑ j, A k j - A k (σ i)) =
      ((Fintype.card I : ℝ) - (∑ j, A k j : ℕ)) * F (∑ j, A k j)
        + (((∑ j, A k j : ℕ) : ℝ) - 1) * F (∑ j, A k j - 1) := by
  set r : ℕ := ∑ j, A k j with hr
  have hs : 1 + ∑ i ∈ univ.erase k, A k (σ i) = r := by
    have h := Finset.add_sum_erase univ (fun i => A k (σ i)) (mem_univ k)
    have h2 : ∑ i, A k (σ i) = r := Equiv.sum_comp σ (A k)
    rw [hσ k] at h
    rw [← h2, ← h]
  have hterm : ∀ i ∈ univ.erase k, F (r - A k (σ i)) =
      F r + (A k (σ i) : ℝ) * (F (r - 1) - F r) := by
    intro i _
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hA k (σ i)) with h0 | h1
    · rw [h0]; simp
    · rw [h1]; simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const, ← Finset.sum_mul,
    Finset.card_erase_of_mem (mem_univ k), Finset.card_univ, nsmul_eq_mul]
  have hcard : 1 ≤ Fintype.card I := Fintype.card_pos_iff.2 ⟨k⟩
  have hS : ((∑ i ∈ univ.erase k, A k (σ i) : ℕ) : ℝ) = (r : ℝ) - 1 := by
    have : ∑ i ∈ univ.erase k, A k (σ i) = r - 1 := by omega
    rw [this, Nat.cast_sub (by omega)]; simp
  rw [← Nat.cast_sum, hS, Nat.cast_sub hcard]
  push_cast
  ring

/-- Sum of `F` over the rows of a minor. -/
lemma minor_sum_F (A : I → J → ℕ) (i : I) (j : J) :
    ∑ k : {k // k ≠ i}, F (∑ l, minor A i j k l) =
      ∑ k ∈ univ.erase i, F (∑ l, A k l - A k j) := by
  have hsub : ∑ k ∈ univ.erase i, F (∑ l, A k l - A k j) =
      ∑ k : {k // k ≠ i}, F (∑ l, A k l - A k j) :=
    Finset.sum_subtype (univ.erase i) (p := fun k => k ≠ i) (by simp)
      (fun k => F (∑ l, A k l - A k j))
  rw [hsub]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  have h1 : ∑ l : {l // l ≠ j}, minor A i j k l = ∑ l ∈ univ.erase j, A k l := by
    exact (Finset.sum_subtype (univ.erase j) (p := fun l => l ≠ j) (by simp)
      (fun l => A k.1 l)).symm
  have h2 := Finset.add_sum_erase univ (fun l => A k l) (mem_univ j)
  rw [h1]
  omega

/-- The `i`-th row bound after the induction hypothesis. -/
noncomputable def Gfun (A : I → J → ℕ) (i : I) (j : J) : ℝ :=
  ∑ k ∈ univ.erase i, F (∑ l, A k l - A k j)

/-- The double sum over admissible bijections and rows. -/
lemma double_sum (A : I → J → ℕ) (hA : ∀ i j, A i j ≤ 1) :
    ∑ i, ∑ σ ∈ adm A, Gfun A i (σ i) =
      ((adm A).card : ℝ) * ∑ k, (((Fintype.card I : ℝ) - (∑ j, A k j : ℕ)) * F (∑ j, A k j)
        + (((∑ j, A k j : ℕ) : ℝ) - 1) * F (∑ j, A k j - 1)) := by
  rw [Finset.sum_comm]
  have : ∀ σ ∈ adm A, ∑ i, Gfun A i (σ i) = ∑ k, (((Fintype.card I : ℝ) - (∑ j, A k j : ℕ))
      * F (∑ j, A k j) + (((∑ j, A k j : ℕ) : ℝ) - 1) * F (∑ j, A k j - 1)) := by
    intro σ hσ
    have hσ' : ∀ i, A i (σ i) = 1 := (mem_filter.1 hσ).2
    unfold Gfun
    rw [Finset.sum_comm' (t' := univ) (s' := fun k => univ.erase k)
      (f := fun i k => F (∑ l, A k l - A k (σ i))) (by intro x y; simp [mem_erase, ne_comm])]
    exact Finset.sum_congr rfl fun k _ => row_count A hA σ hσ' k
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]

end Rows

/-! ### The logarithmic bound (Schrijver) -/

section Main

universe u v

/-- Induction on the number of rows (arbitrary column type `J`). -/
theorem log_bound_aux (n : ℕ) : ∀ {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : I → J → ℕ), (∀ i j, A i j ≤ 1) → Fintype.card I = n →
    Phi ((adm A).card : ℝ) ≤ ((adm A).card : ℝ) * ∑ i, F (∑ j, A i j) := by
  induction n with
  | zero =>
    intro I J _ _ _ _ A hA hn
    have : IsEmpty I := Fintype.card_eq_zero_iff.1 hn
    have hle : (adm A).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro σ _ τ _
      ext i
      exact isEmptyElim i
    have : (adm A).card = 0 ∨ (adm A).card = 1 := by omega
    rcases this with h | h <;> simp [h, Phi]
  | succ n ih =>
    intro I J _ _ _ _ A hA hn
    by_cases hP : (adm A).card = 0
    · simp [hP, Phi]
    have hPpos : (0 : ℝ) < (adm A).card := by exact_mod_cast Nat.pos_of_ne_zero hP
    obtain ⟨σ0, hσ0⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hP)
    have hσ0' : ∀ i, A i (σ0 i) = 1 := (mem_filter.1 hσ0).2
    have hr1 : ∀ i, 1 ≤ ∑ j, A i j := fun i =>
      calc 1 = A i (σ0 i) := (hσ0' i).symm
        _ ≤ ∑ j, A i j :=
          Finset.single_le_sum (f := A i) (fun _ _ => Nat.zero_le _) (mem_univ _)
    have hN : (Fintype.card I : ℝ) = n + 1 := by rw [hn]; push_cast; ring
    have hNpos : (0 : ℝ) < Fintype.card I := by rw [hN]; positivity
    have hIH : ∀ i j, Phi ((adm (minor A i j)).card : ℝ) ≤
        ((adm (minor A i j)).card : ℝ) * Gfun A i j := by
      intro i j
      have := ih (minor A i j) (fun k l => hA k l) (by rw [card_subtype_ne, hn]; rfl)
      rw [minor_sum_F] at this
      exact this
    have hrow : ∀ i, Phi ((adm A).card : ℝ) ≤
        ((adm A).card : ℝ) * Real.log ((∑ j, A i j : ℕ) : ℝ)
          + ∑ j, (A i j : ℝ) * (((adm (minor A i j)).card : ℝ) * Gfun A i j) := by
      intro i
      have key := jensen (univ : Finset J) (fun j => (A i j : ℝ))
        (fun j => ((adm (minor A i j)).card : ℝ))
        (fun j _ => Nat.cast_nonneg _) (fun j _ => Nat.cast_nonneg _) ((∑ j, A i j : ℕ) : ℝ)
        (by exact_mod_cast hr1 i) (by push_cast; rfl)
        (by simpa [← card_adm_eq A hA i] using hPpos)
      beta_reduce at key
      rw [← card_adm_eq A hA i] at key
      refine key.trans (add_le_add_right (Finset.sum_le_sum fun j _ => ?_) _)
      exact mul_le_mul_of_nonneg_left (hIH i j) (Nat.cast_nonneg _)
    have hsum : (Fintype.card I : ℝ) * Phi ((adm A).card : ℝ) ≤
        ((adm A).card : ℝ) * ∑ i, Real.log ((∑ j, A i j : ℕ) : ℝ)
          + ((adm A).card : ℝ) * ∑ k, (((Fintype.card I : ℝ) - (∑ j, A k j : ℕ)) * F (∑ j, A k j)
            + (((∑ j, A k j : ℕ) : ℝ) - 1) * F (∑ j, A k j - 1)) := by
      rw [← double_sum A hA]
      calc (Fintype.card I : ℝ) * Phi ((adm A).card : ℝ)
          = ∑ _i : I, Phi ((adm A).card : ℝ) := by simp
        _ ≤ ∑ i, (((adm A).card : ℝ) * Real.log ((∑ j, A i j : ℕ) : ℝ)
              + ∑ σ ∈ adm A, Gfun A i (σ i)) := by
            refine Finset.sum_le_sum fun i _ => (hrow i).trans ?_
            refine add_le_add_right (le_of_eq ?_) _
            rw [sum_adm_eq A hA i (Gfun A i)]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
    have hcomb : ∑ i, Real.log ((∑ j, A i j : ℕ) : ℝ)
        + ∑ k, (((Fintype.card I : ℝ) - (∑ j, A k j : ℕ)) * F (∑ j, A k j)
            + (((∑ j, A k j : ℕ) : ℝ) - 1) * F (∑ j, A k j - 1))
        = (Fintype.card I : ℝ) * ∑ i, F (∑ j, A i j) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have := L2 _ (hr1 k) (Fintype.card I : ℝ)
      linarith
    have h2 : (Fintype.card I : ℝ) * Phi ((adm A).card : ℝ) ≤
        (Fintype.card I : ℝ) * (((adm A).card : ℝ) * ∑ i, F (∑ j, A i j)) := by
      calc (Fintype.card I : ℝ) * Phi ((adm A).card : ℝ) ≤ _ := hsum
        _ = ((adm A).card : ℝ) * ((∑ i, Real.log ((∑ j, A i j : ℕ) : ℝ)
              + ∑ k, (((Fintype.card I : ℝ) - (∑ j, A k j : ℕ)) * F (∑ j, A k j)
              + (((∑ j, A k j : ℕ) : ℝ) - 1) * F (∑ j, A k j - 1)))) := by ring
        _ = _ := by rw [hcomb]; ring
    exact le_of_mul_le_mul_left h2 hNpos

/-- **Logarithmic Brégman bound** (Schrijver; zero rows allowed): for the number `P` of bijections
`I ≃ J` picking a `1` in every row of the `(0,1)`-matrix `A`, `P log P ≤ P Σᵢ log(rᵢ!)/rᵢ`. -/
theorem log_bound {I : Type u} {J : Type v} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (A : I → J → ℕ) (hA : ∀ i j, A i j ≤ 1) :
    ((adm A).card : ℝ) * Real.log ((adm A).card : ℝ) ≤
      ((adm A).card : ℝ) * ∑ i, Real.log (((∑ j, A i j).factorial : ℕ) : ℝ) / ((∑ j, A i j : ℕ) : ℝ) :=
  log_bound_aux _ A hA rfl

end Main

/-! ### Brégman's theorem -/

/-- The permanent of a `(0,1)`-matrix counts the admissible bijections. -/
lemma permanent_eq_card {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) (hA : ∀ i j, A i j ≤ 1) :
    A.permanent = (adm A).card := by
  rw [← Matrix.permanent_transpose]
  unfold Matrix.permanent adm
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  split_ifs with h
  · exact Finset.prod_eq_one fun i _ => by simpa using h i
  · push Not at h
    obtain ⟨i, hi⟩ := h
    apply Finset.prod_eq_zero (mem_univ i)
    have := hA i (σ i)
    simp only [Matrix.transpose_apply]
    omega

/-- **Brégman's theorem (Minc's conjecture).** For an `n × n` `(0,1)`-matrix `A` with row sums
`rᵢ = Σⱼ A i j`, the permanent satisfies `per A ≤ ∏ᵢ (rᵢ!)^(1/rᵢ)`. The classical statement asks for non-zero row sums;
none is needed here: a zero row makes `per A = 0`, and with `1/0 = 0` its factor is `(0!)^0 = 1`. -/
theorem permanent_le (n : ℕ) (A : Matrix (Fin n) (Fin n) ℕ) (hA : ∀ i j, A i j ≤ 1) :
    (A.permanent : ℝ) ≤ ∏ i, (((∑ j, A i j).factorial : ℕ) : ℝ) ^ ((1 : ℝ) / (∑ j, A i j : ℕ)) := by
  rw [permanent_eq_card A hA]
  by_cases hP : (adm A).card = 0
  · rw [hP]
    simp only [Nat.cast_zero]
    exact Finset.prod_nonneg fun i _ => by positivity
  have hpos : (0 : ℝ) < (adm A).card := by exact_mod_cast Nat.pos_of_ne_zero hP
  have hb := log_bound A hA
  have hlog : Real.log ((adm A).card : ℝ) ≤
      ∑ i, Real.log (((∑ j, A i j).factorial : ℕ) : ℝ) / ((∑ j, A i j : ℕ) : ℝ) :=
    le_of_mul_le_mul_left hb hpos
  calc ((adm A).card : ℝ) = Real.exp (Real.log ((adm A).card : ℝ)) := (Real.exp_log hpos).symm
    _ ≤ Real.exp (∑ i, Real.log (((∑ j, A i j).factorial : ℕ) : ℝ) / ((∑ j, A i j : ℕ) : ℝ)) :=
        Real.exp_le_exp.2 hlog
    _ = ∏ i, Real.exp (Real.log (((∑ j, A i j).factorial : ℕ) : ℝ) / ((∑ j, A i j : ℕ) : ℝ)) :=
        Real.exp_sum _ _
    _ = _ := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Real.rpow_def_of_pos (by exact_mod_cast Nat.factorial_pos _)]
        congr 1
        ring

end Bregman

open Finset
