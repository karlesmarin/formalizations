/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Algebra.Polynomial.RuleOfSigns

/-!
# Alternating coefficients force nonnegative roots

A monic real polynomial whose coefficients alternate in sign, (-1)^(n-k) c_k >= 0, has no negative
root. As a corollary, a real symmetric matrix whose characteristic polynomial alternates is positive
semidefinite.

## Main results

* `AlternatingRoots.root_nonneg_of_alternating`: monic p with alternating coefficients: every root is >= 0
* `AlternatingRoots.posSemidef_of_charpoly_alternating`: real symmetric A with alternating charpoly is PosSemidef

## References

* Mathlib: Matrix.IsHermitian.posSemidef_iff_eigenvalues_nonneg, Matrix.IsHermitian.roots_charpoly_eq_eigenvalues.
* Prueba directa: (-1)^n p(-y) es suma de terminos >= 0 con ultimo termino y^n > 0 para y > 0.
-/

@[expose] public section

namespace AlternatingRoots

open Polynomial Finset

/-- A list of `SignType` all equal to `1` has at most one entry after `destutter (≠)`. -/
private lemma destutter_len_le (t : List SignType) (ht : ∀ x ∈ t, x = 1) :
    ((1 :: t).destutter (· ≠ ·)).length ≤ 1 := by
  induction t with
  | nil => simp
  | cons b t' ih =>
    have hb : b = 1 := ht b (by simp)
    subst hb
    rw [List.destutter_cons_cons]
    simp only [ne_eq, not_true_eq_false, ite_false]
    exact ih (fun x hx => ht x (by simp [hx]))

/-- A list of nonnegative reals has no sign variations. -/
private lemma list_signVariations_eq_zero (l : List ℝ) (h : ∀ x ∈ l, 0 ≤ x) :
    l.signVariations = 0 := by
  unfold List.signVariations
  set L := (l.map SignType.sign).filter (· ≠ 0) with hL
  have hall : ∀ x ∈ L, x = 1 := by
    intro x hx
    rw [hL, List.mem_filter, List.mem_map] at hx
    obtain ⟨⟨y, hy, rfl⟩, hne⟩ := hx
    have hy0 : 0 ≤ y := h y hy
    rcases hy0.lt_or_eq with hpos | heq
    · exact sign_pos hpos
    · subst heq; simp at hne
  clear_value L
  rcases L with _ | ⟨a, t⟩
  · simp
  · have ha : a = 1 := hall a (by simp)
    subst ha
    have := destutter_len_le t (fun x hx => hall x (by simp [hx]))
    rw [List.destutter_cons'] at this ⊢
    omega

/-- **Alternation rule.** A monic real polynomial with `(-1)^(n-k) * coeff k ≥ 0` for all
`k ≤ n = natDegree` has no negative root. This is a corollary of Descartes' rule of signs in
Mathlib (`Polynomial.roots_countP_pos_le_signVariations`). -/
theorem root_nonneg_of_alternating {p : ℝ[X]} (hm : p.Monic)
    (halt : ∀ k ≤ p.natDegree, 0 ≤ (-1 : ℝ) ^ (p.natDegree - k) * p.coeff k)
    {x : ℝ} (hx : p.IsRoot x) : 0 ≤ x := by
  by_contra hneg
  rw [not_le] at hneg
  set n := p.natDegree with hn
  have hy : 0 < -x := by linarith
  have hev : p.eval x = ∑ k ∈ range (n + 1), p.coeff k * x ^ k := by
    rw [eval_eq_sum_range]
  -- q(y) = (-1)^n p(-y), with coefficients (-1)^(n-k) * p.coeff k
  set q : ℝ[X] := ∑ k ∈ range (n + 1), C ((-1 : ℝ) ^ (n - k) * p.coeff k) * X ^ k with hq
  have hqc : ∀ k, q.coeff k = if k ≤ n then (-1 : ℝ) ^ (n - k) * p.coeff k else 0 := by
    intro k
    rw [hq, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp
  have hqn : q.coeff n = 1 := by simp [hqc, hm.coeff_natDegree, hn]
  have hq0 : q ≠ 0 := fun h => by simp [h] at hqn
  have hqeval : q.eval (-x) = (-1 : ℝ) ^ n * p.eval x := by
    rw [hq, eval_finsetSum, hev, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hkn : k ≤ n := by simpa [Nat.lt_succ_iff] using hk
    have h1 : (-1 : ℝ) ^ n = (-1) ^ (n - k) * (-1) ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hkn]
    have h2 : (-x) ^ k = (-1) ^ k * x ^ k := by rw [neg_pow]
    have h3 : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; simp
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    rw [h1, h2]
    calc (-1 : ℝ) ^ (n - k) * p.coeff k * ((-1) ^ k * x ^ k)
        = (-1) ^ (n - k) * (-1) ^ k * (p.coeff k * x ^ k) := by ring
      _ = _ := by ring
  have hroot : q.IsRoot (-x) := by
    show q.eval (-x) = 0
    rw [hqeval, hx.eq_zero, mul_zero]
  have hsv : q.signVariations = 0 := by
    unfold Polynomial.signVariations
    refine list_signVariations_eq_zero _ ?_
    rw [coeffList_of_ne_zero hq0]
    intro c hc
    simp only [List.mem_map, List.mem_reverse, List.mem_range] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    rw [hqc]
    split_ifs with hkn
    · exact halt k hkn
    · exact le_refl _
  have hdesc := Polynomial.roots_countP_pos_le_signVariations (P := q)
  rw [hsv, Nat.le_zero, Multiset.countP_eq_zero] at hdesc
  have hmem : -x ∈ q.roots := (mem_roots hq0).mpr hroot
  exact absurd hy (by simpa using hdesc _ hmem)

/-- **PSD corollary.** A real symmetric matrix whose characteristic polynomial alternates in
sign is positive semidefinite. -/
theorem posSemidef_of_charpoly_alternating {V : Type*} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℝ} (hA : A.IsSymm)
    (halt : ∀ k ≤ A.charpoly.natDegree,
      0 ≤ (-1 : ℝ) ^ (A.charpoly.natDegree - k) * A.charpoly.coeff k) :
    A.PosSemidef := by
  have hH : A.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hA
  rw [hH.posSemidef_iff_eigenvalues_nonneg]
  intro i
  refine root_nonneg_of_alternating (Matrix.charpoly_monic A) halt ?_
  have hmem : hH.eigenvalues i ∈ A.charpoly.roots := by
    rw [hH.roots_charpoly_eq_eigenvalues]; simp
  exact (mem_roots (Matrix.charpoly_monic A).ne_zero).mp hmem

end AlternatingRoots
