/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

-- encaje: núcleo de la prueba del Teorema 3 (thm:bloques, qp ≤ n⌈m/3⌉) de la nota qp_bsr.
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# The block bound `qp(ℙ^{m-1} × ℙ^{n-1}) ≤ n⌈m/3⌉`: linear-algebra core

This file formalizes the three linear-algebra steps of the proof of Theorem 3 (`thm:bloques`) of
C. Marín, *Quadratic persistence of Segre varieties and a linear gap between biquadratic SOS rank
and Zarankiewicz bounds* (2026).

* *Mixed components, graph propagation.* Unknowns `c i j h` (`i j : ZMod n`, `h : Fin 3`) with
  `c i j h = c j i h`, vectors `w k j` (in the note the covectors `a_k × a_j`) such that, at each
  vertex `j`, the vectors `w k j`, `w k' j` for distinct `k, k' ≠ j` are linearly independent,
  and the vertex equations (equation (mixto) of the note)
  `∑_{h, p - h ≠ j} c (p - h) j h • w (p - h) j = 0` for all `j, p`. Then `c i j h = 0` for
  `i ≠ j`. The proof is the one of the note: for `λ = i + j + h` the edges `{x, λ - x - h}` form
  a graph on `ZMod n` without multiple edges (`n ≥ 3`); a vertex `j₀` with `2 j₀ = λ - α`,
  `α ∈ {0, 1}`, carries a removed loop; the reflections for `h = α` and `h = β = 1 - α`
  compose to a shift by `±1`, and walking `j₀, λ - j₀ - β, j₀ ± 1, …` every vertex has an edge
  already known to vanish (or a loop), so its at most two remaining unknowns vanish.
* *Coefficient extraction.* If `∑_{p : ZMod n} x p t^p = 0` for every `n`-th root of unity
  `t ∈ ℂ`, all `x p` vanish (a polynomial of degree `< n` with `n` roots).
* *Internal components.* An alternating `3 × 3` matrix whose (left) radical contains two linearly
  independent vectors is zero.

## Main results

* `SegrePersistence.BlockBound.graph_propagation`
* `SegrePersistence.BlockBound.coeff_extraction`
* `SegrePersistence.BlockBound.internal_vanish`

## What is not covered

The reduction to blocks (projection from `ℝ^{3⌈m/3⌉}` and the decomposition of `⋀²A*` into
internal and mixed components), the identification of `𝒟` with `⋀²A* ⊗ ⋀²B*`, the
factorization `M^{ij} = (a_i × a_j) ⊗ v_{ij}` and the derivation of the vertex equations from
the radical conditions of the points `c_t ⊗ f_t`, the Zariski-openness argument and the passage
to general rational points (hence the statement `qp ≤ n⌈m/3⌉` itself) are not formalized here.
-/

@[expose] public section

open Finset

namespace SegrePersistence

namespace BlockBound

section Graph

variable {n : ℕ} {K W : Type*} [Field K] [AddCommGroup W] [Module K W]

lemma fin3_cast_injective (hn : 3 ≤ n) {h h' : Fin 3}
    (e : ((h : ℕ) : ZMod n) = ((h' : ℕ) : ZMod n)) : h = h' := by
  have := h.isLt
  have := h'.isLt
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at e
  exact Fin.ext e

lemma sum_fin3_eq {M : Type*} [AddCommMonoid M] (f : Fin 3 → M) {h0 h h' : Fin 3}
    (h1 : h ≠ h0) (h2 : h' ≠ h0) (h3 : h' ≠ h) : ∑ k, f k = f h0 + f h + f h' := by
  have hu : ∀ h0 h h' : Fin 3, h ≠ h0 → h' ≠ h0 → h' ≠ h → (univ : Finset (Fin 3)) = {h0, h, h'} :=
    by decide
  rw [hu h0 h h' h1 h2 h3, sum_insert (by simp [h1.symm, h2.symm]),
    sum_insert (by simp [h3.symm]), sum_singleton, add_assoc]

lemma exists_third (h h0 : Fin 3) : ∃ h', h' ≠ h0 ∧ h' ≠ h := by
  fin_cases h <;> fin_cases h0 <;> decide

/-- `Vanish c l x`: every non-loop edge `{x, l - x - h}` at the vertex `x` carries a zero
unknown. -/
def Vanish (c : ZMod n → ZMod n → Fin 3 → K) (l x : ZMod n) : Prop :=
  ∀ h : Fin 3, l - x - ((h : ℕ) : ZMod n) ≠ x → c (l - x - ((h : ℕ) : ZMod n)) x h = 0

/-- At a vertex with one dead edge (a loop, or an unknown already zero) the vertex equation
kills the other two unknowns. -/
lemma vanish_of_dead (hn : 3 ≤ n) (w : ZMod n → ZMod n → W)
    (hw : ∀ j k k', k ≠ j → k' ≠ j → k ≠ k' → LinearIndependent K ![w k j, w k' j])
    (c : ZMod n → ZMod n → Fin 3 → K)
    (heq : ∀ j p : ZMod n, ∑ h ∈ univ.filter (fun h : Fin 3 => p - ((h : ℕ) : ZMod n) ≠ j),
      c (p - ((h : ℕ) : ZMod n)) j h • w (p - ((h : ℕ) : ZMod n)) j = 0)
    (l x : ZMod n) (h0 : Fin 3)
    (hdead : l - x - ((h0 : ℕ) : ZMod n) = x ∨ c (l - x - ((h0 : ℕ) : ZMod n)) x h0 = 0) :
    Vanish c l x := by
  intro h hh
  have yinj : ∀ k k' : Fin 3, l - x - ((k : ℕ) : ZMod n) = l - x - ((k' : ℕ) : ZMod n) →
      k = k' := fun k k' e => fin3_cast_injective hn (sub_right_injective e)
  have hsum := heq x (l - x)
  rw [Finset.sum_filter] at hsum
  by_cases hh0 : h = h0
  · subst hh0
    rcases hdead with e | e
    · exact absurd e hh
    · exact e
  obtain ⟨h', h'0, h'h⟩ := exists_third h h0
  rw [sum_fin3_eq _ hh0 h'0 h'h] at hsum
  have hT0 : (if l - x - ((h0 : ℕ) : ZMod n) ≠ x then
      c (l - x - ((h0 : ℕ) : ZMod n)) x h0 • w (l - x - ((h0 : ℕ) : ZMod n)) x else 0) = 0 := by
    rcases hdead with e | e
    · simp [e]
    · simp [e]
  rw [hT0, zero_add] at hsum
  simp only [ne_eq, hh, not_false_eq_true, ↓reduceIte] at hsum
  by_cases hl : l - x - ((h' : ℕ) : ZMod n) = x
  · simp only [hl, not_true_eq_false, ↓reduceIte, add_zero] at hsum
    have hy0 : l - x - ((h0 : ℕ) : ZMod n) ≠ x := fun e => h'0 (yinj _ _ (hl.trans e.symm))
    have hne : l - x - ((h : ℕ) : ZMod n) ≠ l - x - ((h0 : ℕ) : ZMod n) :=
      fun e => hh0 (yinj _ _ e)
    have hw0 := (hw x _ _ hh hy0 hne).ne_zero 0
    simp only [Matrix.cons_val_zero] at hw0
    exact (smul_eq_zero.mp hsum).resolve_right hw0
  · simp only [hl, not_false_eq_true, ↓reduceIte] at hsum
    have hne : l - x - ((h : ℕ) : ZMod n) ≠ l - x - ((h' : ℕ) : ZMod n) :=
      fun e => h'h (yinj _ _ e).symm
    exact (LinearIndependent.pair_iff.mp (hw x _ _ hh hl hne) _ _ hsum).1

/-- Propagation along one edge: if the neighbour `l - x - h₀` is done, so is `x`. -/
lemma vanish_step (hn : 3 ≤ n) (w : ZMod n → ZMod n → W)
    (hw : ∀ j k k', k ≠ j → k' ≠ j → k ≠ k' → LinearIndependent K ![w k j, w k' j])
    (c : ZMod n → ZMod n → Fin 3 → K) (hc : ∀ i j h, c i j h = c j i h)
    (heq : ∀ j p : ZMod n, ∑ h ∈ univ.filter (fun h : Fin 3 => p - ((h : ℕ) : ZMod n) ≠ j),
      c (p - ((h : ℕ) : ZMod n)) j h • w (p - ((h : ℕ) : ZMod n)) j = 0)
    (l x : ZMod n) (h0 : Fin 3) (hQ : Vanish c l (l - x - ((h0 : ℕ) : ZMod n))) :
    Vanish c l x := by
  apply vanish_of_dead hn w hw c heq l x h0
  by_cases e : l - x - ((h0 : ℕ) : ZMod n) = x
  · exact Or.inl e
  · right
    have hx : l - (l - x - ((h0 : ℕ) : ZMod n)) - ((h0 : ℕ) : ZMod n) = x := by ring
    have := hQ h0 (by rw [hx]; exact Ne.symm e)
    rw [hx] at this
    rw [hc]
    exact this

/-- Walking `j₀, l - j₀ - β, j₀ + δ, l - (j₀ + δ) - β, …` with `δ = β - α = ±1` reaches every
vertex. -/
lemma vanish_all (hn : 3 ≤ n) (w : ZMod n → ZMod n → W)
    (hw : ∀ j k k', k ≠ j → k' ≠ j → k ≠ k' → LinearIndependent K ![w k j, w k' j])
    (c : ZMod n → ZMod n → Fin 3 → K) (hc : ∀ i j h, c i j h = c j i h)
    (heq : ∀ j p : ZMod n, ∑ h ∈ univ.filter (fun h : Fin 3 => p - ((h : ℕ) : ZMod n) ≠ j),
      c (p - ((h : ℕ) : ZMod n)) j h • w (p - ((h : ℕ) : ZMod n)) j = 0)
    (l j0 : ZMod n) (α β : Fin 3) (hloop : l - j0 - ((α : ℕ) : ZMod n) = j0)
    (hδ : (((β : ℕ) : ZMod n) - ((α : ℕ) : ZMod n)) *
      (((β : ℕ) : ZMod n) - ((α : ℕ) : ZMod n)) = 1) :
    ∀ x, Vanish c l x := by
  have : NeZero n := ⟨by omega⟩
  set δ := ((β : ℕ) : ZMod n) - ((α : ℕ) : ZMod n) with hδdef
  have key : ∀ k : ℕ, Vanish c l (j0 + (k : ZMod n) * δ) ∧
      Vanish c l (l - (j0 + (k : ZMod n) * δ) - ((β : ℕ) : ZMod n)) := by
    intro k
    induction k with
    | zero =>
      have h0 : Vanish c l j0 := vanish_of_dead hn w hw c heq l j0 α (Or.inl hloop)
      simp only [Nat.cast_zero, zero_mul, add_zero]
      refine ⟨h0, vanish_step hn w hw c hc heq l _ β ?_⟩
      rw [show l - (l - j0 - ((β : ℕ) : ZMod n)) - ((β : ℕ) : ZMod n) = j0 by ring]
      exact h0
    | succ k ih =>
      have h1 : Vanish c l (j0 + ((k + 1 : ℕ) : ZMod n) * δ) := by
        apply vanish_step hn w hw c hc heq l _ α
        rw [show l - (j0 + ((k + 1 : ℕ) : ZMod n) * δ) - ((α : ℕ) : ZMod n) =
            l - (j0 + (k : ZMod n) * δ) - ((β : ℕ) : ZMod n) by
          push_cast
          linear_combination -hδdef]
        exact ih.2
      refine ⟨h1, vanish_step hn w hw c hc heq l _ β ?_⟩
      rw [show l - (l - (j0 + ((k + 1 : ℕ) : ZMod n) * δ) - ((β : ℕ) : ZMod n)) -
          ((β : ℕ) : ZMod n) = j0 + ((k + 1 : ℕ) : ZMod n) * δ by ring]
      exact h1
  intro x
  have hx : j0 + ((((x - j0) * δ).val : ℕ) : ZMod n) * δ = x := by
    rw [ZMod.natCast_zmod_val]
    linear_combination (x - j0) * hδ
  rw [← hx]
  exact (key _).1

/-- **Graph propagation** (the mixed components of Theorem 3 of the note). With unknowns
`c i j h = c j i h`, vectors `w k j` pairwise independent at each vertex `j`, and the vertex
equations `∑_{h, p - h ≠ j} c (p - h) j h • w (p - h) j = 0` (equation (mixto)), every unknown
`c i j h` with `i ≠ j` vanishes. -/
theorem graph_propagation (hn : 3 ≤ n) (w : ZMod n → ZMod n → W)
    (hw : ∀ j k k', k ≠ j → k' ≠ j → k ≠ k' → LinearIndependent K ![w k j, w k' j])
    (c : ZMod n → ZMod n → Fin 3 → K) (hc : ∀ i j h, c i j h = c j i h)
    (heq : ∀ j p : ZMod n, ∑ h ∈ univ.filter (fun h : Fin 3 => p - ((h : ℕ) : ZMod n) ≠ j),
      c (p - ((h : ℕ) : ZMod n)) j h • w (p - ((h : ℕ) : ZMod n)) j = 0)
    (i j : ZMod n) (h : Fin 3) (hij : i ≠ j) : c i j h = 0 := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨l, hl⟩ : ∃ l : ZMod n, l = i + j + ((h : ℕ) : ZMod n) := ⟨_, rfl⟩
  have hlv : ((l.val : ℕ) : ZMod n) = l := ZMod.natCast_zmod_val l
  have hall : ∀ x, Vanish c l x := by
    rcases Nat.even_or_odd' l.val with ⟨q, hq | hq⟩
    · refine vanish_all hn w hw c hc heq l (q : ZMod n) 0 1 ?_ ?_
      · rw [← hlv, hq]
        push_cast
        simp only [Fin.val_zero, Nat.cast_zero]
        ring
      · simp
    · refine vanish_all hn w hw c hc heq l (q : ZMod n) 1 0 ?_ ?_
      · rw [← hlv, hq]
        push_cast
        simp only [Fin.val_one, Nat.cast_one]
        ring
      · simp
  have hi : l - j - ((h : ℕ) : ZMod n) = i := by rw [hl]; ring
  have := hall j h (by rw [hi]; exact hij)
  rwa [hi] at this

end Graph

/-- **Coefficient extraction.** If `∑_{p : ZMod n} x p t^p` vanishes at every `n`-th root of unity
`t ∈ ℂ`, every coefficient `x p` vanishes. -/
theorem coeff_extraction {n : ℕ} [NeZero n] (x : ZMod n → ℂ)
    (hx : ∀ t : ℂ, t ^ n = 1 → ∑ p : ZMod n, x p * t ^ p.val = 0) (p : ZMod n) : x p = 0 := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  classical
  set P : Polynomial ℂ := ∑ q : ZMod n, Polynomial.C (x q) * Polynomial.X ^ q.val with hP
  have hP0 : P = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P
      (Polynomial.nthRootsFinset n (1 : ℂ))
    · intro t ht
      rw [Polynomial.mem_nthRootsFinset hn] at ht
      simpa [hP, Polynomial.eval_finsetSum] using hx t ht
    · rw [(Complex.isPrimitiveRoot_exp n hn.ne').card_nthRootsFinset]
      have : P.natDegree ≤ n - 1 :=
        Polynomial.natDegree_sum_le_of_forall_le _ _ fun q _ =>
          (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by have := ZMod.val_lt q; omega)
      omega
  have hc := congrArg (fun Q => Polynomial.coeff Q p.val) hP0
  simp only [hP, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at hc
  rw [Finset.sum_eq_single p] at hc
  · simpa using hc
  · intro q _ hq
    simp only [ite_eq_right_iff]
    intro e
    exact absurd (ZMod.val_injective n e).symm hq
  · simp

/-- **Internal components.** An alternating `3 × 3` matrix whose left radical contains two
linearly independent vectors is zero (a nonzero alternating form on `K³` has a one-dimensional
radical). -/
theorem internal_vanish {K : Type*} [Field K] (M : Matrix (Fin 3) (Fin 3) K)
    (hskew : M.transpose = -M) (hdiag : ∀ i, M i i = 0) {a b : Fin 3 → K}
    (hab : LinearIndependent K ![a, b]) (ha : Matrix.vecMul a M = 0)
    (hb : Matrix.vecMul b M = 0) : M = 0 := by
  have hs : ∀ i j, M j i = -M i j := fun i j => by
    have := congrFun (congrFun hskew i) j
    simpa using this
  have h10 := hs 0 1
  have h20 := hs 0 2
  have h21 := hs 1 2
  have ha0 : a 0 * M 0 0 + a 1 * M 1 0 + a 2 * M 2 0 = 0 := by
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_three] using congrFun ha 0
  have ha1 : a 0 * M 0 1 + a 1 * M 1 1 + a 2 * M 2 1 = 0 := by
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_three] using congrFun ha 1
  have ha2 : a 0 * M 0 2 + a 1 * M 1 2 + a 2 * M 2 2 = 0 := by
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_three] using congrFun ha 2
  have hb0 : b 0 * M 0 0 + b 1 * M 1 0 + b 2 * M 2 0 = 0 := by
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_three] using congrFun hb 0
  have hb1 : b 0 * M 0 1 + b 1 * M 1 1 + b 2 * M 2 1 = 0 := by
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_three] using congrFun hb 1
  have hb2 : b 0 * M 0 2 + b 1 * M 1 2 + b 2 * M 2 2 = 0 := by
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_three] using congrFun hb 2
  rw [hdiag, h10, h20] at ha0 hb0
  rw [hdiag, h21] at ha1 hb1
  rw [hdiag] at ha2 hb2
  have hcross := crossProduct_ne_zero_iff_linearIndependent.mpr hab
  have key : ∀ z : K, z * (a 0 * b 1 - a 1 * b 0) = 0 → z * (a 0 * b 2 - a 2 * b 0) = 0 →
      z * (a 1 * b 2 - a 2 * b 1) = 0 → z = 0 := by
    intro z h1 h2 h3
    by_contra hz
    apply hcross
    have e1 := (mul_eq_zero.mp h1).resolve_left hz
    have e2 := (mul_eq_zero.mp h2).resolve_left hz
    have e3 := (mul_eq_zero.mp h3).resolve_left hz
    rw [cross_apply]
    ext k
    fin_cases k
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Pi.zero_apply]
      linear_combination e3
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
        Pi.zero_apply]
      linear_combination -e2
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val, Pi.zero_apply]
      linear_combination e1
  have hp : M 0 1 = 0 := key _
    (by linear_combination (-b 2) * ha2 + (-a 0) * hb0 + (-a 1) * hb1)
    (by linear_combination (b 2) * ha1 + (-a 2) * hb1)
    (by linear_combination (-b 2) * ha0 + (a 2) * hb0)
  have hq : M 0 2 = 0 := key _
    (by linear_combination (b 1) * ha2 + (-a 1) * hb2)
    (by linear_combination (b 0) * ha0 + (b 2) * ha2 + (a 1) * hb1)
    (by linear_combination (b 1) * ha0 + (-a 1) * hb0)
  have hr : M 1 2 = 0 := key _
    (by linear_combination (-b 0) * ha2 + (a 0) * hb2)
    (by linear_combination (b 0) * ha1 + (-a 0) * hb1)
    (by linear_combination (b 1) * ha1 + (b 2) * ha2 + (a 0) * hb0)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hdiag, h10, h20, h21, hp, hq, hr]

end BlockBound

end SegrePersistence
