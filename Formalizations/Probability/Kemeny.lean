/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Kemeny's constant

For a finite Markov chain with transition matrix `P`, a stationary distribution `π` and finite
expected hitting times `m s t` (`m t t = 0`, `m s t = 1 + Σ_k P s k · m k t` for `s ≠ t`), the
expected time `Σ_t π t · m s t` to reach a `π`-random target does not depend on `s` (Theorem of the
Day). Proof: Kac's formula `π_t (1 + Σ_k P_tk m_kt) = 1` from stationarity turns
`f(s) = Σ_t π_t m_st` into a harmonic function `f = P f`, and the hitting-time equations force a
harmonic function to be constant (minimum principle on the set where `f` is maximal).

## Main results

* `Kemeny.kac`: Kac's formula π_t (1 + Σ_k P t k · m k t) = 1
* `Kemeny.harmonic`: f(s) = Σ_t π t · m s t satisfies f = P f
* `Kemeny.exists_const`: Kemeny: Σ_t π t · m s t does not depend on s

## References

* R. Whitty, Theorem of the Day, «Kemeny's Constant» (Statistics/Kemeny).
* J. G. Kemeny, J. L. Snell, Finite Markov Chains, Van Nostrand 1960; P. Doyle, The Kemeny constant of a Markov chain (math.dartmouth.edu/~doyle/docs/kc/kc.pdf).
-/

@[expose] public section

open Finset

namespace Kemeny

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem kac (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hπ : ∀ k, ∑ s, π s * P s k = π k) (hπ1 : ∑ s, π s = 1)
    (m : ι → ι → ℝ) (hmt : ∀ t, m t t = 0)
    (hm : ∀ s t, s ≠ t → m s t = 1 + ∑ k, P s k * m k t) :
    ∀ t, π t * (1 + ∑ k, P t k * m k t) = 1 := by
  intro t
  set g : ι → ℝ := fun s => 1 + ∑ k, P s k * m k t with hg
  have h1 : ∑ s, π s * g s = 1 + ∑ k, π k * m k t := by
    have : ∀ s, π s * g s = π s + ∑ k, (π s * P s k) * m k t := by
      intro s
      simp only [hg, mul_add, mul_one, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    simp only [this, Finset.sum_add_distrib, hπ1]
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_mul, hπ k]
  have h2 : ∑ s, π s * g s = (∑ s, π s * m s t) + π t * g t := by
    have : ∀ s, π s * g s = π s * m s t + if s = t then π t * g t else 0 := by
      intro s
      by_cases hs : s = t
      · subst hs; simp [hmt]
      · simp [hs, hg, hm s t hs]
    rw [Finset.sum_congr rfl (fun s _ => this s)]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have : π t * g t = 1 := by linarith
  exact this

theorem harmonic (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hπ : ∀ k, ∑ s, π s * P s k = π k) (hπ1 : ∑ s, π s = 1)
    (m : ι → ι → ℝ) (hmt : ∀ t, m t t = 0)
    (hm : ∀ s t, s ≠ t → m s t = 1 + ∑ k, P s k * m k t) :
    ∀ s, ∑ t, π t * m s t = ∑ k, P s k * ∑ t, π t * m k t := by
  intro s
  have hk := kac P π hπ hπ1 m hmt hm
  set h : ι → ℝ := fun t => 1 + ∑ k, P s k * m k t with hh
  have h1 : ∑ t, π t * m s t = (∑ t, π t * h t) - π s * h s := by
    have : ∀ t, π t * m s t = π t * h t - if t = s then π s * h s else 0 := by
      intro t
      by_cases ht : t = s
      · subst ht; simp [hmt]
      · simp [ht, hh, hm s t (Ne.symm ht)]
    rw [Finset.sum_congr rfl (fun s _ => this s)]
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have h2 : ∑ t, π t * h t = 1 + ∑ k, P s k * ∑ t, π t * m k t := by
    have : ∀ t, π t * h t = π t + ∑ k, P s k * (π t * m k t) := by
      intro t
      simp only [hh, mul_add, mul_one, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    simp only [this, Finset.sum_add_distrib, hπ1]
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
  have h3 : π s * h s = 1 := hk s
  linarith

theorem exists_const (P : Matrix ι ι ℝ) (hP0 : ∀ s k, 0 ≤ P s k)
    (hP1 : ∀ s, ∑ k, P s k = 1) (π : ι → ℝ) (hπ : ∀ k, ∑ s, π s * P s k = π k)
    (hπ1 : ∑ s, π s = 1)
    (m : ι → ι → ℝ) (hmt : ∀ t, m t t = 0)
    (hm : ∀ s t, s ≠ t → m s t = 1 + ∑ k, P s k * m k t) :
    ∃ K : ℝ, ∀ s, ∑ t, π t * m s t = K := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨0, fun s => (hι.false s).elim⟩
  set f : ι → ℝ := fun s => ∑ t, π t * m s t with hf
  have hharm : ∀ s, f s = ∑ k, P s k * f k := harmonic P π hπ hπ1 m hmt hm
  obtain ⟨s0, -, hs0⟩ := Finset.exists_max_image (Finset.univ : Finset ι) f
    ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  set M := f s0 with hM
  have hle : ∀ k, f k ≤ M := fun k => hs0 k (Finset.mem_univ _)
  -- closedness of the maximum set
  have hclosed : ∀ s, f s = M → ∀ k, 0 < P s k → f k = M := by
    intro s hs k hk
    have hsum : ∑ j, P s j * (M - f j) = 0 := by
      have : ∀ j, P s j * (M - f j) = P s j * M - P s j * f j := fun j => by ring
      simp only [this, Finset.sum_sub_distrib, ← Finset.sum_mul, hP1, ← hharm s, hs]
      ring
    have hnn : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ P s j * (M - f j) :=
      fun j _ => mul_nonneg (hP0 s j) (sub_nonneg.mpr (hle j))
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum k (Finset.mem_univ _)
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hk.ne'
    · linarith
  refine ⟨M, fun s => ?_⟩
  by_contra hne
  have hne' : f s ≠ M := hne
  set S : Finset ι := Finset.univ.filter (fun x => f x = M) with hS
  have hSne : S.Nonempty := ⟨s0, by simp [hS, hM]⟩
  obtain ⟨u, hu, humin⟩ := Finset.exists_min_image S (fun x => m x s) hSne
  have hufm : f u = M := by simpa [hS] using hu
  have hus : u ≠ s := fun h => hne' (h ▸ hufm)
  have key : ∑ k, P u k * m u s ≤ ∑ k, P u k * m k s := by
    refine Finset.sum_le_sum fun k _ => ?_
    rcases (hP0 u k).eq_or_lt with h | h
    · rw [← h]; simp
    · have hkS : k ∈ S := by simp [hS, hclosed u hufm k h]
      exact mul_le_mul_of_nonneg_left (humin k hkS) (hP0 u k)
  rw [← Finset.sum_mul, hP1, one_mul] at key
  have := hm u s hus
  linarith

end Kemeny
