/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Trigonometric
public import Formalizations.Analysis.SpecialFunctions.Dilogarithm.Basic

/-!
# The Eneström–Kakeya theorem

A polynomial `∑_{k=0}^n a_k z^k` with real coefficients `a_0 ≥ a_1 ≥ ⋯ ≥ a_n > 0` has no zero in the
open unit disk. On the unit circle a zero `z` satisfies `z^{n+1} = 1`, and `z^{k+1} = 1` at every
strict descent `a_{k+1} < a_k`; with strictly decreasing coefficients there is no zero in the closed
disk. The proof multiplies by `1 - z`, telescopes, and applies the triangle inequality.

## Main results

* `Dilog.enestrom_kakeya`: no zero in `‖z‖ < 1`.
* `Dilog.enestrom_kakeya_boundary`: the zeros on `‖z‖ = 1` are roots of unity of the stated orders.
* `Dilog.enestrom_kakeya_strict`: strictly decreasing coefficients give no zero in `‖z‖ ≤ 1`.
* `Dilog.monotoneState_never_orthogonal`: `∑ p_k e^{-ikt} ≠ 0` for every real `t` when
  `p_0 > p_1 > ⋯ > p_n > 0`.
* `Dilog.enestrom_kakeya_boundary_series`, `Dilog.strictAnti_series_ne_zero`: the same on the circle for
  summable non-increasing series (no truncation): zeros sit at roots of unity pinned by the descents, and
  strictly decreasing positive populations never orthogonalize. The proof takes real parts of the
  telescoped series instead of the equality case of the triangle inequality.

## References

* A. Hurwitz, *Über einen Satz des Herrn Kakeya*, Tôhoku Math. J. 4 (1913) 89–93, §2: the zeros on the
  unit circle under non-increasing coefficients (roots of unity; coefficients in groups of equal
  consecutive values), with the converse. `enestrom_kakeya_boundary` is his argument.
* Q. I. Rahman, G. Schmeisser, *Analytic Theory of Polynomials*, Oxford University Press, 2002.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Dilog

/-- The telescoped identity `(1 - z)·∑ aₖzᵏ = a₀ − ∑(aₖ−aₖ₊₁)zᵏ⁺¹ − aₙzⁿ⁺¹`, with no sign
or monotonicity hypothesis on the coefficients. The engine behind both the interior
localization and the boundary refinement. -/
private lemma enestrom_telescope {n : ℕ} (a : ℕ → ℝ) (z : ℂ) :
    (1 - z) * (∑ k ∈ range (n + 1), (a k : ℂ) * z ^ k)
      = (a 0 : ℂ) - (∑ k ∈ range n, ((a k - a (k + 1) : ℝ) : ℂ) * z ^ (k + 1))
        - (a n : ℂ) * z ^ (n + 1) := by
  induction n with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, Finset.sum_range_zero, pow_zero, pow_one, mul_one]
    ring
  | succ m ih =>
    rw [Finset.sum_range_succ (fun k => (a k : ℂ) * z ^ k) (m + 1), mul_add, ih,
        Finset.sum_range_succ (fun k => ((a k - a (k + 1) : ℝ) : ℂ) * z ^ (k + 1)) m]
    push_cast
    ring

/-- The Eneström–Kakeya theorem (reciprocal form): a polynomial with positive,
non-increasing real coefficients has no zero strictly inside the unit disc. -/
theorem enestrom_kakeya {n : ℕ} (a : ℕ → ℝ)
    (hpos : ∀ k ≤ n, 0 < a k) (hmono : ∀ k, k < n → a (k + 1) ≤ a k)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ∑ k ∈ range (n + 1), (a k : ℂ) * z ^ k ≠ 0 := by
  intro hS
  set S : ℂ := ∑ k ∈ range (n + 1), (a k : ℂ) * z ^ k with hSdef
  -- The telescoped identity `(1 - z) * S = a₀ - ∑ (aₖ - aₖ₊₁) zᵏ⁺¹ - aₙ zⁿ⁺¹`.
  have key : (1 - z) * S
      = (a 0 : ℂ) - (∑ k ∈ range n, ((a k - a (k + 1) : ℝ) : ℂ) * z ^ (k + 1))
        - (a n : ℂ) * z ^ (n + 1) := by
    rw [hSdef]; exact enestrom_telescope (n := n) a z
  -- `S = 0`, so `a₀ = ∑ (aₖ - aₖ₊₁) zᵏ⁺¹ + aₙ zⁿ⁺¹`.
  rw [hS, mul_zero] at key
  have ha0 : (a 0 : ℂ)
      = (∑ k ∈ range n, ((a k - a (k + 1) : ℝ) : ℂ) * z ^ (k + 1)) + (a n : ℂ) * z ^ (n + 1) := by
    linear_combination -key
  -- Take norms and bound `‖z‖ᵏ⁺¹ ≤ ‖z‖`.
  have hz0 : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
  have hzle : ‖z‖ ≤ 1 := hz.le
  have hpos0 : 0 < a 0 := hpos 0 (Nat.zero_le n)
  -- Norm of the left side.
  have hlhs : ‖(a 0 : ℂ)‖ = a 0 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos0]
  -- Norm bound of the right side.
  have hrhs : ‖(∑ k ∈ range n, ((a k - a (k + 1) : ℝ) : ℂ) * z ^ (k + 1))
        + (a n : ℂ) * z ^ (n + 1)‖
      ≤ ‖z‖ * a 0 := by
    refine le_trans (norm_add_le _ _) ?_
    -- bound each piece
    have hdec : ∀ k ∈ range n, 0 ≤ a k - a (k + 1) := by
      intro k hk; exact sub_nonneg.mpr (hmono k (Finset.mem_range.mp hk))
    have hsum : ‖∑ k ∈ range n, ((a k - a (k + 1) : ℝ) : ℂ) * z ^ (k + 1)‖
        ≤ ∑ k ∈ range n, (a k - a (k + 1)) * ‖z‖ := by
      refine le_trans (norm_sum_le _ _) ?_
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hdec k hk),
        norm_pow]
      have : ‖z‖ ^ (k + 1) ≤ ‖z‖ := by
        calc ‖z‖ ^ (k + 1) ≤ ‖z‖ ^ 1 := by
              apply pow_le_pow_of_le_one hz0 hzle (Nat.succ_le_succ (Nat.zero_le k))
          _ = ‖z‖ := pow_one _
      exact mul_le_mul_of_nonneg_left this (hdec k hk)
    have hlast : ‖(a n : ℂ) * z ^ (n + 1)‖ ≤ a n * ‖z‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hpos n le_rfl), norm_pow]
      have : ‖z‖ ^ (n + 1) ≤ ‖z‖ := by
        calc ‖z‖ ^ (n + 1) ≤ ‖z‖ ^ 1 :=
              pow_le_pow_of_le_one hz0 hzle (Nat.succ_le_succ (Nat.zero_le n))
          _ = ‖z‖ := pow_one _
      exact mul_le_mul_of_nonneg_left this (le_of_lt (hpos n le_rfl))
    have htel : (∑ k ∈ range n, (a k - a (k + 1))) + a n = a 0 := by
      rw [Finset.sum_range_sub' (fun k => a k)]
      ring
    calc ‖∑ k ∈ range n, ((a k - a (k + 1) : ℝ) : ℂ) * z ^ (k + 1)‖
            + ‖(a n : ℂ) * z ^ (n + 1)‖
        ≤ (∑ k ∈ range n, (a k - a (k + 1)) * ‖z‖) + a n * ‖z‖ := by
          exact add_le_add hsum hlast
      _ = ((∑ k ∈ range n, (a k - a (k + 1))) + a n) * ‖z‖ := by
          rw [add_mul, Finset.sum_mul]
      _ = a 0 * ‖z‖ := by rw [htel]
      _ = ‖z‖ * a 0 := by ring
  -- Combine: `a₀ = ‖a₀‖ ≤ ‖z‖ * a₀ < a₀`, contradiction.
  have : a 0 ≤ ‖z‖ * a 0 := by
    calc a 0 = ‖(a 0 : ℂ)‖ := hlhs.symm
      _ = ‖(∑ k ∈ range n, ((a k - a (k + 1) : ℝ) : ℂ) * z ^ (k + 1))
            + (a n : ℂ) * z ^ (n + 1)‖ := by rw [ha0]
      _ ≤ ‖z‖ * a 0 := hrhs
  have hcontra : ‖z‖ * a 0 < a 0 := by
    calc ‖z‖ * a 0 < 1 * a 0 := by
          apply mul_lt_mul_of_pos_right hz hpos0
      _ = a 0 := one_mul _
  exact absurd (lt_of_le_of_lt this hcontra) (lt_irrefl _)

/-! ## Boundary refinement and the monotone clock

The base theorem localises zeros to `‖z‖ ≥ 1`. On the circle `‖z‖ = 1` the same
telescoped identity, read through **real parts** instead of norms, forces a rigid
structure: a boundary zero can only sit at a root of unity. Strict decrease at every step
then rules the circle out entirely. -/

/-- On the unit circle, the real part is `≤ 1`, with equality only at the point `1`. -/
private lemma unit_re_le_one {w : ℂ} (hw : ‖w‖ = 1) : w.re ≤ 1 ∧ (w.re = 1 → w = 1) := by
  have hns : w.re * w.re + w.im * w.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hw]; norm_num
  refine ⟨?_, ?_⟩
  · nlinarith [mul_self_nonneg w.im, mul_self_nonneg (w.re - 1)]
  · intro h1
    have him : w.im = 0 := by
      have : w.im * w.im = 0 := by nlinarith
      exact mul_self_eq_zero.mp this
    exact Complex.ext (by simp [h1]) (by simp [him])

/-- **Boundary Eneström–Kakeya.** If the polynomial vanishes at a point of the unit
circle, that point is a root of unity: `zⁿ⁺¹ = 1`, and `zᵏ⁺¹ = 1` at every step where the
coefficients strictly decrease. -/
theorem enestrom_kakeya_boundary {n : ℕ} (a : ℕ → ℝ)
    (hpos : ∀ k ≤ n, 0 < a k) (hmono : ∀ k, k < n → a (k + 1) ≤ a k)
    {z : ℂ} (hz : ‖z‖ = 1)
    (hS : ∑ k ∈ range (n + 1), (a k : ℂ) * z ^ k = 0) :
    z ^ (n + 1) = 1 ∧ ∀ k, k < n → a (k + 1) < a k → z ^ (k + 1) = 1 := by
  have key := enestrom_telescope (n := n) a z
  rw [hS, mul_zero] at key
  have ha0 : (a 0 : ℂ)
      = (∑ k ∈ range n, ((a k - a (k + 1) : ℝ) : ℂ) * z ^ (k + 1)) + (a n : ℂ) * z ^ (n + 1) := by
    linear_combination -key
  -- combine the `n` differences and the final coefficient into one positive weight `c`
  set c : ℕ → ℝ := fun k => if k = n then a n else a k - a (k + 1) with hc
  set r : ℕ → ℝ := fun k => (z ^ (k + 1)).re with hr
  have hpow : ∀ j, ‖z ^ j‖ = 1 := fun j => by rw [norm_pow, hz, one_pow]
  have hrle : ∀ k, r k ≤ 1 := fun k => (unit_re_le_one (hpow (k + 1))).1
  have hcnn : ∀ k ∈ range (n + 1), 0 ≤ c k := by
    intro k hk
    by_cases h : k = n
    · simp [hc, h]; exact (hpos n le_rfl).le
    · have hkn : k < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) h
      simp only [hc, h, ite_false]; exact sub_nonneg.mpr (hmono k hkn)
  -- the real part of `ha0` reads `a₀ = ∑ c k · r k`
  have hsum_cr : a 0 = ∑ k ∈ range (n + 1), c k * r k := by
    have hre := congrArg Complex.re ha0
    rw [Finset.sum_range_succ]
    simp only [Complex.add_re, Complex.re_sum, Complex.re_ofReal_mul, Complex.ofReal_re] at hre
    rw [hre]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≠ n := Nat.ne_of_lt (Finset.mem_range.mp hk)
      simp only [hc, hr, hkn, ite_false]
    · simp only [hc, hr, ite_true]
  -- the weights telescope to `a₀`
  have hsum_c : ∑ k ∈ range (n + 1), c k = a 0 := by
    rw [Finset.sum_range_succ]
    have : ∑ k ∈ range n, c k = ∑ k ∈ range n, (a k - a (k + 1)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≠ n := Nat.ne_of_lt (Finset.mem_range.mp hk)
      simp only [hc, hkn, ite_false]
    rw [this, Finset.sum_range_sub' (fun k => a k)]
    simp only [hc, ite_true]; ring
  -- each term is `≤` its weight, and the two sums agree, so all are equalities
  have hterm_le : ∀ k ∈ range (n + 1), c k * r k ≤ c k := fun k hk =>
    mul_le_of_le_one_right (hcnn k hk) (hrle k)
  have hsums : ∑ k ∈ range (n + 1), c k * r k = ∑ k ∈ range (n + 1), c k := by
    rw [← hsum_cr, hsum_c]
  have heq : ∀ k ∈ range (n + 1), c k * r k = c k :=
    (Finset.sum_eq_sum_iff_of_le hterm_le).mp hsums
  -- positive weight forces `r k = 1`, hence `z^{k+1} = 1`
  have hroot : ∀ k ∈ range (n + 1), 0 < c k → z ^ (k + 1) = 1 := by
    intro k hk hck
    have hrk : r k = 1 := by
      have := heq k hk
      have : c k * r k = c k * 1 := by rw [this, mul_one]
      exact mul_left_cancel₀ (ne_of_gt hck) this
    exact (unit_re_le_one (hpow (k + 1))).2 hrk
  refine ⟨?_, ?_⟩
  · have hcn : 0 < c n := by simp only [hc, ite_true]; exact hpos n le_rfl
    exact hroot n (Finset.mem_range.mpr (Nat.lt_succ_self n)) hcn
  · intro k hkn hstrict
    have hck : 0 < c k := by
      have hkn' : k ≠ n := Nat.ne_of_lt hkn
      simp only [hc, hkn', ite_false]; linarith
    exact hroot k (Finset.mem_range.mpr (Nat.lt_succ_of_lt hkn)) hck

/-- **Strict Eneström–Kakeya.** If the coefficients are *strictly* decreasing at every
step, the polynomial has no zero on the closed unit disc `‖z‖ ≤ 1`. -/
theorem enestrom_kakeya_strict {n : ℕ} (a : ℕ → ℝ)
    (hpos : ∀ k ≤ n, 0 < a k) (hmono : ∀ k, k < n → a (k + 1) < a k)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ∑ k ∈ range (n + 1), (a k : ℂ) * z ^ k ≠ 0 := by
  rcases lt_or_eq_of_le hz with hlt | heq
  · exact enestrom_kakeya a hpos (fun k hk => (hmono k hk).le) hlt
  · intro hS
    have hz1 : ‖z‖ = 1 := heq
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      simp only [zero_add, Finset.sum_range_one, pow_zero, mul_one] at hS
      exact (hpos 0 le_rfl).ne' (by exact_mod_cast hS)
    · obtain ⟨_, hstep⟩ :=
        enestrom_kakeya_boundary a hpos (fun k hk => (hmono k hk).le) hz1 hS
      have hz_eq : z ^ (0 + 1) = 1 := hstep 0 hnpos (hmono 0 hnpos)
      have hz1' : z = 1 := by simpa using hz_eq
      rw [hz1'] at hS
      simp only [one_pow, mul_one] at hS
      have hsumzero : (∑ k ∈ range (n + 1), a k : ℝ) = 0 := by
        have := congrArg Complex.re hS
        simpa [Complex.re_sum, Complex.ofReal_re] using this
      have hpos_sum : 0 < ∑ k ∈ range (n + 1), a k :=
        Finset.sum_pos (fun k hk => hpos k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
          ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
      linarith

/-- **The monotone clock that never ticks.** A quantum state with strictly decreasing
populations `p₀ > p₁ > ⋯ > pₙ > 0` on the equally spaced energy levels `0, 1, …, n` never
reaches an orthogonal state: its autocorrelation `∑ pₖ e^{-i k t}` is nonzero for every
time `t`. The finite, coefficient-side companion of `zetaState_never_orthogonal`. -/
theorem monotoneState_never_orthogonal {n : ℕ} (p : ℕ → ℝ)
    (hpos : ∀ k ≤ n, 0 < p k) (hmono : ∀ k, k < n → p (k + 1) < p k) (t : ℝ) :
    ∑ k ∈ range (n + 1), (p k : ℂ) * Complex.exp (-(k : ℂ) * (t : ℂ) * Complex.I) ≠ 0 := by
  have hz : ‖Complex.exp (-(t : ℂ) * Complex.I)‖ ≤ 1 := by
    rw [Complex.norm_exp]
    simp [Complex.ofReal_im]
  have key := enestrom_kakeya_strict p hpos hmono (z := Complex.exp (-(t : ℂ) * Complex.I)) hz
  intro hsum
  apply key
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/-- `Re w = 1` and `‖w‖ = 1` force `w = 1`. -/
theorem eq_one_of_re_eq_one {w : ℂ} (hn : ‖w‖ = 1) (hr : w.re = 1) : w = 1 := by
  have h : w.re * w.re + w.im * w.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hn]; norm_num
  rw [hr] at h
  have him : w.im = 0 := by nlinarith
  exact Complex.ext (by simpa using hr) (by simpa using him)

/-- **Eneström–Kakeya on the circle, for series.** Let `p` be summable and non-increasing. If
`∑ pₖ zᵏ = 0` at a point `‖z‖ = 1`, then `z^{k+1} = 1` at every descent `p_{k+1} < p_k`: the zeros on the
circle are roots of unity, pinned by where the populations drop (Remark 1 of the paper, for series). -/
theorem enestrom_kakeya_boundary_series (p : ℕ → ℝ) (hmono : Antitone p)
    (hsum : Summable p) {z : ℂ} (hz : ‖z‖ = 1) (hS : HasSum (fun k => (p k : ℂ) * z ^ k) 0) :
    ∀ k, p (k + 1) < p k → z ^ (k + 1) = 1 := by
  set d : ℕ → ℝ := fun k => p k - p (k + 1) with hd
  have hd0 : ∀ k, 0 ≤ d k := fun k => sub_nonneg.mpr (hmono (Nat.le_succ k))
  -- the decrements telescope to `p 0` (summable `p` tends to `0`)
  have hP := hsum.hasSum
  have hP1 : HasSum (fun k => p (k + 1)) (∑' k, p k - p 0) := by
    have := (hasSum_nat_add_iff' 1).mpr hP
    simpa [Finset.sum_range_one] using this
  have hdsum : HasSum d (p 0) := by
    have := hP.sub hP1
    simpa [hd] using this
  -- `∑ dₖ z^{k+1} = p 0` when the series vanishes: `z S − (S − p 0)` with `S = 0`
  have h1 : HasSum (fun k => (p k : ℂ) * z ^ k * z) 0 := by simpa using hS.mul_right z
  have h2 : HasSum (fun k => (p (k + 1) : ℂ) * z ^ (k + 1)) (0 - (p 0 : ℂ)) := by
    have := (hasSum_nat_add_iff' 1).mpr hS
    simpa [Finset.sum_range_one] using this
  have hdz : HasSum (fun k => ((d k : ℝ) : ℂ) * z ^ (k + 1)) (p 0 : ℂ) := by
    have := h1.sub h2
    convert this using 1
    · funext k; simp only [hd]; push_cast; ring
    · ring
  -- real parts: `∑ dₖ Re z^{k+1} = p 0 = ∑ dₖ`, so `∑ dₖ (1 − Re z^{k+1}) = 0` with nonnegative terms
  have hre : HasSum (fun k => d k * (z ^ (k + 1)).re) (p 0) := by
    have := Complex.reCLM.hasSum hdz
    simpa [Complex.re_ofReal_mul] using this
  have hgap : HasSum (fun k => d k * (1 - (z ^ (k + 1)).re)) 0 := by
    have := hdsum.sub hre
    simpa [mul_sub] using this
  have hnorm : ∀ k : ℕ, ‖z ^ (k + 1)‖ = 1 := fun k => by rw [norm_pow, hz, one_pow]
  have hle : ∀ k : ℕ, (z ^ (k + 1)).re ≤ 1 := fun k => (Complex.re_le_norm _).trans (hnorm k).le
  have hterm : ∀ k, 0 ≤ d k * (1 - (z ^ (k + 1)).re) := fun k =>
    mul_nonneg (hd0 k) (sub_nonneg.mpr (hle k))
  have hzero := (hasSum_zero_iff_of_nonneg hterm).mp hgap
  intro k hk
  have hk' : 0 < d k := sub_pos.mpr hk
  have h0 : d k * (1 - (z ^ (k + 1)).re) = 0 := congrFun hzero k
  have hre1 : (z ^ (k + 1)).re = 1 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hk'.ne'
    · linarith
  exact eq_one_of_re_eq_one (hnorm k) hre1

/-- **Strictly decreasing populations never orthogonalize** (series form): for `p > 0` summable and strictly
decreasing, `∑ pₖ zᵏ ≠ 0` on the whole unit circle. With `p_n = 6/(π² n²)` this is Theorem 4 again, read
from the coefficients as Remark 1 says. -/
theorem strictAnti_series_ne_zero (p : ℕ → ℝ) (hpos : ∀ k, 0 < p k) (hanti : StrictAnti p)
    (hsum : Summable p) {z : ℂ} (hz : ‖z‖ = 1) : ¬ HasSum (fun k => (p k : ℂ) * z ^ k) 0 := by
  intro hS
  have h1 := enestrom_kakeya_boundary_series p hanti.antitone hsum hz hS 0
    (hanti (Nat.lt_succ_self 0))
  rw [zero_add, pow_one] at h1
  subst h1
  have hR : HasSum (fun k => ((p k : ℝ) : ℂ)) ((∑' k, p k : ℝ) : ℂ) := Complex.ofRealCLM.hasSum hsum.hasSum
  have hpos' : 0 < ∑' k, p k := hsum.tsum_pos (fun k => (hpos k).le) 0 (hpos 0)
  have hS' : HasSum (fun k => ((p k : ℝ) : ℂ)) 0 := by simpa using hS
  have h0 : ((∑' k, p k : ℝ) : ℂ) = 0 := hR.unique hS'
  exact hpos'.ne' (by exact_mod_cast h0)

end Dilog
