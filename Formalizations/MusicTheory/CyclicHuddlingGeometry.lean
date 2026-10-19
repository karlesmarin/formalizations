/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.MusicTheory.CyclicHuddling
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic

/-!
# The Huddling inequality for every cyclic group

For every `N ≠ 0` and `B ⊆ ZMod N`, `‖Ahat B 1‖ ≤ ‖Ahat (arc #B) 1‖`, where `arc m = {0, …, m - 1}`,
with equality exactly for the translates of `arc #B`. The proof cuts the circle at the boundary
of an arc selected by the phase of `Ahat B 1`, and uses the monotonicity of the cosine. Both
statements transfer to every unit frequency.

## Main results

* `geometric_selector`.
* `norm_Ahat_one_le_arc`, `norm_Ahat_unit_le_arc`.
* `norm_Ahat_one_eq_arc_iff`, `norm_Ahat_unit_eq_arc_iff`, `maximizer_unit_iff`.

## References

* E. Amiot, *Discrete Fourier transform and Bach's good temperament*, Music Theory Online 15
  (2009), Lemma 2.
* C. Marín, *Huddling, diatonic and pentatonic scales in Z12: Fourier maxima and convex-energy
  minima formalized in Lean 4*, Zenodo (2026), doi:10.5281/zenodo.23121103.
-/

@[expose] public section

namespace MusicTheory

open Finset ZMod Complex

namespace CyclicHuddling

lemma threshold_eq_on_diff {α : Type*} [DecidableEq α]
    (score : α → ℝ) (A B : Finset α) (c : ℝ)
    (hcard : B.card = A.card)
    (hin : ∀ x ∈ A, c ≤ score x)
    (hout : ∀ x ∉ A, score x ≤ c)
    (hsum : (∑ x ∈ B, score x) = ∑ x ∈ A, score x) :
    (∀ x ∈ A \ B, score x = c) ∧ (∀ x ∈ B \ A, score x = c) := by
  have hdeq : (∑ x ∈ B \ A, score x) = ∑ x ∈ A \ B, score x :=
    Finset.sum_sdiff_eq_sum_sdiff_iff.mpr hsum
  have hlow := sum_le_card_nsmul (B \ A) score c
    (fun x hx => hout x (mem_sdiff.mp hx).2)
  have hhigh := card_nsmul_le_sum (A \ B) score c
    (fun x hx => hin x (mem_sdiff.mp hx).1)
  rw [card_sdiff_comm hcard] at hlow
  have hhighEq : (∑ x ∈ A \ B, c) = ∑ x ∈ A \ B, score x := by
    simpa only [sum_const] using le_antisymm hhigh (hdeq ▸ hlow)
  have hlowEq : (∑ x ∈ B \ A, score x) = ∑ x ∈ B \ A, c := by
    rw [hdeq, ← hhighEq]
    simp only [sum_const, card_sdiff_comm hcard]
  refine ⟨?_, ?_⟩
  · have he := (Finset.sum_eq_sum_iff_of_le
      (fun x hx => hin x (mem_sdiff.mp hx).1)).mp hhighEq
    exact fun x hx => (he x hx).symm
  · exact (Finset.sum_eq_sum_iff_of_le
      (fun x hx => hout x (mem_sdiff.mp hx).2)).mp hlowEq

lemma eq_or_swap_of_diff_subset {α : Type*} [DecidableEq α]
    (A B : Finset α) (a b : α) (hcard : B.card = A.card)
    (ha : A \ B ⊆ {a}) (hb : B \ A ⊆ {b}) :
    B = A ∨ B = insert b (A.erase a) := by
  by_cases he : B = A
  · exact Or.inl he
  right
  have hadiff : (A \ B).Nonempty := by
    rw [sdiff_nonempty]
    intro hsub
    exact he (eq_of_subset_of_card_le hsub (by rw [hcard])).symm
  have hbdiff : (B \ A).Nonempty := by
    rw [sdiff_nonempty]
    intro hsub
    exact he (eq_of_subset_of_card_le hsub (by rw [hcard]))
  obtain ⟨x, hx⟩ := hadiff
  have hxa : x = a := mem_singleton.mp (ha hx)
  subst x
  obtain ⟨y, hy⟩ := hbdiff
  have hyb : y = b := mem_singleton.mp (hb hy)
  subst y
  ext z
  simp only [mem_insert, mem_erase]
  constructor
  · intro hz
    by_cases hzA : z ∈ A
    · exact Or.inr ⟨fun hza => (mem_sdiff.mp hx).2 (hza ▸ hz), hzA⟩
    · exact Or.inl (mem_singleton.mp (hb (mem_sdiff.mpr ⟨hz, hzA⟩)))
  · rintro (rfl | ⟨hne, hzA⟩)
    · exact (mem_sdiff.mp hy).1
    · by_contra hz
      exact hne (mem_singleton.mp (ha (mem_sdiff.mpr ⟨hzA, hz⟩)))

lemma cos_ge_of_between {x t : ℝ} (ht : t ≤ Real.pi)
    (hx₁ : -t ≤ x) (hx₂ : x ≤ t) :
    Real.cos t ≤ Real.cos x := by
  rw [← Real.cos_abs x]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x) ht
    (abs_le.mpr ⟨hx₁, hx₂⟩)

lemma cos_gt_of_between {x t : ℝ} (ht : t ≤ Real.pi)
    (hx₁ : -t < x) (hx₂ : x < t) :
    Real.cos t < Real.cos x := by
  rw [← Real.cos_abs x]
  exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg x) ht
    (abs_lt.mpr ⟨hx₁, hx₂⟩)

lemma cos_le_of_between {x t : ℝ} (ht₀ : 0 ≤ t)
    (hx₁ : t ≤ x) (hx₂ : x ≤ 2 * Real.pi - t) :
    Real.cos x ≤ Real.cos t := by
  by_cases hx : x ≤ Real.pi
  · exact Real.cos_le_cos_of_nonneg_of_le_pi ht₀ hx hx₁
  · rw [← Real.cos_two_pi_sub x]
    apply Real.cos_le_cos_of_nonneg_of_le_pi ht₀
    · linarith
    · linarith

lemma cos_lt_of_between {x t : ℝ} (ht₀ : 0 ≤ t)
    (hx₁ : t < x) (hx₂ : x < 2 * Real.pi - t) :
    Real.cos x < Real.cos t := by
  by_cases hx : x ≤ Real.pi
  · exact Real.cos_lt_cos_of_nonneg_of_le_pi ht₀ hx hx₁
  · rw [← Real.cos_two_pi_sub x]
    apply Real.cos_lt_cos_of_nonneg_of_le_pi ht₀
    · linarith
    · linarith

/-- A rotated grid always has a cut with residual angle in a prescribed cell. -/
lemma exists_grid_cut_strict (θ t h : ℝ) (hh : 0 < h) :
    ∃ s : ℤ, t - h < θ - h * s ∧ θ - h * s ≤ t := by
  refine ⟨⌈(θ - t) / h⌉, ?_, ?_⟩
  · have hs := Int.ceil_lt_add_one ((θ - t) / h)
    have hp := mul_lt_mul_of_pos_left hs hh
    have he : h * ((θ - t) / h) = θ - t := by field_simp
    rw [mul_add, he, mul_one] at hp
    linarith
  · have hs := Int.le_ceil ((θ - t) / h)
    have hp := mul_le_mul_of_nonneg_left hs hh.le
    have he : h * ((θ - t) / h) = θ - t := by field_simp
    rw [he] at hp
    linarith

lemma exists_grid_cut (θ t h : ℝ) (hh : 0 < h) :
    ∃ s : ℤ, t - h ≤ θ - h * s ∧ θ - h * s ≤ t := by
  obtain ⟨s, hs₁, hs₂⟩ := exists_grid_cut_strict θ t h hh
  exact ⟨s, hs₁.le, hs₂⟩

lemma grid_projection_inside (N m j : ℕ) (hm : m ≤ N) (hj : j < m)
    (h β : ℝ) (hh : 0 < h) (hperiod : h * N = 2 * Real.pi)
    (hβ₁ : h * m / 2 - h ≤ β) (hβ₂ : β ≤ h * m / 2) :
    Real.cos (h * m / 2) ≤ Real.cos (β - h * j) := by
  have hmR : (m : ℝ) ≤ N := by exact_mod_cast hm
  have hjR : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
  have hmH := mul_le_mul_of_nonneg_left hmR hh.le
  have hjH := mul_le_mul_of_nonneg_left hjR hh.le
  have hj₀ : 0 ≤ h * j := by positivity
  apply cos_ge_of_between
  · nlinarith
  · nlinarith
  · nlinarith

lemma grid_projection_outside (N m j : ℕ) (hj₁ : m ≤ j) (hj₂ : j < N)
    (h β : ℝ) (hh : 0 < h) (hperiod : h * N = 2 * Real.pi)
    (hβ₁ : h * m / 2 - h ≤ β) (hβ₂ : β ≤ h * m / 2) :
    Real.cos (β - h * j) ≤ Real.cos (h * m / 2) := by
  have hj₁R : (m : ℝ) ≤ j := by exact_mod_cast hj₁
  have hj₂R : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj₂
  have hlow := mul_le_mul_of_nonneg_left hj₁R hh.le
  have hhigh := mul_le_mul_of_nonneg_left hj₂R hh.le
  rw [← Real.cos_neg (β - h * j)]
  apply cos_le_of_between
  · positivity
  · nlinarith
  · nlinarith

lemma grid_projection_inside_strict (N m j : ℕ) (hm : m ≤ N)
    (hj₀ : 0 < j) (hj : j < m)
    (h β : ℝ) (hh : 0 < h) (hperiod : h * N = 2 * Real.pi)
    (hβ₁ : h * m / 2 - h < β) (hβ₂ : β ≤ h * m / 2) :
    Real.cos (h * m / 2) < Real.cos (β - h * j) := by
  have hmR : (m : ℝ) ≤ N := by exact_mod_cast hm
  have hjR : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
  have hj₀R : (0 : ℝ) < j := by exact_mod_cast hj₀
  have hmH := mul_le_mul_of_nonneg_left hmR hh.le
  have hjH := mul_le_mul_of_nonneg_left hjR hh.le
  have hjH₀ : 0 < h * j := mul_pos hh hj₀R
  apply cos_gt_of_between
  · nlinarith
  · nlinarith
  · nlinarith

lemma grid_projection_outside_strict (N m j : ℕ) (hj₁ : m < j) (hj₂ : j < N)
    (h β : ℝ) (hh : 0 < h) (hperiod : h * N = 2 * Real.pi)
    (hβ₁ : h * m / 2 - h < β) (hβ₂ : β ≤ h * m / 2) :
    Real.cos (β - h * j) < Real.cos (h * m / 2) := by
  have hj₁R : (m : ℝ) < j := by exact_mod_cast hj₁
  have hj₂R : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj₂
  have hlow := mul_lt_mul_of_pos_left hj₁R hh
  have hhigh := mul_le_mul_of_nonneg_left hj₂R hh.le
  rw [← Real.cos_neg (β - h * j)]
  apply cos_lt_of_between
  · positivity
  · nlinarith
  · nlinarith

variable {N : ℕ} [NeZero N]

lemma re_exp_mul_character (θ : ℝ) (j : ℤ) :
    (Complex.exp ((θ : ℂ) * I) * stdAddChar (-(j : ZMod N))).re =
      Real.cos (θ - (2 * Real.pi / N) * j) := by
  rw [← Int.cast_neg, ZMod.stdAddChar_coe, ← Complex.exp_add]
  have he : (θ : ℂ) * I + 2 * ↑Real.pi * I * ↑(-j) / ↑N =
      (↑(θ - (2 * Real.pi / N) * j) : ℂ) * I := by
    push_cast
    ring
  rw [he]
  simp [Complex.exp_re]

omit [NeZero N] in
lemma mem_tpose_arc_iff (s a : ZMod N) (m : ℕ) :
    a ∈ tpose s (arc (N := N) m) ↔
      ∃ j : ℕ, j < m ∧ (j : ZMod N) + s = a := by
  simp [tpose, arc]

omit [NeZero N] in
lemma arc_swap_endpoint (s : ZMod N) (m : ℕ) (hm₀ : 0 < m) (hmN : m < N) :
    insert ((m : ZMod N) + s) ((tpose s (arc (N := N) m)).erase s) =
      tpose (s + 1) (arc (N := N) m) := by
  ext a
  simp only [mem_insert, mem_erase, mem_tpose_arc_iff]
  constructor
  · rintro (rfl | ⟨hne, j, hj, rfl⟩)
    · refine ⟨m - 1, by omega, ?_⟩
      have hc : ((m - 1 : ℕ) : ZMod N) + 1 = m := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          congrArg (fun n : ℕ => (n : ZMod N)) (Nat.sub_add_cancel (by omega : 1 ≤ m))
      calc
        ((m - 1 : ℕ) : ZMod N) + (s + 1) =
            (((m - 1 : ℕ) : ZMod N) + 1) + s := by ring
        _ = (m : ZMod N) + s := by rw [hc]
    · have hj₀ : 0 < j := by
        by_contra hn
        have hz : j = 0 := by omega
        exact hne (by simp [hz])
      refine ⟨j - 1, by omega, ?_⟩
      have hc : ((j - 1 : ℕ) : ZMod N) + 1 = j := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          congrArg (fun n : ℕ => (n : ZMod N)) (Nat.sub_add_cancel (by omega : 1 ≤ j))
      calc
        ((j - 1 : ℕ) : ZMod N) + (s + 1) =
            (((j - 1 : ℕ) : ZMod N) + 1) + s := by ring
        _ = (j : ZMod N) + s := by rw [hc]
  · rintro ⟨j, hj, rfl⟩
    have hshift : (j : ZMod N) + (s + 1) = ((j + 1 : ℕ) : ZMod N) + s := by
      push_cast
      ring
    by_cases he : j + 1 = m
    · exact Or.inl (by rw [hshift, he])
    · refine Or.inr ⟨?_, j + 1, by omega, hshift.symm⟩
      rw [hshift]
      intro hz
      have hz' : ((j + 1 : ℕ) : ZMod N) = 0 := by simpa using hz
      have hv := congrArg ZMod.val hz'
      rw [ZMod.val_natCast_of_lt (by omega : j + 1 < N)] at hv
      simp only [ZMod.val_zero] at hv
      omega

/-- In any direction the regular polygon has a consecutive block of `m`
    vertices separated from the others by a projection threshold. -/
theorem geometric_selector_with_boundary (m : ℕ) (hm : m ≤ N)
    (u : ℂ) (hu : ‖u‖ = 1) :
    ∃ s : ZMod N, ∃ c : ℝ,
      (∀ a ∈ tpose s (arc (N := N) m),
        c ≤ (u * stdAddChar (-(a * 1))).re) ∧
      (∀ a ∉ tpose s (arc (N := N) m),
        (u * stdAddChar (-(a * 1))).re ≤ c) ∧
      (∀ a ∈ tpose s (arc (N := N) m), a ≠ s →
        c < (u * stdAddChar (-(a * 1))).re) ∧
      (∀ a ∉ tpose s (arc (N := N) m), a ≠ (m : ZMod N) + s →
        (u * stdAddChar (-(a * 1))).re < c) := by
  let h : ℝ := 2 * Real.pi / N
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hh : 0 < h := by dsimp [h]; positivity
  have hperiod : h * N = 2 * Real.pi := by dsimp [h]; field_simp
  obtain ⟨s, hs₁, hs₂⟩ := exists_grid_cut_strict u.arg (h * m / 2) h hh
  have huform : u = Complex.exp ((u.arg : ℂ) * I) := by
    simpa [hu] using (Complex.norm_mul_exp_arg_mul_I u).symm
  have hscore (j : ℕ) :
      (u * stdAddChar (-(((j : ZMod N) + (s : ZMod N)) * 1))).re =
        Real.cos ((u.arg - h * s) - h * j) := by
    rw [mul_one]
    nth_rw 1 [huform]
    have hc : (j : ZMod N) + (s : ZMod N) = ((j : ℤ) + s : ℤ) := by
      push_cast
      rfl
    rw [hc, re_exp_mul_character]
    congr 1
    push_cast
    dsimp [h]
    ring
  refine ⟨(s : ZMod N), Real.cos (h * m / 2), ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨j, hj, rfl⟩ := (mem_tpose_arc_iff _ _ _).mp ha
    rw [hscore]
    exact grid_projection_inside N m j hm hj h _ hh hperiod hs₁.le hs₂
  · intro a ha
    let j := (a - (s : ZMod N)).val
    have hjN : j < N := ZMod.val_lt _
    have hja : (j : ZMod N) + (s : ZMod N) = a := by
      dsimp [j]
      rw [ZMod.natCast_zmod_val, sub_add_cancel]
    have hmj : m ≤ j := by
      by_contra hn
      exact ha ((mem_tpose_arc_iff _ _ _).mpr ⟨j, by omega, hja⟩)
    rw [← hja, hscore]
    exact grid_projection_outside N m j hmj hjN h _ hh hperiod hs₁.le hs₂
  · intro a ha hne
    obtain ⟨j, hj, rfl⟩ := (mem_tpose_arc_iff _ _ _).mp ha
    have hj₀ : 0 < j := by
      by_contra hn
      have hjz : j = 0 := by omega
      exact hne (by simp [hjz])
    rw [hscore]
    exact grid_projection_inside_strict N m j hm hj₀ hj h _ hh hperiod hs₁ hs₂
  · intro a ha hne
    let j := (a - (s : ZMod N)).val
    have hjN : j < N := ZMod.val_lt _
    have hja : (j : ZMod N) + (s : ZMod N) = a := by
      dsimp [j]
      rw [ZMod.natCast_zmod_val, sub_add_cancel]
    have hmj : m < j := by
      have hjm : ¬ j < m := fun hj =>
        ha ((mem_tpose_arc_iff _ _ _).mpr ⟨j, hj, hja⟩)
      have hne' : j ≠ m := by
        intro he
        exact hne (by simpa [he] using hja.symm)
      omega
    rw [← hja, hscore]
    exact grid_projection_outside_strict N m j hmj hjN h _ hh hperiod hs₁ hs₂

theorem geometric_selector (m : ℕ) (hm : m ≤ N) (u : ℂ) (hu : ‖u‖ = 1) :
    ∃ s : ZMod N, ∃ c : ℝ,
      (∀ a ∈ tpose s (arc (N := N) m),
        c ≤ (u * stdAddChar (-(a * 1))).re) ∧
      (∀ a ∉ tpose s (arc (N := N) m),
        (u * stdAddChar (-(a * 1))).re ≤ c) := by
  obtain ⟨s, c, hin, hout, _, _⟩ := geometric_selector_with_boundary m hm u hu
  exact ⟨s, c, hin, hout⟩

/-- The Huddling inequality for an arbitrary nonzero cyclic order. -/
theorem norm_Ahat_one_le_arc (B : Finset (ZMod N)) :
    ‖Ahat B 1‖ ≤ ‖Ahat (arc (N := N) B.card) 1‖ := by
  have hm : B.card ≤ N := by simpa using B.card_le_univ
  exact norm_Ahat_one_le_arc_of_geometric_selector B.card hm B rfl
    (geometric_selector B.card hm)

/-- Huddling at any primitive frequency, with the same frequency-one bound. -/
theorem norm_Ahat_unit_le_arc (B : Finset (ZMod N)) (k : ZMod N) (hk : IsUnit k) :
    ‖Ahat B k‖ ≤ ‖Ahat (arc (N := N) B.card) 1‖ := by
  have hm : B.card ≤ N := by simpa using B.card_le_univ
  exact norm_Ahat_unit_le_arc_of_geometric_selector B.card hm B rfl k hk
    (geometric_selector B.card hm)

lemma eq_tpose_arc_of_norm_eq (B : Finset (ZMod N))
    (hm₀ : 0 < B.card) (hmN : B.card < N)
    (heq : ‖Ahat B 1‖ = ‖Ahat (arc (N := N) B.card) 1‖) :
    ∃ s : ZMod N, B = tpose s (arc (N := N) B.card) := by
  obtain ⟨u, hu, hre⟩ := exists_phase_real_eq_norm (Ahat B 1)
  obtain ⟨s, c, hin, hout, hinStrict, houtStrict⟩ :=
    geometric_selector_with_boundary B.card hmN.le u hu
  let A := tpose s (arc (N := N) B.card)
  have hcard : B.card = A.card := by dsimp [A]; rw [card_tpose, card_arc _ hmN.le]
  have hp := re_amplitude_le_of_threshold u 1 A B c hcard hin hout
  have hupper : (u * Ahat A 1).re ≤ ‖Ahat (arc (N := N) B.card) 1‖ := by
    calc
      (u * Ahat A 1).re ≤ ‖u * Ahat A 1‖ := Complex.re_le_norm _
      _ = ‖Ahat (arc (N := N) B.card) 1‖ := by
        dsimp [A]
        rw [norm_mul, hu, one_mul, norm_tpose]
  have hpEq : (u * Ahat B 1).re = (u * Ahat A 1).re := by
    rw [hre] at hp ⊢
    linarith
  have hsum : (∑ a ∈ B, (u * stdAddChar (-(a * 1))).re) =
      ∑ a ∈ A, (u * stdAddChar (-(a * 1))).re := by
    simpa only [Ahat, Finset.mul_sum, Complex.re_sum] using hpEq
  obtain ⟨hAdiff, hBdiff⟩ := threshold_eq_on_diff
    (fun a : ZMod N => (u * stdAddChar (-(a * 1))).re) A B c hcard hin hout hsum
  have hAsub : A \ B ⊆ {s} := by
    intro a ha
    apply mem_singleton.mpr
    by_contra hne
    have hlt := hinStrict a (mem_sdiff.mp ha).1 hne
    have he := hAdiff a ha
    linarith
  have hBsub : B \ A ⊆ {(B.card : ZMod N) + s} := by
    intro a ha
    apply mem_singleton.mpr
    by_contra hne
    have hlt := houtStrict a (mem_sdiff.mp ha).2 hne
    have he := hBdiff a ha
    linarith
  rcases eq_or_swap_of_diff_subset A B s ((B.card : ZMod N) + s)
      hcard hAsub hBsub with hsame | hswap
  · exact ⟨s, hsame⟩
  · refine ⟨s + 1, ?_⟩
    rw [arc_swap_endpoint s B.card hm₀ hmN] at hswap
    exact hswap

/-- Equality in Huddling holds exactly for a consecutive arc, including the
    empty and full sets. Boundary ties allow the adjacent arc and no other set. -/
theorem norm_Ahat_one_eq_arc_iff (B : Finset (ZMod N)) :
    ‖Ahat B 1‖ = ‖Ahat (arc (N := N) B.card) 1‖ ↔
      ∃ s : ZMod N, B = tpose s (arc (N := N) B.card) := by
  constructor
  · intro heq
    by_cases hz : B.card = 0
    · have hB : B = ∅ := card_eq_zero.mp hz
      refine ⟨0, ?_⟩
      simp [hB, arc, tpose]
    by_cases hfull : B.card = N
    · have hB : B = univ := B.eq_univ_of_card (by simpa using hfull)
      have hA : tpose 0 (arc (N := N) B.card) = univ := by
        apply Finset.eq_univ_of_card
        rw [card_tpose, card_arc _ (by omega)]
        simpa using hfull
      exact ⟨0, hB.trans hA.symm⟩
    have hm : B.card ≤ N := by simpa using B.card_le_univ
    exact eq_tpose_arc_of_norm_eq B (by omega) (by omega) heq
  · rintro ⟨s, hs⟩
    calc
      ‖Ahat B 1‖ = ‖Ahat (tpose s (arc (N := N) B.card)) 1‖ :=
        congrArg (fun C => ‖Ahat C 1‖) hs
      _ = ‖Ahat (arc (N := N) B.card) 1‖ := norm_tpose _ _ _

/-- At a primitive frequency, equality holds precisely when multiplication by
    that frequency sends the pitch set to a consecutive arc. -/
theorem norm_Ahat_unit_eq_arc_iff (B : Finset (ZMod N)) (k : ZMod N)
    (hk : IsUnit k) :
    ‖Ahat B k‖ = ‖Ahat (arc (N := N) B.card) 1‖ ↔
      ∃ s : ZMod N, B.image (· * k) = tpose s (arc (N := N) B.card) := by
  have he := norm_Ahat_one_eq_arc_iff (B.image (· * k))
  rw [card_image_mul_unit B k hk, ← Ahat_unit_frequency B k hk] at he
  exact he

/-- The extremal formulation: a set maximizes the primitive Fourier magnitude
    among sets of its cardinality exactly when its frequency image is an arc. -/
theorem maximizer_unit_iff (B : Finset (ZMod N)) (k : ZMod N) (hk : IsUnit k) :
    (∀ C : Finset (ZMod N), C.card = B.card → ‖Ahat C k‖ ≤ ‖Ahat B k‖) ↔
      ∃ s : ZMod N, B.image (· * k) = tpose s (arc (N := N) B.card) := by
  rw [← norm_Ahat_unit_eq_arc_iff B k hk]
  constructor
  · intro hmax
    apply le_antisymm (norm_Ahat_unit_le_arc B k hk)
    let C := (arc (N := N) B.card).image (· * (↑(hk.unit⁻¹) : ZMod N))
    have hkinv : IsUnit (↑(hk.unit⁻¹) : ZMod N) := (hk.unit⁻¹).isUnit
    have hCcard : C.card = B.card := by
      dsimp [C]
      rw [card_image_mul_unit _ _ hkinv, card_arc _ (by simpa using B.card_le_univ)]
    have hCimage : C.image (· * k) = arc (N := N) B.card := by
      dsimp [C]
      rw [Finset.image_image]
      have hi : (↑(hk.unit⁻¹) : ZMod N) * k = 1 := by
        simpa only [hk.unit_spec] using Units.inv_mul hk.unit
      have hf : ((fun x : ZMod N => x * k) ∘
          fun x => x * (↑(hk.unit⁻¹) : ZMod N)) = id := by
        funext x
        simp only [Function.comp_apply, mul_assoc, hi, mul_one, id_eq]
      rw [hf, Finset.image_id]
    have hc := hmax C hCcard
    rw [Ahat_unit_frequency C k hk, hCimage] at hc
    exact hc
  · intro he C hcard
    calc
      ‖Ahat C k‖ ≤ ‖Ahat (arc (N := N) C.card) 1‖ := norm_Ahat_unit_le_arc C k hk
      _ = ‖Ahat B k‖ := by rw [hcard, he]

end CyclicHuddling

end MusicTheory
