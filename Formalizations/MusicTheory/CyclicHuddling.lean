/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Basic.Complex.BigOperators

/-!
# Fourier amplitudes of subsets of a finite cyclic group

For `A ⊆ ZMod N`, `Ahat A k = ∑ a ∈ A, stdAddChar (-(a * k))`, which equals Mathlib's `ZMod.dft`
of the indicator (`Ahat_eq_dft`). This file collects the interface used by the Huddling
inequality: transposition, complementation, consecutive arcs and their geometric sums, unit
frequencies, and the threshold argument that reduces the inequality to a geometric selector.

## Main results

* `Ahat_eq_dft`, `Ahat_tpose`, `Ahat_compl`, `norm_Ahat_le_card`.
* `card_arc`, `Ahat_arc`, `Ahat_arc_geom`.
* `sum_le_of_threshold`, `sum_lt_of_strict_threshold`.
* `norm_Ahat_one_le_arc_of_geometric_selector`, `norm_Ahat_unit_le_arc_of_geometric_selector`.

## References

* E. Amiot, *Discrete Fourier transform and Bach's good temperament*, Music Theory Online 15
  (2009).
* C. Marín, *Huddling, diatonic and pentatonic scales in Z12: Fourier maxima and convex-energy
  minima formalized in Lean 4*, Zenodo (2026), doi:10.5281/zenodo.23121103.
-/

@[expose] public section

namespace MusicTheory

open Finset ZMod AddChar Complex
open scoped ComplexConjugate

namespace CyclicHuddling

/-- Every complex amplitude has a unit phase whose real projection is its norm.
    This turns a bound on all directional projections into a norm bound. -/
theorem exists_phase_real_eq_norm (z : ℂ) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ (u * z).re = ‖z‖ := by
  by_cases hz : z = 0
  · refine ⟨1, by simp, ?_⟩
    simp [hz]
  · refine ⟨conj z / (‖z‖ : ℂ), ?_, ?_⟩
    · simp [hz]
    · have hn : (‖z‖ : ℂ) ≠ 0 := by simp [hz]
      rw [div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq]
      simp [pow_two, hz]

/-! The exchange step in the geometric Huddling proof is independent of roots of unity. -/

/-- A set containing all scores above a threshold maximizes their sum among
    sets of the same cardinality. This is the finite exchange argument needed
    after projecting the cyclic roots onto any chosen direction. -/
theorem sum_le_of_threshold {α : Type*} [DecidableEq α]
    (score : α → ℝ) (A B : Finset α) (c : ℝ)
    (hcard : B.card = A.card)
    (hin : ∀ x ∈ A, c ≤ score x)
    (hout : ∀ x ∉ A, score x ≤ c) :
    (∑ x ∈ B, score x) ≤ ∑ x ∈ A, score x := by
  calc
    (∑ x ∈ B, score x) =
        (∑ x ∈ B ∩ A, score x) + ∑ x ∈ B \ A, score x := by
      rw [sum_inter_add_sum_sdiff]
    _ ≤ (∑ x ∈ A ∩ B, score x) + (B \ A).card • c := by
      rw [inter_comm]
      gcongr
      exact sum_le_card_nsmul _ _ _ (fun x hx => hout x (mem_sdiff.mp hx).2)
    _ = (∑ x ∈ A ∩ B, score x) + (A \ B).card • c := by
      rw [card_sdiff_comm hcard]
    _ ≤ (∑ x ∈ A ∩ B, score x) + ∑ x ∈ A \ B, score x := by
      gcongr
      exact card_nsmul_le_sum _ _ _ (fun x hx => hin x (mem_sdiff.mp hx).1)
    _ = ∑ x ∈ A, score x := by
      rw [sum_inter_add_sum_sdiff]

/-- Strict separation at the threshold makes the maximizer unique at its
    cardinality. The geometric equality analysis must account for boundary ties. -/
theorem sum_lt_of_strict_threshold {α : Type*} [DecidableEq α]
    (score : α → ℝ) (A B : Finset α) (c : ℝ)
    (hcard : B.card = A.card)
    (hin : ∀ x ∈ A, c < score x)
    (hout : ∀ x ∉ A, score x ≤ c)
    (hne : B ≠ A) :
    (∑ x ∈ B, score x) < ∑ x ∈ A, score x := by
  have hdiff : (A \ B).Nonempty := by
    rw [sdiff_nonempty]
    intro hsub
    exact hne (eq_of_subset_of_card_le hsub (by rw [hcard])).symm
  have hlow : (∑ x ∈ B \ A, score x) ≤ (B \ A).card • c :=
    sum_le_card_nsmul _ _ _ (fun x hx => hout x (mem_sdiff.mp hx).2)
  have hhigh : (A \ B).card • c < ∑ x ∈ A \ B, score x := by
    simpa only [sum_const] using
      (Finset.sum_lt_sum_of_nonempty hdiff
        (fun x hx => hin x (mem_sdiff.mp hx).1))
  calc
    (∑ x ∈ B, score x) =
        (∑ x ∈ B ∩ A, score x) + ∑ x ∈ B \ A, score x := by
      rw [sum_inter_add_sum_sdiff]
    _ ≤ (∑ x ∈ A ∩ B, score x) + (B \ A).card • c := by
      rw [inter_comm]
      simpa only [add_comm] using add_le_add_left hlow _
    _ = (∑ x ∈ A ∩ B, score x) + (A \ B).card • c := by
      rw [card_sdiff_comm hcard]
    _ < (∑ x ∈ A ∩ B, score x) + ∑ x ∈ A \ B, score x :=
      by simpa only [add_comm] using add_lt_add_left hhigh _
    _ = ∑ x ∈ A, score x := by
      rw [sum_inter_add_sum_sdiff]

variable {N : ℕ} [NeZero N]

/-- The unnormalized Fourier coefficient of a subset of `ZMod N`. -/
noncomputable def Ahat (A : Finset (ZMod N)) (k : ZMod N) : ℂ :=
  ∑ a ∈ A, stdAddChar (-(a * k))

/-- The set-sum convention is Mathlib's discrete Fourier transform of its
    zero-one indicator. -/
theorem Ahat_eq_dft (A : Finset (ZMod N)) (k : ZMod N) :
    Ahat A k = ZMod.dft (fun a => if a ∈ A then (1 : ℂ) else 0) k := by
  rw [Ahat, ZMod.dft_apply]
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_mem,
    Finset.univ_inter]

/-- Transpose a subset by one residue. -/
def tpose (s : ZMod N) (A : Finset (ZMod N)) : Finset (ZMod N) :=
  A.map ⟨(· + s), add_left_injective s⟩

/-- The frequency-zero coefficient is the number of selected residues. -/
theorem Ahat_zero (A : Finset (ZMod N)) : Ahat A 0 = (A.card : ℂ) := by
  simp [Ahat]

/-- The elementary cardinality bound is valid at every frequency, including
    nonprimitive frequencies where the consecutive-arc extremal bound fails. -/
theorem norm_Ahat_le_card (A : Finset (ZMod N)) (k : ZMod N) :
    ‖Ahat A k‖ ≤ (A.card : ℝ) := by
  calc
    ‖Ahat A k‖ ≤ ∑ a ∈ A, ‖(stdAddChar (-(a * k)) : ℂ)‖ := by
      simpa [Ahat] using norm_sum_le (s := A)
        (f := fun a : ZMod N => (stdAddChar (-(a * k)) : ℂ))
    _ = A.card := by
      simp [ZMod.stdAddChar_apply]

/-- Translation changes only Fourier phase. -/
theorem Ahat_tpose (s : ZMod N) (A : Finset (ZMod N)) (k : ZMod N) :
    Ahat (tpose s A) k = stdAddChar (-(s * k)) * Ahat A k := by
  rw [Ahat, Ahat, tpose, Finset.sum_map, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [← map_add_eq_mul]
  congr 1
  ring

/-- Translation preserves every Fourier magnitude. -/
theorem norm_tpose (s : ZMod N) (A : Finset (ZMod N)) (k : ZMod N) :
    ‖Ahat (tpose s A) k‖ = ‖Ahat A k‖ := by
  rw [Ahat_tpose, norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul]

/-- Multiplication by a unit relabels a primitive-frequency coefficient as a
    frequency-one coefficient of the relabeled set. -/
theorem Ahat_unit_frequency (A : Finset (ZMod N)) (k : ZMod N)
    (hk : IsUnit k) :
    Ahat A k = Ahat (A.image (· * k)) 1 := by
  rw [Ahat, Ahat, Finset.sum_image]
  · simp
  · intro a _ b _ hab
    exact hk.mul_left_injective hab

omit [NeZero N] in
/-- Relabeling by a unit preserves the set size. -/
theorem card_image_mul_unit (A : Finset (ZMod N)) (k : ZMod N)
    (hk : IsUnit k) :
    (A.image (· * k)).card = A.card := by
  exact Finset.card_image_of_injective A hk.mul_left_injective

omit [NeZero N] in
/-- Translation preserves the number of selected residues. -/
theorem card_tpose (s : ZMod N) (A : Finset (ZMod N)) :
    (tpose s A).card = A.card := by
  simp [tpose]

/-- The complete character sum vanishes at nonzero frequency. -/
theorem sum_character_eq_zero {k : ZMod N} (hk : k ≠ 0) :
    (∑ a : ZMod N, stdAddChar (-(a * k))) = 0 := by
  have h := AddChar.sum_mulShift (R := ZMod N) (-k) (isPrimitive_stdAddChar N)
  rw [ite_eq_right (by simpa using hk), Nat.cast_zero] at h
  rw [← h]
  exact Finset.sum_congr rfl fun a _ => by rw [mul_neg, ← neg_mul]

/-- Away from zero frequency, complementation reverses the Fourier coefficient. -/
theorem Ahat_compl {k : ZMod N} (hk : k ≠ 0) (A : Finset (ZMod N)) :
    Ahat Aᶜ k = -Ahat A k := by
  have hsplit : Ahat A k + Ahat Aᶜ k = ∑ a : ZMod N, stdAddChar (-(a * k)) := by
    rw [Ahat, Ahat, ← Finset.sum_union (disjoint_compl_right)]
    rw [Finset.union_compl]
  rw [eq_neg_iff_add_eq_zero, add_comm, hsplit, sum_character_eq_zero hk]

/-- The first `m` residues, viewed as a cyclic arc. -/
def arc (m : ℕ) : Finset (ZMod N) :=
  (range m).image (fun j : ℕ => (j : ZMod N))

omit [NeZero N] in
/-- In the natural range, an arc contains exactly `m` residues. -/
theorem card_arc (m : ℕ) (hm : m ≤ N) : (arc (N := N) m).card = m := by
  rw [arc, card_image_of_injOn]
  · exact card_range m
  · intro a ha b hb hab
    have haN : a < N := (mem_range.mp ha).trans_le hm
    have hbN : b < N := (mem_range.mp hb).trans_le hm
    have h := congrArg ZMod.val hab
    simpa only [ZMod.val_natCast_of_lt haN, ZMod.val_natCast_of_lt hbN] using h

/-- An arc coefficient is a consecutive character sum. -/
theorem Ahat_arc (m : ℕ) (hm : m ≤ N) (k : ZMod N) :
    Ahat (arc (N := N) m) k =
      ∑ j ∈ range m, stdAddChar (-((j : ZMod N) * k)) := by
  rw [Ahat, arc, sum_image]
  intro a ha b hb hab
  have haN : a < N := (mem_range.mp ha).trans_le hm
  have hbN : b < N := (mem_range.mp hb).trans_le hm
  have h := congrArg ZMod.val hab
  simpa only [ZMod.val_natCast_of_lt haN, ZMod.val_natCast_of_lt hbN] using h

/-- The cyclic arc has a geometric-series Fourier coefficient. -/
theorem Ahat_arc_geom (m : ℕ) (hm : m ≤ N) (k : ZMod N) :
    Ahat (arc (N := N) m) k =
      ∑ j ∈ range m, (stdAddChar (-k)) ^ j := by
  rw [Ahat_arc m hm]
  refine sum_congr rfl fun j _ => ?_
  rw [← map_nsmul_eq_pow]
  congr 1
  simp only [nsmul_eq_mul]
  ring

/-- The geometric-series identity for an arc, without dividing by a possibly
    vanishing denominator at frequency zero. -/
theorem Ahat_arc_mul_sub (m : ℕ) (hm : m ≤ N) (k : ZMod N) :
    Ahat (arc (N := N) m) k * (stdAddChar (-k) - 1) =
      (stdAddChar (-k)) ^ m - 1 := by
  rw [Ahat_arc_geom m hm]
  exact geom_sum_mul _ _

/-- The real projection of a Fourier coefficient is controlled by the
    finite top-score exchange lemma. A geometric description of the top-score
    sets of roots of unity is the remaining analytic step in Huddling. -/
theorem re_amplitude_le_of_threshold (u : ℂ) (k : ZMod N)
    (A B : Finset (ZMod N)) (c : ℝ)
    (hcard : B.card = A.card)
    (hin : ∀ a ∈ A, c ≤ (u * stdAddChar (-(a * k))).re)
    (hout : ∀ a ∉ A, (u * stdAddChar (-(a * k))).re ≤ c) :
    (u * Ahat B k).re ≤ (u * Ahat A k).re := by
  have h := sum_le_of_threshold
    (fun a : ZMod N => (u * stdAddChar (-(a * k))).re) A B c hcard hin hout
  simpa only [Ahat, Finset.mul_sum, Complex.re_sum] using h

/-- Strictly separated projected scores give strict Fourier-projection
    inequality unless the chosen subset is the maximizing set itself. -/
theorem re_amplitude_lt_of_strict_threshold (u : ℂ) (k : ZMod N)
    (A B : Finset (ZMod N)) (c : ℝ)
    (hcard : B.card = A.card)
    (hin : ∀ a ∈ A, c < (u * stdAddChar (-(a * k))).re)
    (hout : ∀ a ∉ A, (u * stdAddChar (-(a * k))).re ≤ c)
    (hne : B ≠ A) :
    (u * Ahat B k).re < (u * Ahat A k).re := by
  have h := sum_lt_of_strict_threshold
    (fun a : ZMod N => (u * stdAddChar (-(a * k))).re)
    A B c hcard hin hout hne
  simpa only [Ahat, Finset.mul_sum, Complex.re_sum] using h

/-- At frequency one, the full norm bound follows once each directional
    projection has a translated arc above a separating threshold. Other
    primitive frequencies require pulling the arc back by their inverse. -/
theorem norm_Ahat_one_le_arc_of_geometric_selector (m : ℕ) (hm : m ≤ N)
    (B : Finset (ZMod N)) (hcard : B.card = m)
    (hgeom : ∀ u : ℂ, ‖u‖ = 1 →
      ∃ s : ZMod N, ∃ c : ℝ,
        (∀ a ∈ tpose s (arc (N := N) m),
          c ≤ (u * stdAddChar (-(a * 1))).re) ∧
        (∀ a ∉ tpose s (arc (N := N) m),
          (u * stdAddChar (-(a * 1))).re ≤ c)) :
    ‖Ahat B 1‖ ≤ ‖Ahat (arc (N := N) m) 1‖ := by
  obtain ⟨u, hu, hre⟩ := exists_phase_real_eq_norm (Ahat B 1)
  obtain ⟨s, c, hin, hout⟩ := hgeom u hu
  have hsize : (tpose s (arc (N := N) m)).card = B.card := by
    rw [card_tpose, card_arc m hm, hcard]
  have hp := re_amplitude_le_of_threshold u 1
    (tpose s (arc (N := N) m)) B c hsize.symm hin hout
  calc
    ‖Ahat B 1‖ = (u * Ahat B 1).re := hre.symm
    _ ≤ (u * Ahat (tpose s (arc (N := N) m)) 1).re := hp
    _ ≤ ‖u * Ahat (tpose s (arc (N := N) m)) 1‖ := Complex.re_le_norm _
    _ = ‖Ahat (arc (N := N) m) 1‖ := by
      rw [norm_mul, hu, one_mul, norm_tpose]

/-- The same geometric selector controls every primitive frequency after
    relabeling the selected pitches by multiplication by that frequency. -/
theorem norm_Ahat_unit_le_arc_of_geometric_selector (m : ℕ) (hm : m ≤ N)
    (B : Finset (ZMod N)) (hcard : B.card = m) (k : ZMod N) (hk : IsUnit k)
    (hgeom : ∀ u : ℂ, ‖u‖ = 1 →
      ∃ s : ZMod N, ∃ c : ℝ,
        (∀ a ∈ tpose s (arc (N := N) m),
          c ≤ (u * stdAddChar (-(a * 1))).re) ∧
        (∀ a ∉ tpose s (arc (N := N) m),
          (u * stdAddChar (-(a * 1))).re ≤ c)) :
    ‖Ahat B k‖ ≤ ‖Ahat (arc (N := N) m) 1‖ := by
  rw [Ahat_unit_frequency B k hk]
  apply norm_Ahat_one_le_arc_of_geometric_selector m hm _ ?_ hgeom
  rw [card_image_mul_unit B k hk, hcard]

end CyclicHuddling

end MusicTheory
