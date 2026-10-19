/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.MusicTheory.DiatonicExtremality

/-!
# Homometry, complementation and the pentatonic extremality

Homometric sets have the same interval vector, hence the same all-pairs energy for every
potential; homometry is preserved by complementation; the diatonic has no homometric partner
outside its orbit. Complementation changes the energy by a constant depending only on the size,
which transfers the diatonic results to the pentatonic.

## Main results

* `energy_eq_of_homometric`, `homometric_compl`, `energy_compl_eq_of_homometric`.
* `diatonic_homometric_iff`.
* `m5_preserves_a6`, `m5_commutes_tritone`.
* `energy_compl`.
* `pentatonic_norm_max`, `pentatonic_norm_unique`, `pentatonic_energy_min`,
  `pentatonic_spectral_energy_equivalence`.

## References

* N. Bushaw, B. Cody, C. Leffler, *Sets of vertices with extremal energy*, arXiv:2407.18785,
  Theorem 3.5.
* C. Marín, *Huddling, diatonic and pentatonic scales in Z12: Fourier maxima and convex-energy
  minima formalized in Lean 4*, Zenodo (2026), doi:10.5281/zenodo.23121103.
-/

@[expose] public section

namespace MusicTheory

open Finset AllPairsEvenness

namespace ExtremalityConnections

/-- Bridge the unordered energy convention to the earlier ordered Fourier convention.
    At distance zero this is merely an identity between the definitions; energies use 1..6. -/
theorem iv_eq_raw_div_two (A : Finset (ZMod 12)) (k : ℕ) :
    iv A k = Fourier.IVraw A k / 2 := by
  unfold iv Fourier.IVraw
  rw [card_filter, sum_product]
  simp only [cdist, Fourier.ivc, neg_sub]
  rfl

/-- Homometry fixes every unordered interval-vector entry. -/
theorem homometric_iv_eq (A B : Finset (ZMod 12)) (h : Fourier.Homometric A B) (k : ℕ) :
    iv A k = iv B k := by
  rw [iv_eq_raw_div_two, iv_eq_raw_div_two,
    Fourier.IVraw_eq_sum_autocorr, Fourier.IVraw_eq_sum_autocorr]
  congr 1
  exact sum_congr rfl (fun d _ => h d)

/-- Every all-pairs distance potential is blind to homometric differences. No convexity needed. -/
theorem energy_eq_of_homometric (V : ℕ → ℝ) (A B : Finset (ZMod 12))
    (h : Fourier.Homometric A B) : E V A = E V B := by
  unfold E
  exact sum_congr rfl (fun j _ => by rw [homometric_iv_eq A B h])

theorem homometric_tpose (s : ZMod 12) (A : Finset (ZMod 12)) :
    Fourier.Homometric (Fourier.tpose s A) A := by
  rw [Fourier.homometric_iff_normSq_dft_eq]
  intro t
  simp only [Complex.normSq_eq_norm_sq, Huddling.norm_tpose]

theorem energy_tpose (V : ℕ → ℝ) (s : ZMod 12) (A : Finset (ZMod 12)) :
    E V (Fourier.tpose s A) = E V A :=
  energy_eq_of_homometric V _ _ (homometric_tpose s A)

set_option maxRecDepth 100000 in
theorem diatonic_orbit_eq_transpositions : orbitTI = Huddling.orbitT D := by
  decide +kernel

/-- Extremal spectral rigidity: the diatonic has no nontrivial homometric partner. -/
theorem diatonic_homometric_iff (A : Finset (ZMod 12)) :
    Fourier.Homometric A D ↔ A ∈ orbitTI := by
  constructor
  · intro h
    have hcard : A.card = 7 := by
      have h0 := h 0
      simpa only [Fourier.autocorr_zero, DiatonicExtremality.diatonic_card] using h0
    apply (DiatonicExtremality.diatonic_spectral_unique A hcard).mp
    exact congrArg Complex.re (congrFun ((Fourier.homometric_iff_powerSpec_eq A D).mp h) 5)
  · intro h
    rw [diatonic_orbit_eq_transpositions] at h
    obtain ⟨s, _, rfl⟩ := mem_image.mp h
    exact homometric_tpose s D

/-- M5 preserves the full sixth coefficient, hence the parity observable `a₆`. -/
theorem m5_preserves_a6 (A : Finset (ZMod 12)) :
    Fourier.Ahat (Huddling.m5 A) 6 = Fourier.Ahat A 6 := by
  have h := MTransform.Ahat_mul MTransform.u5 A 6
  have hc : (5 : ZMod 12) * 6 = 6 := by decide
  simp only [MTransform.u5_coe, hc] at h
  exact h

/-- The coordinate change commutes with the tritone transposition `T₆`. -/
theorem m5_commutes_tritone (A : Finset (ZMod 12)) :
    Huddling.m5 (Fourier.tpose 6 A) = Fourier.tpose 6 (Huddling.m5 A) := by
  simpa only [show (5 : ZMod 12) * 6 = 6 by decide] using Huddling.m5_tpose 6 A

theorem tpose_compl (s : ZMod 12) (A : Finset (ZMod 12)) :
    (Fourier.tpose s A)ᶜ = Fourier.tpose s Aᶜ := by
  ext x
  simp only [mem_compl, Fourier.mem_tpose]

/-- Complementing a set preserves every nonzero-frequency magnitude. -/
theorem norm_compl (A : Finset (ZMod 12)) (t : ZMod 12) (ht : t ≠ 0) :
    ‖Fourier.Ahat Aᶜ t‖ = ‖Fourier.Ahat A t‖ := by
  rw [Fourier.Ahat_compl ht, norm_neg]

/-- Complement interval identity in autocorrelation form, including the zero difference. -/
theorem commonTones_compl (A : Finset (ZMod 12)) (t : ZMod 12) :
    Fourier.commonTones Aᶜ t + 2 * A.card = 12 + Fourier.commonTones A t := by
  have hc := card_compl_add_card (A ∪ Fourier.tpose t A)
  have hu := card_union_add_card_inter A (Fourier.tpose t A)
  have hi : (A ∪ Fourier.tpose t A)ᶜ = Aᶜ ∩ Fourier.tpose t Aᶜ := by
    rw [compl_union, tpose_compl]
  rw [hi] at hc
  have htcard : (Fourier.tpose t A).card = A.card := card_map _
  have huniv : Fintype.card (ZMod 12) = 12 := ZMod.card 12
  unfold Fourier.commonTones
  omega

/-- Homometry survives complementation: the zero autocorrelation fixes cardinality,
    and every other autocorrelation receives the same complement correction. -/
theorem homometric_compl (A B : Finset (ZMod 12)) (h : Fourier.Homometric A B) :
    Fourier.Homometric Aᶜ Bᶜ := by
  have hcard : A.card = B.card := by
    have h0 := h 0
    simpa only [Fourier.autocorr_zero] using h0
  intro t
  have ha := commonTones_compl A t
  have hb := commonTones_compl B t
  simp only [Fourier.commonTones_eq_autocorr] at ha hb
  have ht := h t
  omega

/-- The homometry/complement square commutes for every all-pairs potential. -/
theorem energy_compl_eq_of_homometric (V : ℕ → ℝ)
    (A B : Finset (ZMod 12)) (h : Fourier.Homometric A B) :
    E V Aᶜ = E V Bᶜ :=
  energy_eq_of_homometric V Aᶜ Bᶜ (homometric_compl A B h)

theorem iv_eq_commonTones (A : Finset (ZMod 12)) (k : ℕ) (h1 : 1 ≤ k) (h5 : k ≤ 5) :
    iv A k = Fourier.commonTones A (k : ZMod 12) := by
  rw [iv_eq_raw_div_two, Fourier.IVraw_eq_two_commonTones A k h1 h5]
  omega

/-- The complement theorem in unordered-pair convention, away from the tritone. -/
theorem iv_compl_add (A : Finset (ZMod 12)) (k : ℕ) (h1 : 1 ≤ k) (h5 : k ≤ 5) :
    iv Aᶜ k + 2 * A.card = 12 + iv A k := by
  rw [iv_eq_commonTones Aᶜ k h1 h5, iv_eq_commonTones A k h1 h5]
  exact commonTones_compl A k

/-- At the tritone the complement correction is half as large. -/
theorem iv_compl_tritone_add (A : Finset (ZMod 12)) :
    iv Aᶜ 6 + A.card = 6 + iv A 6 := by
  have h := congrArg (fun n : ℕ => n / 2) (commonTones_compl A 6)
  rw [iv_eq_raw_div_two, iv_eq_raw_div_two, Fourier.IVraw_tritone,
    Fourier.IVraw_tritone]
  omega

/-- Complementation changes energy by a cardinality-dependent constant.
    This is the C12 instance of Bushaw--Cody--Leffler, Theorem 3.5 (2025 version). -/
theorem energy_compl (V : ℕ → ℝ) (A : Finset (ZMod 12)) :
    E V Aᶜ - E V A =
      (6 - (A.card : ℝ)) * (2 * (V 1 + V 2 + V 3 + V 4 + V 5) + V 6) := by
  have h1 := iv_compl_add A 1 (by omega) (by omega)
  have h2 := iv_compl_add A 2 (by omega) (by omega)
  have h3 := iv_compl_add A 3 (by omega) (by omega)
  have h4 := iv_compl_add A 4 (by omega) (by omega)
  have h5 := iv_compl_add A 5 (by omega) (by omega)
  have h6 := iv_compl_tritone_add A
  have hr1 : (iv Aᶜ 1 : ℝ) = iv A 1 + 12 - 2 * A.card := by exact_mod_cast (by omega : (iv Aᶜ 1 : ℤ) = iv A 1 + 12 - 2 * A.card)
  have hr2 : (iv Aᶜ 2 : ℝ) = iv A 2 + 12 - 2 * A.card := by exact_mod_cast (by omega : (iv Aᶜ 2 : ℤ) = iv A 2 + 12 - 2 * A.card)
  have hr3 : (iv Aᶜ 3 : ℝ) = iv A 3 + 12 - 2 * A.card := by exact_mod_cast (by omega : (iv Aᶜ 3 : ℤ) = iv A 3 + 12 - 2 * A.card)
  have hr4 : (iv Aᶜ 4 : ℝ) = iv A 4 + 12 - 2 * A.card := by exact_mod_cast (by omega : (iv Aᶜ 4 : ℤ) = iv A 4 + 12 - 2 * A.card)
  have hr5 : (iv Aᶜ 5 : ℝ) = iv A 5 + 12 - 2 * A.card := by exact_mod_cast (by omega : (iv Aᶜ 5 : ℤ) = iv A 5 + 12 - 2 * A.card)
  have hr6 : (iv Aᶜ 6 : ℝ) = iv A 6 + 6 - A.card := by exact_mod_cast (by omega : (iv Aᶜ 6 : ℤ) = iv A 6 + 6 - A.card)
  simp only [E, sum_range_succ, sum_range_zero, zero_add, Nat.reduceAdd]
  rw [hr1, hr2, hr3, hr4, hr5, hr6]
  ring

theorem diatonic_compl : Dᶜ = Fourier.tpose 6 P := by decide

set_option maxRecDepth 100000 in
theorem pentatonic_orbit : Huddling.orbitT Dᶜ = orbitOf P := by decide +kernel

theorem compl_mem_orbit_iff (A B : Finset (ZMod 12)) :
    Aᶜ ∈ Huddling.orbitT B ↔ A ∈ Huddling.orbitT Bᶜ := by
  constructor
  · intro h
    obtain ⟨s, _, hs⟩ := mem_image.mp h
    exact mem_image.mpr ⟨s, mem_univ _, by simpa only [tpose_compl, compl_compl] using congrArg (fun X => Xᶜ) hs⟩
  · intro h
    obtain ⟨s, _, hs⟩ := mem_image.mp h
    exact mem_image.mpr ⟨s, mem_univ _, by simpa only [tpose_compl, compl_compl] using congrArg (fun X => Xᶜ) hs⟩

theorem five_compl_card (A : Finset (ZMod 12)) (hA : A.card = 5) : Aᶜ.card = 7 := by
  rw [card_compl, ZMod.card, hA]

/-- The five-note spectral bound follows from the seven-note one without another census. -/
theorem pentatonic_norm_max (A : Finset (ZMod 12)) (hA : A.card = 5) :
    ‖Fourier.Ahat A 5‖ ≤ 2 + Real.sqrt 3 := by
  simpa only [norm_compl A 5 (by decide)] using
    DiatonicExtremality.diatonic_norm_max Aᶜ (five_compl_card A hA)

theorem pentatonic_norm_unique (A : Finset (ZMod 12)) (hA : A.card = 5) :
    ‖Fourier.Ahat A 5‖ = 2 + Real.sqrt 3 ↔ A ∈ orbitOf P := by
  have h := DiatonicExtremality.diatonic_norm_unique Aᶜ (five_compl_card A hA)
  simpa only [norm_compl A 5 (by decide), diatonic_orbit_eq_transpositions,
    compl_mem_orbit_iff, pentatonic_orbit] using h

/-- The five/seven-note energy gaps coincide, for every real potential. -/
theorem pentatonic_energy_gap (V : ℕ → ℝ) (A : Finset (ZMod 12)) (hA : A.card = 5) :
    E V A - E V P = E V Aᶜ - E V D := by
  have ha := energy_compl V A
  have hd := energy_compl V D
  rw [hA] at ha
  rw [DiatonicExtremality.diatonic_card, diatonic_compl, energy_tpose] at hd
  norm_num at ha hd
  linarith

theorem pentatonic_energy_min (V : ℕ → ℝ) (hV : DiatonicExtremality.Admissible V)
    (A : Finset (ZMod 12)) (hA : A.card = 5) : E V P ≤ E V A := by
  have he := DiatonicExtremality.diatonic_energy_min V hV Aᶜ (five_compl_card A hA)
  have hg := pentatonic_energy_gap V A hA
  linarith

theorem pentatonic_spectral_energy_equivalence (V : ℕ → ℝ)
    (hV : DiatonicExtremality.StrictAdmissible V) (A : Finset (ZMod 12)) (hA : A.card = 5) :
    ‖Fourier.Ahat A 5‖ = 2 + Real.sqrt 3 ↔ E V P = E V A := by
  have h := DiatonicExtremality.spectral_energy_equivalence V hV Aᶜ (five_compl_card A hA)
  rw [norm_compl A 5 (by decide)] at h
  have hg := pentatonic_energy_gap V A hA
  constructor
  · intro hn
    have he := h.mp hn
    linarith
  · intro he
    apply h.mpr
    linarith

end ExtremalityConnections

end MusicTheory
