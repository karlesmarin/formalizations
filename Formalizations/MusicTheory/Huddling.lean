/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.MusicTheory.MTransform
public import Formalizations.MusicTheory.CyclicHuddlingGeometry
public import Mathlib.Data.Finset.Powerset

/-!
# Huddling in `ℤ/12`

Among pitch-class sets of a given size, the consecutive collections maximize the first Fourier
magnitude, with equality exactly for their transpositions (the twelve-tone case of
`CyclicHuddlingGeometry`). Through the multiplication by 5, the chains of fifths maximize the
fifth coefficient.

## Main results

* `arc_maximizes_power`, `arc_unique`, `arc_maximizes_norm`.
* `fifth_frequency_max`, `fifth_frequency_unique`.

## References

* E. Amiot, *Discrete Fourier transform and Bach's good temperament*, Music Theory Online 15
  (2009), Lemma 2.
* C. Marín, *Huddling, diatonic and pentatonic scales in Z12: Fourier maxima and convex-energy
  minima formalized in Lean 4*, Zenodo (2026), doi:10.5281/zenodo.23121103.
-/

@[expose] public section

namespace MusicTheory

open Finset

namespace Huddling

/-- The twelve-tone Fourier interface agrees with the general set-sum interface. -/
theorem Ahat_eq_cyclic (A : Finset (ZMod 12)) (k : ZMod 12) :
    Fourier.Ahat A k = CyclicHuddling.Ahat A k := Fourier.Ahat_apply A k

/-- The consecutive collection C_k = {0,...,k-1} in ZMod 12. -/
def arc (k : ℕ) : Finset (ZMod 12) := (range k).image (fun x : ℕ => (x : ZMod 12))

/-- The transposition orbit; equality at the Fourier maximum is equality up to transposition. -/
def orbitT (A : Finset (ZMod 12)) : Finset (Finset (ZMod 12)) :=
  (univ : Finset (ZMod 12)).image (fun t => Fourier.tpose t A)

/-- Multiplication by five, an involution because 5² = 1 in ZMod 12. -/
def m5 (A : Finset (ZMod 12)) : Finset (ZMod 12) :=
  A.image (fun a => (5 : ZMod 12) * a)

/-- A consecutive chain in the circle-of-fifths coordinates. -/
def fifthArc (k : ℕ) : Finset (ZMod 12) := m5 (arc k)

@[simp] theorem m5_card (A : Finset (ZMod 12)) : (m5 A).card = A.card := by
  exact card_image_of_injOn (MTransform.unit_mul_injOn MTransform.u5)

@[simp] theorem m5_involutive (A : Finset (ZMod 12)) : m5 (m5 A) = A := by
  unfold m5
  rw [image_image]
  have h : (5 : ZMod 12) * 5 = 1 := by decide
  change A.image (fun a => (5 : ZMod 12) * (5 * a)) = A
  have hf : (fun a : ZMod 12 => 5 * (5 * a)) = (fun a => a) := by
    funext a
    rw [← mul_assoc, h, one_mul]
  rw [hf]
  exact image_id

theorem m5_tpose (t : ZMod 12) (A : Finset (ZMod 12)) :
    m5 (Fourier.tpose t A) = Fourier.tpose (5 * t) (m5 A) := by
  unfold m5 Fourier.tpose
  simp only [map_eq_image, image_image, Function.Embedding.coeFn_mk]
  congr 1
  funext a
  change (5 : ZMod 12) * (a + t) = 5 * a + 5 * t
  ring

theorem m5_mem_orbit_iff (A B : Finset (ZMod 12)) :
    m5 A ∈ orbitT B ↔ A ∈ orbitT (m5 B) := by
  constructor
  · intro h
    obtain ⟨t, _, ht⟩ := mem_image.mp h
    refine mem_image.mpr ⟨5 * t, mem_univ _, ?_⟩
    have h' := congrArg m5 ht
    simpa only [m5_tpose, m5_involutive] using h'
  · intro h
    obtain ⟨t, _, ht⟩ := mem_image.mp h
    refine mem_image.mpr ⟨5 * t, mem_univ _, ?_⟩
    have h' := congrArg m5 ht
    simpa only [m5_tpose, m5_involutive] using h'

/-- M5 permutes the Fourier power at frequencies 1 and 5, on the shared Fourier definitions. -/
theorem powerSpec_m5 (A : Finset (ZMod 12)) :
    Fourier.powerSpec (m5 A) 1 = Fourier.powerSpec A 5 := by
  have h : Fourier.Ahat (m5 A) 1 = Fourier.Ahat A 5 := MTransform.Ahat_M5 A
  simp only [Fourier.powerSpec, h]

/-- Real power is the square of the complex magnitude. -/
theorem powerSpec_re_eq_norm_sq (A : Finset (ZMod 12)) (t : ZMod 12) :
    (Fourier.powerSpec A t).re = ‖Fourier.Ahat A t‖ ^ 2 := by
  simp only [Fourier.powerSpec, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

/-- Transposition changes phase and preserves magnitude at every frequency. -/
theorem norm_tpose (s : ZMod 12) (A : Finset (ZMod 12)) (t : ZMod 12) :
    ‖Fourier.Ahat (Fourier.tpose s A) t‖ = ‖Fourier.Ahat A t‖ := by
  rw [Fourier.Ahat_tpose, norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul]

theorem powerSpec_tpose_re (s : ZMod 12) (A : Finset (ZMod 12)) (t : ZMod 12) :
    (Fourier.powerSpec (Fourier.tpose s A) t).re = (Fourier.powerSpec A t).re := by
  rw [powerSpec_re_eq_norm_sq, powerSpec_re_eq_norm_sq, norm_tpose]

theorem powerSpec_one_re_eq_iff (A B : Finset (ZMod 12)) :
    (Fourier.powerSpec A 1).re = (Fourier.powerSpec B 1).re ↔
      MTransform.psZ A = MTransform.psZ B := by
  have hinj : Function.Injective MTransform.toR3 :=
    Zsqrtd.toReal_injective (by norm_num) MTransform.three_nonsquare
  constructor
  · intro h
    apply hinj
    rw [MTransform.toReal_psZ, MTransform.toReal_psZ, h]
  · intro h
    have h' := congrArg MTransform.toR3 h
    rw [MTransform.toReal_psZ, MTransform.toReal_psZ] at h'
    linarith

/-- Huddling inequality: the consecutive collection maximizes a1 at fixed cardinality. -/
theorem arc_maximizes_power (A : Finset (ZMod 12)) :
    (Fourier.powerSpec A 1).re ≤ (Fourier.powerSpec (arc A.card) 1).re := by
  have h : ‖Fourier.Ahat A 1‖ ≤ ‖Fourier.Ahat (arc A.card) 1‖ := by
    rw [Ahat_eq_cyclic, Ahat_eq_cyclic]
    exact CyclicHuddling.norm_Ahat_one_le_arc A
  rw [powerSpec_re_eq_norm_sq, powerSpec_re_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- Equality in Huddling holds precisely for the transposes of the consecutive collection. -/
theorem arc_unique (A : Finset (ZMod 12)) :
    (Fourier.powerSpec A 1).re = (Fourier.powerSpec (arc A.card) 1).re ↔
      A ∈ orbitT (arc A.card) := by
  rw [powerSpec_re_eq_norm_sq, powerSpec_re_eq_norm_sq,
    sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Ahat_eq_cyclic, Ahat_eq_cyclic]
  change (‖CyclicHuddling.Ahat A 1‖ =
    ‖CyclicHuddling.Ahat (CyclicHuddling.arc A.card) 1‖) ↔ _
  rw [CyclicHuddling.norm_Ahat_one_eq_arc_iff]
  simp only [orbitT, mem_image, mem_univ, true_and]
  exact exists_congr (fun s => eq_comm)

/-- Backward-compatible finite certificate, now derived from the structural
    theorem. Despite its historical name, no census is evaluated. -/
theorem huddling_census :
    ∀ A ∈ (univ : Finset (ZMod 12)).powerset,
      MTransform.psZ A ≤ MTransform.psZ (arc A.card) ∧
        (MTransform.psZ A = MTransform.psZ (arc A.card) → A ∈ orbitT (arc A.card)) := by
  intro A _
  refine ⟨(MTransform.powerSpec_one_re_le_iff _ _).mp (arc_maximizes_power A), ?_⟩
  intro he
  exact (arc_unique A).mp ((powerSpec_one_re_eq_iff A (arc A.card)).mpr he)

/-- The same maximum in the magnitude formulation used by Amiot. -/
theorem arc_maximizes_norm (A : Finset (ZMod 12)) :
    ‖Fourier.Ahat A 1‖ ≤ ‖Fourier.Ahat (arc A.card) 1‖ := by
  have h := arc_maximizes_power A
  rw [powerSpec_re_eq_norm_sq, powerSpec_re_eq_norm_sq] at h
  nlinarith [norm_nonneg (Fourier.Ahat A 1), norm_nonneg (Fourier.Ahat (arc A.card) 1)]

/-- Huddling transported through M5: a fifth chain maximizes the fifth Fourier magnitude. -/
theorem fifth_frequency_max (A : Finset (ZMod 12)) :
    (Fourier.powerSpec A 5).re ≤ (Fourier.powerSpec (fifthArc A.card) 5).re := by
  have h := arc_maximizes_power (m5 A)
  have href : Fourier.powerSpec (fifthArc A.card) 5 = Fourier.powerSpec (arc A.card) 1 := by
    rw [← powerSpec_m5, fifthArc, m5_involutive]
  simpa only [m5_card, powerSpec_m5, href] using h

/-- The fifth-frequency equality class is exactly the transposition orbit of a fifth chain. -/
theorem fifth_frequency_unique (A : Finset (ZMod 12)) :
    (Fourier.powerSpec A 5).re = (Fourier.powerSpec (fifthArc A.card) 5).re ↔
      A ∈ orbitT (fifthArc A.card) := by
  have href : Fourier.powerSpec (fifthArc A.card) 5 = Fourier.powerSpec (arc A.card) 1 := by
    rw [← powerSpec_m5, fifthArc, m5_involutive]
  rw [href, ← powerSpec_m5]
  simpa only [m5_card, m5_mem_orbit_iff, fifthArc] using arc_unique (m5 A)

end Huddling

end MusicTheory
