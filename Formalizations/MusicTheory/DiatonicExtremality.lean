/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.MusicTheory.Huddling
public import Formalizations.MusicTheory.CyclicHuddlingClosedForm
public import Formalizations.MusicTheory.AllPairsEvenness

/-!
# The diatonic maximizes the fifth Fourier coefficient and minimizes convex energies

Among the 7-subsets of `ℤ/12`, the diatonic collection maximizes `‖Ahat A 5‖`, with value
`2 + √3 = sin (7π/12) / sin (π/12)`, and the maximizers are exactly its twelve transpositions
(Huddling through the multiplication by 5). It also minimizes every all-pairs energy with convex
`V` decreasing at the top, uniquely under strict hypotheses, so the two extremal problems have the
same solutions.

## Main results

* `diatonic_norm_value`, `diatonic_norm_max`, `diatonic_norm_unique`.
* `diatonic_sine_ratio_value`, `pentatonic_sine_ratio_value`.
* `diatonic_energy_min`, `diatonic_energy_unique`.
* `spectral_energy_equivalence`.

## References

* E. Amiot, *Discrete Fourier transform and Bach's good temperament*, Music Theory Online 15
  (2009).
* C. Marín, *Huddling, diatonic and pentatonic scales in Z12: Fourier maxima and convex-energy
  minima formalized in Lean 4*, Zenodo (2026), doi:10.5281/zenodo.23121103.
-/

@[expose] public section

namespace MusicTheory

open Finset AllPairsEvenness

namespace DiatonicExtremality

/-- Weak discrete convexity on distances 1,...,6 and the decreasing upper boundary. -/
def Admissible (V : ℕ → ℝ) : Prop :=
  0 ≤ V 1 - 2 * V 2 + V 3 ∧ 0 ≤ V 2 - 2 * V 3 + V 4 ∧
  0 ≤ V 3 - 2 * V 4 + V 5 ∧ 0 ≤ V 4 - 2 * V 5 + V 6 ∧ V 6 ≤ V 5

/-- The strict hypotheses needed to identify the equality class. -/
def StrictAdmissible (V : ℕ → ℝ) : Prop :=
  0 < V 1 - 2 * V 2 + V 3 ∧ 0 < V 2 - 2 * V 3 + V 4 ∧
  0 < V 3 - 2 * V 4 + V 5 ∧ 0 < V 4 - 2 * V 5 + V 6 ∧ V 6 < V 5

@[simp] theorem diatonic_card : D.card = 7 := by decide

/-- M5 sends the diatonic to a consecutive seven-note collection, transposed by seven. -/
theorem m5_diatonic : Huddling.m5 D = Fourier.tpose 7 (Huddling.arc 7) := by decide

theorem fifthArc_to_diatonic : Fourier.tpose 11 (Huddling.fifthArc 7) = D := by decide

set_option maxRecDepth 100000 in
/-- A seven-note fifth chain and the diatonic have exactly the same transposition/TI orbit. -/
theorem fifthArc_seven_orbit : Huddling.orbitT (Huddling.fifthArc 7) = orbitTI := by
  decide +kernel

theorem diatonic_mem_orbit : D ∈ orbitTI := by decide

theorem reference_power_eq :
    (Fourier.powerSpec (Huddling.fifthArc 7) 5).re = (Fourier.powerSpec D 5).re := by
  have hmem : D ∈ Huddling.orbitT (Huddling.fifthArc D.card) := by
    rw [diatonic_card, fifthArc_seven_orbit]
    exact diatonic_mem_orbit
  simpa only [diatonic_card] using ((Huddling.fifth_frequency_unique D).mpr hmem).symm

/-- Among all seven-note collections, the diatonic maximizes the fifth Fourier power. -/
theorem diatonic_spectral_max (A : Finset (ZMod 12)) (hA : A.card = 7) :
    (Fourier.powerSpec A 5).re ≤ (Fourier.powerSpec D 5).re := by
  simpa only [hA, reference_power_eq] using Huddling.fifth_frequency_max A

/-- The spectral equality class is precisely the twelve diatonic transpositions. -/
theorem diatonic_spectral_unique (A : Finset (ZMod 12)) (hA : A.card = 7) :
    (Fourier.powerSpec A 5).re = (Fourier.powerSpec D 5).re ↔ A ∈ orbitTI := by
  simpa only [hA, reference_power_eq, fifthArc_seven_orbit] using Huddling.fifth_frequency_unique A

theorem diatonic_power_value : (Fourier.powerSpec D 5).re = 7 + 4 * Real.sqrt 3 := by
  have h := MTransform.toReal_psZ (Huddling.m5 D)
  have hc : MTransform.psZ (Huddling.m5 D) = ⟨14, 8⟩ := by decide
  rw [hc, Huddling.powerSpec_m5] at h
  simp only [MTransform.toR3, Zsqrtd.toReal, Zsqrtd.lift_apply_apply] at h
  norm_num at h
  linarith

/-- The familiar exact diatonic magnitude: |a5| = 2 + sqrt(3). -/
theorem diatonic_norm_value : ‖Fourier.Ahat D 5‖ = 2 + Real.sqrt 3 := by
  have h := diatonic_power_value
  rw [Huddling.powerSpec_re_eq_norm_sq] at h
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith [norm_nonneg (Fourier.Ahat D 5), Real.sqrt_nonneg 3]

/-- Euler's sine ratio equals the exact seven-note constant used by the library. -/
theorem diatonic_sine_ratio_value :
    Real.sin (Real.pi * 7 / 12) / Real.sin (Real.pi / 12) = 2 + Real.sqrt 3 := by
  have hphase : ‖Fourier.Ahat (Huddling.m5 D) 1‖ =
      ‖Fourier.Ahat (Huddling.arc 7) 1‖ := by
    rw [m5_diatonic, Huddling.norm_tpose]
  have hM : Fourier.Ahat (Huddling.m5 D) 1 = Fourier.Ahat D 5 := MTransform.Ahat_M5 D
  rw [hM, diatonic_norm_value] at hphase
  have hr := CyclicHuddling.norm_Ahat_arc_sine_ratio (N := 12) (by norm_num) 7 (by norm_num)
  norm_num only [Nat.cast_ofNat] at hr
  rw [← hr]
  rw [Huddling.Ahat_eq_cyclic] at hphase
  exact hphase.symm

/-- Five- and seven-note maxima share one constant by sine complementation. -/
theorem pentatonic_sine_ratio_value :
    Real.sin (Real.pi * 5 / 12) / Real.sin (Real.pi / 12) = 2 + Real.sqrt 3 := by
  have hc := CyclicHuddling.sine_ratio_complement (N := 12) 7 (by norm_num)
  norm_num only [Nat.reduceSub, Nat.cast_ofNat] at hc
  rw [hc, diatonic_sine_ratio_value]

theorem diatonic_norm_max (A : Finset (ZMod 12)) (hA : A.card = 7) :
    ‖Fourier.Ahat A 5‖ ≤ 2 + Real.sqrt 3 := by
  have h := diatonic_spectral_max A hA
  rw [Huddling.powerSpec_re_eq_norm_sq, Huddling.powerSpec_re_eq_norm_sq,
    diatonic_norm_value] at h
  nlinarith [norm_nonneg (Fourier.Ahat A 5), Real.sqrt_nonneg 3]

theorem diatonic_norm_unique (A : Finset (ZMod 12)) (hA : A.card = 7) :
    ‖Fourier.Ahat A 5‖ = 2 + Real.sqrt 3 ↔ A ∈ orbitTI := by
  rw [← diatonic_spectral_unique A hA, Huddling.powerSpec_re_eq_norm_sq,
    Huddling.powerSpec_re_eq_norm_sq, diatonic_norm_value]
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).symm

/-- Finite input to the symbolic Abel engine, bundled so interval counts are shared. -/
def EnergyCertificate (A : Finset (ZMod 12)) : Prop :=
  (dg D A 0 + dg D A 1 + dg D A 2 + dg D A 3 + dg D A 4 + dg D A 5 = 0) ∧
  (0 ≤ DD (dg D A) 0 ∧ 0 ≤ DD (dg D A) 1 ∧ 0 ≤ DD (dg D A) 2 ∧
    0 ≤ DD (dg D A) 3 ∧ 0 ≤ DD (dg D A) 4) ∧
  (A ∉ orbitTI → 0 < DD (dg D A) 0 ∨ 0 < DD (dg D A) 1 ∨ 0 < DD (dg D A) 2 ∨
    0 < DD (dg D A) 3 ∨ 0 < DD (dg D A) 4) ∧
  (A ∈ orbitTI → iv A 1 = iv D 1 ∧ iv A 2 = iv D 2 ∧ iv A 3 = iv D 3 ∧
    iv A 4 = iv D 4 ∧ iv A 5 = iv D 5 ∧ iv A 6 = iv D 6)

instance (A : Finset (ZMod 12)) : Decidable (EnergyCertificate A) := by
  unfold EnergyCertificate
  infer_instance

/-- Exact seven-note census for the energy proof, assembled from the censuses of
    `AllPairsEvenness`. -/
theorem energy_census : ∀ A ∈ (univ : Finset (ZMod 12)).powersetCard 7, EnergyCertificate A :=
  fun A hA => ⟨census_hsum A hA, census_DD A hA, census_offorbit A hA,
    fun h => census_onorbit A h⟩

set_option maxRecDepth 100000 in
theorem orbit_card : ∀ A ∈ orbitTI, A.card = 7 := by
  decide +kernel

theorem seven_mem (A : Finset (ZMod 12)) (hA : A.card = 7) :
    A ∈ (univ : Finset (ZMod 12)).powersetCard 7 :=
  mem_powersetCard.mpr ⟨subset_univ A, hA⟩

/-- Every weakly admissible potential has the diatonic as an all-pairs ground state. -/
theorem diatonic_energy_min (V : ℕ → ℝ) (hV : Admissible V)
    (A : Finset (ZMod 12)) (hA : A.card = 7) : E V D ≤ E V A := by
  obtain ⟨hc0, hc1, hc2, hc3, hdec⟩ := hV
  exact groundStateG D V hc0 hc1 hc2 hc3 hdec _
    (fun B hB => (energy_census B hB).1)
    (fun B hB => (energy_census B hB).2.1) A (seven_mem A hA)

/-- With strict convexity/decrease, the energy equality class is the diatonic orbit. -/
theorem diatonic_energy_unique (V : ℕ → ℝ) (hV : StrictAdmissible V)
    (A : Finset (ZMod 12)) (hA : A.card = 7) : E V D = E V A ↔ A ∈ orbitTI := by
  obtain ⟨hc0, hc1, hc2, hc3, hdec⟩ := hV
  exact uniqueG D V hc0 hc1 hc2 hc3 hdec _ orbitTI
    (fun B hB => (energy_census B hB).1)
    (fun B hB => (energy_census B hB).2.1)
    (fun B hB => (energy_census B hB).2.2.1)
    (fun B hB => (energy_census B (seven_mem B (orbit_card B hB))).2.2.2 hB)
    A (seven_mem A hA)

/-- The connection: the fifth Fourier maximum and every strict convex-energy minimum
    have exactly the same seven-note equality class. -/
theorem spectral_energy_equivalence (V : ℕ → ℝ) (hV : StrictAdmissible V)
    (A : Finset (ZMod 12)) (hA : A.card = 7) :
    ‖Fourier.Ahat A 5‖ = 2 + Real.sqrt 3 ↔ E V D = E V A := by
  rw [diatonic_norm_unique A hA, diatonic_energy_unique V hV A hA]

end DiatonicExtremality

end MusicTheory
