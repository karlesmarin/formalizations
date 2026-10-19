/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Tactic.Ring

/-!
# The discrete Fourier transform of a pitch-class set

A pitch-class set `A ⊆ ℤ/12` is represented by its `0/1` indicator `ind A : ZMod 12 → ℂ`, and its
Fourier transform is Mathlib's `ZMod.dft` of the indicator: `Ahat A = 𝓕 (ind A)`, so
`Ahat A t = ∑ a ∈ A, exp (-2πi a t / 12)`. This file proves the classical invariants of
pitch-class set theory in terms of `Ahat`, ordered by how much of the phase of `Ahat` they use.

## Main results

* `Ahat_zero`, `Ahat_tpose`, `Ahat_compl`: `Ahat A 0 = #A`; transposition multiplies by a
  character; complementation negates every nonzero coefficient.
* `autocorr_eq_invDFT`, `IVraw_eq_invDFT_power`: the autocorrelation, hence the interval vector, is
  the inverse transform of the power spectrum `‖Ahat A‖²`.
* `homometric_iff_powerSpec_eq`: two sets are homometric (Z-related) iff they have the same power
  spectrum.
* `hexachord_IVraw_eq_nat`: Babbitt's hexachord theorem.
* `commonTonesInv_eq_sumcorr`, `sumcorr_eq_invDFT`: common tones under inversion are a function
  of `Ahat A ^ 2`.
* `carterPair_triple_distinct`: the triple correlation separates a homometric pair.
* `Ahat_injective`, `Ahat_eq_iff`: `Ahat` is a complete invariant.
* `tpose_iff_Ahat_ramp`, `inv_iff_Ahat_conj_ramp`, `setClass_iff_Ahat_mod_phase`: transposition and
  inversion classes in terms of `Ahat`.
* `IsDeep_iff_commonTones_nodup`, `diatonic_isDeep`: deep scales.

## References

* E. Amiot, *Music Through Fourier Space*, Springer (2016).
* C. Marín, *The phase taxonomy of pitch-class set invariants*, Zenodo (2026),
  doi:10.5281/zenodo.20826773.
* C. Marín, *The Tonnetz spectrum is the generating triad's Fourier balance profile*,
  Zenodo (2026), doi:10.5281/zenodo.20862821.
-/

@[expose] public section

namespace MusicTheory

open Finset ZMod AddChar
open scoped ZMod

namespace Fourier

/-- The 0/1 indicator of a pc-set, as a complex-valued function on `ZMod 12`. -/
noncomputable def ind (A : Finset (ZMod 12)) : ZMod 12 → ℂ := fun j => if j ∈ A then 1 else 0

/-- The DFT of a pc-set: `Â A t = Σ_{a ∈ A} exp(−2πi·a·t/12)`. -/
noncomputable def Ahat (A : Finset (ZMod 12)) : ZMod 12 → ℂ := 𝓕 (ind A)

/-- `Â A t` is the sum of `stdAddChar(−(a·t))` over `a ∈ A` (indicator collapses the sum to `A`). -/
lemma Ahat_apply (A : Finset (ZMod 12)) (t : ZMod 12) :
    Ahat A t = ∑ a ∈ A, stdAddChar (-(a * t)) := by
  unfold Ahat ind
  rw [dft_apply]
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]

/-- **Step 1.** The DC coefficient is the cardinality: `Â A 0 = |A|`. -/
theorem Ahat_zero (A : Finset (ZMod 12)) : Ahat A 0 = (A.card : ℂ) := by
  rw [Ahat_apply]
  simp

/-- Transposition `Tₖ : a ↦ a + k`, as a `Finset` embedding (matches `IntervalVector.tpose`). -/
def tpose (k : ZMod 12) (A : Finset (ZMod 12)) : Finset (ZMod 12) :=
  A.map ⟨(· + k), add_left_injective k⟩

/-- **Step 2 (transposition).** `Â (Tₖ A) t = exp(−2πi·k·t/12) · Â A t`. -/
theorem Ahat_tpose (k : ZMod 12) (A : Finset (ZMod 12)) (t : ZMod 12) :
    Ahat (tpose k A) t = stdAddChar (-(k * t)) * Ahat A t := by
  rw [Ahat_apply, Ahat_apply, tpose, Finset.sum_map, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [← map_add_eq_mul]
  congr 1
  ring

/-- The DFT of the all-ones indicator vanishes off `0`: `𝓕 (fun _ => 1) t = 0` for `t ≠ 0`. -/
lemma dft_one_apply_ne {t : ZMod 12} (ht : t ≠ 0) :
    (∑ j : ZMod 12, stdAddChar (-(j * t))) = 0 := by
  have h := AddChar.sum_mulShift (R := ZMod 12) (-t) (isPrimitive_stdAddChar 12)
  rw [ite_eq_right (by simpa using ht), Nat.cast_zero] at h
  rw [← h]
  exact Finset.sum_congr rfl fun j _ => by rw [mul_neg, ← neg_mul]

/-- **Step 2 (complement) — the B.2 engine.** `Â Aᶜ t = −Â A t` for `t ≠ 0`. -/
theorem Ahat_compl {t : ZMod 12} (ht : t ≠ 0) (A : Finset (ZMod 12)) :
    Ahat Aᶜ t = - Ahat A t := by
  have hsplit : Ahat A t + Ahat Aᶜ t = ∑ j : ZMod 12, stdAddChar (-(j * t)) := by
    rw [Ahat_apply, Ahat_apply, ← Finset.sum_union (disjoint_compl_right)]
    rw [Finset.union_compl]
  rw [eq_neg_iff_add_eq_zero, add_comm, hsplit, dft_one_apply_ne ht]

open Complex in
/-- The circle character is unitary: `conj (stdAddChar x) = stdAddChar (−x)`. -/
lemma conj_stdAddChar (x : ZMod 12) :
    (starRingEnd ℂ) (stdAddChar x) = stdAddChar (-x) := by
  rw [stdAddChar_apply, stdAddChar_apply, map_neg_eq_inv, Circle.coe_inv_eq_conj]

/-- The (ordered) autocorrelation of a pc-set: the number of ordered pairs `(a,b) ∈ A×A`
    whose difference `a − b` equals `d`. This is `IVraw` graded by raw difference, not by `ivc`. -/
def autocorr (A : Finset (ZMod 12)) (d : ZMod 12) : ℕ :=
  ∑ a ∈ A, ∑ b ∈ A, if a - b = d then 1 else 0

/-- The power spectrum `|Â A|² = Â A · conj (Â A)`, as a function `ZMod 12 → ℂ`. -/
noncomputable def powerSpec (A : Finset (ZMod 12)) : ZMod 12 → ℂ :=
  fun t => Ahat A t * (starRingEnd ℂ) (Ahat A t)

/-- The power spectrum expanded as a double sum over `A × A`. -/
lemma powerSpec_apply (A : Finset (ZMod 12)) (t : ZMod 12) :
    powerSpec A t = ∑ a ∈ A, ∑ b ∈ A, stdAddChar (-(a * t)) * stdAddChar (b * t) := by
  unfold powerSpec
  rw [Ahat_apply, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [conj_stdAddChar, neg_neg]

/-- **Step 3 — THE BRIDGE.** The ordered interval-difference count is the inverse DFT of the
    power spectrum (Wiener–Khinchin / autocorrelation theorem), as complex numbers:
    `#{(a,b)∈A×A : a−b=d} = 𝓕⁻(|Â A|²) d`. -/
theorem autocorr_eq_invDFT (A : Finset (ZMod 12)) (d : ZMod 12) :
    (autocorr A d : ℂ) = 𝓕⁻ (powerSpec A) d := by
  rw [invDFT_apply]
  -- inner sum: Σ_t stdAddChar(t*d) • powerSpec A t = 12 * autocorr A d
  have key : ∑ t : ZMod 12, stdAddChar (t * d) • powerSpec A t = (12 : ℂ) * (autocorr A d : ℂ) := by
    simp only [smul_eq_mul, powerSpec_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    -- now Σ_a Σ_b Σ_t  stdAddChar(t*d) * (stdAddChar(-(a*t)) * stdAddChar(b*t))
    unfold autocorr
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    -- inner: Σ_t  stdAddChar(t*d) * (stdAddChar(-(a*t)) * stdAddChar(b*t))  =  12 * [a-b=d]
    have hmerge : ∀ t : ZMod 12,
        stdAddChar (t * d) * (stdAddChar (-(a * t)) * stdAddChar (b * t))
          = stdAddChar (t * (d - a + b)) := by
      intro t
      rw [← map_add_eq_mul, ← map_add_eq_mul]
      congr 1; ring
    rw [Finset.sum_congr rfl (fun t _ => hmerge t)]
    have horth := AddChar.sum_mulShift (R := ZMod 12) (d - a + b) (isPrimitive_stdAddChar 12)
    have hiff : (d - a + b = 0) ↔ (a - b = d) := by
      constructor
      · intro h; linear_combination -h
      · intro h; linear_combination -h
    rw [horth, ZMod.card]
    by_cases h : a - b = d
    · rw [ite_eq_left h, ite_eq_left (hiff.mpr h)]; push_cast; ring
    · rw [ite_eq_right h, ite_eq_right (fun hc => h (hiff.mp hc))]; push_cast; ring
  rw [key, smul_eq_mul, ← mul_assoc]
  norm_num

/-! ### The keystone: interval vector = inverse DFT of the power spectrum.

`ivc`/`IVraw` are the same definitions as in `IntervalVector`. -/

/-- Interval class of a difference (= `IntervalVector.ivc`). -/
def ivc (d : ZMod 12) : ℕ := min d.val (-d).val

/-- Raw (ordered) interval vector (= `IntervalVector.IVraw`). -/
def IVraw (A : Finset (ZMod 12)) (k : ℕ) : ℕ :=
  ∑ a ∈ A, ∑ b ∈ A, if ivc (a - b) = k then 1 else 0

/-- `IVraw` regraded: summing the autocorrelation over all differences of a fixed interval class
    recovers the raw interval vector. -/
lemma IVraw_eq_sum_autocorr (A : Finset (ZMod 12)) (k : ℕ) :
    IVraw A k = ∑ d ∈ Finset.univ.filter (fun d => ivc d = k), autocorr A d := by
  unfold IVraw autocorr
  symm
  -- RHS: Σ_d Σ_a Σ_b ;  push the d-sum innermost: Σ_d Σ_a Σ_b = Σ_a Σ_b Σ_d
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  -- inner: Σ_{d : ivc d = k} (if a-b=d then 1 else 0)  =  (if ivc(a-b)=k then 1 else 0)
  rw [Finset.sum_ite_eq (Finset.univ.filter (fun d => ivc d = k)) (a - b) (fun _ => (1 : ℕ))]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Keystone (B.1 ↔ D.1).** The raw interval vector is the inverse DFT of the power spectrum,
    summed over each interval class:  `IVraw A k = Σ_{ivc d = k} 𝓕⁻(|Â A|²) d`. -/
theorem IVraw_eq_invDFT_power (A : Finset (ZMod 12)) (k : ℕ) :
    (IVraw A k : ℂ) = ∑ d ∈ Finset.univ.filter (fun d => ivc d = k), 𝓕⁻ (powerSpec A) d := by
  rw [IVraw_eq_sum_autocorr]
  push_cast
  exact Finset.sum_congr rfl fun d _ => autocorr_eq_invDFT A d

/-! ### O.1 — The common-tone theorem under transposition (rides on `autocorr`).

`commonTones A k` = number of pitch classes held fixed when `A` is transposed by `k`, i.e.
`#(A ∩ Tₖ A)`. Lewin's ordered interval function makes this the autocorrelation:
`commonTones A k = #{(a,b)∈A×A : a−b=k} = autocorr A k`, hence `= 𝓕⁻(|Â A|²) k` (via Step 3).
The relation to the interval vector carries the **tritone doubling**: the `ivc`-fibre is a doubleton
`{k,−k}` for `1≤k≤5` (⇒ `IVraw A k = 2·commonTones A k`) but a singleton `{6}` at the tritone
(⇒ `IVraw A 6 = commonTones A 6` — the `T₆` fixed point, same central element as the 6-30 finding). -/

/-- The pitch classes of `A` held fixed under transposition by `k`: `#(A ∩ Tₖ A)`. -/
def commonTones (A : Finset (ZMod 12)) (k : ZMod 12) : ℕ := (A ∩ tpose k A).card

/-- `x` survives a transposition by `k` iff its preimage `x − k` is also in `A`. -/
lemma mem_tpose (k : ZMod 12) (A : Finset (ZMod 12)) (x : ZMod 12) :
    x ∈ tpose k A ↔ x - k ∈ A := by
  unfold tpose
  rw [Finset.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩; simpa using ha
  · intro h; exact ⟨x - k, h, by simp⟩

/-- Common tones as a filtered cardinality: `{x ∈ A : x − k ∈ A}`. -/
lemma commonTones_eq_card_filter (A : Finset (ZMod 12)) (k : ZMod 12) :
    commonTones A k = (A.filter (fun x => x - k ∈ A)).card := by
  unfold commonTones
  congr 1
  ext x
  simp only [Finset.mem_inter, Finset.mem_filter, mem_tpose]

/-- The autocorrelation collapses one index: `autocorr A k = #{a ∈ A : a − k ∈ A}`. -/
lemma autocorr_eq_card_filter (A : Finset (ZMod 12)) (k : ZMod 12) :
    autocorr A k = (A.filter (fun a => a - k ∈ A)).card := by
  unfold autocorr
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show (∑ b ∈ A, if a - b = k then (1 : ℕ) else 0)
        = ∑ b ∈ A, if b = a - k then (1 : ℕ) else 0 from
      Finset.sum_congr rfl fun b _ => by
        by_cases h : b = a - k
        · rw [ite_eq_left h, ite_eq_left (show a - b = k by rw [h]; ring)]
        · rw [ite_eq_right h, ite_eq_right (fun hh => h (by linear_combination -hh))]]
  rw [Finset.sum_ite_eq' A (a - k) (fun _ => (1 : ℕ))]

/-- **O.1 master identity.** Held tones under `Tₖ` = the ordered autocorrelation at `k`. -/
theorem commonTones_eq_autocorr (A : Finset (ZMod 12)) (k : ZMod 12) :
    commonTones A k = autocorr A k := by
  rw [commonTones_eq_card_filter, autocorr_eq_card_filter]

/-- **O.1, Fourier form.** Held tones under `Tₖ` are the inverse DFT of the power spectrum:
    `#(A ∩ Tₖ A) = 𝓕⁻(|Â A|²) k`. -/
theorem commonTones_eq_invDFT (A : Finset (ZMod 12)) (k : ZMod 12) :
    (commonTones A k : ℂ) = 𝓕⁻ (powerSpec A) k := by
  rw [commonTones_eq_autocorr]; exact autocorr_eq_invDFT A k

/-- At `k = 0` everything is held: `commonTones A 0 = |A|`. -/
theorem commonTones_zero (A : Finset (ZMod 12)) : commonTones A 0 = A.card := by
  rw [commonTones_eq_card_filter]
  congr 1
  exact Finset.filter_true_of_mem fun x hx => by simpa using hx

/-- Autocorrelation is even in the difference: `autocorr A (−k) = autocorr A k`
    (swap the two indices). This is what forces the `ivc`-fibre to fold `{k,−k}`. -/
theorem autocorr_neg (A : Finset (ZMod 12)) (k : ZMod 12) :
    autocorr A (-k) = autocorr A k := by
  unfold autocorr
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : a - b = k
  · rw [ite_eq_left (show b - a = -k by linear_combination -h), ite_eq_left h]
  · rw [ite_eq_right (fun hh => h (by linear_combination -hh)), ite_eq_right h]

/-- The `ivc`-fibre over a class `1 ≤ k ≤ 5` is the doubleton `{k, −k}`. -/
lemma ivc_fibre_lt (k : ℕ) (h1 : 1 ≤ k) (h5 : k ≤ 5) :
    (Finset.univ.filter (fun d : ZMod 12 => ivc d = k)) = {(k : ZMod 12), -(k : ZMod 12)} := by
  interval_cases k <;> decide

/-- The `ivc`-fibre over the tritone class `6` is the singleton `{6}` (the `T₆` fixed point). -/
lemma ivc_fibre_tritone :
    (Finset.univ.filter (fun d : ZMod 12 => ivc d = 6)) = {(6 : ZMod 12)} := by decide

/-- **O.1 interval-vector bridge, generic class.** For `1 ≤ k ≤ 5` the raw interval vector is
    *twice* the common-tone count: `IVraw A k = 2 · commonTones A k` (each unordered interval
    counted both ways). Equivalently `commonTones A k = ICV[k]` for the textbook `ICV = IVraw/2`. -/
theorem IVraw_eq_two_commonTones (A : Finset (ZMod 12)) (k : ℕ) (h1 : 1 ≤ k) (h5 : k ≤ 5) :
    IVraw A k = 2 * commonTones A (k : ZMod 12) := by
  rw [IVraw_eq_sum_autocorr, ivc_fibre_lt k h1 h5,
      Finset.sum_pair (by interval_cases k <;> decide), autocorr_neg,
      commonTones_eq_autocorr, two_mul]

/-- **O.1 tritone anomaly.** At `k = 6` the fibre is a singleton, so there is NO factor 2:
    `IVraw A 6 = commonTones A 6`. Since textbook `ICV[6] = IVraw A 6 / 2`, this is the famous
    `commonTones A 6 = 2 · ICV[6]` doubling — `T₆` fixes a note onto itself. -/
theorem IVraw_tritone (A : Finset (ZMod 12)) : IVraw A 6 = commonTones A 6 := by
  rw [IVraw_eq_sum_autocorr, ivc_fibre_tritone, Finset.sum_singleton, commonTones_eq_autocorr]

/-! ### The interval vector is the power spectrum folded over conjugate pairs.

The object `{k,−k}` that indexes the interval-vector fibres here (`ivc_fibre_lt`) is the SAME object
that indexes the dihedral blocks of the `T/I` action in the DFT basis — `InversionDFT.conjPair k`
(= `InversionDFT.block k`'s spanning frequencies). This block welds the invariant-theory side (this
file, Note #2) to the representation-theory side (`InversionDFT.lean`, Note #3): both are functions on,
or folds over, the inversion quotient `ℤ₁₂/(k∼−k)`. The fresh content is `powerSpec_neg` — that the
power spectrum is constant on each conjugate pair, hence descends to that quotient — which is exactly
why homometry (`homometric_iff_powerSpec_eq`) is equality of a function on the conjugate pairs. The
literal cross-file identity `ivc_fibre_lt k = InversionDFT.conjPair k` is left to the de-dup cleanup. -/

/-- **The DFT of a real pc-set is Hermitian: `Â(−t) = conj(Â(t))`.** Each term `stdAddChar(-(a·(−t)))`
    is the conjugate of `stdAddChar(-(a·t))` (`conj_stdAddChar`). -/
theorem Ahat_neg (A : Finset (ZMod 12)) (t : ZMod 12) :
    Ahat A (-t) = (starRingEnd ℂ) (Ahat A t) := by
  rw [Ahat_apply, Ahat_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [conj_stdAddChar]
  congr 1
  ring

/-- **The power spectrum is constant on conjugate pairs: `|Â|²(−t) = |Â|²(t)`.** Since `Â` is
    Hermitian (`Ahat_neg`), `powerSpec` descends to the inversion quotient `ℤ₁₂/(t∼−t)` — the conjugate
    pairs `{t,−t}` that also index the dihedral blocks (`InversionDFT.conjPair`). The "lives on the
    quotient" fact behind both the interval vector and the block decomposition. -/
theorem powerSpec_neg (A : Finset (ZMod 12)) (t : ZMod 12) :
    powerSpec A (-t) = powerSpec A t := by
  unfold powerSpec
  rw [Ahat_neg, Complex.conj_conj, mul_comm]

/-- **The interval vector is the power spectrum folded over the conjugate pair.**
    For `1 ≤ k ≤ 5`, `IVraw A k = 𝓕⁻(|Â|²)(k) + 𝓕⁻(|Â|²)(−k)` — the inverse DFT of the power spectrum
    summed over the conjugate pair `{k,−k}` (= `InversionDFT.conjPair k` = the dihedral block index).
    With `powerSpec_neg` the two summands coincide, recovering `IVraw = 2·commonTones`. One object —
    the conjugate pair — behind the interval vector (Note #2) and the dihedral blocks (Note #3). -/
theorem IVraw_eq_powerSpec_conjPair (A : Finset (ZMod 12)) (k : ℕ) (h1 : 1 ≤ k) (h5 : k ≤ 5) :
    (IVraw A k : ℂ) = 𝓕⁻ (powerSpec A) (k : ZMod 12) + 𝓕⁻ (powerSpec A) (-(k : ZMod 12)) := by
  have hsym : 𝓕⁻ (powerSpec A) (-(k : ZMod 12)) = 𝓕⁻ (powerSpec A) (k : ZMod 12) := by
    rw [← commonTones_eq_invDFT, ← commonTones_eq_invDFT, commonTones_eq_autocorr,
        commonTones_eq_autocorr, autocorr_neg]
  rw [hsym, ← two_mul, ← commonTones_eq_invDFT, IVraw_eq_two_commonTones A k h1 h5]
  push_cast
  ring

/-- Whole-tone scale `{0,2,4,6,8,10}`: `T₆` maps it onto itself, so all 6 notes are held —
    `commonTones = 6 = 2·ICV[6]` (here `IVraw = 6`, textbook `ICV[6] = 3`). -/
example : commonTones {0, 2, 4, 6, 8, 10} 6 = 6 := by decide
example : IVraw {0, 2, 4, 6, 8, 10} 6 = 6 := by decide
/-- C major triad `{0,4,7}`: a fifth (`k=7≡−5`) holds 1 note; matches `ICV[5] = 1`. -/
example : commonTones {0, 4, 7} 5 = 1 := by decide

/-! ### L.4 — Deep scales (rides on `IVraw`).

A pitch-class set is **deep** when its interval-class multiplicities are all distinct. Via O.1 those
multiplicities are exactly the transposition common-tone counts (doubled off the tritone), so a deep
scale is one where *every* transposition shares a different number of notes with the original — the
property that makes the diatonic scale a maximally-articulated reference (Gamer 1967, Browne 1981).
This formalizes the definition and its witnesses, not new mathematics;
in particular the chromatic aggregate is NOT deep, correcting a common misconception. -/

/-- A scale is **deep** iff its six interval-vector entries `IVraw A 1 … IVraw A 6` are all distinct. -/
def IsDeep (A : Finset (ZMod 12)) : Prop := (List.map (IVraw A) [1, 2, 3, 4, 5, 6]).Nodup

/-- **O.1 reading of deepness.** The interval-vector entries ARE the transposition common-tone counts,
    doubled on classes `1..5` and taken raw at the tritone `6` (the `T₆` fixed-point doubling). -/
theorem IVraw_list_eq_commonTones (A : Finset (ZMod 12)) :
    List.map (IVraw A) [1, 2, 3, 4, 5, 6]
      = [2 * commonTones A 1, 2 * commonTones A 2, 2 * commonTones A 3,
         2 * commonTones A 4, 2 * commonTones A 5, commonTones A 6] := by
  simp only [List.map_cons, List.map_nil]
  rw [IVraw_eq_two_commonTones A 1 (by norm_num) (by norm_num),
      IVraw_eq_two_commonTones A 2 (by norm_num) (by norm_num),
      IVraw_eq_two_commonTones A 3 (by norm_num) (by norm_num),
      IVraw_eq_two_commonTones A 4 (by norm_num) (by norm_num),
      IVraw_eq_two_commonTones A 5 (by norm_num) (by norm_num),
      IVraw_tritone A]
  norm_num

/-- **Deepness in common-tone terms.** A scale is deep iff the six counts
    `2·#(A∩T₁A), …, 2·#(A∩T₅A), #(A∩T₆A)` are all distinct. -/
theorem IsDeep_iff_commonTones_nodup (A : Finset (ZMod 12)) :
    IsDeep A ↔ [2 * commonTones A 1, 2 * commonTones A 2, 2 * commonTones A 3,
                2 * commonTones A 4, 2 * commonTones A 5, commonTones A 6].Nodup := by
  unfold IsDeep; rw [IVraw_list_eq_commonTones]

/-- **The diatonic scale `{0,2,4,5,7,9,11}` is deep** — `IVraw = [4,10,8,6,12,2]`, all distinct
    Each transposition retains a different number of notes. -/
theorem diatonic_isDeep : IsDeep {0, 2, 4, 5, 7, 9, 11} := by unfold IsDeep; decide

/-- **The augmented triad `{0,4,8}` is NOT deep** — `IVraw = [0,0,0,6,0,0]` (its `T₄`-symmetry
    collapses every class but the major third). A cheap non-deep witness. -/
theorem augmented_not_isDeep : ¬ IsDeep {0, 4, 8} := by unfold IsDeep; decide

/-! The **chromatic aggregate `ℤ₁₂` is NOT deep**: `IVraw = [24,24,24,24,24,12]`, so the multiplicities are not distinct — deep ≠ "uses all intervals".
(Not checked here.) -/

/-! ### Step 4 — Babbitt's hexachord theorem (B.2) as a DFT corollary. -/

/-- **Step 4 (Babbitt B.2).** A hexachord and its complement have equal Fourier magnitude away
    from `t = 0`:  `|A| = 6 → ∀ t ≠ 0, ‖Â A t‖ = ‖Â Aᶜ t‖`.  Since `IVraw` is determined by the
    power spectrum (`IVraw_eq_invDFT_power`), and the power spectrum is `‖Â·‖²`, this gives `A` and
    `Aᶜ` the same interval vector — Babbitt's hexachord theorem. -/
theorem hexachord_abs_eq (A : Finset (ZMod 12)) (_hA : A.card = 6) {t : ZMod 12} (ht : t ≠ 0) :
    ‖Ahat A t‖ = ‖Ahat Aᶜ t‖ := by
  rw [Ahat_compl ht, norm_neg]

/-- The power spectra of a hexachord and its complement agree off `t = 0`
    (the form actually feeding `IVraw_eq_invDFT_power`). -/
theorem hexachord_powerSpec_eq (A : Finset (ZMod 12)) (_hA : A.card = 6) {t : ZMod 12} (ht : t ≠ 0) :
    powerSpec A t = powerSpec Aᶜ t := by
  unfold powerSpec
  rw [Ahat_compl ht, map_neg, neg_mul_neg]

/-- The power spectrum at the origin is `|A|²` (the DC term: `Â A 0 = |A|`). -/
lemma powerSpec_zero (A : Finset (ZMod 12)) : powerSpec A 0 = (A.card : ℂ) * (A.card : ℂ) := by
  unfold powerSpec
  rw [Ahat_zero, map_natCast]

/-- A hexachord and its complement have the **same power spectrum at every frequency** — not just
    off `t = 0` (`hexachord_powerSpec_eq`): at `t = 0` both equal `|A|² = |Aᶜ|² = 36`. -/
theorem hexachord_powerSpec_eq_all (A : Finset (ZMod 12)) (hA : A.card = 6) :
    powerSpec A = powerSpec Aᶜ := by
  funext t
  rcases eq_or_ne t 0 with rfl | ht
  · have hc : Aᶜ.card = 6 := by rw [Finset.card_compl, ZMod.card, hA]
    rw [powerSpec_zero, powerSpec_zero, hA, hc]
  · exact hexachord_powerSpec_eq A hA ht

/-- **Babbitt's hexachord theorem (B.2 capstone).** A hexachord and its complement have the
    **same interval vector**:  `IVraw A k = IVraw Aᶜ k` for every interval class `k`. The interval
    vector is the inverse DFT of the power spectrum (`IVraw_eq_invDFT_power`), and a hexachord shares
    its full power spectrum with its complement (`hexachord_powerSpec_eq_all`) — so the interval
    content is forced to agree. (Babbitt 1955 / Lewin 1959.) -/
theorem hexachord_IVraw_eq (A : Finset (ZMod 12)) (hA : A.card = 6) (k : ℕ) :
    (IVraw A k : ℂ) = IVraw Aᶜ k := by
  rw [IVraw_eq_invDFT_power, IVraw_eq_invDFT_power, hexachord_powerSpec_eq_all A hA]

/-- **Babbitt's hexachord theorem, over ℕ.** The interval-vector entries (natural numbers) of a
    hexachord and its complement coincide. -/
theorem hexachord_IVraw_eq_nat (A : Finset (ZMod 12)) (hA : A.card = 6) (k : ℕ) :
    IVraw A k = IVraw Aᶜ k := by
  exact_mod_cast hexachord_IVraw_eq A hA k

/-! ### P1 — Homometry and the crystallographic phase problem (rides on `autocorr_eq_invDFT`).

Two pc-sets are **homometric** when they share the same autocorrelation `autocorr`. In crystallography
that autocorrelation is the **Patterson function** (Patterson 1934) and `|Â|²` is the X-ray **diffraction
intensity** (structure factor). The theorem below is the discrete **phase problem**: the Patterson function
determines, and is determined by, the power spectrum `|Â|²` (Wiener–Khinchin, `autocorr_eq_invDFT`) — but
NOT the phase of `Â`, so distinct sets can share a diffraction pattern. In music this is exactly the
**Z-relation**: same interval content, not T/I-related. Refs: Patterson (1934); Lewin / Soderberg
("homometry"); Mandereau–Andreatta–Amiot–Agon, J.Math&Music 5(2) 2011 (Z-relation ↔ Patterson). -/

/-- The **Patterson function** of a pc-set = its (ordered) autocorrelation. -/
def Patterson (A : Finset (ZMod 12)) (d : ZMod 12) : ℕ := autocorr A d

/-- Two pc-sets are **homometric** iff they have the same autocorrelation / Patterson function
    (equivalently, the same directed interval content). -/
def Homometric (A B : Finset (ZMod 12)) : Prop := ∀ d, autocorr A d = autocorr B d

/-- **P1 — the discrete phase problem.** Two pc-sets are homometric iff they have the same power
    spectrum `|Â|²`. Autocorrelation and diffraction intensity determine each other (Wiener–Khinchin);
    the information lost — what homometry cannot see — is the PHASE of `Â`. -/
theorem homometric_iff_powerSpec_eq (A B : Finset (ZMod 12)) :
    Homometric A B ↔ powerSpec A = powerSpec B := by
  constructor
  · intro h
    apply dft.symm.injective
    funext d
    rw [← autocorr_eq_invDFT A d, ← autocorr_eq_invDFT B d]
    exact_mod_cast h d
  · intro h d
    have : (autocorr A d : ℂ) = (autocorr B d : ℂ) := by
      rw [autocorr_eq_invDFT, autocorr_eq_invDFT, h]
    exact_mod_cast this

/-- **P1, crystallographic form.** Homometric ⟺ equal **diffraction intensity** `|Â|²` (the structure
    factor `normSq Â`) at every frequency. The phase of `Â` is invisible to this data. -/
theorem homometric_iff_normSq_dft_eq (A B : Finset (ZMod 12)) :
    Homometric A B ↔ ∀ t, Complex.normSq (Ahat A t) = Complex.normSq (Ahat B t) := by
  rw [homometric_iff_powerSpec_eq]
  constructor
  · intro h t
    have ht := congrFun h t
    unfold powerSpec at ht
    rw [Complex.mul_conj, Complex.mul_conj] at ht
    exact_mod_cast ht
  · intro h
    funext t
    unfold powerSpec
    rw [Complex.mul_conj, Complex.mul_conj, h t]

/-- The classic **Z-related / homometric pair**: the all-interval tetrachords 4-Z15 `{0,1,4,6}` and
    4-Z29 `{0,1,3,7}` share the autocorrelation `[4,1,1,1,1,1,2,1,1,1,1,1]`,
    yet are not T/I-related — same diffraction, different phase. -/
theorem allIntervalTetrachords_homometric : Homometric {0, 1, 4, 6} {0, 1, 3, 7} := by
  unfold Homometric; decide

/-! ### P2 — The phase-taxonomy capstone: the FULL DFT is a complete invariant.

The whole "phase taxonomy" of pc-set invariants organizes around exactly how much of `Â` each
invariant retains:

  • `|Â|²` (= `powerSpec` = autocorrelation = interval vector, B.1/D.1) is **phase-BLIND** and
    therefore NOT a complete invariant — homometry collapses it: distinct sets share it
    (`allIntervalTetrachords_homometric`, the all-interval tetrachords `{0,1,4,6}`≉`{0,1,3,7}`).
  • `Â²` (= `sqSpec` = the sum/index vector, O.2) retains *some* phase — enough to split that
    homometric pair (`sumVector_distinguishes_homometric`) — but still not all of it.
  • The **FULL `Â`** (magnitude AND phase) IS a complete invariant: it determines the pc-set
    exactly (`Ahat_injective` below). The phase carries precisely the information `|Â|` discards.

This is the capstone of the taxonomy. It is not new mathematics: DFT
injectivity is classical (the transform is a `LinearEquiv`, `ZMod.dft`); the contribution is the
organization — pinning each invariant to its slice of `Â` and machine-checking the completeness
boundary that homometry sits just below. -/

/-- The indicator is `0/1`-valued, so `x ∈ A ↔ ind A x = 1` (the set is recoverable from `ind`). -/
lemma mem_iff_ind_eq_one (A : Finset (ZMod 12)) (x : ZMod 12) : x ∈ A ↔ ind A x = 1 := by
  unfold ind
  by_cases h : x ∈ A <;> simp [h]

/-- The indicator map `ind : Finset (ZMod 12) → (ZMod 12 → ℂ)` is injective: a pc-set is determined
    by its `0/1` indicator (recover membership as `ind A x = 1`, using `(1 : ℂ) ≠ 0`). -/
lemma ind_injective : Function.Injective (ind : Finset (ZMod 12) → (ZMod 12 → ℂ)) := by
  intro A B h
  ext x
  rw [mem_iff_ind_eq_one, mem_iff_ind_eq_one, h]

/-- **P2 — the complete-invariant capstone.** The full DFT `Â` determines the pitch-class SET
    exactly: `Â A = Â B → A = B`. The transform `ZMod.dft` is a `LinearEquiv` (hence injective),
    and the indicator recovers the set, so the phase of `Â` is exactly the data that completes the
    interval vector to a total invariant. -/
theorem Ahat_injective {A B : Finset (ZMod 12)} (h : Ahat A = Ahat B) : A = B :=
  ind_injective (dft.injective h)

/-- **P2, biconditional form.** Equal full DFT ⟺ equal pc-set. (`⟸` is just `congrArg`.) -/
theorem Ahat_eq_iff {A B : Finset (ZMod 12)} : Ahat A = Ahat B ↔ A = B :=
  ⟨Ahat_injective, fun h => congrArg Ahat h⟩

/-! ### The common-tone theorem under INVERSION (the sum / index vector)

Where the previous section counts tones held under *transposition* `Tₖ` (the *difference* pairing `a−b`, governed by the
interval vector / `|Â|²`, phase-blind), this one counts tones held under *inversion* `I_j(x) = j − x` — the
*sum* pairing `a+a′`, governed by the **sum (index) vector** `ISUM`. Its transform is `Â(t)²` (the
coefficient SQUARED, not `|Â|²`), so `ISUM` is **phase-DEPENDENT**: it sees exactly the phase that
homometry / the Z-relation (`|Â|²`) cannot. Combinatorial identity is classical (Lewin, *GMIT* 1987;
Rahn, *Basic Atonal Theory* 1980); the "phase ≈ pitch-class sum" intuition is Tymoczko–Yust (MCM 2019,
under transposition — a *different* theorem). Unlike O.1's interval
vector there is **no tritone factor-2**: `ISUM` counts the ordered pair `(a, j−a)` directly, the held
axis tone `x` (`2x = j`, even `j`) contributing the diagonal pair `(x,x)` exactly once. -/

/-- Inversion image `I_j A = {j − a : a ∈ A}` (axis `j/2`). -/
def inv (j : ZMod 12) (A : Finset (ZMod 12)) : Finset (ZMod 12) :=
  A.map ⟨(j - ·), sub_right_injective⟩

/-- `x` survives the inversion `I_j` iff its partner `j − x` is also in `A`. -/
lemma mem_inv (j : ZMod 12) (A : Finset (ZMod 12)) (x : ZMod 12) :
    x ∈ inv j A ↔ j - x ∈ A := by
  unfold inv
  rw [Finset.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩; simpa using ha
  · intro h; exact ⟨j - x, h, by simp⟩

/-- Pitch classes of `A` held fixed under inversion `I_j`: `#(A ∩ I_j A)`. -/
def commonTonesInv (A : Finset (ZMod 12)) (j : ZMod 12) : ℕ := (A ∩ inv j A).card

/-- **The sum (index) vector** `ISUM(A)(j) = #{(a,b) ∈ A×A : a + b = j}` — the sum-pairing count. -/
def sumcorr (A : Finset (ZMod 12)) (j : ZMod 12) : ℕ :=
  ∑ a ∈ A, ∑ b ∈ A, if a + b = j then 1 else 0

/-- The **sum spectrum**: the SQUARE of the coefficient (not its squared magnitude). -/
noncomputable def sqSpec (A : Finset (ZMod 12)) : ZMod 12 → ℂ :=
  fun t => Ahat A t * Ahat A t

/-- `sqSpec = Â²` — and the phase is retained (contrast `powerSpec = Â · conj Â = |Â|²`). -/
lemma sqSpec_eq_sq (A : Finset (ZMod 12)) (t : ZMod 12) : sqSpec A t = (Ahat A t) ^ 2 := by
  rw [sqSpec, sq]

/-- The sum spectrum expanded as a double sum over `A × A`. -/
lemma sqSpec_apply (A : Finset (ZMod 12)) (t : ZMod 12) :
    sqSpec A t = ∑ a ∈ A, ∑ b ∈ A, stdAddChar (-(a * t)) * stdAddChar (-(b * t)) := by
  unfold sqSpec
  rw [Ahat_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]

/-- Common tones under `I_j` as a filtered cardinality: `{x ∈ A : j − x ∈ A}`. -/
lemma commonTonesInv_eq_card_filter (A : Finset (ZMod 12)) (j : ZMod 12) :
    commonTonesInv A j = (A.filter (fun x => j - x ∈ A)).card := by
  unfold commonTonesInv
  congr 1
  ext x
  simp only [Finset.mem_inter, Finset.mem_filter, mem_inv]

/-- The sum vector collapses one index: `sumcorr A j = #{a ∈ A : j − a ∈ A}`. -/
lemma sumcorr_eq_card_filter (A : Finset (ZMod 12)) (j : ZMod 12) :
    sumcorr A j = (A.filter (fun a => j - a ∈ A)).card := by
  unfold sumcorr
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show (∑ b ∈ A, if a + b = j then (1 : ℕ) else 0)
        = ∑ b ∈ A, if b = j - a then (1 : ℕ) else 0 from
      Finset.sum_congr rfl fun b _ => by
        by_cases h : b = j - a
        · rw [ite_eq_left h, ite_eq_left (show a + b = j by rw [h]; ring)]
        · rw [ite_eq_right h, ite_eq_right (fun hh => h (by linear_combination hh))]]
  rw [Finset.sum_ite_eq' A (j - a) (fun _ => (1 : ℕ))]

/-- **O.2 master identity.** Held tones under `I_j` = the sum (index) vector at `j`:
    `#(A ∩ I_j A) = #{(a,b) ∈ A×A : a + b = j}`. (Lewin/Rahn.) -/
theorem commonTonesInv_eq_sumcorr (A : Finset (ZMod 12)) (j : ZMod 12) :
    commonTonesInv A j = sumcorr A j := by
  rw [commonTonesInv_eq_card_filter, sumcorr_eq_card_filter]

/-- **O.2, the phase-dependent Fourier form.** The sum vector is the inverse DFT of the SQUARED
    coefficient: `#{(a,b)∈A×A : a+b=j} = 𝓕⁻(Â A ²) j`. Where O.1's `|Â|²` discards the phase,
    here the phase survives — this is why `ISUM` distinguishes some homometric sets. -/
theorem sumcorr_eq_invDFT (A : Finset (ZMod 12)) (j : ZMod 12) :
    (sumcorr A j : ℂ) = 𝓕⁻ (sqSpec A) j := by
  rw [invDFT_apply]
  have key : ∑ t : ZMod 12, stdAddChar (t * j) • sqSpec A t = (12 : ℂ) * (sumcorr A j : ℂ) := by
    simp only [smul_eq_mul, sqSpec_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    unfold sumcorr
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hmerge : ∀ t : ZMod 12,
        stdAddChar (t * j) * (stdAddChar (-(a * t)) * stdAddChar (-(b * t)))
          = stdAddChar (t * (j - a - b)) := by
      intro t
      rw [← map_add_eq_mul, ← map_add_eq_mul]
      congr 1; ring
    rw [Finset.sum_congr rfl (fun t _ => hmerge t)]
    have horth := AddChar.sum_mulShift (R := ZMod 12) (j - a - b) (isPrimitive_stdAddChar 12)
    have hiff : (j - a - b = 0) ↔ (a + b = j) := by
      constructor
      · intro h; linear_combination -h
      · intro h; linear_combination -h
    rw [horth, ZMod.card]
    by_cases h : a + b = j
    · rw [ite_eq_left h, ite_eq_left (hiff.mpr h)]; push_cast; ring
    · rw [ite_eq_right h, ite_eq_right (fun hc => h (hiff.mp hc))]; push_cast; ring
  rw [key, smul_eq_mul, ← mul_assoc]
  norm_num

/-- **O.2, Fourier form.** Held tones under `I_j` are the inverse DFT of `Â²`: `#(A ∩ I_j A) = 𝓕⁻(Â A ²) j`. -/
theorem commonTonesInv_eq_invDFT (A : Finset (ZMod 12)) (j : ZMod 12) :
    (commonTonesInv A j : ℂ) = 𝓕⁻ (sqSpec A) j := by
  rw [commonTonesInv_eq_sumcorr]; exact sumcorr_eq_invDFT A j

/-- **Phase visibility (the headline).** The homometric pair 4-Z15 `{0,1,4,6}` / 4-Z29 `{0,1,3,7}`
    share the interval vector (`allIntervalTetrachords_homometric`, i.e. equal `|Â|²`), yet the
    inversional common-tone count tells them apart: about axis `j = 0` one holds 2 tones, the other 1.
    The sum/index vector (`Â²`) sees the phase the interval vector (`|Â|²`) cannot. -/
theorem sumVector_distinguishes_homometric :
    commonTonesInv {0, 1, 4, 6} 0 ≠ commonTonesInv {0, 1, 3, 7} 0 := by decide

/-- C major `{0,4,7}`, axis `j = 0`: one common tone (the held pc `0`). -/
example : commonTonesInv {0, 4, 7} 0 = 1 := by decide
/-- Whole-tone `{0,2,4,6,8,10}`, axis `j = 0`: inversionally symmetric, all 6 held. -/
example : commonTonesInv {0, 2, 4, 6, 8, 10} 0 = 6 := by decide

/-! ### Rhythmic Oddity Property (Chemillier–Truchet 2003)

A cyclic rhythm `A ⊆ ℤₙ` has the **Rhythmic Oddity Property** when it cannot be split into two arcs of
equal length — equivalently (for `n = 12`, `n/2 = 6`) no two onsets are **antipodal** (differ by the
tritone `6`). This is the SAME `T₆` central element as the 6-30 finding and the tritone factor in O.1:
ROP ⟺ the autocorrelation / interval-vector entry at the tritone vanishes. -/

/-- **N.1 — ROP.** `A` has the Rhythmic Oddity Property iff it is disjoint from its tritone-transpose,
    i.e. no onset has an antipode (a partner 6 apart). -/
def HasROP (A : Finset (ZMod 12)) : Prop := Disjoint A (tpose 6 A)

/-- ROP ⟺ no tones are held under the tritone transposition `T₆`. -/
theorem rop_iff_commonTones_zero (A : Finset (ZMod 12)) :
    HasROP A ↔ commonTones A 6 = 0 := by
  rw [HasROP, commonTones, Finset.card_eq_zero, Finset.disjoint_iff_inter_eq_empty]

/-- ROP ⟺ the autocorrelation vanishes at the tritone (`autocorr A 6 = 0`). -/
theorem rop_iff_autocorr_zero (A : Finset (ZMod 12)) :
    HasROP A ↔ autocorr A 6 = 0 := by
  rw [rop_iff_commonTones_zero, commonTones_eq_autocorr]

/-- ROP ⟺ the interval vector's tritone entry vanishes (`IVraw A 6 = 0`) — the B.1 face. -/
theorem rop_iff_IVraw_tritone_zero (A : Finset (ZMod 12)) :
    HasROP A ↔ IVraw A 6 = 0 := by
  rw [rop_iff_commonTones_zero, ← IVraw_tritone]

/-- **Lopsidedness bound (pigeonhole).** ROP forces at most `n/2 = 6` onsets: `A` and its disjoint
    tritone-copy `T₆ A` have equal size and together fit inside `ℤ₁₂`, so `2|A| ≤ 12`.
    Corollary: no 7-subset of `ℤ₁₂` is ROP. -/
theorem rop_card_le (A : Finset (ZMod 12)) (h : HasROP A) : A.card ≤ 6 := by
  have hcard : (tpose 6 A).card = A.card := by rw [tpose, Finset.card_map]
  have hunion : (A ∪ tpose 6 A).card = A.card + (tpose 6 A).card :=
    Finset.card_union_of_disjoint h
  have hle : (A ∪ tpose 6 A).card ≤ 12 := by
    simpa using Finset.card_le_univ (A ∪ tpose 6 A)
  rw [hunion, hcard] at hle
  omega

/-- The cluster `{0,1,2,3,4,5}` is ROP and **tight** (`|A| = 6 = n/2`). -/
example : HasROP {0, 1, 2, 3, 4, 5} := by rw [rop_iff_commonTones_zero]; decide
/-- The whole-tone scale is maximally non-ROP: `T₆` maps it onto itself (`autocorr 6 = 6`). -/
example : ¬ HasROP {0, 2, 4, 6, 8, 10} := by rw [rop_iff_commonTones_zero]; decide
/-- The diatonic scale is not ROP — it contains the tritone `5–11` (`autocorr 6 = 2`). -/
example : ¬ HasROP {0, 2, 4, 5, 7, 9, 11} := by rw [rop_iff_commonTones_zero]; decide

/-! ### Set-class completeness: the T/I-orbit ⟺ DFT-up-to-phase characterization.

That no two of the 224 T/I orbits share their DFT up to phase is here a
THEOREM over all of `ZMod 12`. The point: membership of `B` in the T/I-orbit of `A` (`B = Tₖ A`
for some `k`, or `B = I_j A` for some `j`) is EXACTLY the statement that `B̂` equals `Â` up to a
transposition phase ramp `stdAddChar(−k·t)`, or up to conjugation-plus-ramp. The forward maps are
the existing `Ahat_tpose` / `Ahat_inv`; injectivity (`Ahat_injective`) supplies the converses. The
completeness of the set-class fingerprint thus follows from DFT injectivity, not from enumeration. -/

/-- **Inversion analog of `Ahat_tpose`.** `Â (I_j A) t = stdAddChar(−j·t) · conj(Â A t)`. The
    conjugate appears because `I_j` reflects the sum, turning `stdAddChar(−(a·t))` into
    `stdAddChar(a·t) = conj(stdAddChar(−(a·t)))`. -/
theorem Ahat_inv (j : ZMod 12) (A : Finset (ZMod 12)) (t : ZMod 12) :
    Ahat (inv j A) t = stdAddChar (-(j * t)) * (starRingEnd ℂ) (Ahat A t) := by
  rw [Ahat_apply, Ahat_apply, inv, Finset.sum_map, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [conj_stdAddChar, neg_neg, ← map_add_eq_mul]
  congr 1
  ring

/-- **Transposition ⟺ DFT ramp.** `B = Tₖ A` iff `B̂ = stdAddChar(−k·t) · Â A` pointwise.
    Forward is `Ahat_tpose`; backward is `Ahat_injective`. -/
theorem tpose_iff_Ahat_ramp (k : ZMod 12) (A B : Finset (ZMod 12)) :
    B = tpose k A ↔ Ahat B = fun t => stdAddChar (-(k * t)) * Ahat A t := by
  constructor
  · intro h; subst h; funext t; exact Ahat_tpose k A t
  · intro h; apply Ahat_injective; rw [h]; funext t; exact (Ahat_tpose k A t).symm

/-- **Inversion ⟺ conjugated DFT ramp.** `B = I_j A` iff `B̂ = stdAddChar(−j·t) · conj(Â A)`
    pointwise. Forward is `Ahat_inv`; backward is `Ahat_injective`. -/
theorem inv_iff_Ahat_conj_ramp (j : ZMod 12) (A B : Finset (ZMod 12)) :
    B = inv j A ↔ Ahat B = fun t => stdAddChar (-(j * t)) * (starRingEnd ℂ) (Ahat A t) := by
  constructor
  · intro h; subst h; funext t; exact Ahat_inv j A t
  · intro h; apply Ahat_injective; rw [h]; funext t; exact (Ahat_inv j A t).symm

/-- **Set-class completeness, the headline.** `B` lies in the T/I-orbit of `A`
    (`B = Tₖ A` for some `k`, or `B = I_j A` for some `j`) IFF its DFT `B̂` equals `Â` up to a
    transposition ramp, or up to conjugation-plus-ramp. The set-class fingerprint is therefore a
    COMPLETE invariant of the orbit — the "0 collisions" computation made into a theorem over all
    of `ZMod 12`, with DFT injectivity (`Ahat_injective`) as the engine. -/
theorem setClass_iff_Ahat_mod_phase (A B : Finset (ZMod 12)) :
    ((∃ k, B = tpose k A) ∨ (∃ j, B = inv j A)) ↔
      ((∃ k, Ahat B = fun t => stdAddChar (-(k * t)) * Ahat A t) ∨
       (∃ j, Ahat B = fun t => stdAddChar (-(j * t)) * (starRingEnd ℂ) (Ahat A t))) := by
  constructor
  · rintro (⟨k, hk⟩ | ⟨j, hj⟩)
    · exact Or.inl ⟨k, (tpose_iff_Ahat_ramp k A B).mp hk⟩
    · exact Or.inr ⟨j, (inv_iff_Ahat_conj_ramp j A B).mp hj⟩
  · rintro (⟨k, hk⟩ | ⟨j, hj⟩)
    · exact Or.inl ⟨k, (tpose_iff_Ahat_ramp k A B).mpr hk⟩
    · exact Or.inr ⟨j, (inv_iff_Ahat_conj_ramp j A B).mpr hj⟩

/-! ### The real-space TRIPLE CORRELATION: the missing middle row of the taxonomy.

The phase taxonomy so far has a 2nd-order row (`|Â|²` = interval vector = autocorrelation, phase-blind,
collapsed by homometry) and the full-`Â` capstone (complete invariant, all phase). The **triple
correlation** `triple A j k = #{x : x, x−j, x−k ∈ A}` is the missing *middle* row: a **3rd-order**,
**phase-blind** (built from real-space membership only), **transposition-invariant** statistic whose
Fourier dual is the **bispectrum** `Â(t₁)·Â(t₂)·conj Â(t₁+t₂)`. Crucially it **resolves homometry**:
it tells apart the all-interval tetrachords 4-Z15 `{0,1,4,6}` / 4-Z29 `{0,1,3,7}` that `|Â|²` cannot
(`carterPair_triple_distinct`). It is genuinely *finer* than the interval vector yet still a real,
combinatorial, transposition-invariant object — the classical reason the triple correlation /
bispectrum reconstructs a signal up to translation where the power spectrum fails. It is **not**
inversion-invariant (`triple_not_inversionInvariant`), so it sits strictly between the T-orbit and the
full T/I data: folded by inversion it would complete to a T/I invariant. Refs: the 3-deck / triple
correlation of combinatorics; bispectral reconstruction (Tukey); Amiot's DFT-of-pc-sets program. -/

/-- The **triple correlation** of a pc-set: the number of pitch classes `x` with `x`, `x−j`, `x−k`
    all in `A` (real-space 3-deck). Equivalently `#(A ∩ Tⱼ A ∩ Tₖ A)` since `x ∈ Tⱼ A ↔ x−j ∈ A`. -/
def triple (A : Finset (ZMod 12)) (j k : ZMod 12) : ℕ := (A ∩ tpose j A ∩ tpose k A).card

/-- `tpose` distributes over intersection (it is a `Finset.map` by an embedding). -/
lemma tpose_inter (m : ZMod 12) (A B : Finset (ZMod 12)) :
    tpose m (A ∩ B) = tpose m A ∩ tpose m B := by
  unfold tpose; rw [Finset.map_inter]

/-- Translations commute: `Tⱼ (Tₘ A) = Tₘ (Tⱼ A)` (both shift by `j + m`). -/
lemma tpose_tpose (j m : ZMod 12) (A : Finset (ZMod 12)) :
    tpose j (tpose m A) = tpose m (tpose j A) := by
  ext x
  rw [mem_tpose, mem_tpose, mem_tpose, mem_tpose]
  constructor
  · intro h; rw [show x - m - j = x - j - m by ring]; exact h
  · intro h; rw [show x - j - m = x - m - j by ring]; exact h

/-- The cardinality is unchanged by `tpose` (it is an injective `Finset.map`). -/
lemma card_tpose (m : ZMod 12) (A : Finset (ZMod 12)) : (tpose m A).card = A.card := by
  unfold tpose; rw [Finset.card_map]

/-- **Transposition invariance.** The triple correlation is unchanged when the whole
    set is transposed: `triple (Tₘ A) j k = triple A j k`. (`Tₘ` commutes with `Tⱼ`/`Tₖ` and
    distributes over `∩`, then `card` is map-invariant.) This is the defining feature: a 3rd-order
    statistic that, like the interval vector, is blind to absolute transposition. -/
theorem triple_tpose_invariant (m : ZMod 12) (A : Finset (ZMod 12)) (j k : ZMod 12) :
    triple (tpose m A) j k = triple A j k := by
  unfold triple
  rw [tpose_tpose j m A, tpose_tpose k m A, ← tpose_inter, ← tpose_inter, card_tpose]

/-- **Homometry resolution.** The triple correlation distinguishes the all-interval
    tetrachords 4-Z15 `{0,1,4,6}` and 4-Z29 `{0,1,3,7}`, which are homometric
    (`allIntervalTetrachords_homometric`: equal interval vector `|Â|²`) yet NOT T/I-related. At
    `(j,k) = (1,6)` the first holds `0`, the second `1` — the 3rd-order statistic sees what the
    2nd-order `|Â|²` is blind to. This is the Z-relation broken by the bispectrum. -/
theorem carterPair_triple_distinct :
    ∃ j k, triple {0, 1, 4, 6} j k ≠ triple {0, 1, 3, 7} j k :=
  ⟨1, 6, by decide⟩

/-- **Not inversion-invariant.** The triple correlation distinguishes a set from its
    inversion `I₀ A = inv 0 A`: at `A = {0,1,4,6}`, `(j,k) = (1,4)`, `A` holds `0` but `I₀ A` holds
    `1`. So `triple` is strictly finer than a T/I invariant — it lives between the T-orbit and the
    full T/I data; folding it by inversion would complete it to a T/I-complete object. -/
theorem triple_not_inversionInvariant :
    ∃ (A : Finset (ZMod 12)) (j k : ZMod 12), triple A j k ≠ triple (inv 0 A) j k :=
  ⟨{0, 1, 4, 6}, 1, 4, by decide⟩

/-! ### Parity marginals of the index vector are phase-blind

The per-frequency index vector `sumcorr A j = ISUM` is phase-AWARE: its transform is `Â²` (`sqSpec`),
so it splits homometric pairs (`sumVector_distinguishes_homometric`). A refinement:
its **parity marginals** — the partial sums over even `j` and over odd `j` — are PHASE-BLIND, i.e.
functions of `|Â|²` (`powerSpec`) alone. The mechanism is the recurring `{0,6}` 2-torsion (inversion-
fixed frequencies): `Σ_{j even} f(j) = ½(Σ_j f(j) + Σ_j (−1)ʲ f(j))`, and for `f = 𝓕⁻(sqSpec)` the two
character sums collapse to `sqSpec 0 = |A|²` and `sqSpec 6 = Â(6)²`; since `Â(6)` is real (`6 = −6`),
`Â(6)² = |Â(6)|² = powerSpec 6`. So the marginals see only `|Â|²` at the inversion-fixed `t ∈ {0,6}`.

Combinatorially the same fact is the parity bridge `a+b even ⟺ a,b same parity ⟺ a−b even`, so the
even/odd marginal of the SUM count equals the even/odd marginal of the DIFFERENCE count (autocorrelation,
the canonical phase-blind statistic). -/

/-- The even residues of `ℤ₁₂` (the `{0,2,4,6,8,10}` index set; `2·ℤ₆`, contains the `{0,6}` 2-torsion). -/
def evenSet : Finset (ZMod 12) := {0, 2, 4, 6, 8, 10}

/-- The odd residues of `ℤ₁₂` (the `{1,3,5,7,9,11}` index set). -/
def oddSet : Finset (ZMod 12) := {1, 3, 5, 7, 9, 11}

/-- A marginal of `sumcorr` over an index set `S` counts the ordered pairs whose SUM lands in `S`:
    `Σ_{j∈S} sumcorr A j = #{(a,b)∈A² : a+b ∈ S}`. -/
lemma sum_sumcorr_eq (A : Finset (ZMod 12)) (S : Finset (ZMod 12)) :
    ∑ j ∈ S, sumcorr A j = ∑ a ∈ A, ∑ b ∈ A, if a + b ∈ S then 1 else 0 := by
  unfold sumcorr
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_ite_eq S (a + b) (fun _ => (1 : ℕ))]

/-- A marginal of `autocorr` over a difference set `D` counts the ordered pairs whose DIFFERENCE lands
    in `D`: `Σ_{d∈D} autocorr A d = #{(a,b)∈A² : a−b ∈ D}`. -/
lemma sum_autocorr_eq (A : Finset (ZMod 12)) (D : Finset (ZMod 12)) :
    ∑ d ∈ D, autocorr A d = ∑ a ∈ A, ∑ b ∈ A, if a - b ∈ D then 1 else 0 := by
  unfold autocorr
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_ite_eq D (a - b) (fun _ => (1 : ℕ))]

/-- **The parity bridge.** For every `a,b ∈ ℤ₁₂`, `a+b` is even iff `a−b` is even (they differ by `2b`).
    Pointwise over all `144` pairs by `decide`; this is what makes the marginals phase-blind. -/
lemma sum_mem_evenSet_iff_diff (a b : ZMod 12) :
    (a + b ∈ evenSet) ↔ (a - b ∈ evenSet) := by
  unfold evenSet; revert a b; decide

/-- Likewise for the odd index set. -/
lemma sum_mem_oddSet_iff_diff (a b : ZMod 12) :
    (a + b ∈ oddSet) ↔ (a - b ∈ oddSet) := by
  unfold oddSet; revert a b; decide

/-- **Parity marginal = autocorrelation marginal (even).** The even-`j` marginal of the index vector
    equals the even-`d` marginal of the autocorrelation — the sum count and the difference count agree
    on each parity class (`a+b even ⟺ a−b even`). -/
theorem sum_evenSet_sumcorr_eq_autocorr (A : Finset (ZMod 12)) :
    ∑ j ∈ evenSet, sumcorr A j = ∑ d ∈ evenSet, autocorr A d := by
  rw [sum_sumcorr_eq, sum_autocorr_eq]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [sum_mem_evenSet_iff_diff a b]

/-- **Parity marginal = autocorrelation marginal (odd).** -/
theorem sum_oddSet_sumcorr_eq_autocorr (A : Finset (ZMod 12)) :
    ∑ j ∈ oddSet, sumcorr A j = ∑ d ∈ oddSet, autocorr A d := by
  rw [sum_sumcorr_eq, sum_autocorr_eq]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [sum_mem_oddSet_iff_diff a b]

/-- `autocorr A 0 = |A|`: every element pairs with itself (the diagonal), nothing else has `a−a=0`. -/
lemma autocorr_zero (A : Finset (ZMod 12)) : autocorr A 0 = A.card := by
  rw [← commonTones_eq_autocorr, commonTones_zero]

/-- **ID-8 (odd marginal, the ℕ form).** The odd-index marginal of the index vector folds onto the
    short autocorrelation classes: `Σ_{j∈{1,3,5,7,9,11}} sumcorr A j = 2·(c₁+c₃+c₅)` where `cₖ =
    autocorr A k`. (`autocorr_neg`: `c₇=c₅, c₉=c₃, c₁₁=c₁`.) -/
theorem sumcorr_odd_marginal (A : Finset (ZMod 12)) :
    ∑ j ∈ oddSet, sumcorr A j
      = 2 * (autocorr A 1 + autocorr A 3 + autocorr A 5) := by
  rw [sum_oddSet_sumcorr_eq_autocorr]
  show autocorr A 1 + (autocorr A 3 + (autocorr A 5 + (autocorr A 7
        + (autocorr A 9 + (autocorr A 11 + 0))))) = _
  rw [show (7 : ZMod 12) = -5 by decide, show (9 : ZMod 12) = -3 by decide,
      show (11 : ZMod 12) = -1 by decide, autocorr_neg, autocorr_neg, autocorr_neg]
  ring

/-- **ID-7 (even marginal, the ℕ form).** The even-index marginal: `Σ_{j∈{0,2,4,6,8,10}} sumcorr A j
      = |A| + 2·(c₂+c₄) + c₆` where `cₖ = autocorr A k`. The lone `|A|` is the diagonal `c₀ = |A|`
    and the lone `c₆` is the tritone self-fixed class (`6 = −6`), both 2-torsion — the same `{0,6}`. -/
theorem sumcorr_even_marginal (A : Finset (ZMod 12)) :
    ∑ j ∈ evenSet, sumcorr A j
      = A.card + 2 * (autocorr A 2 + autocorr A 4) + autocorr A 6 := by
  rw [sum_evenSet_sumcorr_eq_autocorr]
  show autocorr A 0 + (autocorr A 2 + (autocorr A 4 + (autocorr A 6
        + (autocorr A 8 + (autocorr A 10 + 0))))) = _
  rw [autocorr_zero, show (8 : ZMod 12) = -4 by decide, show (10 : ZMod 12) = -2 by decide,
      autocorr_neg, autocorr_neg]
  ring

/-! #### The phase-blind ℂ-form (THE PAYLOAD): marginals = `(|Â(0)|² ± |Â(6)|²)/2`.

The even/odd marginals depend ONLY on `powerSpec` (= `|Â|²`) at the inversion-fixed frequencies `0`
and `6` — even though the per-`j` index vector itself is phase-aware. Proved via the DFT route on
`sumcorr_eq_invDFT`: summing `𝓕⁻(sqSpec)` against the even/odd parity sets picks out exactly `sqSpec 0`
and `sqSpec 6`, and `Â(6)` is real so `sqSpec 6 = Â(6)² = |Â(6)|² = powerSpec 6`. -/

/-- `sqSpec A 0 = powerSpec A 0 = |A|²` (the DC term is real and equals `|Â(0)|²`). -/
lemma sqSpec_zero (A : Finset (ZMod 12)) : sqSpec A 0 = powerSpec A 0 := by
  rw [sqSpec, powerSpec, Ahat_zero, map_natCast]

/-- `6` is its own negative as a multiplier mod `12`: `-(a·6) = a·6` for every `a` (the `2`-torsion). -/
lemma neg_mul_six (a : ZMod 12) : -(a * 6) = a * 6 := by revert a; decide

/-- `Â(6)` is real: `conj (Â A 6) = Â A 6`. Because `6 = −6` in `ℤ₁₂`, the inversion-fixed frequency
    is its own conjugate (`stdAddChar(−(a·6))` is `±1`). This is the `{0,6}` 2-torsion made analytic. -/
lemma Ahat_six_real (A : Finset (ZMod 12)) : (starRingEnd ℂ) (Ahat A 6) = Ahat A 6 := by
  rw [Ahat_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [conj_stdAddChar, neg_neg, neg_mul_six]

/-- `sqSpec A 6 = powerSpec A 6 = |Â(6)|²` (the tritone frequency is real, so its square is its
    squared magnitude). The second inversion-fixed point of the `{0,6}` 2-torsion. -/
lemma sqSpec_six (A : Finset (ZMod 12)) : sqSpec A 6 = powerSpec A 6 := by
  rw [sqSpec, powerSpec, Ahat_six_real]

/-- The even and odd index sets PARTITION `ℤ₁₂` (their disjoint union is the universe). -/
lemma evenSet_union_oddSet : evenSet ∪ oddSet = Finset.univ := by
  unfold evenSet oddSet; decide

lemma evenSet_disjoint_oddSet : Disjoint evenSet oddSet := by
  unfold evenSet oddSet; decide

/-- `powerSpec` as the FORWARD DFT of the autocorrelation: `powerSpec A t = Σ_d stdAddChar(−(d·t))·c(d)`
    (apply `𝓕` to `autocorr_eq_invDFT`; `𝓕∘𝓕⁻ = id`). -/
lemma powerSpec_eq_dft_autocorr (A : Finset (ZMod 12)) (t : ZMod 12) :
    powerSpec A t = ∑ d : ZMod 12, stdAddChar (-(d * t)) * (autocorr A d : ℂ) := by
  have hid : powerSpec A = 𝓕 (fun d => (autocorr A d : ℂ)) := by
    have hcast : (fun d => (autocorr A d : ℂ)) = 𝓕⁻ (powerSpec A) := by
      funext d; exact autocorr_eq_invDFT A d
    rw [hcast, dft.apply_symm_apply]
  rw [hid, dft_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [smul_eq_mul]

/-- `powerSpec A 0` is the TOTAL pair count `Σ_d c(d) = |A|²` (forward DFT at the DC frequency). -/
lemma powerSpec_zero_eq_sum_autocorr (A : Finset (ZMod 12)) :
    powerSpec A 0 = ∑ d : ZMod 12, (autocorr A d : ℂ) := by
  rw [powerSpec_eq_dft_autocorr]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [mul_zero, neg_zero, map_zero_eq_one, one_mul]

/-- The tritone character value: `stdAddChar (6 : ℤ₁₂) = exp(πi) = −1`. The analytic root of the
    `(−1)ᵈ` sign that makes frequency `6` a parity detector. -/
lemma stdAddChar_six : stdAddChar (6 : ZMod 12) = -1 := by
  have hc : ((6 : ℤ) : ZMod 12) = (6 : ZMod 12) := by norm_cast
  rw [← hc, stdAddChar_coe, ← Complex.exp_pi_mul_I]
  congr 1
  push_cast
  ring

/-- On the even residues `stdAddChar(−(d·6)) = 1`; on the odd residues it is `−1` (since `d·6` is `0`
    or `6` in `ℤ₁₂`). The `{0,6}`-frequency reads off the parity of `d`. -/
lemma stdAddChar_neg_mul_six (d : ZMod 12) :
    stdAddChar (-(d * 6)) = if d ∈ evenSet then (1 : ℂ) else -1 := by
  by_cases h : d ∈ evenSet
  · rw [ite_eq_left h, show (-(d * 6)) = 0 from by revert h; unfold evenSet; revert d; decide,
        map_zero_eq_one]
  · rw [ite_eq_right h, show (-(d * 6)) = 6 from by
        revert h; unfold evenSet; revert d; decide, stdAddChar_six]

/-- `powerSpec A 6` is the SIGNED pair count `Σ_d (−1)ᵈ c(d) = Σ_even c − Σ_odd c` (forward DFT at the
    inversion-fixed tritone frequency `6`; `stdAddChar(−6d) = (−1)ᵈ`). -/
lemma powerSpec_six_eq_signed_autocorr (A : Finset (ZMod 12)) :
    powerSpec A 6 = ∑ d ∈ evenSet, (autocorr A d : ℂ) - ∑ d ∈ oddSet, (autocorr A d : ℂ) := by
  rw [powerSpec_eq_dft_autocorr, ← evenSet_union_oddSet,
      Finset.sum_union evenSet_disjoint_oddSet, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun d hd => ?_
    rw [stdAddChar_neg_mul_six, ite_eq_left hd, one_mul]
  · refine Finset.sum_congr rfl fun d hd => ?_
    rw [stdAddChar_neg_mul_six, ite_eq_right (Finset.disjoint_right.mp evenSet_disjoint_oddSet hd),
        neg_one_mul]

/-- **The phase-blind payload (even, ℂ-form).** The even-index marginal of the index vector equals
    `(|Â(0)|² + |Â(6)|²)/2 = (powerSpec 0 + powerSpec 6)/2`. It is a function of `|Â|²` alone — at the
    inversion-fixed frequencies `{0,6}` — even though `sumcorr` per-`j` is phase-aware. -/
theorem sumcorr_even_marginal_phaseblind (A : Finset (ZMod 12)) :
    ∑ j ∈ evenSet, (sumcorr A j : ℂ) = (powerSpec A 0 + powerSpec A 6) / 2 := by
  rw [powerSpec_zero_eq_sum_autocorr, powerSpec_six_eq_signed_autocorr,
      ← evenSet_union_oddSet, Finset.sum_union evenSet_disjoint_oddSet]
  -- LHS = Σ_even sumcorr = Σ_even autocorr (the parity bridge, cast to ℂ)
  have hL : ∑ j ∈ evenSet, (sumcorr A j : ℂ) = ∑ d ∈ evenSet, (autocorr A d : ℂ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum, sum_evenSet_sumcorr_eq_autocorr]
  rw [hL]; ring

/-- **The phase-blind payload (odd, ℂ-form).** The odd-index marginal equals
    `(|Â(0)|² − |Â(6)|²)/2 = (powerSpec 0 − powerSpec 6)/2`. Again `|Â|²` at `{0,6}` only. -/
theorem sumcorr_odd_marginal_phaseblind (A : Finset (ZMod 12)) :
    ∑ j ∈ oddSet, (sumcorr A j : ℂ) = (powerSpec A 0 - powerSpec A 6) / 2 := by
  rw [powerSpec_zero_eq_sum_autocorr, powerSpec_six_eq_signed_autocorr,
      ← evenSet_union_oddSet, Finset.sum_union evenSet_disjoint_oddSet]
  have hR : ∑ j ∈ oddSet, (sumcorr A j : ℂ) = ∑ d ∈ oddSet, (autocorr A d : ℂ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum, sum_oddSet_sumcorr_eq_autocorr]
  rw [hR]; ring

/-! #### The punchline witness: per-`j` index vectors DIFFER (phase-aware), marginals AGREE (phase-blind).

The homometric Z-pair 4-Z15 `{0,1,4,6}` and 4-Z29 `{0,1,3,7}` are NOT T/I-related; their index vectors
`sumcorr` differ at individual `j` (`sumVector_distinguishes_homometric` — that is why `Â²` resolves the
Z-relation). Yet their PARITY MARGINALS coincide — the phase-collapse made concrete. -/

/-- The per-`j` index vectors differ at `j = 0`: `{0,1,4,6}` holds `2`, `{0,1,3,7}` holds `1`. -/
theorem carterPair_sumcorr_differs : sumcorr {0, 1, 4, 6} 0 ≠ sumcorr {0, 1, 3, 7} 0 := by decide

/-- ...yet the EVEN-index marginals agree (phase-blind). -/
theorem carterPair_even_marginal_agree :
    ∑ j ∈ evenSet, sumcorr {0, 1, 4, 6} j = ∑ j ∈ evenSet, sumcorr {0, 1, 3, 7} j := by decide

/-- ...and the ODD-index marginals agree (phase-blind). -/
theorem carterPair_odd_marginal_agree :
    ∑ j ∈ oddSet, sumcorr {0, 1, 4, 6} j = ∑ j ∈ oddSet, sumcorr {0, 1, 3, 7} j := by decide

end Fourier

end MusicTheory
