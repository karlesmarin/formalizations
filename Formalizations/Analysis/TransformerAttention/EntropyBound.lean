/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Jensen

/-!
# Shannon entropy on N points is at most log N, with equality iff uniform

Formalizes part (i) of the positional entropy area law: for a probability vector p on a finite
nonempty type of cardinality N, -sum p log p <= log N, with equality iff p is uniform. Proved from
Mathlib's strict concavity of negMulLog via Jensen with uniform weights. Convention: Real.log,
natural logarithm, 0 log 0 = 0. Implicit hypotheses made explicit: p nonnegative, summing to 1. The
paper states (i) for `p(d) ∝ d^(−γ)` with `γ > 0` and "equality iff `γ = 0`", which is not
consistent as written (and at `N = 1` equality holds for every `γ`); what is formalized is the
Gibbs-inequality form its proof uses. Not formalized: the power-law specialization p(d) proportional
to d^(-gamma), and parts (ii) and (iii) (Euler-Maclaurin asymptotics, zeta limit).

## Main results

* `TransformerAttention.EntropyBound.entropy_le_log_card`: entropy of a probability vector on N points is at most log N
* `TransformerAttention.EntropyBound.entropy_eq_log_card_iff`: equality iff the distribution is uniform

## References

* C. Marín, *Predicting How Transformers Attend Analytic Power-Law Theory, Phase Transitions, and
  Practical Compression Tools*, Zenodo (2026), doi:10.5281/zenodo.20314038, `thm:area_law`.
-/

@[expose] public section

open Finset Real

namespace TransformerAttention.EntropyBound
variable {ι : Type*} [Fintype ι] [Nonempty ι]

private lemma card_pos' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos

private lemma sum_w : ∑ _i : ι, (1 / (Fintype.card ι : ℝ)) = 1 := by
  have := (card_pos' (ι := ι)).ne'
  simp [Finset.sum_const]

omit [Nonempty ι] in
private lemma sum_negMulLog_eq (p : ι → ℝ) :
    ∑ i, (1 / (Fintype.card ι : ℝ)) • negMulLog (p i)
      = (1 / (Fintype.card ι : ℝ)) * (-∑ i, p i * log (p i)) := by
  simp only [smul_eq_mul, ← Finset.mul_sum, negMulLog]
  congr 1
  rw [← Finset.sum_neg_distrib]
  simp

omit [Nonempty ι] in
private lemma negMulLog_inv_card :
    negMulLog (1 / (Fintype.card ι : ℝ)) = (1 / (Fintype.card ι : ℝ)) * log (Fintype.card ι) := by
  rw [negMulLog]
  simp [Real.log_inv]

/-- Part (i), inequality: the entropy of a probability distribution on `N` points is `≤ log N`
(Jensen for the concave `negMulLog` with uniform weights). -/
theorem entropy_le_log_card (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    -∑ i, p i * log (p i) ≤ log (Fintype.card ι) := by
  have hN := card_pos' (ι := ι)
  have h := concaveOn_negMulLog.le_map_sum (t := univ) (w := fun _ => 1 / (Fintype.card ι : ℝ))
    (p := p) (fun _ _ => by positivity) sum_w (fun i _ => hp i)
  rw [sum_negMulLog_eq, ← Finset.smul_sum, hsum, smul_eq_mul, mul_one, negMulLog_inv_card] at h
  have := (mul_le_mul_iff_of_pos_left (by positivity : (0 : ℝ) < 1 / (Fintype.card ι : ℝ))).1 h
  exact this

/-- Part (i), equality case: equality holds iff `p` is uniform (strict Jensen). -/
theorem entropy_eq_log_card_iff (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    -∑ i, p i * log (p i) = log (Fintype.card ι) ↔ ∀ i, p i = 1 / (Fintype.card ι : ℝ) := by
  have hN := card_pos' (ι := ι)
  have key := strictConcaveOn_negMulLog.map_sum_eq_iff (t := univ)
    (w := fun _ => 1 / (Fintype.card ι : ℝ)) (p := p) (fun _ _ => by positivity) sum_w
    (fun i _ => hp i)
  rw [sum_negMulLog_eq, ← Finset.smul_sum, hsum, smul_eq_mul, mul_one, negMulLog_inv_card] at key
  have hc : (1 / (Fintype.card ι : ℝ)) * log (Fintype.card ι)
      = (1 / (Fintype.card ι : ℝ)) * (-∑ i, p i * log (p i)) ↔
      -∑ i, p i * log (p i) = log (Fintype.card ι) := by
    rw [mul_right_inj' (by positivity)]
    exact eq_comm
  rw [← hc, key]
  simp

end TransformerAttention.EntropyBound