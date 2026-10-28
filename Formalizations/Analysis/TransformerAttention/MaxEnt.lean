/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FunProp

/-!
# Maximum entropy with a log-distance constraint is a power law

Among probability distributions on the distances `1, …, N` with prescribed `E[log d] = λ`, the power
law `p_γ(d) = d^(−γ)/Σ_e e^(−γ)` is the unique maximiser of Shannon entropy, and when
`0 < λ < (1/N) Σ_d log d` the exponent `γ > 0` is unique. This corrects Theorem 6.2 of «Predicting
How Transformers Attend» (Part I, v3), which omitted the condition on `λ`. Proof: Gibbs' inequality
— `Σ p log p_γ` is the same for every feasible `p`, so `H(p_γ) − H(p)` is a relative entropy,
nonnegative by `log x ≤ x − 1` and zero only at `p = p_γ`; the exponent comes from the intermediate
value theorem.

## Main results

* `MaxEntPowerLaw.maxent_power_law`: corrected MaxEnt theorem: unique γ > 0, unique entropy maximiser

## References

* C. Marín, «Predicting How Transformers Attend», Zenodo 20314038 (v3), Thm 6.2 (corregido).
* E. T. Jaynes, Phys. Rev. 106 (1957) 620; T. Cover, J. Thomas, Elements of Information Theory (2006), §12.
-/

@[expose] public section

open Finset Real

namespace MaxEntPowerLaw

/-- `E_p[log d]` for a distribution `p` on distances `1..N`. -/
noncomputable def logMean {N : ℕ} (p : Fin N → ℝ) : ℝ := ∑ i, p i * Real.log ((i : ℝ) + 1)

/-- Shannon entropy `-Σ p log p`. -/
noncomputable def entropy {N : ℕ} (p : Fin N → ℝ) : ℝ := -∑ i, p i * Real.log (p i)

/-- The power law `p_γ(d) = d^(-γ) / Σ_e e^(-γ)` on distances `1..N`. -/
noncomputable def powerLaw (N : ℕ) (γ : ℝ) (i : Fin N) : ℝ :=
  ((i : ℝ) + 1) ^ (-γ) / ∑ j : Fin N, ((j : ℝ) + 1) ^ (-γ)

/-- Unnormalised weight `d^(-γ)` written with `exp`. -/
noncomputable def wt {N : ℕ} (γ : ℝ) (i : Fin N) : ℝ := Real.exp (-γ * Real.log ((i : ℝ) + 1))

/-- Partition function. -/
noncomputable def Z (N : ℕ) (γ : ℝ) : ℝ := ∑ i : Fin N, wt γ i

theorem rpow_eq {N : ℕ} (γ : ℝ) (i : Fin N) : ((i : ℝ) + 1) ^ (-γ) = wt γ i := by
  have h : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  rw [Real.rpow_def_of_pos h, wt, mul_comm]

theorem powerLaw_eq {N : ℕ} (γ : ℝ) (i : Fin N) : powerLaw N γ i = wt γ i / Z N γ := by
  simp only [powerLaw, Z, rpow_eq]

theorem Z_pos {N : ℕ} (hN : 0 < N) (γ : ℝ) : 0 < Z N γ :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨⟨0, hN⟩, Finset.mem_univ _⟩

theorem pl_pos {N : ℕ} (hN : 0 < N) (γ : ℝ) (i : Fin N) : 0 < powerLaw N γ i := by
  rw [powerLaw_eq]; exact div_pos (Real.exp_pos _) (Z_pos hN γ)

theorem pl_sum {N : ℕ} (hN : 0 < N) (γ : ℝ) : ∑ i, powerLaw N γ i = 1 := by
  simp only [powerLaw_eq, ← Finset.sum_div]
  exact div_self (Z_pos hN γ).ne'

theorem log_pl {N : ℕ} (hN : 0 < N) (γ : ℝ) (i : Fin N) :
    Real.log (powerLaw N γ i) = -γ * Real.log ((i : ℝ) + 1) - Real.log (Z N γ) := by
  rw [powerLaw_eq, wt, Real.log_div (Real.exp_pos _).ne' (Z_pos hN γ).ne', Real.log_exp]

theorem sum_mul_log_pl {N : ℕ} (hN : 0 < N) (γ : ℝ) (p : Fin N → ℝ) (hp : ∑ i, p i = 1) :
    ∑ i, p i * Real.log (powerLaw N γ i) = -γ * logMean p - Real.log (Z N γ) := by
  calc ∑ i, p i * Real.log (powerLaw N γ i)
      = ∑ i, (-γ * (p i * Real.log ((i : ℝ) + 1)) - p i * Real.log (Z N γ)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [log_pl hN]; ring
    _ = -γ * logMean p - Real.log (Z N γ) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hp, one_mul]; rfl

/-- Termwise Gibbs inequality. -/
theorem term_gibbs (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ a * (Real.log a - Real.log b) - (a - b) ∧
      (a * (Real.log a - Real.log b) - (a - b) = 0 → a = b) := by
  rcases ha.eq_or_lt with h | h
  · subst h
    refine ⟨by simp [hb.le], fun h' => ?_⟩
    simp at h'; linarith
  · have key : a * (Real.log a - Real.log b) - (a - b) = a * ((b / a - 1) - Real.log (b / a)) := by
      rw [Real.log_div hb.ne' h.ne']; field_simp; ring
    have hx : 0 < b / a := div_pos hb h
    refine ⟨?_, fun h' => ?_⟩
    · rw [key]; exact mul_nonneg h.le (sub_nonneg.2 (Real.log_le_sub_one_of_pos hx))
    · by_contra hne
      have hne' : b / a ≠ 1 := fun e => hne ((div_eq_one_iff_eq h.ne').1 e).symm
      have := Real.log_lt_sub_one_of_pos hx hne'
      rw [key] at h'
      have : 0 < a * ((b / a - 1) - Real.log (b / a)) := mul_pos h (by linarith)
      linarith

theorem gibbs_le {N : ℕ} (hN : 0 < N) (γ : ℝ) (p : Fin N → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) (hlm : logMean p = logMean (powerLaw N γ)) :
    entropy p ≤ entropy (powerLaw N γ) ∧ (entropy p = entropy (powerLaw N γ) → p = powerLaw N γ) := by
  set q := powerLaw N γ with hq
  have hq1 : ∑ i, q i = 1 := pl_sum hN γ
  have hcross : ∑ i, p i * Real.log (q i) = ∑ i, q i * Real.log (q i) := by
    rw [hq, sum_mul_log_pl hN γ p hp1, sum_mul_log_pl hN γ _ (pl_sum hN γ), hlm]
  set t : Fin N → ℝ := fun i => p i * (Real.log (p i) - Real.log (q i)) - (p i - q i) with ht
  have hsum : ∑ i, t i = entropy q - entropy p := by
    have e1 : ∑ i, t i = ∑ i, p i * Real.log (p i) - ∑ i, p i * Real.log (q i)
        - (∑ i, p i - ∑ i, q i) := by
      simp only [ht, mul_sub, Finset.sum_sub_distrib]
    rw [e1, hp1, hq1, hcross]; unfold entropy; ring
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ t i := fun i _ => (term_gibbs (p i) (q i) (hp0 i) (pl_pos hN γ i)).1
  refine ⟨?_, fun heq => ?_⟩
  · have := Finset.sum_nonneg hnn
    linarith
  · have h0 : ∑ i, t i = 0 := by rw [hsum]; linarith
    rw [Finset.sum_eq_zero_iff_of_nonneg hnn] at h0
    funext i
    exact (term_gibbs (p i) (q i) (hp0 i) (pl_pos hN γ i)).2 (h0 i (Finset.mem_univ _))

theorem logMean_pl {N : ℕ} (_hN : 0 < N) (γ : ℝ) :
    logMean (powerLaw N γ) = (∑ i : Fin N, wt γ i * Real.log ((i : ℝ) + 1)) / Z N γ := by
  unfold logMean
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [powerLaw_eq]; ring

theorem continuous_logMean {N : ℕ} (hN : 0 < N) : Continuous fun γ : ℝ => logMean (powerLaw N γ) := by
  have : (fun γ : ℝ => logMean (powerLaw N γ))
      = fun γ => (∑ i : Fin N, wt γ i * Real.log ((i : ℝ) + 1)) / Z N γ := by
    funext γ; exact logMean_pl hN γ
  rw [this]
  have hw : ∀ i : Fin N, Continuous fun γ : ℝ => wt γ i := fun i => by unfold wt; fun_prop
  refine Continuous.div ?_ ?_ (fun γ => (Z_pos hN γ).ne')
  · exact continuous_finsetSum _ (fun i _ => (hw i).mul continuous_const)
  · exact continuous_finsetSum _ (fun i _ => hw i)

theorem logMean_zero {N : ℕ} (hN : 0 < N) :
    logMean (powerLaw N 0) = (∑ i : Fin N, Real.log ((i : ℝ) + 1)) / N := by
  rw [logMean_pl hN]
  simp [wt, Z]

theorem Z_ge_one {N : ℕ} (hN : 0 < N) (γ : ℝ) : 1 ≤ Z N γ := by
  have := Finset.single_le_sum (f := fun j : Fin N => wt γ j) (fun j _ => (Real.exp_pos _).le)
    (Finset.mem_univ (⟨0, hN⟩ : Fin N))
  simpa [wt, Z] using this

theorem logMean_le {N : ℕ} (hN : 0 < N) (γ : ℝ) (hγ : 0 ≤ γ) :
    logMean (powerLaw N γ) ≤ N * Real.exp (-γ * Real.log 2) * Real.log N := by
  rw [logMean_pl hN]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hE : 0 < Real.exp (-γ * Real.log 2) := Real.exp_pos _
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      wt γ i * Real.log ((i : ℝ) + 1) ≤ Real.exp (-γ * Real.log 2) * Real.log N := by
    intro i _
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0
    · simp [wt, h0]; positivity
    · have hi1 : (2 : ℝ) ≤ (i : ℝ) + 1 := by
        have : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast h0
        linarith
      have hiN : (i : ℝ) + 1 ≤ N := by
        have : (i : ℕ) + 1 ≤ N := i.isLt
        exact_mod_cast this
      have hl2 : Real.log 2 ≤ Real.log ((i : ℝ) + 1) := Real.log_le_log (by norm_num) hi1
      have hlN : Real.log ((i : ℝ) + 1) ≤ Real.log N :=
        Real.log_le_log (by positivity) hiN
      have hlpos : 0 ≤ Real.log ((i : ℝ) + 1) := le_trans (Real.log_nonneg (by norm_num)) hl2
      have hw : wt γ i ≤ Real.exp (-γ * Real.log 2) := by
        unfold wt
        apply Real.exp_le_exp.2
        nlinarith
      exact mul_le_mul hw hlN hlpos hE.le
  have hS : ∑ i : Fin N, wt γ i * Real.log ((i : ℝ) + 1) ≤ N * Real.exp (-γ * Real.log 2) * Real.log N := by
    calc _ ≤ ∑ _i : Fin N, Real.exp (-γ * Real.log 2) * Real.log N := Finset.sum_le_sum hterm
      _ = _ := by simp; ring
  have hS0 : 0 ≤ ∑ i : Fin N, wt γ i * Real.log ((i : ℝ) + 1) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (Real.exp_pos _).le
      (Real.log_nonneg (by have : (0 : ℝ) ≤ (i : ℝ) := by positivity
                           linarith)))
  exact le_trans (div_le_self hS0 (Z_ge_one hN γ)) hS

theorem exists_gamma (N : ℕ) (hN : 2 ≤ N) (lam : ℝ) (h0 : 0 < lam)
    (h1 : lam < (∑ i : Fin N, Real.log ((i : ℝ) + 1)) / N) :
    ∃ γ : ℝ, 0 < γ ∧ logMean (powerLaw N γ) = lam := by
  have hN0 : 0 < N := by omega
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht : Filter.Tendsto (fun γ : ℝ => (N : ℝ) * Real.exp (-γ * Real.log 2) * Real.log N)
      Filter.atTop (nhds 0) := by
    have h1 := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.tendsto_id.atTop_mul_const hlog2)
    have h2 := (h1.const_mul (N : ℝ)).mul_const (Real.log N)
    simpa [Function.comp_def, neg_mul] using h2
  obtain ⟨Γ, hΓ, hΓ0⟩ := ((ht.eventually (gt_mem_nhds h0)).and (Filter.eventually_ge_atTop 0)).exists
  have hfΓ : logMean (powerLaw N Γ) < lam := lt_of_le_of_lt (logMean_le hN0 Γ hΓ0) hΓ
  have hf0 := logMean_zero hN0
  have hcont := (continuous_logMean hN0).continuousOn (s := Set.Icc 0 Γ)
  have hmem : lam ∈ Set.Icc (logMean (powerLaw N Γ)) (logMean (powerLaw N 0)) :=
    ⟨hfΓ.le, by rw [hf0]; exact h1.le⟩
  obtain ⟨γ, ⟨hγ0, _⟩, hγ⟩ := intermediate_value_Icc' hΓ0 hcont hmem
  refine ⟨γ, ?_, hγ⟩
  rcases hγ0.eq_or_lt with h | h
  · subst h
    have hγ' : logMean (powerLaw N 0) = lam := hγ
    rw [hf0] at hγ'; linarith
  · exact h

theorem gamma_unique {N : ℕ} (hN : 2 ≤ N) (lam γ₁ γ₂ : ℝ)
    (h₁ : logMean (powerLaw N γ₁) = lam) (h₂ : logMean (powerLaw N γ₂) = lam) : γ₁ = γ₂ := by
  have hN0 : 0 < N := by omega
  have a := gibbs_le hN0 γ₂ (powerLaw N γ₁) (fun i => (pl_pos hN0 γ₁ i).le) (pl_sum hN0 γ₁)
    (by rw [h₁, h₂])
  have b := gibbs_le hN0 γ₁ (powerLaw N γ₂) (fun i => (pl_pos hN0 γ₂ i).le) (pl_sum hN0 γ₂)
    (by rw [h₁, h₂])
  have hq : powerLaw N γ₁ = powerLaw N γ₂ := a.2 (le_antisymm a.1 b.1)
  have e0 := congrFun hq ⟨0, hN0⟩
  have e1 := congrFun hq ⟨1, by omega⟩
  have w0 : ∀ γ : ℝ, wt γ (⟨0, hN0⟩ : Fin N) = 1 := fun γ => by simp [wt]
  have w1 : ∀ γ : ℝ, wt γ (⟨1, by omega⟩ : Fin N) = Real.exp (-γ * Real.log 2) := fun γ => by
    simp [wt]; norm_num
  rw [powerLaw_eq, powerLaw_eq, w0, w0] at e0
  rw [powerLaw_eq, powerLaw_eq, w1, w1] at e1
  have hZ : Z N γ₁ = Z N γ₂ := by simpa using e0
  rw [hZ] at e1
  have hz := (Z_pos hN0 γ₂).ne'
  have e3 := Real.exp_injective ((div_left_inj' hz).1 e1)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : γ₁ * Real.log 2 = γ₂ * Real.log 2 := by linarith
  exact mul_right_cancel₀ hlog2.ne' this

/-- **MaxEnt power law (corrected Theorem 6.2).** -/
theorem maxent_power_law (N : ℕ) (hN : 2 ≤ N) (lam : ℝ) (h0 : 0 < lam)
    (h1 : lam < (∑ i : Fin N, Real.log ((i : ℝ) + 1)) / N) :
    ∃! γ : ℝ, 0 < γ ∧ logMean (powerLaw N γ) = lam ∧
      ∀ p : Fin N → ℝ, (∀ i, 0 ≤ p i) → ∑ i, p i = 1 → logMean p = lam →
        entropy p ≤ entropy (powerLaw N γ) ∧ (entropy p = entropy (powerLaw N γ) → p = powerLaw N γ) := by
  have hN0 : 0 < N := by omega
  obtain ⟨γ, hγ0, hγ⟩ := exists_gamma N hN lam h0 h1
  refine ⟨γ, ⟨hγ0, hγ, fun p hp0 hp1 hpl => gibbs_le hN0 γ p hp0 hp1 (by rw [hpl, hγ])⟩, ?_⟩
  rintro γ' ⟨_, h', _⟩
  exact gamma_unique hN lam γ' γ h' hγ

end MaxEntPowerLaw


end
