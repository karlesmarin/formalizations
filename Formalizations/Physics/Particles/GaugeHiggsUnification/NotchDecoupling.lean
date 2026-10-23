/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# The notch decouples the fermion sector from the leading curvature

The leading Kaluza–Klein order of the curvature at the half point is
`𝒟 = π² (∑_{m ≡ 2 (4)} m² δ(m) − ∑_{m ≡ 0 (4)} m² δ(m))`, with `δ(m) = mult(m,0) − mult(m,1)` over a
finite set of levels. It is linear in `δ` and vanishes when `δ(m) = 0` at every even `m` (the notch),
so the fermion sector drops out and `𝒟` is the gauge part alone. On `range (2N)` it is the plain
alternating weight `−4π² ∑_{m' < N} (−1)^{m'} m'² δ(2m')`. That `𝒟` is the leading curvature is
physics and is not formalized here.

## Main results

* `GaugeHiggsUnification.NotchDecoupling.curv_add`: `𝒟` is additive in `δ`.
* `GaugeHiggsUnification.NotchDecoupling.curv_eq_zero_of_even`: `δ = 0` on even levels gives `𝒟 = 0`.
* `GaugeHiggsUnification.NotchDecoupling.curv_decoupling`: the fermion imbalance drops out.
* `GaugeHiggsUnification.NotchDecoupling.curv_range_eq_alternating`: the alternating form.

## References

* C. Marín, *A Centre-Charge Selection Rule for the Wilson-Line Potential: The Fundamental
  Domain of Gauge-Higgs Unification Is Representation-Dependent (Part III)*, Zenodo (2026),
  doi:10.5281/zenodo.21466370, Corollary `cor:decoupling` and eq. `(Dstruct)`.
-/

@[expose] public section

namespace GaugeHiggsUnification.NotchDecoupling

open Finset

/-- The leading Kaluza–Klein curvature built from the imbalance `δ` over the levels `S`. -/
noncomputable def curv (S : Finset ℕ) (δ : ℕ → ℝ) : ℝ :=
  Real.pi ^ 2 * (∑ m ∈ S.filter (fun m => m % 4 = 2), (m : ℝ) ^ 2 * δ m
    - ∑ m ∈ S.filter (fun m => m % 4 = 0), (m : ℝ) ^ 2 * δ m)

theorem curv_add (S : Finset ℕ) (δ₁ δ₂ : ℕ → ℝ) :
    curv S (δ₁ + δ₂) = curv S δ₁ + curv S δ₂ := by
  unfold curv
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem curv_eq_zero_of_even {S : Finset ℕ} {δ : ℕ → ℝ} (h : ∀ m ∈ S, Even m → δ m = 0) :
    curv S δ = 0 := by
  unfold curv
  have h1 : ∑ m ∈ S.filter (fun m => m % 4 = 2), (m : ℝ) ^ 2 * δ m = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    obtain ⟨hmS, hmod⟩ := Finset.mem_filter.mp hm
    rw [h m hmS (Nat.even_iff.mpr (by omega)), mul_zero]
  have h2 : ∑ m ∈ S.filter (fun m => m % 4 = 0), (m : ℝ) ^ 2 * δ m = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    obtain ⟨hmS, hmod⟩ := Finset.mem_filter.mp hm
    rw [h m hmS (Nat.even_iff.mpr (by omega)), mul_zero]
  rw [h1, h2]
  ring

/-- Decoupling: if the fermion imbalance vanishes on every even level, `𝒟` is the gauge part alone. -/
theorem curv_decoupling {S : Finset ℕ} (δG δF : ℕ → ℝ) (h : ∀ m ∈ S, Even m → δF m = 0) :
    curv S (δG + δF) = curv S δG := by
  rw [curv_add, curv_eq_zero_of_even h, add_zero]

/-- The paper's rewriting `m = 2m'`: a plain alternating weight. -/
theorem curv_range_eq_alternating (N : ℕ) (δ : ℕ → ℝ) :
    curv (range (2 * N)) δ = -4 * Real.pi ^ 2 * ∑ k ∈ range N, (-1 : ℝ) ^ k * (k : ℝ) ^ 2 * δ (2 * k) := by
  -- single-sum form of `curv`
  have hcurv : ∀ S : Finset ℕ, curv S δ = Real.pi ^ 2 *
      ∑ m ∈ S, (if m % 4 = 2 then (1 : ℝ) else if m % 4 = 0 then -1 else 0) * (m : ℝ) ^ 2 * δ m := by
    intro S
    unfold curv
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    split_ifs <;> first | omega | ring
  -- one step: levels 2n and 2n+1
  have step : ∀ n : ℕ,
      (if (2 * n) % 4 = 2 then (1 : ℝ) else if (2 * n) % 4 = 0 then -1 else 0) * ((2 * n : ℕ) : ℝ) ^ 2 * δ (2 * n)
        + (if (2 * n + 1) % 4 = 2 then (1 : ℝ) else if (2 * n + 1) % 4 = 0 then -1 else 0)
          * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * δ (2 * n + 1)
        = -4 * ((-1 : ℝ) ^ n * (n : ℝ) ^ 2 * δ (2 * n)) := by
    intro n
    rcases Nat.even_or_odd n with hev | hod
    · have e1 : (2 * n) % 4 = 0 := by obtain ⟨j, hj⟩ := hev; omega
      have e2 : (2 * n + 1) % 4 = 1 := by obtain ⟨j, hj⟩ := hev; omega
      have e3 : (-1 : ℝ) ^ n = 1 := hev.neg_one_pow
      simp only [e1, e2, e3]
      norm_num
      ring
    · have e1 : (2 * n) % 4 = 2 := by obtain ⟨j, hj⟩ := hod; omega
      have e2 : (2 * n + 1) % 4 = 3 := by obtain ⟨j, hj⟩ := hod; omega
      have e3 : (-1 : ℝ) ^ n = -1 := hod.neg_one_pow
      simp only [e1, e2, e3]
      norm_num
      ring
  have key : ∀ N : ℕ,
      ∑ m ∈ range (2 * N), (if m % 4 = 2 then (1 : ℝ) else if m % 4 = 0 then -1 else 0) * (m : ℝ) ^ 2 * δ m
        = -4 * ∑ k ∈ range N, (-1 : ℝ) ^ k * (k : ℝ) ^ 2 * δ (2 * k) := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]
      simp only [Finset.sum_range_succ]
      rw [ih]
      linarith [step n]
  rw [hcurv, key N]
  ring

end GaugeHiggsUnification.NotchDecoupling
