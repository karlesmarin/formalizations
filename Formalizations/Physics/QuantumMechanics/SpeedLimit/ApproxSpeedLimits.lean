/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.Physics.QuantumMechanics.SpeedLimit.QuditEntangling
public import Formalizations.Physics.QuantumMechanics.SpeedLimit.QuditEntanglingShift
public import Formalizations.Physics.QuantumMechanics.SpeedLimit.GateEigenphases
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Robust (approximate) quantum speed limits

The exact speed limits of `QuditEntangling` and `GateEigenphases` assume that the target state is
reached exactly. Here the target is reached only up to a **state infidelity** `ε`. Everything
follows from the triangle inequality for the Fubini–Study angle
`fsAngle u v = arccos ‖⟪u, v⟫‖`: a state of fidelity `≥ 1 − ε` with a target lies at angle
`≤ arccos √(1 − ε) = arcsin √ε` from it.

Here `ε` is the infidelity of one specific input/output pair of states, `‖⟪target, U ψ⟫‖² ≥ 1 − ε`.
It is **not** an average gate infidelity (which would need an average over inputs).

The statements were suggested by an external review.

## Main results

* `QSL.Qudit.pi_div_four_sub_le_entangling_time_approx`: if the evolution maps a unit product
  vector to `Φ` with `‖⟪Bell, Φ⟫‖² ≥ 1 − ε`, then `π/4 − arcsin √ε ≤ J · ∑ τₖ`
  (exact case `ε = 0`: `QSL.Qudit.pi_div_four_le_entangling_time`)
* `QSL.Qudit.pi_div_four_sub_le_entangling_time_shift_approx`: the same with `‖H − c • 1‖ ≤ J`
* `QSL.Gate.two_arccos_sqrt_le_time_approx`: transferring `ψ₀` to a state of fidelity `≥ 1 − ε`
  with an orthogonal unit vector `ψ₁` takes `2 · arccos √ε ≤ Ω · ∑ τₖ`

Tightness (not formalized): with `H = (Ω/2) σₓ`, `ψ₀ = e₀`, `ψ₁ = e₁`, the transfer probability is
`P₁(T) = sin² (Ω T / 2)`, so for `ε = cos² (Ω T / 2)` the bound `2 arccos √ε = Ω T` is attained.

## References

* L. Mandelstam, I. Tamm, *The uncertainty relation between energy and time in non-relativistic
  quantum mechanics*, J. Phys. USSR 9 (1945) 249.
* W. Dür, G. Vidal, J. I. Cirac, N. Linden, S. Popescu, *Entanglement capabilities of nonlocal
  Hamiltonians*, Phys. Rev. Lett. 87 (2001) 137901 (the exact case `ε = 0`).
-/

@[expose] public section

noncomputable section

open scoped Matrix Kronecker
open scoped Matrix.Norms.L2Operator
open NormedSpace
open QSL.TwoQubit (act)

namespace QSL.Qudit

section Core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A pair of vectors with `‖⟪u, v⟫‖² ≥ 1 − ε` lies at Fubini–Study angle `≤ arcsin √ε`. -/
lemma fsAngle_le_arcsin_sqrt {u v : E} {ε : ℝ} (hε : 0 ≤ ε)
    (h : 1 - ε ≤ ‖inner ℂ u v‖ ^ 2) : fsAngle u v ≤ Real.arcsin (Real.sqrt ε) := by
  rw [Real.arcsin_eq_arccos (Real.sqrt_nonneg _), Real.sq_sqrt hε, fsAngle]
  refine Real.arccos_le_arccos ?_
  calc Real.sqrt (1 - ε) ≤ Real.sqrt (‖inner ℂ u v‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = ‖inner ℂ u v‖ := Real.sqrt_sq (norm_nonneg _)

/-- If `Φ` is within angle `θ < π/4` of a target `T`, and `T` is at angle `≥ π/4` from `p`, then
`Φ` has overlap at most `cos (π/4 − θ)` with the unit vector `p`. -/
lemma norm_inner_le_cos_of_angle {T Φ p : E} (hT : ‖T‖ = 1) (hΦ : ‖Φ‖ = 1) (hp : ‖p‖ = 1)
    {θ : ℝ} (hθ : θ < Real.pi / 4) (hTΦ : fsAngle T Φ ≤ θ) (hTp : Real.pi / 4 ≤ fsAngle T p) :
    ‖inner ℂ Φ p‖ ≤ Real.cos (Real.pi / 4 - θ) := by
  have tri := fsAngle_le_fsAngle_add_fsAngle hT hΦ hp
  have h1 : Real.pi / 4 - θ ≤ Real.arccos ‖inner ℂ Φ p‖ := by
    unfold fsAngle at tri hTΦ hTp
    linarith
  have hle : ‖inner ℂ Φ p‖ ≤ 1 := (norm_inner_le_norm Φ p).trans (by rw [hΦ, hp, one_mul])
  have hge : -1 ≤ ‖inner ℂ Φ p‖ := by linarith [norm_nonneg (inner ℂ Φ p)]
  calc ‖inner ℂ Φ p‖ = Real.cos (Real.arccos ‖inner ℂ Φ p‖) := (Real.cos_arccos hge hle).symm
    _ ≤ Real.cos (Real.pi / 4 - θ) :=
        Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (Real.arccos_le_pi _) h1

end Core

section Bipartite

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma norm_bellPair {i₀ i₁ : ι} {j₀ j₁ : κ} (hi : i₀ ≠ i₁) :
    ‖bellPair i₀ i₁ j₀ j₁‖ = 1 := by
  have hne : (i₀, j₀) ≠ (i₁, j₁) := fun h => hi (Prod.ext_iff.1 h).1
  have h : ‖bellPair i₀ i₁ j₀ j₁‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_eq_add (i₀, j₀) (i₁, j₁) hne]
    · simp [bellPair, hne, hne.symm]
      norm_num
    · intro x hx
      simp [bellPair, hx.1, hx.2]
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 (by rw [h, one_pow])

/-- Shared reduction: from the closeness of `Φ` to the Bell vector to an overlap bound `λ` and the
resulting inequality `π/4 − θ ≤ arccos λ`, in the nontrivial case `θ < π/4`. -/
private lemma bell_overlap_bound {i₀ i₁ : ι} {j₀ j₁ : κ} (hi : i₀ ≠ i₁) (hj : j₀ ≠ j₁)
    (Φ : EuclideanSpace ℂ (ι × κ)) (hΦ : ‖Φ‖ = 1) {θ : ℝ} (hθ : θ < Real.pi / 4)
    (hBΦ : fsAngle (bellPair i₀ i₁ j₀ j₁) Φ ≤ θ) (x : EuclideanSpace ℂ ι)
    (y : EuclideanSpace ℂ κ) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖inner ℂ Φ (prodVec x y)‖ ≤ Real.cos (Real.pi / 4 - θ) := by
  have hbell := norm_bellPair (j₀ := j₀) (j₁ := j₁) hi
  refine norm_inner_le_cos_of_angle hbell hΦ (by rw [norm_prodVec, hx, hy, one_mul]) hθ hBΦ ?_
  rw [fsAngle, ← arccos_inv_sqrt_two]
  exact Real.arccos_le_arccos (norm_inner_bellPair_prodVec_le hi hj x y hx hy)

/-- **Robust Bell-pair entangling time.** Let `H` be a Hermitian interaction with `‖H‖ ≤ J` and
`U = ∏ₖ exp (−i τₖ (Aₖ ⊗ 1 + 1 ⊗ Bₖ + H))` with arbitrary Hermitian local controls. If `U` maps a
unit product vector to a unit vector `Φ` whose state infidelity with the two-level Bell vector is at
most `ε`, i.e. `‖⟪Bell, Φ⟫‖² ≥ 1 − ε`, then `π/4 − arcsin √ε ≤ J · ∑ τₖ`.
Here `ε` is the infidelity of this one input/output pair, not an average gate infidelity.
For `ε = 0` this is `pi_div_four_le_entangling_time` (Dür et al. 2001). -/
theorem pi_div_four_sub_le_entangling_time_approx (H : Matrix (ι × κ) (ι × κ) ℂ)
    (hH : H.IsHermitian) (J : ℝ) (hJ : ‖H‖ ≤ J) (steps : List (ℝ × Matrix ι ι ℂ × Matrix κ κ ℂ))
    (hτ : ∀ s ∈ steps, 0 ≤ s.1) (hA : ∀ s ∈ steps, s.2.1.IsHermitian)
    (hB : ∀ s ∈ steps, s.2.2.IsHermitian) (a : EuclideanSpace ℂ ι) (b : EuclideanSpace ℂ κ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) {i₀ i₁ : ι} {j₀ j₁ : κ} (hi : i₀ ≠ i₁) (hj : j₀ ≠ j₁)
    (Φ : EuclideanSpace ℂ (ι × κ)) (hΦ : ‖Φ‖ = 1)
    (hU : act (steps.map fun s => exp ((-(s.1 : ℂ) * Complex.I) •
        (s.2.1 ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ s.2.2 + H))).prod
        (prodVec a b) = Φ)
    {ε : ℝ} (hε : 0 ≤ ε) (hfid : 1 - ε ≤ ‖inner ℂ (bellPair i₀ i₁ j₀ j₁) Φ‖ ^ 2) :
    Real.pi / 4 - Real.arcsin (Real.sqrt ε) ≤ J * (steps.map Prod.fst).sum := by
  set θ := Real.arcsin (Real.sqrt ε) with hθ
  have hBΦ : fsAngle (bellPair i₀ i₁ j₀ j₁) Φ ≤ θ := fsAngle_le_arcsin_sqrt hε hfid
  have hsum : 0 ≤ (steps.map Prod.fst).sum :=
    List.sum_nonneg fun x hx => by
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
      exact hτ s hs
  have hJ0 : 0 ≤ J := (norm_nonneg H).trans hJ
  rcases le_or_gt (Real.pi / 4) θ with h | h
  · nlinarith [mul_nonneg hJ0 hsum]
  · have key := arccos_le_entangling_time H hH J hJ steps hτ hA hB a b ha hb Φ hU _
      (bell_overlap_bound hi hj Φ hΦ h hBΦ)
    rwa [Real.arccos_cos (by linarith [Real.arcsin_nonneg.2 (Real.sqrt_nonneg ε)])
      (by linarith [Real.pi_pos, Real.arcsin_nonneg.2 (Real.sqrt_nonneg ε)])] at key

/-- **Robust Bell-pair entangling time, shifted coupling.** As
`pi_div_four_sub_le_entangling_time_approx`, with `‖H − c • 1‖ ≤ J` for some real `c`. -/
theorem pi_div_four_sub_le_entangling_time_shift_approx (H : Matrix (ι × κ) (ι × κ) ℂ)
    (hH : H.IsHermitian) (c J : ℝ) (hJ : ‖H - (c : ℂ) • (1 : Matrix (ι × κ) (ι × κ) ℂ)‖ ≤ J)
    (steps : List (ℝ × Matrix ι ι ℂ × Matrix κ κ ℂ))
    (hτ : ∀ s ∈ steps, 0 ≤ s.1) (hA : ∀ s ∈ steps, s.2.1.IsHermitian)
    (hB : ∀ s ∈ steps, s.2.2.IsHermitian) (a : EuclideanSpace ℂ ι) (b : EuclideanSpace ℂ κ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) {i₀ i₁ : ι} {j₀ j₁ : κ} (hi : i₀ ≠ i₁) (hj : j₀ ≠ j₁)
    (Φ : EuclideanSpace ℂ (ι × κ)) (hΦ : ‖Φ‖ = 1)
    (hU : act (steps.map fun s => exp ((-(s.1 : ℂ) * Complex.I) •
        (s.2.1 ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ s.2.2 + H))).prod
        (prodVec a b) = Φ)
    {ε : ℝ} (hε : 0 ≤ ε) (hfid : 1 - ε ≤ ‖inner ℂ (bellPair i₀ i₁ j₀ j₁) Φ‖ ^ 2) :
    Real.pi / 4 - Real.arcsin (Real.sqrt ε) ≤ J * (steps.map Prod.fst).sum := by
  set θ := Real.arcsin (Real.sqrt ε) with hθ
  have hBΦ : fsAngle (bellPair i₀ i₁ j₀ j₁) Φ ≤ θ := fsAngle_le_arcsin_sqrt hε hfid
  have hsum : 0 ≤ (steps.map Prod.fst).sum :=
    List.sum_nonneg fun x hx => by
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
      exact hτ s hs
  have hJ0 : 0 ≤ J := (norm_nonneg _).trans hJ
  rcases le_or_gt (Real.pi / 4) θ with h | h
  · nlinarith [mul_nonneg hJ0 hsum]
  · have key := arccos_le_entangling_time_shift H hH c J hJ steps hτ hA hB a b ha hb Φ hU _
      (bell_overlap_bound hi hj Φ hΦ h hBΦ)
    rwa [Real.arccos_cos (by linarith [Real.arcsin_nonneg.2 (Real.sqrt_nonneg ε)])
      (by linarith [Real.pi_pos, Real.arcsin_nonneg.2 (Real.sqrt_nonneg ε)])] at key

end Bipartite

end QSL.Qudit

namespace QSL.Gate

open QSL.Qudit

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Robust state-transfer time.** Let `U = ∏ₖ exp (−i τₖ Hₖ)` with `τₖ ≥ 0`, `Hₖ` Hermitian and
`‖Hₖ − cₖ • 1‖ ≤ Ω / 2`. If `ψ₀ ⊥ ψ₁` are unit vectors and `U ψ₀ = ψ` is a unit vector with state
infidelity at most `ε` relative to `ψ₁`, i.e. `‖⟪ψ₁, ψ⟫‖² ≥ 1 − ε`, then
`2 · arccos √ε ≤ Ω · ∑ τₖ`. Here `ε` is the infidelity of this one input/output pair, not an
average gate infidelity. (Tight: `H = (Ω/2) σₓ` gives `P₁(T) = sin² (Ω T / 2)`.) -/
theorem two_arccos_sqrt_le_time_approx (Ω : ℝ) (steps : List (ℝ × ℝ × Matrix n n ℂ))
    (hτ : ∀ s ∈ steps, 0 ≤ s.1) (hH : ∀ s ∈ steps, s.2.2.IsHermitian)
    (hΩ : ∀ s ∈ steps, ‖s.2.2 - (s.2.1 : ℂ) • (1 : Matrix n n ℂ)‖ ≤ Ω / 2)
    (ψ₀ ψ₁ ψ : EuclideanSpace ℂ n) (h₀ : ‖ψ₀‖ = 1) (h₁ : ‖ψ₁‖ = 1) (hψ : ‖ψ‖ = 1)
    (horth : inner ℂ ψ₁ ψ₀ = 0)
    (hU : act (steps.map fun s => exp ((-(s.1 : ℂ) * Complex.I) • s.2.2)).prod ψ₀ = ψ)
    {ε : ℝ} (hε : 0 ≤ ε) (hfid : 1 - ε ≤ ‖inner ℂ ψ₁ ψ‖ ^ 2) :
    2 * Real.arccos (Real.sqrt ε) ≤ Ω * (steps.map Prod.fst).sum := by
  have hang := fsAngle_le_time_halfWidth Ω steps hτ hH hΩ ψ₀ h₀
  rw [hU] at hang
  have tri := fsAngle_le_fsAngle_add_fsAngle h₁ hψ h₀
  have hπ : fsAngle ψ₁ ψ₀ = Real.pi / 2 := by
    rw [fsAngle, horth, norm_zero, Real.arccos_zero]
  have hs := fsAngle_le_arcsin_sqrt hε hfid
  rw [hπ] at tri
  rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  linarith

end QSL.Gate
