/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The joint eigenspaces of two commuting involutions

For two commuting involutions `P₀, P₁` of a finite-dimensional space over a field of characteristic zero and
signs `ε₀, ε₁ = ±1`, the operator `¼ (1 + ε₀P₀)(1 + ε₁P₁)` is a projection onto the joint eigenspace
`{P₀ = ε₀, P₁ = ε₁}`, so its trace is the dimension of that space:
`dim = ¼ [dim V + ε₀ tr P₀ + ε₁ tr P₁ + ε₀ε₁ tr (P₀P₁)]` (the parity count of Proposition 3 of
«What the Higgs Potential Cannot See»).

## Main results

* `LinearMap.isProj_jointProj`: `¼ (1 + ε₀P₀)(1 + ε₁P₁)` projects onto the joint eigenspace.
* `LinearMap.finrank_joint_eigenspace`: the dimension formula.
-/

@[expose] public section

open Module LinearMap

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The projector `¼ (1 + ε₀P₀)(1 + ε₁P₁)` onto the joint eigenspace `{P₀ = ε₀, P₁ = ε₁}` of two commuting
involutions (`ε₀, ε₁ = ±1`). -/
noncomputable def jointProj (P₀ P₁ : V →ₗ[K] V) (ε₀ ε₁ : K) : V →ₗ[K] V :=
  (4 : K)⁻¹ • ((1 + ε₀ • P₀) * (1 + ε₁ • P₁))

theorem isProj_jointProj [CharZero K] (P₀ P₁ : V →ₗ[K] V) (h₀ : P₀ * P₀ = 1) (h₁ : P₁ * P₁ = 1)
    (hc : P₀ * P₁ = P₁ * P₀) {ε₀ ε₁ : K} (hε₀ : ε₀ = 1 ∨ ε₀ = -1) (hε₁ : ε₁ = 1 ∨ ε₁ = -1) :
    IsProj (ker (P₀ - ε₀ • 1) ⊓ ker (P₁ - ε₁ • 1)) (jointProj P₀ P₁ ε₀ ε₁) := by
  have hP0 : ∀ x, P₀ (P₀ x) = x := fun x => by simpa using congrArg (fun f : V →ₗ[K] V => f x) h₀
  have hP1 : ∀ x, P₁ (P₁ x) = x := fun x => by simpa using congrArg (fun f : V →ₗ[K] V => f x) h₁
  have hc' : ∀ x, P₀ (P₁ x) = P₁ (P₀ x) := fun x => by simpa using congrArg (fun f : V →ₗ[K] V => f x) hc
  have e0 : ε₀ * ε₀ = 1 := by rcases hε₀ with rfl | rfl <;> norm_num
  have e1 : ε₁ * ε₁ = 1 := by rcases hε₁ with rfl | rfl <;> norm_num
  have hE : ∀ x, jointProj P₀ P₁ ε₀ ε₁ x
      = (4 : K)⁻¹ • (x + ε₁ • P₁ x + ε₀ • P₀ x + (ε₀ * ε₁) • P₀ (P₁ x)) := by
    intro x
    simp only [jointProj, smul_apply, Module.End.mul_apply, add_apply, Module.End.one_apply, map_add, map_smul]
    module
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · simp only [Submodule.mem_inf, mem_ker, sub_apply, smul_apply, Module.End.one_apply, sub_eq_zero]
    constructor
    · simp only [hE, map_add, map_smul, hP0, hc']
      rcases hε₀ with rfl | rfl <;> rcases hε₁ with rfl | rfl <;> module
    · simp only [hE, map_add, map_smul, hP1, hc']
      rcases hε₀ with rfl | rfl <;> rcases hε₁ with rfl | rfl <;> module
  · simp only [Submodule.mem_inf, mem_ker, sub_apply, smul_apply, Module.End.one_apply, sub_eq_zero] at hx
    obtain ⟨hx0, hx1⟩ := hx
    simp only [hE, hx1, map_smul, hx0]
    rcases hε₀ with rfl | rfl <;> rcases hε₁ with rfl | rfl <;> module

/-- **Proposition 3 of ghu-higgs-cannot-see, in general form**: for two commuting involutions `P₀, P₁` of a
finite-dimensional space over a field of characteristic zero and signs `ε₀, ε₁ = ±1`, the joint eigenspace
`{P₀ = ε₀, P₁ = ε₁}` has dimension `¼ [dim + ε₀ tr P₀ + ε₁ tr P₁ + ε₀ε₁ tr (P₀P₁)]`. -/
theorem finrank_joint_eigenspace [CharZero K] [FiniteDimensional K V] (P₀ P₁ : V →ₗ[K] V)
    (h₀ : P₀ * P₀ = 1) (h₁ : P₁ * P₁ = 1)
    (hc : P₀ * P₁ = P₁ * P₀) {ε₀ ε₁ : K} (hε₀ : ε₀ = 1 ∨ ε₀ = -1) (hε₁ : ε₁ = 1 ∨ ε₁ = -1) :
    (finrank K ↥(LinearMap.ker (P₀ - ε₀ • 1) ⊓ LinearMap.ker (P₁ - ε₁ • 1)) : K) =
      (finrank K V + ε₀ * LinearMap.trace K V P₀ + ε₁ * LinearMap.trace K V P₁ +
        ε₀ * ε₁ * LinearMap.trace K V (P₀ * P₁)) / 4 := by
  rw [← (isProj_jointProj P₀ P₁ h₀ h₁ hc hε₀ hε₁).trace]
  have hexp : (1 + ε₀ • P₀) * (1 + ε₁ • P₁) = 1 + ε₁ • P₁ + ε₀ • P₀ + (ε₀ * ε₁) • (P₀ * P₁) := by
    rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, smul_mul_smul_comm]
    abel
  rw [jointProj, hexp]
  simp only [map_smul, map_add, LinearMap.trace_one, smul_eq_mul]
  ring

end LinearMap
