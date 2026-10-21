/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# The Jacobian of a residual stream is an ordered product

For a residual stream `h_{ℓ+1} = h_ℓ + w_ℓ(h_ℓ)` with differentiable layers `w_ℓ` on a real normed space, the
derivative of the whole stream is the ORDERED product of the layer Jacobians `I + w_ℓ′`, each evaluated at the
point the stream has reached (Theorem 1 of transformers-attend-III, «recurrence factorisation»). Expanding the
product gives `J − I = Σ_k w_k′ + (cross terms)`.

## Main results

* `step`, `flow`, `jac`: one residual layer, the stream through a list of layers (head first), and the ordered
  product of `I + fderiv w` along the trajectory.
* `hasFDerivAt_flow`: `HasFDerivAt (flow ws) (jac ws x) x`.

## References

* C. Marín, *Transformers attend (Part III)*, Theorem 1 (`thm:bridge`).
-/

@[expose] public section

namespace TransformerAttention.ResidualJacobian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One residual layer `h ↦ h + w h`. -/
def step (w : E → E) : E → E := fun h => h + w h

/-- The residual stream through the layers of a list, the head first. -/
def flow : List (E → E) → E → E
  | [] => id
  | w :: ws => flow ws ∘ step w

/-- The ordered product of the layer Jacobians `I + w′` along the trajectory, the head layer first (rightmost). -/
noncomputable def jac : List (E → E) → E → E →L[ℝ] E
  | [], _ => ContinuousLinearMap.id ℝ E
  | w :: ws, x => (jac ws (step w x)).comp (ContinuousLinearMap.id ℝ E + fderiv ℝ w x)

/-- Recurrence factorisation: for differentiable layers, the derivative of the residual stream at `x` is the
ordered product of the layer Jacobians `I + w_k′` evaluated along the trajectory from `x`. -/
theorem hasFDerivAt_flow (ws : List (E → E)) (hw : ∀ w ∈ ws, Differentiable ℝ w) (x : E) :
    HasFDerivAt (flow ws) (jac ws x) x := by
  induction ws generalizing x with
  | nil => exact hasFDerivAt_id x
  | cons w ws ih =>
    have hstep : HasFDerivAt (step w) (ContinuousLinearMap.id ℝ E + fderiv ℝ w x) x :=
      (hasFDerivAt_id x).add ((hw w (List.mem_cons_self ..)).differentiableAt.hasFDerivAt)
    exact (ih (fun v hv => hw v (List.mem_cons_of_mem _ hv)) (step w x)).comp x hstep

end TransformerAttention.ResidualJacobian
