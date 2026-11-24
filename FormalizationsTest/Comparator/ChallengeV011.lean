/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
import Mathlib

/-!
# Comparator challenge for the Reusable jewels of v0.11

The statements below are the trusted input of `lake comparator`: they are written from the classical
sources (Margolus–Levitin, Physica D 120 (1998); Praeger, J. Algebra 144 (1991)), each with `sorry`.
The comparator checks that the solution module proves exactly these statements, with the standard
axioms only, and replays the proofs through the kernel.
-/

namespace Formalizations.Reusable

/-- Margolus–Levitin (`ℏ = 1`): a state whose autocorrelation vanishes at time `τ` needs
`π ≤ 2 ⟨E⟩ τ` (energies nonnegative, normalized weights). -/
theorem margolus_levitin {p E : ℕ → ℝ} {Ebar τ : ℝ} (hp : ∀ n, 0 ≤ p n) (hE : ∀ n, 0 ≤ E n)
    (hτ : 0 ≤ τ) (hsum : HasSum p 1) (hmean : HasSum (fun n => p n * E n) Ebar)
    (hRe : HasSum (fun n => p n * Real.cos (E n * τ)) 0)
    (hIm : HasSum (fun n => p n * Real.sin (E n * τ)) 0) :
    Real.pi ≤ 2 * Ebar * τ := by
  sorry

/-- Praeger's theorem on bounded movement. -/
theorem praeger_bounded_movement {G Ω : Type*} [Group G] [MulAction G Ω] (m : ℕ) (hm : 1 ≤ m)
    (hfix : ∀ x : Ω, ∃ g : G, g • x ≠ x)
    (hmove : ∀ (Γ : Finset Ω) (g : G), (∀ x ∈ Γ, g • x ∉ Γ) → Γ.card ≤ m) :
    Finite Ω ∧ Nat.card (MulAction.orbitRel.Quotient G Ω) ≤ 2 * m - 1 ∧
      (∀ x : Ω, Nat.card (MulAction.orbit G x) ≤ 3 * m) ∧
      Nat.card Ω ≤ 3 * m + Nat.card (MulAction.orbitRel.Quotient G Ω) - 1 := by
  sorry

end Formalizations.Reusable
