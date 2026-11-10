/-
Usage example of the reusable layer, area NumberTheory, with the minimal import of that area: the
same code a user pastes into a file of their own project (README, section "Reusable layer").
-/
import Formalizations.Reusable.NumberTheory

open Formalizations.Reusable

/-- Wolstenholme as a divisibility: `p³ ∣ C(2p, p) − 2` in `ℤ` for every prime `p ≥ 5`. -/
example (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    (p : ℤ) ^ 3 ∣ (Nat.choose (2 * p) p : ℤ) - 2 := by
  have h := Nat.modEq_iff_dvd.1 (wolstenholme_choose_modEq p hp h5).2.symm
  push_cast at h
  exact h
