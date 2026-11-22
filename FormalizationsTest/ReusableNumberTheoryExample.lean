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

/-- Touchard at `n = 0`: `B(p) ≡ 2 (mod p)` for every prime `p`. -/
example (p : ℕ) [Fact p.Prime] : ((p.bell : ℕ) : ZMod p) = 2 := by
  have h := touchard_bell_add_prime p 0
  simp only [zero_add, Nat.bell_zero, Nat.bell_one, Nat.cast_one] at h
  rw [h]; norm_num

/-- Dedekind reciprocity at `h = k = 1`: `s(1, 1) + s(1, 1) = 0`. -/
example : DedekindSum.ded 1 1 + DedekindSum.ded 1 1 = 0 := by
  have h := ded_reciprocity (h := 1) (k := 1) (by norm_num) one_pos one_pos
  norm_num at h
  rw [h]; norm_num

/-- `τ ∗ φ = σ` at `n = 6`: `2 + 4 + 2 + 4 = 12`. -/
example : ∑ d ∈ (6 : ℕ).divisors, d.divisors.card * Nat.totient (6 / d) = ∑ d ∈ (6 : ℕ).divisors, d :=
  sum_card_divisors_mul_totient 6
