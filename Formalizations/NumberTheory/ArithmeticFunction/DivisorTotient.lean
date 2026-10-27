/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Data.Nat.Totient

/-!
# The Dirichlet identity τ ∗ φ = σ

For every `n`, `Σ_{d ∣ n} τ(d) φ(n/d) = σ(n)`, with `τ` the number of divisors, `φ` Euler's totient
and `σ` the sum of divisors. In the ring of arithmetic functions `τ = ζ ∗ ζ` and `φ ∗ ζ = id`
(Mathlib's `Nat.sum_totient`), so `τ ∗ φ = ζ ∗ (ζ ∗ φ) = ζ ∗ id = σ`.

## Main results

* `DivisorTotient.sum_card_divisors_mul_totient`: sum over d | n of tau(d) * phi(n/d) equals sigma(n)

## References

* Classical Dirichlet-series identity (e.g. G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*, Ch. XVI). Found missing from Mathlib by excovery.identidades_mathlib.
-/

@[expose] public section

open ArithmeticFunction
open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma

namespace DivisorTotient

/-- Euler's totient as an arithmetic function. -/
private def phi : ArithmeticFunction ℕ := ⟨Nat.totient, by simp⟩

private theorem phi_apply (n : ℕ) : phi n = Nat.totient n := rfl

private theorem phi_mul_zeta : phi * ζ = pow 1 := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => phi a * ζ b)]
    have : ∀ d ∈ n.divisors, phi d * ζ (n / d) = Nat.totient d := by
      intro d hd
      have hd' : n / d ≠ 0 := (Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)).ne'
      simp [phi_apply, zeta_apply, hd']
    rw [Finset.sum_congr rfl this, Nat.sum_totient]
    simp

private theorem sigma_zero_eq : σ 0 = (ζ : ArithmeticFunction ℕ) * ζ := by
  rw [← zeta_mul_pow_eq_sigma, pow_zero_eq_zeta]

private theorem conv_eq : σ 0 * phi = σ 1 := by
  rw [sigma_zero_eq, ← zeta_mul_pow_eq_sigma, ← phi_mul_zeta]
  ring

/-- **Dirichlet identity `τ ∗ φ = σ`.** For every `n`, `Σ_{d ∣ n} τ(d) φ(n/d) = σ(n)`, where `τ(d)` is the
number of divisors of `d`, `φ` Euler's totient and `σ(n)` the sum of the divisors of `n`. -/
theorem sum_card_divisors_mul_totient (n : ℕ) :
    ∑ d ∈ n.divisors, d.divisors.card * Nat.totient (n / d) = ∑ d ∈ n.divisors, d := by
  have h := congrArg (fun f : ArithmeticFunction ℕ => f n) conv_eq
  simp only [mul_apply, sigma_one_apply] at h
  rw [← h, Nat.sum_divisorsAntidiagonal (fun a b => σ 0 a * phi b)]
  simp [sigma_zero_apply, phi_apply]

end DivisorTotient
