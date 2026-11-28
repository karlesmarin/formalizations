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

/-- `reverse_cyclotomic` at `n = 6`: the sixth cyclotomic polynomial is palindromic. -/
example : (Polynomial.cyclotomic 6 ℝ).reverse = Polynomial.cyclotomic 6 ℝ :=
  reverse_cyclotomic 6 (by decide)

/-- There is a positive period for the Fibonacci sequence modulo 10. -/
example : ∃ period, 0 < period ∧ ∀ n, Nat.fib (n + period) ≡ Nat.fib n [MOD 10] :=
  exists_fib_modEq_period 10 (by decide)

/-- Every positive period modulo 10 is divisible by two. -/
example (period : ℕ) (hpos : 0 < period)
    (hper : ∀ n, Nat.fib (n + period) ≡ Nat.fib n [MOD 10]) : 2 ∣ period :=
  even_iff_two_dvd.mp (even_of_fib_modEq_period 10 (by decide) period hpos hper)

/-- The prime 5 divides `F₅`, by the vanishing of the Legendre symbol. -/
example : (Nat.fib 5 : ZMod 5) = 0 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [fib_prime_eq_legendreSym, (legendreSym.eq_zero_iff 5 5).mpr (by decide), Int.cast_zero]

/-- The odd indices which divide their associated Fibonacci sums form an infinite set. -/
example : {k : ℕ | Odd k ∧ k ∣ (∑ i ∈ Finset.Icc 1 k, Nat.fib i)}.Infinite :=
  flynn_connolly.2

/-- Doubling sends some point of the cyclic interval `{0, 1}` modulo 5 outside the interval. -/
example : ∃ x : ZMod 5, x.val < 2 ∧ 2 ≤ ((2 : ZMod 5) * x).val := by
  let a : (ZMod 5)ˣ := ⟨2, 3, by decide, by decide⟩
  have h := amiot_interval (n := 5) (k := 2) (by decide) (by decide) 0 a (by decide) (by decide)
  push Not at h
  simpa [a] using h
