/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.NumberTheory.Wolstenholme
public import Formalizations.Combinatorics.Enumerative.Touchard
public import Formalizations.NumberTheory.DedekindSum
public import Formalizations.NumberTheory.ArithmeticFunction.DivisorTotient
public import Formalizations.NumberTheory.Cyclotomic.ParityBounds
public import Formalizations.NumberTheory.Fibonacci.Pisano
public import Formalizations.NumberTheory.Fibonacci.FibLegendre
public import Formalizations.NumberTheory.Fibonacci.SumDivisibility
public import Formalizations.NumberTheory.SymplecticCharacterOrders.Segments

/-!
# Reusable layer: number theory

Stable names for archive results in number theory. Each theorem re-exposes its archive proof.

## Main results

* `Formalizations.Reusable.reverse_cyclotomic`: cyclotomic polynomials over ℝ are palindromic
  for `n ≥ 2` (archive: `CycloParity.reverse_cyclotomic`).

* `Formalizations.Reusable.sum_card_divisors_mul_totient`: the Dirichlet identity `τ ∗ φ = σ`,
  `Σ_{d ∣ n} τ(d) φ(n/d) = σ(n)` (archive: `DivisorTotient.sum_card_divisors_mul_totient`).
* `Formalizations.Reusable.ded_reciprocity`: Dedekind's reciprocity law for the Dedekind sums `s(h, k)`
  (archive: `DedekindSum.ded_reciprocity`).
* `Formalizations.Reusable.wolstenholme_choose_modEq`: Wolstenholme's theorem,
  `C(2p − 1, p − 1) ≡ 1` and `C(2p, p) ≡ 2 (mod p³)` for primes `p ≥ 5` (archive:
  `Wolstenholme.choose_modEq`).
* `Formalizations.Reusable.touchard_bell_add_prime`: Touchard's congruence for Bell numbers,
  `B(n + p) ≡ B(n) + B(n + 1) (mod p)` for every prime `p` (archive: `Touchard.bell_add_prime`).
* `Formalizations.Reusable.exists_fib_modEq_period` and
  `Formalizations.Reusable.even_of_fib_modEq_period`: Fibonacci numbers are periodic modulo every
  positive modulus, and every positive period is even for modulus greater than two.
* `Formalizations.Reusable.fib_prime_eq_legendreSym`: `F_p ≡ (5/p) (mod p)` for every prime `p`.
* `Formalizations.Reusable.flynn_connolly`: infinitely many odd `k` divide `F₁ + ⋯ + Fₖ`, with a
  family of examples constructed from Fibonacci numbers at twice or four times certain primes.
* `Formalizations.Reusable.amiot_interval`: a cyclic interval of length between `2` and `n − 2`
  cannot be preserved by multiplication by a unit other than `±1`.
-/

@[expose] public section

namespace Formalizations.Reusable

/-- **Wolstenholme's theorem (1862).** For a prime `p ≥ 5`,
`C(2p − 1, p − 1) ≡ 1 (mod p³)` and, equivalently, `C(2p, p) ≡ 2 (mod p³)`, with Mathlib's
`Nat.choose` and `Nat.ModEq`. The proof shows that the harmonic sum `Σ_{k<p} 1/k` vanishes in
`ZMod (p²)` and expands `(p − 1)! · C(2p − 1, p − 1) = Π_{k<p} (p + k)` in `ZMod (p³)`.

* Archive: `Wolstenholme.choose_modEq` (`Formalizations.NumberTheory.Wolstenholme`); the module
  cites no paper DOI of ours.
* Classical reference: J. Wolstenholme, *On certain properties of prime numbers*, Quart. J. Pure
  Appl. Math. 5 (1862) 35–39.
* Example: for `p = 5`, `C(9, 4) = 126 = 1 + 125`. -/
theorem wolstenholme_choose_modEq (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    Nat.choose (2 * p - 1) (p - 1) ≡ 1 [MOD p ^ 3] ∧ Nat.choose (2 * p) p ≡ 2 [MOD p ^ 3] :=
  Wolstenholme.choose_modEq p hp h5

/-- **Touchard's congruence (1933).** For a prime `p` and every `n`, the Bell numbers (Mathlib's
`Nat.bell`) satisfy `B(n + p) = B(n) + B(n + 1)` in `ZMod p`; in particular `B(p) ≡ 2 (mod p)`. The
proof uses the umbral functional `L(Xⁿ) = B(n)` on `(ZMod p)[X]`, for which the falling factorial of
order `p` is `X^p − X`.

* Archive: `Touchard.bell_add_prime` (`Formalizations.Combinatorics.Enumerative.Touchard`); the
  module cites no paper DOI of ours.
* Classical reference: J. Touchard, *Propriétés arithmétiques de certains nombres récurrents*,
  Ann. Soc. Sci. Bruxelles A 53 (1933) 21–31.
* Example: `B(5) = 52 ≡ 2 (mod 5)`. -/
theorem touchard_bell_add_prime (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ((n + p).bell : ZMod p) = n.bell + (n + 1).bell :=
  Touchard.bell_add_prime p n


/-- **Dedekind reciprocity.** For coprime positive integers `h, k`, the Dedekind sums
`s(h, k) = Σ_{r<k} ((r/k)) ((hr/k))`, with the sawtooth `((x)) = x - ⌊x⌋ - 1/2` (and `0` at integers), satisfy
`s(h, k) + s(k, h) = (h² + k² + 1) / (12 h k) − 1/4`.

* Archive: `DedekindSum.ded_reciprocity` (`Formalizations.NumberTheory.DedekindSum`, with the definitions
  `DedekindSum.saw` and `DedekindSum.ded`); the module cites no paper DOI of ours.
* Classical reference: R. Dedekind, in B. Riemann, *Gesammelte mathematische Werke* (2nd ed., 1892), 466–478;
  H. Rademacher, E. Grosswald, *Dedekind Sums*, Carus Math. Monogr. 16 (1972).
* Example: `s(1, 1) + s(1, 1) = 0`. -/
theorem ded_reciprocity {h k : ℕ} (hc : Nat.Coprime h k) (hh : 0 < h) (hk : 0 < k) :
    DedekindSum.ded h k + DedekindSum.ded k h = ((h : ℚ) ^ 2 + k ^ 2 + 1) / (12 * h * k) - 1 / 4 :=
  DedekindSum.ded_reciprocity hc hh hk


/-- **The Dirichlet identity `τ ∗ φ = σ`.** For every `n`, `Σ_{d ∣ n} τ(d) φ(n/d) = σ(n)`, where `τ(d)` is the
number of divisors of `d`, `φ` Euler's totient and `σ(n)` the sum of the divisors of `n`.

* Archive: `DivisorTotient.sum_card_divisors_mul_totient` (`Formalizations.NumberTheory.ArithmeticFunction.DivisorTotient`);
  the module cites no paper DOI of ours.
* Classical reference: G. H. Hardy, E. M. Wright, *An Introduction to the Theory of Numbers*, Ch. XVI (the
  arithmetical functions φ, d and σ).
* Example: for `n = 6`, `τ(1)φ(6) + τ(2)φ(3) + τ(3)φ(2) + τ(6)φ(1) = 2 + 4 + 2 + 4 = 12 = σ(6)`. -/
theorem sum_card_divisors_mul_totient (n : ℕ) :
    ∑ d ∈ n.divisors, d.divisors.card * Nat.totient (n / d) = ∑ d ∈ n.divisors, d :=
  DivisorTotient.sum_card_divisors_mul_totient n

/-- **Cyclotomic reciprocity.** For `n ≥ 2`, reversing the coefficients of the real cyclotomic
polynomial `Φₙ` leaves it unchanged.

* Archive: `CycloParity.reverse_cyclotomic` (`Formalizations.NumberTheory.Cyclotomic.ParityBounds`).
* Classical reference: G. J. O. Jameson, *The cyclotomic polynomials*, Proposition 1.3.
* Example: `Φ₆ = X² - X + 1` is palindromic. -/
theorem reverse_cyclotomic (n : ℕ) (hn : 2 ≤ n) :
    (Polynomial.cyclotomic n ℝ).reverse = Polynomial.cyclotomic n ℝ :=
  CycloParity.reverse_cyclotomic n hn

/-- **Existence of Pisano periods.** For every positive modulus `m`, the Fibonacci sequence
has a positive period modulo `m`, valid from index zero.

* Archive: `Pisano.exists_period` (`Formalizations.NumberTheory.Fibonacci.Pisano`).
* Classical reference: D. D. Wall, *Fibonacci series modulo m*, Amer. Math. Monthly 67 (1960),
  525–532. -/
theorem exists_fib_modEq_period (m : ℕ) (hm : 0 < m) :
    ∃ period, 0 < period ∧ ∀ n, Nat.fib (n + period) ≡ Nat.fib n [MOD m] :=
  Pisano.exists_period m hm

/-- **Parity of Pisano periods.** When `m > 2`, every positive period of the Fibonacci sequence
modulo `m` is even.

* Archive: `Pisano.even_of_period` (`Formalizations.NumberTheory.Fibonacci.Pisano`).
* Classical reference: D. D. Wall, *Fibonacci series modulo m*, Amer. Math. Monthly 67 (1960),
  525–532. -/
theorem even_of_fib_modEq_period (m : ℕ) (hm : 2 < m) (period : ℕ) (hperiod : 0 < period)
    (hper : ∀ n, Nat.fib (n + period) ≡ Nat.fib n [MOD m]) : Even period :=
  Pisano.even_of_period m hm period hperiod hper

/-- **Fibonacci numbers at primes.** For every prime `p`, the Fibonacci number `F_p` equals the
Legendre symbol `(5/p)` in `ZMod p`, including `p = 2` and `p = 5`.

* Archive: `FibLegendre.fib_prime_eq_legendreSym` (`Formalizations.NumberTheory.Fibonacci.FibLegendre`).
* Classical reference: É. Lucas, *Théorie des fonctions numériques simplement périodiques*,
  Amer. J. Math. 1 (1878). -/
theorem fib_prime_eq_legendreSym (p : ℕ) [Fact p.Prime] :
    (Nat.fib p : ZMod p) = (legendreSym p 5 : ZMod p) := by
  simpa only [Int.cast_natCast] using FibLegendre.fib_prime_eq_legendreSym p

/-- **Flynn-Connolly's theorem.** For each odd prime `p` with `p ≡ 2 (mod 3)` and
`p ≡ ±2 (mod 5)`, both `F_(2p)` and `F_(4p)` are odd and satisfy `F_(k+2) ≡ 1 (mod k)`
when substituted for `k`. Infinitely many odd `k` divide `F₁ + ⋯ + Fₖ`.

* Archive: `FibonacciSumDivisibility.flynn_connolly`
  (`Formalizations.NumberTheory.Fibonacci.SumDivisibility`).
* Reference: O. Flynn-Connolly, *On the divisibility of sums of Fibonacci numbers*,
  INTEGERS 25 (2025), A87, Theorem 2 and Corollary 2. -/
theorem flynn_connolly :
    (∀ p n : ℕ, p.Prime → p % 2 = 1 → p % 3 = 2 → (p % 5 = 2 ∨ p % 5 = 3) →
      (n = 2 * p ∨ n = 4 * p) →
      Nat.fib n % 2 = 1 ∧ Nat.fib (Nat.fib n + 2) % Nat.fib n = 1) ∧
    {k : ℕ | Odd k ∧ k ∣ (∑ i ∈ Finset.Icc 1 k, Nat.fib i)}.Infinite :=
  FibonacciSumDivisibility.flynn_connolly

/-- **Amiot's interval lemma.** For `1 < k < n − 1`, some point of the cyclic interval of length
`k` starting at `c₀` leaves the interval when multiplied by any specified unit `a ≠ ±1`.
Membership in this interval is expressed by `(x - c₀).val < k`.

* Archive: `Segmentos.amiot_interval` (`Formalizations.NumberTheory.SymplecticCharacterOrders.Segments`).
* Classical reference: E. Amiot, *About the number of generators of a musical scale* (2009),
  Theorem 1. -/
theorem amiot_interval {n k : ℕ} (hk1 : 1 < k) (hk2 : k < n - 1) (c₀ : ZMod n)
    (a : (ZMod n)ˣ) (ha1 : (a : ZMod n) ≠ 1) (ha2 : (a : ZMod n) ≠ -1) :
    ¬ ∀ x : ZMod n, (x - c₀).val < k → ((a : ZMod n) * x - c₀).val < k :=
  Segmentos.amiot_interval hk1 hk2 c₀ a ha1 ha2

end Formalizations.Reusable
