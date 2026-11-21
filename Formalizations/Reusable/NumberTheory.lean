/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.NumberTheory.Wolstenholme
public import Formalizations.Combinatorics.Enumerative.Touchard
public import Formalizations.NumberTheory.DedekindSum

/-!
# Reusable layer: number theory

Stable names for congruences of the archive. Each theorem is proved by the archive theorem it
re-exposes (no proof is copied). The module imported here is general number theory, not a paper of
the archive, and imports only Mathlib.

## Main results

* `Formalizations.Reusable.ded_reciprocity`: Dedekind's reciprocity law for the Dedekind sums `s(h, k)`
  (archive: `DedekindSum.ded_reciprocity`).
* `Formalizations.Reusable.wolstenholme_choose_modEq`: Wolstenholme's theorem,
  `C(2p − 1, p − 1) ≡ 1` and `C(2p, p) ≡ 2 (mod p³)` for primes `p ≥ 5` (archive:
  `Wolstenholme.choose_modEq`).
* `Formalizations.Reusable.touchard_bell_add_prime`: Touchard's congruence for Bell numbers,
  `B(n + p) ≡ B(n) + B(n + 1) (mod p)` for every prime `p` (archive: `Touchard.bell_add_prime`).
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

end Formalizations.Reusable
