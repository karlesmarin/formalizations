/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.NumberTheory.Wolstenholme

/-!
# Reusable layer: number theory

Stable names for congruences of the archive. Each theorem is proved by the archive theorem it
re-exposes (no proof is copied). The module imported here is general number theory, not a paper of
the archive, and imports only Mathlib.

## Main results

* `Formalizations.Reusable.wolstenholme_choose_modEq`: Wolstenholme's theorem,
  `C(2p − 1, p − 1) ≡ 1` and `C(2p, p) ≡ 2 (mod p³)` for primes `p ≥ 5` (archive:
  `Wolstenholme.choose_modEq`).
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

end Formalizations.Reusable
