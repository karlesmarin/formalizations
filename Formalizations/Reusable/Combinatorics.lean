/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.Combinatorics.Choose.MiddleBinomialDensity

/-!
# Reusable layer: combinatorics and number theory

A stable name for Pomerance's density theorem on divisors of the middle binomial coefficient. The
theorem is proved by the archive theorem it re-exposes (no proof is copied).

## Main results

* `Formalizations.Reusable.pomerance_density_add_dvd_centralBinom`: for every `k ≥ 1`, the
  proportion of `n < x` with `n + k ∣ C(2n, n)` tends to `1` (archive:
  `MiddleBinomial.tendsto_density_add_dvd_centralBinom`).
-/

@[expose] public section

open Filter Topology

namespace Formalizations.Reusable

/-- **Pomerance's theorem on the middle binomial coefficient** (Theorem 2 of the paper). For every
integer `k ≥ 1`, the set of `n` with `n + k ∣ C(2n, n)` has asymptotic density `1`:
`#{n < x : n + k ∣ C(2n, n)} / x → 1` as `x → ∞`. (For `k = 1` every `n` qualifies: `C(2n, n)/(n+1)`
is the Catalan number.)

* Archive: `MiddleBinomial.tendsto_density_add_dvd_centralBinom`
  (`Formalizations.Combinatorics.Choose.MiddleBinomialDensity`, with the counting of base-`p`
  digits `≥ p/2` for the primes `p < 2k`).
* Paper formalized: C. Pomerance, *Divisors of the middle binomial coefficient*, Amer. Math. Monthly
  122 (2015) 636–644, Theorem 2, doi:10.4169/amer.math.monthly.122.7.636.
* Example: `pomerance_density_add_dvd_centralBinom 2 (by norm_num)`: almost every `n` has
  `n + 2 ∣ C(2n, n)`. -/
theorem pomerance_density_add_dvd_centralBinom (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun x : ℕ =>
        (((Finset.range x).filter (fun n => n + k ∣ Nat.centralBinom n)).card : ℝ) / x)
      atTop (𝓝 1) :=
  MiddleBinomial.tendsto_density_add_dvd_centralBinom k hk

end Formalizations.Reusable
