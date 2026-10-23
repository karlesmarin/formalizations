/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Order.Basic

/-!
# Divisibility counts of the six positive-root values of G2 at q = 2, 3

Combinatorial half of Corollary cor:g2 of "characters at a_P". For lambda = a w1 + b w2, the six
values (lambda+rho, alpha) are u, v, u+v, 2u+v, 3u+v, 3u+2v with u = a+1, v = 3(b+1); N_q counts
those divisible by q and r_q the same count on 1,3,4,5,6,9. We prove N_3 = r_3 iff a is not 2 mod 3
and N_2 = r_2 iff a, b are not both odd, together with the strict forms N_q > r_q. The
identification of "character vanishes at a_P^k" with "N_q > r_q" is the paper's criterion and is NOT
formalized; no Lie theory is used.

## Main results

* `KostantAlphabet.G2Counts.N_three_eq_iff`: N_3 = r_3 iff a is not 2 mod 3
* `KostantAlphabet.G2Counts.N_two_eq_iff`: N_2 = r_2 iff a, b are not both odd
* `KostantAlphabet.G2Counts.N_three_gt_iff`: r_3 < N_3 iff a = 2 mod 3
* `KostantAlphabet.G2Counts.N_two_gt_iff`: r_2 < N_2 iff a, b both odd

## References

* C. Marín, *Integer character values on the ρ-line of Sp(2m)*, Zenodo (2026),
  doi:10.5281/zenodo.22683561, `cor:g2`.
-/

@[expose] public section

namespace KostantAlphabet.G2Counts
/-- The six values `(λ+ρ, α)` for `λ = aω₁ + bω₂`. -/
def values (a b : ℕ) : List ℕ :=
  [a + 1, 3 * (b + 1), (a + 1) + 3 * (b + 1), 2 * (a + 1) + 3 * (b + 1),
   3 * (a + 1) + 3 * (b + 1), 3 * (a + 1) + 2 * (3 * (b + 1))]

/-- `N_q(λ)`: number of the six values divisible by `q`. -/
def N (q a b : ℕ) : ℕ := (values a b).countP (fun x => decide (q ∣ x))

/-- `r_q`: multiples of `q` among `1,3,4,5,6,9`. -/
def r (q : ℕ) : ℕ := ([1, 3, 4, 5, 6, 9] : List ℕ).countP (fun x => decide (q ∣ x))

theorem r_three : r 3 = 3 := by decide
theorem r_two : r 2 = 2 := by decide

/-- `q = 3`: `N₃ = r₃ ↔ a ≢ 2 (3)`. -/
theorem N_three_eq_iff (a b : ℕ) : N 3 a b = r 3 ↔ ¬ a % 3 = 2 := by
  rw [r_three]
  simp only [N, values, List.countP_cons, List.countP_nil, decide_eq_true_eq]
  split_ifs <;> omega

/-- `q = 2`: `N₂ = r₂ ↔ ¬(a, b both odd)`. -/
theorem N_two_eq_iff (a b : ℕ) : N 2 a b = r 2 ↔ ¬ (a % 2 = 1 ∧ b % 2 = 1) := by
  rw [r_two]
  simp only [N, values, List.countP_cons, List.countP_nil, decide_eq_true_eq]
  split_ifs <;> omega

/-- `q = 3`: `N₃ > r₃` exactly when `a ≡ 2 (3)` (and `N₃ ≥ r₃` always). -/
theorem N_three_gt_iff (a b : ℕ) : r 3 < N 3 a b ↔ a % 3 = 2 := by
  rw [r_three]
  simp only [N, values, List.countP_cons, List.countP_nil, decide_eq_true_eq]
  split_ifs <;> omega

/-- `q = 2`: `N₂ > r₂` exactly when `a, b` both odd. -/
theorem N_two_gt_iff (a b : ℕ) : r 2 < N 2 a b ↔ (a % 2 = 1 ∧ b % 2 = 1) := by
  rw [r_two]
  simp only [N, values, List.countP_cons, List.countP_nil, decide_eq_true_eq]
  split_ifs <;> omega

end KostantAlphabet.G2Counts