/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Lamé's theorem on Euclid's algorithm

`Lame.euclidSteps a b` counts the division steps `(a, b) ↦ (b, a mod b)` of Euclid's algorithm until
`b = 0`. If the algorithm on `(x, y)` with `y > 0` takes `n` steps, then `F_{n+1} ≤ y` (Fibonacci
numbers, `F_1 = F_2 = 1`), with equality at consecutive Fibonacci numbers; since `10^k ≤ F_{5k+2}`,
`n` is at most five times the number of decimal digits of `y` (Lamé, 1844). The proof is a strong
induction on `b` with the invariant `F_{n+1} ≤ b` and, when `b < a`, `F_{n+2} ≤ a`.

## Main results

* `Lame.fib_euclidSteps_le`: F_(n+1) <= y and n <= 5 * (decimal digits of y), n = Euclid steps on (x, y)

## References

* G. Lamé, *Note sur la limite du nombre des divisions dans la recherche du plus grand commun diviseur entre deux nombres entiers*, C. R. Acad. Sci. Paris 19 (1844), 867–870.
-/

@[expose] public section

namespace Lame

/-- Number of division steps of Euclid's algorithm on `(a, b)`: `(a, b) ↦ (b, a mod b)` until `b = 0`. -/
def euclidSteps : ℕ → ℕ → ℕ
  | _, 0 => 0
  | a, b + 1 => euclidSteps (b + 1) (a % (b + 1)) + 1
termination_by _ b => b
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos _)

private lemma steps_succ (a b : ℕ) (hb : 0 < b) :
    euclidSteps a b = euclidSteps b (a % b) + 1 := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
  rw [euclidSteps]

private lemma steps_zero (a : ℕ) : euclidSteps a 0 = 0 := by
  rw [euclidSteps]

private lemma aux (b : ℕ) : ∀ a, 0 < b →
    Nat.fib (euclidSteps a b + 1) ≤ b ∧ (b < a → Nat.fib (euclidSteps a b + 2) ≤ a) := by
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro a hb
    have hr : a % b < b := Nat.mod_lt _ hb
    have hdiv := Nat.div_add_mod a b
    rw [steps_succ a b hb]
    rcases Nat.eq_zero_or_pos (a % b) with h0 | hpos
    · rw [h0, steps_zero]
      refine ⟨by simp; omega, fun hba => ?_⟩
      have h2 : 2 ≤ a / b := by
        by_contra hlt
        have h1 : a / b ≤ 1 := by omega
        have : b * (a / b) ≤ b * 1 := Nat.mul_le_mul_left _ h1
        omega
      have : b * 2 ≤ b * (a / b) := Nat.mul_le_mul_left _ h2
      have h3 : Nat.fib (0 + 1 + 2) = 2 := by decide
      rw [h3]
      omega
    · have hb' : Nat.fib (euclidSteps b (a % b) + 2) ≤ b := (ih (a % b) hr b hpos).2 hr
      have h1 := (ih (a % b) hr b hpos).1
      refine ⟨hb', fun hba => ?_⟩
      have hq : 1 ≤ a / b := (Nat.le_div_iff_mul_le hb).2 (by omega)
      have : b * 1 ≤ b * (a / b) := Nat.mul_le_mul_left _ hq
      have e : Nat.fib (euclidSteps b (a % b) + 1 + 2)
          = Nat.fib (euclidSteps b (a % b) + 1) + Nat.fib (euclidSteps b (a % b) + 2) :=
        Nat.fib_add_two
      rw [e]
      omega

private lemma fib_ge_pow (k : ℕ) : 10 ^ k ≤ Nat.fib (5 * k + 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : 5 * (k + 1) + 2 = 5 * k + 7 := by ring
    rw [e, pow_succ]
    generalize 5 * k = j at ih ⊢
    have h2 : Nat.fib (j + 2) = Nat.fib j + Nat.fib (j + 1) := Nat.fib_add_two
    have h3 : Nat.fib (j + 3) = Nat.fib (j + 1) + Nat.fib (j + 2) := Nat.fib_add_two
    have h4 : Nat.fib (j + 4) = Nat.fib (j + 2) + Nat.fib (j + 3) := Nat.fib_add_two
    have h5 : Nat.fib (j + 5) = Nat.fib (j + 3) + Nat.fib (j + 4) := Nat.fib_add_two
    have h6 : Nat.fib (j + 6) = Nat.fib (j + 4) + Nat.fib (j + 5) := Nat.fib_add_two
    have h7 : Nat.fib (j + 7) = Nat.fib (j + 5) + Nat.fib (j + 6) := Nat.fib_add_two
    have hm : Nat.fib j ≤ Nat.fib (j + 1) := Nat.fib_mono (Nat.le_succ j)
    omega

/-- **Lamé's theorem (1844).** If Euclid's algorithm on `(x, y)`, `y > 0`, takes `n` steps, then
`F_{n+1} ≤ y`; hence `n` is at most five times the number of decimal digits of `y`. -/
theorem fib_euclidSteps_le (x y : ℕ) (hy : 0 < y) :
    Nat.fib (euclidSteps x y + 1) ≤ y ∧ euclidSteps x y ≤ 5 * (Nat.digits 10 y).length := by
  have h1 := (aux y x hy).1
  refine ⟨h1, ?_⟩
  by_contra hlt
  have hlt' : 5 * (Nat.digits 10 y).length + 2 ≤ euclidSteps x y + 1 := by omega
  have hy10 : y < 10 ^ (Nat.digits 10 y).length :=
    Nat.lt_base_pow_length_digits (by norm_num)
  have h2 := Nat.fib_mono hlt'
  have h3 := fib_ge_pow (Nat.digits 10 y).length
  omega

end Lame
