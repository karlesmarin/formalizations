/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases

/-!
# Fibonacci numbers at primes and the Legendre symbol

For every prime `p`, `F(p) ≡ (5/p) (mod p)` (with `(5/5) = 0`). With `M` the Fibonacci matrix over
`ZMod p` and `S = 2M - 1`, one has `S² = 5`; the Frobenius on the commuting matrices gives
`2 M^p = 5^{(p-1)/2} S + 1`, whose `(0, 1)` entry is `F(p) = 5^{(p-1)/2}`, which is the Legendre
symbol by Euler's criterion (`legendreSym.eq_pow`); `p = 2` is checked directly.

## Main results

* `FibLegendre.fib_prime_eq_legendreSym`: F(p) = (5/p) in ZMod p for every prime p

## References

* E. Lucas, *Théorie des fonctions numériques simplement périodiques*, Amer. J. Math. 1 (1878).
* The companion divisibility p ∣ F(p − (5/p)) is in facebookresearch/atlas-lean, `MathlibExt/NumberTheory/Recurrences/FibonacciPrimeDivisibility.lean`.
-/

@[expose] public section

namespace FibLegendre

/-- The Fibonacci matrix `[[1,1],[1,0]]` over `ZMod p`. -/
private def M (p : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod p) := !![1, 1; 1, 0]

private theorem M_sq (p : ℕ) : M p * M p = M p + 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M, Matrix.mul_apply, Fin.sum_univ_two]

private theorem M_pow (p n : ℕ) :
    M p ^ (n + 1) = (Nat.fib (n + 1) : ZMod p) • M p + (Nat.fib n : ZMod p) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : M p ^ (n + 1 + 1) = M p ^ (n + 1) * M p := pow_succ _ _
    rw [h, ih, add_mul, smul_mul_assoc, smul_mul_assoc, M_sq, Matrix.one_mul, Nat.fib_add_two]
    simp only [smul_add, Nat.cast_add, add_smul]
    abel

private theorem M_pow_entry (p n : ℕ) : (M p ^ (n + 1)) 0 1 = (Nat.fib (n + 1) : ZMod p) := by
  rw [M_pow]
  simp [M]

/-- **Fibonacci numbers at primes.** For every prime `p`, `F(p) ≡ (5/p) (mod p)`, with `(5/p)` the
Legendre symbol (`0` for `p = 5`). -/
theorem fib_prime_eq_legendreSym (p : ℕ) [Fact p.Prime] :
    ((Nat.fib p : ℤ) : ZMod p) = (legendreSym p 5 : ZMod p) := by
  have hp : p.Prime := Fact.out
  rw [legendreSym.eq_pow]
  push_cast
  rcases hp.eq_two_or_odd' with h2 | hodd
  · subst h2
    revert hp
    decide +revert
  obtain ⟨m, hm⟩ := hodd
  have hdiv : p / 2 = m := by omega
  rw [hdiv]
  have hp2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 ((ZMod.natCast_eq_zero_iff 2 p).1 h')
    omega
  let σ : ZMod p →+* Matrix (Fin 2) (Fin 2) (ZMod p) := algebraMap (ZMod p) _
  have hσ : ∀ (c : ZMod p) (A : Matrix (Fin 2) (Fin 2) (ZMod p)) (i j : Fin 2),
      (σ c * A) i j = c * A i j := by
    intro c A i j
    simp [σ, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_mul]
  let S : Matrix (Fin 2) (Fin 2) (ZMod p) := σ 2 * M p - 1
  have hS2 : S * S = σ 5 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [S, σ, M, Matrix.mul_apply, Fin.sum_univ_two, Matrix.algebraMap_eq_diagonal,
        Matrix.diagonal_apply, Matrix.one_apply] <;> ring
  have hSpow : S ^ p = σ ((5 : ZMod p) ^ m) * S := by
    refine (congrArg (fun k => S ^ k) hm).trans ?_
    rw [pow_succ, pow_mul, sq, hS2, ← map_pow]
  have hinj : Function.Injective (algebraMap (ZMod p) (Matrix (Fin 2) (Fin 2) (ZMod p))) := by
    intro a b h
    have := congrFun (congrFun h 0) 0
    simpa [Matrix.algebraMap_eq_diagonal] using this
  have : CharP (Matrix (Fin 2) (Fin 2) (ZMod p)) p := charP_of_injective_algebraMap hinj p
  have hfrob : (S + 1) ^ p = S ^ p + 1 := by
    rw [add_pow_char_of_commute (R := Matrix (Fin 2) (Fin 2) (ZMod p)) (p := p) (Commute.one_right S), one_pow]
  have hS1 : S + 1 = σ 2 * M p := sub_add_cancel _ _
  have hcomm : Commute (σ 2) (M p) := Algebra.commutes _ _
  have hfrob2 : (σ 2 * M p) ^ p = σ 2 * M p ^ p := by
    rw [hcomm.mul_pow, ← map_pow, ZMod.pow_card]
  have key : σ 2 * M p ^ p = σ ((5 : ZMod p) ^ m) * S + 1 := by
    rw [← hfrob2, ← hS1, hfrob, hSpow]
  have hent := congrArg (fun A => A 0 1) key
  have hF : (M p ^ p) 0 1 = (Nat.fib p : ZMod p) := by
    have := M_pow_entry p (p - 1)
    rwa [Nat.sub_add_cancel hp.one_lt.le] at this
  rw [hσ, hF, Matrix.add_apply, hσ] at hent
  simp [S, σ, M, Matrix.algebraMap_eq_diagonal] at hent
  exact mul_left_cancel₀ hp2 (by linear_combination hent)

end FibLegendre
