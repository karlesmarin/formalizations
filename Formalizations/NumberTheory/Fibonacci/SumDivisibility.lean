/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Formalizations.NumberTheory.Fibonacci.Pisano
public import Formalizations.NumberTheory.Fibonacci.FibLegendre
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

/-!
# Infinitely many odd k divide F_1 + ⋯ + F_k (Flynn-Connolly 2025)

For an odd prime `p` with `p ≡ 2 (mod 3)` and `p ≡ ±2 (mod 5)`, and `n = 2p` or `n = 4p`, the
Fibonacci number `F_n` is odd and `F_{F_n + 2} ≡ 1 (mod F_n)`, so `F_n` divides
`F_1 + ⋯ + F_{F_n} = F_{F_n + 2} − 1`; by Dirichlet's theorem there are infinitely many odd `k` with
`k ∣ F_1 + ⋯ + F_k`, the conjecture of Fatehizadeh and Yaqubi (O. Flynn-Connolly, INTEGERS 25 (2025)
A87). The statements are those of atlas-lean's `FibonacciSumDivisibilityWanted`. Proof: for even `n`
the Pisano period of `F_n` divides `2n` (Cassini); for such `p`, `p ∣ F_{p+1}` (from `F_p ≡ (5/p)`,
proved earlier in this library), so the period modulo `4p` and `8p` divides `2(p + 1)`.

## Main results

* `FibonacciSumDivisibility.period_fib_even`: for even n, F_{k+2n} ≡ F_k (mod F_n)
* `FibonacciSumDivisibility.fib_succ_prime_dvd`: p ∣ F_{p+1} when p ≡ ±2 (mod 5)
* `FibonacciSumDivisibility.flynn_connolly`: Theorem 2 and Corollary 2 (atlas-lean wanted statements)

## References

* O. Flynn-Connolly, «On the divisibility of sums of Fibonacci numbers», INTEGERS 25 (2025) A87; arXiv:2504.09938 v3, Thm 2 y Cor 2.
* A. Fatehizadeh, D. Yaqubi, «Average of the Fibonacci numbers», J. Integer Seq. 25 (2022), Art. 22.2.6 (la conjetura).
* facebookresearch/atlas-lean, WantedExt/NumberTheory/Recurrences/FibonacciSumDivisibilityWanted.lean (Apache-2.0).
-/

@[expose] public section

namespace FibonacciSumDivisibility

open Nat

/-- `F_{k+T} ≡ F_k (mod m)` for all `k`. -/
def Per (m T : ℕ) : Prop := ∀ k, ((Nat.fib (k + T) : ℕ) : ZMod m) = (Nat.fib k : ℕ)

theorem per_of_return {m : ℕ} (T : ℕ) (h0 : ((Nat.fib T : ℕ) : ZMod m) = 0)
    (h1 : ((Nat.fib (T + 1) : ℕ) : ZMod m) = 1) : Per m T := by
  intro k
  cases T with
  | zero => simp
  | succ t =>
    have hft : ((Nat.fib t : ℕ) : ZMod m) = 1 := by
      have e : Nat.fib (t + 2) = Nat.fib t + Nat.fib (t + 1) := Nat.fib_add_two
      have := h1
      rw [e] at this
      push_cast at this h0
      linear_combination this - h0
    have e : Nat.fib (k + (t + 1)) = Nat.fib k * Nat.fib t + Nat.fib (k + 1) * Nat.fib (t + 1) := by
      exact Nat.fib_add k t
    rw [e]
    push_cast
    rw [hft, h0]
    ring

theorem per_mul {m T : ℕ} (h : Per m T) (j : ℕ) : Per m (j * T) := by
  induction j with
  | zero => intro k; simp
  | succ j ih =>
    intro k
    rw [show k + (j + 1) * T = (k + T) + j * T by ring, ih (k + T), h k]

theorem per_crt {a b T : ℕ} (hc : Nat.Coprime a b) (h1 : Per a T) (h2 : Per b T) : Per (a * b) T := by
  intro k
  rw [ZMod.natCast_eq_natCast_iff]
  exact (Nat.modEq_and_modEq_iff_modEq_mul hc).1
    ⟨(ZMod.natCast_eq_natCast_iff _ _ _).1 (h1 k), (ZMod.natCast_eq_natCast_iff _ _ _).1 (h2 k)⟩

/-- **Proposition 2** (Flynn-Connolly): for even `n > 1`, `F_{k+2n} ≡ F_k (mod F_n)`. -/
theorem period_fib_even (n : ℕ) (hn : Even n) (_hn1 : 1 < n) :
    ∀ k, Nat.fib (k + 2 * n) ≡ Nat.fib k [MOD Nat.fib n] := by
  have hP : Per (Nat.fib n) (2 * n) := by
    apply per_of_return
    · rw [ZMod.natCast_eq_zero_iff]
      exact Nat.fib_dvd n (2 * n) ⟨2, by ring⟩
    · have hc := congrArg (Int.cast : ℤ → ZMod (Nat.fib n)) (Pisano.cassini n)
      have hpar : (-1 : ℤ) ^ (n + 1) = -1 := by
        rw [pow_succ, hn.neg_one_pow]; norm_num
      rw [hpar] at hc
      have e : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
      rw [e] at hc
      have h0 : ((Nat.fib n : ℕ) : ZMod (Nat.fib n)) = 0 := ZMod.natCast_self _
      push_cast at hc
      rw [h0] at hc
      rw [show 2 * n + 1 = 2 * n + 1 from rfl, Nat.fib_two_mul_add_one]
      push_cast
      rw [h0]
      linear_combination -hc
  intro k
  exact (ZMod.natCast_eq_natCast_iff _ _ _).1 (hP k)

/-- The `(0,0)` entry of the Frobenius identity for the Fibonacci matrix (copy of the method of
`FibLegendre.fib_prime_eq_legendreSym`, whose `(0,1)` entry gives `F_p`): `2 F_{p+1} = 5^{(p-1)/2} + 1`. -/
theorem two_fib_succ (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) * (Nat.fib (p + 1) : ℕ) = (5 : ZMod p) ^ (p / 2) + 1 := by
  have hp : p.Prime := Fact.out
  have hodd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hp).2 hp2
  obtain ⟨m, hm⟩ : ∃ m, p = 2 * m + 1 := ⟨p / 2, by omega⟩
  have hdiv : p / 2 = m := by omega
  rw [hdiv]
  have hp2' : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 ((ZMod.natCast_eq_zero_iff 2 p).1 h')
    omega
  let M : Matrix (Fin 2) (Fin 2) (ZMod p) := !![1, 1; 1, 0]
  have M_sq : M * M = M + 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M, Matrix.mul_apply, Fin.sum_univ_two]
  have M_pow : ∀ n : ℕ, M ^ (n + 1) = (Nat.fib (n + 1) : ZMod p) • M
      + (Nat.fib n : ZMod p) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h : M ^ (n + 1 + 1) = M ^ (n + 1) * M := pow_succ _ _
      rw [h, ih, add_mul, smul_mul_assoc, smul_mul_assoc, M_sq, Matrix.one_mul, Nat.fib_add_two]
      simp only [smul_add, Nat.cast_add, add_smul]
      abel
  let σ : ZMod p →+* Matrix (Fin 2) (Fin 2) (ZMod p) := algebraMap (ZMod p) _
  have hσ : ∀ (c : ZMod p) (A : Matrix (Fin 2) (Fin 2) (ZMod p)) (i j : Fin 2),
      (σ c * A) i j = c * A i j := by
    intro c A i j
    simp [σ, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_mul]
  let S : Matrix (Fin 2) (Fin 2) (ZMod p) := σ 2 * M - 1
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
    rw [add_pow_char_of_commute (R := Matrix (Fin 2) (Fin 2) (ZMod p)) (p := p) (Commute.one_right S),
      one_pow]
  have hS1 : S + 1 = σ 2 * M := sub_add_cancel _ _
  have hcomm : Commute (σ 2) M := Algebra.commutes _ _
  have hfrob2 : (σ 2 * M) ^ p = σ 2 * M ^ p := by
    rw [hcomm.mul_pow, ← map_pow, ZMod.pow_card]
  have key : σ 2 * M ^ p = σ ((5 : ZMod p) ^ m) * S + 1 := by
    rw [← hfrob2, ← hS1, hfrob, hSpow]
  have hent := congrArg (fun A => A 0 0) key
  have hF : (M ^ p) 0 0 = (Nat.fib (p + 1) : ZMod p) := by
    have h1 := M_pow (p - 1)
    rw [Nat.sub_add_cancel hp.one_lt.le] at h1
    rw [h1]
    have e : Nat.fib (p + 1) = Nat.fib (p - 1) + Nat.fib p := by
      have := @Nat.fib_add_two (p - 1)
      rwa [show p - 1 + 2 = p + 1 by omega, show p - 1 + 1 = p by omega] at this
    rw [e]
    simp [M]
    ring
  rw [hσ, hF, Matrix.add_apply, hσ] at hent
  simp [S, σ, M, Matrix.algebraMap_eq_diagonal] at hent
  linear_combination hent

theorem not_square_two : ¬IsSquare (2 : ZMod 5) := by
  have h : ∀ r : ZMod 5, (2 : ZMod 5) ≠ r * r := by decide
  exact fun ⟨r, hr⟩ => h r hr

theorem not_square_three : ¬IsSquare (3 : ZMod 5) := by
  have h : ∀ r : ZMod 5, (3 : ZMod 5) ≠ r * r := by decide
  exact fun ⟨r, hr⟩ => h r hr

/-- `legendreSym p 5 = -1` for a prime `p ≡ ±2 (mod 5)`. -/
theorem legendreSym_five (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (h5 : p % 5 = 2 ∨ p % 5 = 3) :
    legendreSym p 5 = -1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hqr : legendreSym p ((5 : ℕ) : ℤ) = legendreSym 5 (p : ℤ) :=
    legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := p) (by norm_num) hp2
  rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) by norm_num, hqr, legendreSym.mod 5 (p : ℤ)]
  rcases h5 with h | h
  · rw [show (p : ℤ) % ((5 : ℕ) : ℤ) = 2 by omega, legendreSym.eq_neg_one_iff]
    push_cast
    exact not_square_two
  · rw [show (p : ℤ) % ((5 : ℕ) : ℤ) = 3 by omega, legendreSym.eq_neg_one_iff]
    push_cast
    exact not_square_three

/-- **Wall** (case `(5/p) = -1`): for a prime `p ≡ ±2 (mod 5)`, `F_p ≡ -1` and `p ∣ F_{p+1}`. -/
theorem fib_succ_prime_dvd (p : ℕ) (hp : p.Prime) (h5 : p % 5 = 2 ∨ p % 5 = 3) :
    p ∣ Nat.fib (p + 1) ∧ ((Nat.fib p : ℕ) : ZMod p) = -1 := by
  have : Fact p.Prime := ⟨hp⟩
  rcases hp.eq_two_or_odd with h2 | hodd
  · subst h2
    decide +revert
  have hp2 : p ≠ 2 := by omega
  have hl := legendreSym_five p hp2 h5
  have hF : ((Nat.fib p : ℕ) : ZMod p) = -1 := by
    have := FibLegendre.fib_prime_eq_legendreSym p
    rw [hl] at this
    simpa using this
  refine ⟨?_, hF⟩
  rw [← ZMod.natCast_eq_zero_iff]
  have h2 := two_fib_succ p hp2
  have hpow : (5 : ZMod p) ^ (p / 2) = -1 := by
    have := legendreSym.eq_pow p 5
    rw [hl] at this
    push_cast at this
    simpa using this.symm
  rw [hpow] at h2
  have hp2' : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 ((ZMod.natCast_eq_zero_iff 2 p).1 h')
    omega
  exact mul_left_cancel₀ hp2' (by linear_combination h2)

/-- The period `2p + 2 = 2(p+1)` modulo `p`. -/
theorem per_p (p : ℕ) (hp : p.Prime) (h5 : p % 5 = 2 ∨ p % 5 = 3) : Per p (2 * p + 2) := by
  obtain ⟨hb, ha⟩ := fib_succ_prime_dvd p hp h5
  have hb' : ((Nat.fib (p + 1) : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hb
  have e2 : (Nat.fib (p + 2) : ZMod p) = Nat.fib p + Nat.fib (p + 1) := by
    rw [Nat.fib_add_two]; push_cast; ring
  apply per_of_return
  · have : Nat.fib (2 * p + 2) = Nat.fib (p + 1) * Nat.fib p + Nat.fib (p + 1 + 1) * Nat.fib (p + 1) := by
      rw [show 2 * p + 2 = (p + 1) + p + 1 by ring, Nat.fib_add]
    rw [this]
    push_cast
    rw [show p + 1 + 1 = p + 2 by rfl, e2, hb']
    ring
  · have : Nat.fib (2 * p + 2 + 1) = Nat.fib (p + 1) * Nat.fib (p + 1) + Nat.fib (p + 1 + 1) * Nat.fib (p + 1 + 1) := by
      rw [show 2 * p + 2 + 1 = (p + 1) + (p + 1) + 1 by ring, Nat.fib_add]
    rw [this]
    push_cast
    rw [show p + 1 + 1 = p + 2 by rfl, e2, hb', ha]
    ring

theorem per_four : Per 4 6 := by
  apply per_of_return <;> norm_num [Nat.fib_add_two] <;> decide

theorem per_eight : Per 8 12 := by
  apply per_of_return <;> norm_num [Nat.fib_add_two] <;> decide

theorem per_two : Per 2 3 := by
  apply per_of_return <;> norm_num [Nat.fib_add_two] <;> decide

section Hyp

variable {p : ℕ} (hp : p.Prime) (hpodd : p % 2 = 1) (hp3 : p % 3 = 2) (hp5 : p % 5 = 2 ∨ p % 5 = 3)

include hp hpodd hp3 hp5

theorem per_4p : Per (4 * p) (2 * p + 2) := by
  have hc : Nat.Coprime 4 p := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2
    (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega))
  refine per_crt hc ?_ (per_p p hp hp5)
  obtain ⟨j, hj⟩ : 6 ∣ p + 1 := by omega
  have := per_mul per_four (2 * j)
  rwa [show 2 * j * 6 = 2 * p + 2 by omega] at this

theorem per_8p : Per (8 * p) (2 * p + 2) := by
  have hc : Nat.Coprime 8 p := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2
    (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega))
  refine per_crt hc ?_ (per_p p hp hp5)
  obtain ⟨j, hj⟩ : 6 ∣ p + 1 := by omega
  have := per_mul per_eight j
  rwa [show j * 12 = 2 * p + 2 by omega] at this

/-- `F_{2p} ≡ -1 (mod 4p)`. -/
theorem fib_two_mul_mod : (4 * p) ∣ Nat.fib (2 * p) + 1 := by
  have P := per_4p hp hpodd hp3 hp5
  have hA := P 0
  have hB := P 1
  rw [zero_add] at hA
  rw [add_comm 1 (2 * p + 2)] at hB
  replace hB : ((Nat.fib (2 * p + 3) : ℕ) : ZMod (4 * p)) = ((Nat.fib 1 : ℕ) : ZMod (4 * p)) := hB
  have e3 : Nat.fib (2 * p + 3) = Nat.fib (2 * p + 1) + Nat.fib (2 * p + 2) := Nat.fib_add_two
  have e2 : Nat.fib (2 * p + 2) = Nat.fib (2 * p) + Nat.fib (2 * p + 1) := Nat.fib_add_two
  rw [← ZMod.natCast_eq_zero_iff]
  simp only [Nat.fib_zero, Nat.fib_one, Nat.cast_zero, Nat.cast_one] at hA hB
  have e3' := congrArg (Nat.cast : ℕ → ZMod (4 * p)) e3
  have e2' := congrArg (Nat.cast : ℕ → ZMod (4 * p)) e2
  push_cast at e3' e2' hA hB ⊢
  linear_combination -e2' + e3' + 2 * hA - hB

/-- `F_{4p} ≡ -3 (mod 8p)`. -/
theorem fib_four_mul_mod : (8 * p) ∣ Nat.fib (4 * p) + 3 := by
  have P := per_mul (per_8p hp hpodd hp3 hp5) 2
  have hA := P 0
  have hB := P 1
  rw [zero_add, show 2 * (2 * p + 2) = 4 * p + 4 by ring] at hA
  rw [add_comm 1 _, show 2 * (2 * p + 2) = 4 * p + 4 by ring] at hB
  replace hB : ((Nat.fib (4 * p + 5) : ℕ) : ZMod (8 * p)) = ((Nat.fib 1 : ℕ) : ZMod (8 * p)) := hB
  have e1 : Nat.fib (4 * p + 2) = Nat.fib (4 * p) + Nat.fib (4 * p + 1) := Nat.fib_add_two
  have e2 : Nat.fib (4 * p + 3) = Nat.fib (4 * p + 1) + Nat.fib (4 * p + 2) := Nat.fib_add_two
  have e3 : Nat.fib (4 * p + 4) = Nat.fib (4 * p + 2) + Nat.fib (4 * p + 3) := Nat.fib_add_two
  have e4 : Nat.fib (4 * p + 5) = Nat.fib (4 * p + 3) + Nat.fib (4 * p + 4) := Nat.fib_add_two
  rw [← ZMod.natCast_eq_zero_iff]
  simp only [Nat.fib_zero, Nat.fib_one, Nat.cast_zero, Nat.cast_one] at hA hB
  have e1' := congrArg (Nat.cast : ℕ → ZMod (8 * p)) e1
  have e2' := congrArg (Nat.cast : ℕ → ZMod (8 * p)) e2
  have e3' := congrArg (Nat.cast : ℕ → ZMod (8 * p)) e3
  have e4' := congrArg (Nat.cast : ℕ → ZMod (8 * p)) e4
  push_cast at e1' e2' e3' e4' hA hB ⊢
  have x3 : (Nat.fib (4 * p + 3) : ZMod (8 * p)) = 1 := by linear_combination -e4' + hB - hA
  have x2 : (Nat.fib (4 * p + 2) : ZMod (8 * p)) = -1 := by linear_combination -e3' + hA - x3
  have x1 : (Nat.fib (4 * p + 1) : ZMod (8 * p)) = 2 := by linear_combination -e2' + x3 - x2
  linear_combination -e1' + x2 - x1

end Hyp

/-- `F_n` is odd when `3 ∤ n`. -/
theorem fib_odd_of_not_dvd (n : ℕ) (h : n % 3 ≠ 0) : Nat.fib n % 2 = 1 := by
  have h1 := per_mul per_two (n / 3) (n % 3)
  rw [show n % 3 + n / 3 * 3 = n by omega] at h1
  have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).1 h1
  have h3 : Nat.fib (n % 3) % 2 = 1 := by
    have : n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases this with h | h <;> rw [h] <;> decide
  unfold Nat.ModEq at h2
  omega

/-- Core step: if `F_n` has period `2n` and `2n ∣ F_n + 1` or `2n ∣ F_n + 3` (`n ≥ 4` even) then
`F_{F_n+2} ≡ 1 (mod F_n)`. -/
theorem fibfib_mod (n : ℕ) (hn : Even n) (hn4 : 4 ≤ n)
    (h : (2 * n) ∣ Nat.fib n + 1 ∨ (2 * n) ∣ Nat.fib n + 3) :
    Nat.fib (Nat.fib n + 2) % Nat.fib n = 1 := by
  have hF : 1 < Nat.fib n := by
    have : Nat.fib 4 ≤ Nat.fib n := Nat.fib_mono hn4
    have h4 : Nat.fib 4 = 3 := by decide
    omega
  have P : Per (Nat.fib n) (2 * n) := fun k => (ZMod.natCast_eq_natCast_iff _ _ _).2
    (period_fib_even n hn (by omega) k)
  have hone : ∀ c : ℕ, ((Nat.fib (1 + c * (2 * n)) : ℕ) : ZMod (Nat.fib n)) = 1 := by
    intro c
    have := per_mul P c 1
    simpa using this
  have hzero : ∀ c : ℕ, ((Nat.fib (c * (2 * n)) : ℕ) : ZMod (Nat.fib n)) = 0 := by
    intro c
    have := per_mul P c 0
    simpa using this
  have key : ((Nat.fib (Nat.fib n + 2) : ℕ) : ZMod (Nat.fib n)) = ((1 : ℕ) : ZMod (Nat.fib n)) := by
    rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
    · have e : Nat.fib n + 2 = 1 + c * (2 * n) := by rw [mul_comm c]; linarith
      rw [e, hone c]; simp
    · have e : Nat.fib n + 4 = 1 + c * (2 * n) := by rw [mul_comm c]; linarith
      have e2 : Nat.fib n + 3 = c * (2 * n) := by rw [mul_comm c]; linarith
      have h4 : Nat.fib (Nat.fib n + 4) = Nat.fib (Nat.fib n + 2) + Nat.fib (Nat.fib n + 3) :=
        Nat.fib_add_two
      have a := hone c
      have b := hzero c
      rw [← e] at a
      rw [← e2] at b
      rw [h4] at a
      push_cast at a b
      rw [b] at a
      simpa using a
  have := (ZMod.natCast_eq_natCast_iff _ _ _).1 key
  unfold Nat.ModEq at this
  rw [this]
  exact Nat.mod_eq_of_lt hF

/-- **Theorem 2** (Flynn-Connolly) for a prime `p`. -/
theorem theorem_two (p n : ℕ) (hp : p.Prime) (hpodd : p % 2 = 1) (hp3 : p % 3 = 2)
    (hp5 : p % 5 = 2 ∨ p % 5 = 3) (hn : n = 2 * p ∨ n = 4 * p) :
    Nat.fib n % 2 = 1 ∧ Nat.fib (Nat.fib n + 2) % Nat.fib n = 1 := by
  have hp5' : 5 ≤ p := by
    have := hp.two_le
    omega
  refine ⟨fib_odd_of_not_dvd n (by omega), ?_⟩
  rcases hn with rfl | rfl
  · refine fibfib_mod (2 * p) ⟨p, by ring⟩ (by omega) (Or.inl ?_)
    have := fib_two_mul_mod hp hpodd hp3 hp5
    rwa [show 2 * (2 * p) = 4 * p by ring]
  · refine fibfib_mod (4 * p) ⟨2 * p, by ring⟩ (by omega) (Or.inr ?_)
    have := fib_four_mul_mod hp hpodd hp3 hp5
    rwa [show 2 * (4 * p) = 8 * p by ring]

theorem sum_fib_Icc (k : ℕ) : (∑ i ∈ Finset.Icc 1 k, Nat.fib i) + 1 = Nat.fib (k + 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : Nat.fib (k + 1 + 2) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
    rw [Finset.sum_Icc_succ_top (by omega), e]
    omega

set_option linter.unusedVariables false in
/-- **Flynn-Connolly (2025).** Theorem 2 and Corollary 2. -/
theorem flynn_connolly :
    (∀ (p n : ℕ) (hp : p.Prime) (hpodd : p % 2 = 1)
      (hp3 : p % 3 = 2) (hp5 : p % 5 = 2 ∨ p % 5 = 3)
      (hn : n = 2 * p ∨ n = 4 * p),
      Nat.fib n % 2 = 1 ∧
        Nat.fib (Nat.fib n + 2) % Nat.fib n = 1) ∧
    {k : ℕ | Odd k ∧ k ∣ (∑ i ∈ Finset.Icc 1 k, Nat.fib i)}.Infinite := by
  refine ⟨fun p n hp hpodd hp3 hp5 hn => theorem_two p n hp hpodd hp3 hp5 hn, ?_⟩
  apply Set.infinite_of_forall_exists_gt
  intro N
  have hu : IsUnit (2 : ZMod 15) := ⟨⟨2, 8, by decide, by decide⟩, rfl⟩
  obtain ⟨p, hpN, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu (N + 5)
  have hp15 : p % 15 = 2 := by
    have := (ZMod.natCast_eq_natCast_iff' p 2 15).1 (by simpa using hmod)
    omega
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hp3 : p % 3 = 2 := by omega
  have hp5 : p % 5 = 2 ∨ p % 5 = 3 := Or.inl (by omega)
  have T := theorem_two p (2 * p) hp hpodd hp3 hp5 (Or.inl rfl)
  refine ⟨Nat.fib (2 * p), ⟨Nat.odd_iff.2 T.1, ?_⟩, ?_⟩
  · have hs := sum_fib_Icc (Nat.fib (2 * p))
    have hd := Nat.dvd_sub_mod (n := Nat.fib (2 * p)) (Nat.fib (Nat.fib (2 * p) + 2))
    rw [T.2] at hd
    have : (∑ i ∈ Finset.Icc 1 (Nat.fib (2 * p)), Nat.fib i) =
        Nat.fib (Nat.fib (2 * p) + 2) - 1 := by omega
    rwa [this]
  · have := Nat.le_fib_self (n := 2 * p) (by omega)
    omega

end FibonacciSumDivisibility
