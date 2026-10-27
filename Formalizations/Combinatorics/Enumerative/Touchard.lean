/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Combinatorics.Enumerative.Bell
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Tactic.Ring

/-!
# Touchard's congruence for Bell numbers

For a prime `p` and every `n`, the Bell numbers satisfy `B(n + p) ≡ B(n) + B(n + 1) (mod p)`; in
particular `B(p) ≡ 2 (mod p)`. The proof uses the umbral functional `L` on `(ZMod p)[X]` with
`L(Xⁿ) = B(n)`: the recurrence `Nat.bell_succ` gives `L(X f) = L(f(X + 1))`, hence
`L((X)ₖ h) = L(h(X + k))` for the falling factorial; in `ZMod p` the falling factorial of order `p`
is `X^p - X` (both monic of degree `p` with the same `p` roots), which yields the congruence.

## Main results

* `Touchard.bell_add_prime`: B(n + p) = B(n) + B(n + 1) in ZMod p for a prime p

## References

* J. Touchard, *Propriétés arithmétiques de certains nombres récurrents*, Ann. Soc. Sci. Bruxelles A 53 (1933), 21–31.
-/

@[expose] public section

open Polynomial

namespace Touchard

variable (p : ℕ) [Fact p.Prime]

/-- The umbral functional `L(X^n) = B(n)` on `(ZMod p)[X]`. -/
private noncomputable def L : (ZMod p)[X] →ₗ[ZMod p] ZMod p :=
  Polynomial.lsum fun n => (Nat.bell n : ZMod p) • LinearMap.id

private theorem L_monomial (n : ℕ) (c : ZMod p) : L p (monomial n c) = (Nat.bell n : ZMod p) * c := by
  simp [L, Polynomial.lsum_apply, Polynomial.sum_monomial_index]

private theorem L_X_pow (n : ℕ) : L p (X ^ n) = (Nat.bell n : ZMod p) := by
  have h := L_monomial p n 1
  rwa [← C_mul_X_pow_eq_monomial, C_1, one_mul, mul_one] at h

private theorem L_X_pow_succ (n : ℕ) : L p ((X + 1) ^ n) = (Nat.bell (n + 1) : ZMod p) := by
  rw [add_comm, add_pow, map_sum, Nat.bell_succ, ← Nat.range_succ_eq_Iic]
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  have : ((n.choose i : ℕ) : (ZMod p)[X]) = C (n.choose i : ZMod p) := by simp
  rw [one_pow, one_mul, this, mul_comm, ← smul_eq_C_mul, map_smul, L_X_pow]
  simp

private theorem L_X_mul (f : (ZMod p)[X]) : L p (X * f) = L p (f.comp (X + 1)) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [mul_add, map_add, hf, hg, add_comp, map_add]
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, mul_smul_comm, map_smul, smul_comp, map_smul,
      X_pow_comp, ← pow_succ', L_X_pow, L_X_pow_succ]

/-- `L(x (x-1) ⋯ (x-k+1) · h(x)) = L(h(x+k))`. -/
private theorem L_descPochhammer (k : ℕ) :
    ∀ h : (ZMod p)[X], L p (descPochhammer (ZMod p) k * h) = L p (h.comp (X + (k : (ZMod p)[X]))) := by
  induction k with
  | zero => intro h; simp
  | succ k ih =>
    intro h
    rw [descPochhammer_succ_left, mul_assoc, L_X_mul, mul_comp, comp_assoc]
    have e1 : (X - 1 : (ZMod p)[X]).comp (X + 1) = X := by simp
    have e2 : (X + 1 : (ZMod p)[X]).comp (X + (k : (ZMod p)[X])) = X + ((k + 1 : ℕ) : (ZMod p)[X]) := by
      simp; ring
    rw [e1, comp_X, ih, comp_assoc, e2]

/-- In characteristic `p`, the falling factorial `x (x-1) ⋯ (x-p+1)` is `x^p - x`. -/
private theorem descPochhammer_eq : descPochhammer (ZMod p) p = X ^ p - X := by
  have hp : p.Prime := Fact.out
  have hdeg : (descPochhammer (ZMod p) p).degree = p := by
    rw [degree_eq_natDegree (monic_descPochhammer _ _).ne_zero, descPochhammer_natDegree]
  have hmon : (X ^ p - X : (ZMod p)[X]).Monic := monic_X_pow_sub (by simpa using hp.one_lt)
  have hdeg' : (X ^ p - X : (ZMod p)[X]).degree = p := by
    rw [degree_eq_natDegree hmon.ne_zero,
      FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp.one_lt]
  refine Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq (Finset.univ : Finset (ZMod p)) ?_ ?_
  · rw [Finset.card_univ, ZMod.card]
    have := degree_sub_lt_left (hdeg.trans hdeg'.symm) (monic_descPochhammer _ _).ne_zero
      ((monic_descPochhammer _ _).leadingCoeff.trans hmon.leadingCoeff.symm)
    rwa [hdeg] at this
  · intro a _
    rw [descPochhammer_eval_eq_prod_range]
    have h0 : ∏ j ∈ Finset.range p, (a - (j : ZMod p)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.2 (ZMod.val_lt a)) (by simp)
    rw [h0]
    simp [ZMod.pow_card]

/-- **Touchard's congruence (1933).** For a prime `p` and every `n`, the Bell numbers satisfy
`B(n + p) ≡ B(n) + B(n + 1) (mod p)`; in particular `B(p) ≡ 2 (mod p)`. -/
theorem bell_add_prime (n : ℕ) :
    ((n + p).bell : ZMod p) = n.bell + (n + 1).bell := by
  have h := L_descPochhammer p p (X ^ n)
  rw [descPochhammer_eq, CharP.cast_eq_zero, add_zero, comp_X, sub_mul, map_sub, ← pow_add, ← pow_succ', L_X_pow, L_X_pow, L_X_pow] at h
  rw [add_comm n p]
  linear_combination h

end Touchard
