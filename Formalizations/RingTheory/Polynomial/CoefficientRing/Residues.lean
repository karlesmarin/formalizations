/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.RingTheory.Polynomial.CoefficientRing.StableIntervals
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# Residual coefficients of `(X − 1)(X^r − 1)^N` and `(X^r − 1)^N /ₘ (X − 1)`

Over any commutative ring, for `r ≥ 3` and `N ≥ 1`:
* `P = (X − 1)(X^r − 1)^N` (degree `L = N r + 1`) has `coeff P (L − 1) = −1` and
  `coeff P (L − 2) = 0`;
* `Q = (X^r − 1)^N /ₘ (X − 1)` (degree `L = N r − 1`, an exact quotient) has
  `coeff Q (L − 1) = coeff Q (L − 2) = 1`.
Together with the identities `NotaPuente.lemma_5_5` this gives `τ₊ ∈ A` when `a1² − a2` is a unit
of the subring `A`, and `τ₋ ∈ A` when `a2` is.

The passage from "residue `1` modulo the radical" to "unit of the local order", and the
identification of `a1`, `a2` with the elementary symmetric functions of the roots of `P` or `Q`
modulo the radical, are not formalized here.

## Main results

* `NotaPuente.Residues.coeff_P`, `NotaPuente.Residues.coeff_Q`: the two top coefficients.
* `NotaPuente.Residues.residue_P`, `NotaPuente.Residues.residue_Q`: `e1² − e2 = 1`, resp. `e2 = 1`.
* `NotaPuente.Residues.mem_of_mul_eq`: `d τ = n`, `n ∈ A`, `d` a unit of `A` ⇒ `τ ∈ A`.
* `NotaPuente.Residues.tau_plus_mem`, `NotaPuente.Residues.tau_minus_mem`.

## References

* C. Marín, *Non-real orders of character values of `GL(n)`*, preprint (2026).
* C. Marín, *The ring of character values depends only on the segment: SU(n), Sp(2m) and GL(n) at
  a torsion element*, Zenodo (2026), doi:10.5281/zenodo.22847476.
-/

@[expose] public section

namespace NotaPuente.Residues

open Polynomial

section Coeffs

variable {R : Type*} [CommRing R]

/-- Top coefficients of `(X^r - 1)^N`: for `N r < k + r`, the coefficient is `1` at `k = N r`, else `0`
(i.e. `(X^r - 1)^N = X^(N r) + (terms of degree ≤ N r - r)`). -/
lemma coeff_pow_top {r : ℕ} (hr : 1 ≤ r) (N : ℕ) :
    ∀ k, N * r < k + r → ((X ^ r - 1 : R[X]) ^ N).coeff k = if k = N * r then 1 else 0 := by
  induction N with
  | zero => intro k _; simp [coeff_one]
  | succ N ih =>
    intro k hk
    rw [add_one_mul] at hk ⊢
    have hk0 : ((X ^ r - 1 : R[X]) ^ N).coeff k = 0 := by
      rw [ih k (by omega), ite_eq_right (by omega)]
    rw [pow_succ, mul_sub, mul_one, coeff_sub, coeff_mul_X_pow', hk0]
    by_cases hrk : r ≤ k
    · rw [ite_eq_left hrk, ih (k - r) (by omega), sub_zero]
      exact if_congr (by omega) rfl rfl
    · rw [ite_eq_right hrk, ite_eq_right (by omega), sub_zero]

lemma natDegree_pow_le' {r : ℕ} (hr : 1 ≤ r) (N : ℕ) : ((X ^ r - 1 : R[X]) ^ N).natDegree ≤ N * r :=
  natDegree_le_iff_coeff_eq_zero.mpr fun k hk => by
    rw [coeff_pow_top hr N k (by omega), ite_eq_right (by omega)]

/-- **Lemma 5.6 (i), case `L = N r + 1`.** For `P = (X - 1)(X^r - 1)^N`, `r ≥ 3`, `N ≥ 1`:
`coeff P L = 1`, `coeff P (L-1) = -1`, `coeff P (L-2) = 0`, with `L - 1 = N r`, `L - 2 = N r - 1`.
So `e1 = -coeff P (L-1) = 1`, `e2 = coeff P (L-2) = 0`. -/
theorem coeff_P {r N : ℕ} (hr : 3 ≤ r) (hN : 1 ≤ N) :
    ((X - 1) * (X ^ r - 1 : R[X]) ^ N).coeff (N * r + 1) = 1 ∧
    ((X - 1) * (X ^ r - 1 : R[X]) ^ N).coeff (N * r) = -1 ∧
    ((X - 1) * (X ^ r - 1 : R[X]) ^ N).coeff (N * r - 1) = 0 := by
  have hNr : 3 ≤ N * r := le_trans hr (Nat.le_mul_of_pos_left r hN)
  obtain ⟨a, ha⟩ : ∃ a, N * r = a + 2 := ⟨N * r - 2, by omega⟩
  have F := coeff_pow_top (R := R) (r := r) (by omega) N
  rw [ha, show a + 2 - 1 = a + 1 by omega, sub_mul, one_mul, coeff_sub, coeff_sub, coeff_sub,
    coeff_X_mul, coeff_X_mul, coeff_X_mul, F (a + 2) (by omega), F (a + 1) (by omega),
    F (a + 3) (by omega), F a (by omega), ha]
  simp

/-- `(X - 1) * ((X^r - 1)^N /ₘ (X - 1)) = (X^r - 1)^N` for `N ≥ 1` (exact division). -/
lemma mul_divByMonic_pow {r N : ℕ} (hN : 1 ≤ N) :
    (X - 1) * ((X ^ r - 1 : R[X]) ^ N /ₘ (X - 1)) = (X ^ r - 1) ^ N := by
  have h := (mul_divByMonic_eq_iff_isRoot (p := (X ^ r - 1 : R[X]) ^ N) (a := 1)).mpr (by
    simp [IsRoot, eval_pow, zero_pow (by omega : N ≠ 0)])
  rwa [C_1] at h

/-- **Lemma 5.6 (i), case `L = N r - 1`.** For `Q = (X^r - 1)^N /ₘ (X - 1)`, `r ≥ 3`, `N ≥ 1`:
`coeff Q L = 1`, `coeff Q (L-1) = 1`, `coeff Q (L-2) = 1`, with `L = N r - 1`.
So `e1 = -coeff Q (L-1) = -1`, `e2 = coeff Q (L-2) = 1`. -/
theorem coeff_Q {r N : ℕ} (hr : 3 ≤ r) (hN : 1 ≤ N) :
    ((X ^ r - 1 : R[X]) ^ N /ₘ (X - 1)).coeff (N * r - 1) = 1 ∧
    ((X ^ r - 1 : R[X]) ^ N /ₘ (X - 1)).coeff (N * r - 2) = 1 ∧
    ((X ^ r - 1 : R[X]) ^ N /ₘ (X - 1)).coeff (N * r - 3) = 1 := by
  nontriviality R
  have hNr : 3 ≤ N * r := le_trans hr (Nat.le_mul_of_pos_left r hN)
  obtain ⟨a, ha⟩ : ∃ a, N * r = a + 3 := ⟨N * r - 3, by omega⟩
  set Q := (X ^ r - 1 : R[X]) ^ N /ₘ (X - 1) with hQdef
  have F := coeff_pow_top (R := R) (r := r) (by omega) N
  have hQ := mul_divByMonic_pow (R := R) (r := r) hN
  rw [← hQdef] at hQ
  -- `coeff Q k = 0` for `k ≥ N r`
  have hdeg : Q.natDegree ≤ a + 2 := by
    have h1 := natDegree_divByMonic ((X ^ r - 1 : R[X]) ^ N) (monic_X_sub_C (1 : R))
    rw [natDegree_X_sub_C, C_1, ← hQdef] at h1
    have h2 := natDegree_pow_le' (R := R) (r := r) (by omega) N
    omega
  have hQ3 : Q.coeff (a + 3) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  -- `coeff F (k+1) = coeff Q k - coeff Q (k+1)`
  have hrec : ∀ k, ((X ^ r - 1 : R[X]) ^ N).coeff (k + 1) = Q.coeff k - Q.coeff (k + 1) := by
    intro k
    rw [← hQ, sub_mul, one_mul, coeff_sub, coeff_X_mul]
  have e3 := hrec (a + 2)
  have e2 := hrec (a + 1)
  have e1 := hrec a
  rw [F (a + 2 + 1) (by omega), ite_eq_left (by omega), hQ3] at e3
  rw [F (a + 1 + 1) (by omega), ite_eq_right (by omega)] at e2
  rw [F (a + 1) (by omega), ite_eq_right (by omega)] at e1
  rw [ha, show a + 3 - 1 = a + 2 by omega, show a + 3 - 2 = a + 1 by omega,
    show a + 3 - 3 = a by omega]
  refine ⟨by linear_combination -e3, by linear_combination -e3 - e2,
    by linear_combination -e3 - e2 - e1⟩

/-- **Lemma 5.6 (ii)**, case `L = N r + 1`: `e1² - e2 = 1`, with `e1 = -coeff P (L-1)`,
`e2 = coeff P (L-2)`. -/
theorem residue_P {r N : ℕ} (hr : 3 ≤ r) (hN : 1 ≤ N) :
    (-((X - 1) * (X ^ r - 1 : R[X]) ^ N).coeff (N * r)) ^ 2
      - ((X - 1) * (X ^ r - 1 : R[X]) ^ N).coeff (N * r - 1) = 1 := by
  obtain ⟨-, h1, h2⟩ := coeff_P (R := R) hr hN
  rw [h1, h2]; ring

/-- **Lemma 5.6 (ii)**, case `L = N r - 1`: `e2 = coeff Q (L-2) = 1` (and `e1² - e2 = 0`). -/
theorem residue_Q {r N : ℕ} (hr : 3 ≤ r) (hN : 1 ≤ N) :
    ((X ^ r - 1 : R[X]) ^ N /ₘ (X - 1)).coeff (N * r - 3) = 1 ∧
    (-((X ^ r - 1 : R[X]) ^ N /ₘ (X - 1)).coeff (N * r - 2)) ^ 2
      - ((X ^ r - 1 : R[X]) ^ N /ₘ (X - 1)).coeff (N * r - 3) = 0 := by
  obtain ⟨-, h1, h2⟩ := coeff_Q (R := R) hr hN
  rw [h1, h2]; constructor <;> ring

end Coeffs

/-! ## Lemma 5.6 (iii): the algebraic step -/

/-- If `d τ = n` with `n ∈ A` and `d` a unit of the subring `A` (`e ∈ A`, `e d = 1`), then `τ ∈ A`. -/
theorem mem_of_mul_eq {S : Type*} [CommRing S] (A : Subring S) {d e τ n : S} (he : e ∈ A)
    (hed : e * d = 1) (hn : n ∈ A) (h : d * τ = n) : τ ∈ A := by
  have : τ = e * n := by rw [← h, ← mul_assoc, hed, one_mul]
  rw [this]; exact A.mul_mem he hn

/-! ## Lemma 5.5

`a1`, `a2` and `lemma_5_5` are those of
`Formalizations.RingTheory.Polynomial.CoefficientRing.StableIntervals` (namespace `NotaPuente`). -/

section Tau

variable {K : Type*} [Field K]

/-- **Lemma 5.6 (iii), `τ₊`.** If `a1, a2 ∈ A` and `a1² - a2` is a unit of `A`, then
`τ₊ = t^(L-1) + t^(-(L-1)) ∈ A`. -/
theorem tau_plus_mem (A : Subring K) {t : K} (ht : t ≠ 0) {L : ℕ} (hL : 2 ≤ L)
    (h1 : a1 t L ∈ A) (h2 : a2 t L ∈ A) {e : K} (he : e ∈ A)
    (hu : e * (a1 t L ^ 2 - a2 t L) = 1) :
    t ^ ((L : ℤ) - 1) + t ^ (-((L : ℤ) - 1)) ∈ A := by
  refine mem_of_mul_eq A he hu ?_ (lemma_5_5 ht hL).1
  have h2' : (2 : K) * a2 t L ∈ A := by rw [two_mul]; exact A.add_mem h2 h2
  exact A.mul_mem h1 (A.sub_mem (A.add_mem A.one_mem (A.pow_mem h1 2)) h2')

/-- **Lemma 5.6 (iii), `τ₋`.** If `a1, a2 ∈ A` and `a2` is a unit of `A`, then
`τ₋ = t^(L+1) + t^(-(L+1)) ∈ A`. -/
theorem tau_minus_mem (A : Subring K) {t : K} (ht : t ≠ 0) {L : ℕ} (hL : 2 ≤ L)
    (h1 : a1 t L ∈ A) (h2 : a2 t L ∈ A) {e : K} (he : e ∈ A) (hu : e * a2 t L = 1) :
    t ^ ((L : ℤ) + 1) + t ^ (-((L : ℤ) + 1)) ∈ A := by
  refine mem_of_mul_eq A he hu ?_ (lemma_5_5 ht hL).2
  have h2' : (2 : K) * a2 t L ∈ A := by rw [two_mul]; exact A.add_mem h2 h2
  exact A.mul_mem h1 (A.sub_mem (A.sub_mem (A.pow_mem h1 2) h2') A.one_mem)

end Tau


end NotaPuente.Residues
