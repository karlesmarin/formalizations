/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.RingTheory.PowerSeries.Log
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The power-series logarithm of a product

For power series `f`, `g` with constant coefficient `1` over a `ℚ`-algebra,
`logOf (f * g) = logOf f + logOf g` and `logOf (f ^ n) = n • logOf f`, where
`logOf f = log(1 + X)` substituted at `f - 1` (Mathlib's `PowerSeries.logOf`). The proof is by
uniqueness of antiderivatives (`PowerSeries.derivative.ext`): no topology and no `exp`.

## Main results

* `PowerSeries.deriv_logOf_mul`: `(logOf h)' · h = h'` for `h` with constant coefficient `1`.
* `PowerSeries.logOf_mul`: `logOf (f * g) = logOf f + logOf g`.
* `PowerSeries.logOf_one`, `PowerSeries.logOf_pow`: `logOf 1 = 0`, `logOf (f ^ n) = n • logOf f`.
* `PowerSeries.coeff_logTrunc_pow`, `PowerSeries.polyPL_coeff`: the coefficient form of
  `logOf ((1 + X) ^ p) = p • log(1 + X)` for the truncated logarithm, as a power series and as a
  polynomial. This is the form used for the Adams eigen-relation of the Connes–Kreimer Hopf algebra
  (`Formalizations.RingTheory.HopfAlgebra.ConnesKreimer.Eulerian`).

Mathlib has `logOf`, `derivative_log_mul_one_add_X` (`(log(1 + X))' · (1 + X) = 1`, used here) and
`logOf_exp`, but at the pinned commit not the additivity `logOf_mul`.

## References

* C. Marín, *How a Tree Forgets Its Order: the Eulerian idempotent and the Adams spectrum on the
  commutative Connes–Kreimer–Butcher Hopf algebra of rooted trees, machine-checked in Lean 4*
  (2026), doi:10.5281/zenodo.20774821. Ported from `PowerSeriesLogMul.lean` of
  [karlesmarin/connes-kreimer-lean](https://github.com/karlesmarin/connes-kreimer-lean)
  (Lean v4.30.0-rc2).
-/

@[expose] public section

namespace PowerSeries

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- The derivative `(log(1+X))'` substituted at `h-1` is the inverse of `h`
(for `h` with constant term `1`): `(log A)'.subst (h-1) * h = 1`. -/
theorem deriv_log_subst_mul {h : A⟦X⟧} (hh : constantCoeff h = 1) :
    (d⁄dX (log A)).subst (h - 1) * h = 1 := by
  have hS : HasSubst (h - 1 : A⟦X⟧) :=
    HasSubst.of_constantCoeff_zero' (by simp [hh])
  have hsub1 : (1 : A⟦X⟧).subst (h - 1) = 1 := by rw [← coe_substAlgHom hS, map_one]
  have hsub : (1 + X : A⟦X⟧).subst (h - 1) = h := by
    rw [subst_add hS, hsub1, subst_X hS]; ring
  calc (d⁄dX (log A)).subst (h - 1) * h
      = h * (d⁄dX (log A)).subst (h - 1) := by ring
    _ = ((1 + X : A⟦X⟧).subst (h - 1)) * (d⁄dX (log A)).subst (h - 1) := by rw [hsub]
    _ = ((1 + X : A⟦X⟧) * d⁄dX (log A)).subst (h - 1) := by rw [subst_mul hS]
    _ = (1 : A⟦X⟧).subst (h - 1) := by rw [mul_comm, derivative_log_mul_one_add_X]
    _ = 1 := hsub1

/-- The chain-rule form of the derivative of `logOf`: `(logOf h)' · h = h'`
for `h` with constant term `1`. -/
theorem deriv_logOf_mul {h : A⟦X⟧} (hh : constantCoeff h = 1) :
    d⁄dX (logOf h) * h = d⁄dX h := by
  have hS : HasSubst (h - 1 : A⟦X⟧) :=
    HasSubst.of_constantCoeff_zero' (by simp [hh])
  have hd : d⁄dX (logOf h) = (d⁄dX (log A)).subst (h - 1) * d⁄dX h := by
    rw [logOf_eq, derivative_subst hS, map_sub, Derivation.map_one_eq_zero, sub_zero]
  rw [hd, mul_right_comm, deriv_log_subst_mul hh, one_mul]

/-- **Logarithm of a product** at the power-series level:
`logOf (f · g) = logOf f + logOf g` for `f`, `g` with constant term `1`. -/
theorem logOf_mul [HasUniqueDiv A] {f g : A⟦X⟧}
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) :
    logOf (f * g) = logOf f + logOf g := by
  have hfg : constantCoeff (f * g) = 1 := by rw [map_mul, hf, hg, one_mul]
  have hfgU : IsUnit (f * g) := isUnit_iff_constantCoeff.2 (by rw [hfg]; exact isUnit_one)
  -- cancel the unit `f * g` on the right
  have hcancel : ∀ {P Q : A⟦X⟧}, P * (f * g) = Q * (f * g) → P = Q := by
    intro P Q h
    obtain ⟨U, hU⟩ := hfgU
    have h2 : P * (f * g) * ↑U⁻¹ = Q * (f * g) * ↑U⁻¹ := by rw [h]
    rwa [← hU, mul_assoc, mul_assoc, U.mul_inv, mul_one, mul_one] at h2
  apply derivative.ext
  · -- derivatives agree
    apply hcancel
    rw [map_add, add_mul, deriv_logOf_mul hfg]
    have e1 : d⁄dX (logOf f) * (f * g) = d⁄dX f * g := by
      rw [← mul_assoc, deriv_logOf_mul hf]
    have e2 : d⁄dX (logOf g) * (f * g) = d⁄dX g * f := by
      rw [mul_comm f g, ← mul_assoc, deriv_logOf_mul hg]
    rw [e1, e2, Derivation.leibniz]
    simp only [smul_eq_mul]
    ring
  · -- constant terms agree (both 0)
    rw [constantCoeff_logOf hfg, map_add, constantCoeff_logOf hf, constantCoeff_logOf hg, add_zero]

/-- `logOf 1 = 0`. -/
@[simp]
theorem logOf_one [HasUniqueDiv A] : logOf (1 : A⟦X⟧) = 0 := by
  have h := logOf_mul (A := A) (f := 1) (g := 1) (by simp) (by simp)
  rw [mul_one] at h
  have : logOf (1 : A⟦X⟧) + 0 = logOf (1 : A⟦X⟧) + logOf (1 : A⟦X⟧) := by
    rw [add_zero]; exact h
  exact (add_left_cancel this).symm

/-- **Logarithm of a power**: `logOf (f ^ n) = n • logOf f` for `f` with constant term `1`. -/
theorem logOf_pow [HasUniqueDiv A] {f : A⟦X⟧} (hf : constantCoeff f = 1) (n : ℕ) :
    logOf (f ^ n) = n • logOf f := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hfk : constantCoeff (f ^ k) = 1 := by rw [map_pow, hf, one_pow]
    rw [pow_succ, logOf_mul hfk hf, ih, succ_nsmul]

omit [Algebra ℚ A] in
/-- A series with zero constant coefficient has its `d`-th power vanishing below degree `d`. -/
theorem coeff_pow_eq_zero_of_lt {g : A⟦X⟧} (hg : constantCoeff g = 0) {d m : ℕ} (hmd : m < d) :
    coeff m (g ^ d) = 0 :=
  (X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (X_dvd_iff.2 hg) d)) m hmd

/-- **Coefficient form of `logOf_pow`.** The degree-`≤N` truncation of the log series, substituted
at `(1+X)^p − 1`, has `m`-th coefficient `p · cₘ` for `m ≤ N` (`cₘ = coeff m (log A)`). -/
theorem coeff_logTrunc_pow [HasUniqueDiv A] (p N m : ℕ) (hm : m ≤ N) :
    coeff m (∑ j ∈ Finset.range (N + 1),
        coeff j (log A) • ((1 + X : A⟦X⟧) ^ p - 1) ^ j)
      = p • coeff m (log A) := by
  set g : A⟦X⟧ := (1 + X) ^ p - 1 with hgdef
  have hgc : constantCoeff g = 0 := by
    rw [hgdef, map_sub, map_pow, map_add, constantCoeff_X, constantCoeff_one, add_zero, one_pow,
      sub_self]
  have hS : HasSubst g := HasSubst.of_constantCoeff_zero' hgc
  have hfin : (∑ᶠ d : ℕ, coeff d (log A) • coeff m (g ^ d))
      = ∑ j ∈ Finset.range (N + 1), coeff j (log A) • coeff m (g ^ j) := by
    apply finsum_eq_finsetSum_of_support_subset
    intro d hd
    simp only [Function.mem_support, ne_eq] at hd
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hge
    push Not at hge
    exact hd (by rw [coeff_pow_eq_zero_of_lt hgc (by omega : m < d), smul_zero])
  rw [map_sum]
  simp only [map_smul]
  rw [← hfin, ← coeff_subst' hS (log A) m,
      show (log A).subst g = logOf ((1 + X : A⟦X⟧) ^ p) from (logOf_eq _).symm,
      logOf_pow (by simp : constantCoeff (1 + X : A⟦X⟧) = 1) p, logOf_one_add_X, map_nsmul]

/-- **Polynomial form of `coeff_logTrunc_pow`**, for evaluation at a ring element through
`Polynomial.eval₂`. -/
theorem polyPL_coeff [HasUniqueDiv A] (p N m : ℕ) (hm : m ≤ N) :
    (∑ j ∈ Finset.range (N + 1),
        Polynomial.C (coeff j (log A)) * ((1 + Polynomial.X) ^ p - 1) ^ j).coeff m
      = p • coeff m (log A) := by
  have hterm : ∀ j, Polynomial.coeToPowerSeries.ringHom
        (Polynomial.C (coeff j (log A)) * ((1 + Polynomial.X) ^ p - 1) ^ j)
      = coeff j (log A) • ((1 + X : A⟦X⟧) ^ p - 1) ^ j := by
    intro j
    simp only [map_mul, map_pow, map_sub, map_add, map_one,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X]
    rw [← smul_eq_C_mul]
  rw [← Polynomial.coeff_coe, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum,
      Finset.sum_congr rfl (fun j _ => hterm j)]
  exact coeff_logTrunc_pow p N m hm

end PowerSeries
