/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

/-!
# Removing one root of unity: `V_s = q^(q-2)` and `M_s = M_0` (Proposition 8.2, `prop:Ms`)

Let `ζ ∈ ℂ` be a primitive `q`-th root of unity, `μ_q = {x | x^q = 1}` (`nthRootsFinset q 1`) and
`U_a = μ_q ∖ {a}` for `a ∈ μ_q` (`a = ζ^s`).  For the ordered products over `U_a`:

* `V_a = ∏_{x ≠ y} ‖x - y‖`   (`Vs`),
* `C_a = ∏_{x y, x y ≠ 1} ‖1 - x y‖`   (`Cs`, pairs `x = y` included),
* `D_a = ∏_{x, x² ≠ 1} ‖1 - x²‖`   (`Ds`),  and `D = ∏_{x ∈ μ_q, x² ≠ 1} ‖1 - x²‖`   (`Dfull`).

## Main results

* `WeylProductMs.vandermonde_punctured`: `V_a = q^(q-2)` (step S2 of the note).
* `WeylProductMs.CD_punctured`: `C_a · D_a = q^(q-2) · D` (steps S3–S6).
* `WeylProductMs.prop_Ms`: `V_a · C_a · D_a = V_b · C_b · D_b` (`prop:Ms`, in ordered form:
  `M_s² = M_0²`); `prop_Ms_zmod` is the same for `a = ζ^s`, `s : ZMod q`.

The statement is about moduli; the complex product without absolute values does depend on `s`.
Not formalised: the unordered form `A_s · B_s · D_s` of the note (`M_s² = V_s C_s D_s` is the
relation of the note between the two forms).

## References

* C. Marín, *Integer character values on the ρ-line of Sp(2m)*, Zenodo (2026),
  doi:10.5281/zenodo.22683560, Proposition 8.2.
-/

@[expose] public section

open Polynomial Finset

namespace WeylProductMs

/-- `μ_q`, the `q`-th roots of unity in `ℂ`. -/
noncomputable abbrev mu (q : ℕ) : Finset ℂ := Polynomial.nthRootsFinset q (1 : ℂ)

/-- `V_a = ∏_{x ≠ y ∈ U_a} ‖x - y‖` over ordered pairs, `U_a = μ_q ∖ {a}`. -/
noncomputable def Vs (q : ℕ) (a : ℂ) : ℝ :=
  ∏ x ∈ (mu q).erase a, ∏ y ∈ ((mu q).erase a).erase x, ‖x - y‖

/-- `C_a = ∏_{(x,y) ∈ U_a × U_a, x y ≠ 1} ‖1 - x y‖` (ordered pairs, `x = y` allowed). -/
noncomputable def Cs (q : ℕ) (a : ℂ) : ℝ :=
  ∏ x ∈ (mu q).erase a, ∏ y ∈ ((mu q).erase a).filter (fun y => x * y ≠ 1), ‖1 - x * y‖

/-- `D_a = ∏_{x ∈ U_a, x² ≠ 1} ‖1 - x²‖`. -/
noncomputable def Ds (q : ℕ) (a : ℂ) : ℝ :=
  ∏ x ∈ ((mu q).erase a).filter (fun x => x ^ 2 ≠ 1), ‖1 - x ^ 2‖

/-- `D = ∏_{x ∈ μ_q, x² ≠ 1} ‖1 - x²‖`. -/
noncomputable def Dfull (q : ℕ) : ℝ :=
  ∏ x ∈ (mu q).filter (fun x => x ^ 2 ≠ 1), ‖1 - x ^ 2‖

/-- The factor `‖1 - x y‖`, set to `1` when it vanishes. -/
noncomputable def hh (x y : ℂ) : ℝ := if x * y ≠ 1 then ‖1 - x * y‖ else 1

section Basic

variable {q : ℕ} {ζ : ℂ}

lemma mem_mu (hq : 0 < q) {x : ℂ} : x ∈ mu q ↔ x ^ q = 1 := by
  simp [mu, mem_nthRootsFinset hq]

lemma norm_of_mem (hq : 0 < q) {x : ℂ} (hx : x ∈ mu q) : ‖x‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one ((mem_mu hq).1 hx) hq.ne'

lemma hh_symm (x y : ℂ) : hh x y = hh y x := by
  simp only [hh, mul_comm x y]

lemma hh_ne_zero (x y : ℂ) : hh x y ≠ 0 := by
  unfold hh
  split_ifs with h
  · rw [norm_ne_zero_iff, sub_ne_zero]; exact fun e => h e.symm
  · exact one_ne_zero

lemma hh_pos (x y : ℂ) : 0 < hh x y := by
  unfold hh; split_ifs with h
  · rw [norm_pos_iff, sub_ne_zero]; exact fun e => h e.symm
  · exact one_pos

lemma card_mu (hζ : IsPrimitiveRoot ζ q) : (mu q).card = q := hζ.card_nthRootsFinset

/-- `∏_{y ∈ μ_q ∖ {x}} (x - y) = q x^{q-1}`: differentiate `X^q - 1 = ∏ (X - y)` at `x`. -/
lemma prod_sub_erase (hζ : IsPrimitiveRoot ζ q) (hq : 0 < q) {x : ℂ} (hx : x ∈ mu q) :
    ∏ y ∈ (mu q).erase x, (x - y) = (q : ℂ) * x ^ (q - 1) := by
  classical
  have h1 := Polynomial.X_pow_sub_one_eq_prod (R := ℂ) hq hζ
  have h2 := congrArg (fun p : ℂ[X] => eval x (derivative p)) h1
  simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, eval_mul, eval_C,
    eval_pow, eval_X] at h2
  have h3 := eval_multiset_prod_X_sub_C_derivative (S := (mu q).val) (r := x) hx
  have h4 : (∏ ζ ∈ mu q, (X - C ζ) : ℂ[X]) = (Multiset.map (fun a => X - C a) (mu q).val).prod :=
    rfl
  rw [h4] at h2
  rw [h3] at h2
  have h5 : ∏ y ∈ (mu q).erase x, (x - y) =
      (Multiset.map (fun a => x - a) ((mu q).val.erase x)).prod := by
    rw [← Finset.erase_val]; rfl
  rw [h5, ← h2]

lemma prod_norm_sub_erase (hζ : IsPrimitiveRoot ζ q) (hq : 0 < q) {x : ℂ} (hx : x ∈ mu q) :
    ∏ y ∈ (mu q).erase x, ‖x - y‖ = q := by
  have h := congrArg norm (prod_sub_erase hζ hq hx)
  rw [norm_prod, norm_mul, norm_pow, norm_of_mem hq hx, one_pow, mul_one] at h
  simpa using h

/-- `∏_{y ∈ μ_q} hh x y = q` for `x ∈ μ_q`. -/
lemma prod_hh (hζ : IsPrimitiveRoot ζ q) (hq : 0 < q) {x : ℂ} (hx : x ∈ mu q) :
    ∏ y ∈ mu q, hh x y = q := by
  classical
  have hx0 : x ≠ 0 := by
    intro h; rw [h] at hx; have := (mem_mu hq).1 hx; simp [hq.ne'] at this
  have hxi : x⁻¹ ∈ mu q := by
    rw [mem_mu hq, inv_pow, (mem_mu hq).1 hx, inv_one]
  have hfil : (mu q).filter (fun y => x * y ≠ 1) = (mu q).erase x⁻¹ := by
    ext y
    simp only [mem_filter, mem_erase]
    have key : x * y = 1 ↔ y = x⁻¹ := by
      rw [mul_comm]; exact mul_eq_one_iff_eq_inv₀ hx0
    simp only [ne_eq, key]; tauto
  have : ∏ y ∈ mu q, hh x y = ∏ y ∈ (mu q).filter (fun y => x * y ≠ 1), ‖1 - x * y‖ := by
    rw [prod_filter]; rfl
  rw [this, hfil, ← prod_norm_sub_erase hζ hq hxi]
  refine prod_congr rfl fun y _ => ?_
  have : 1 - x * y = x * (x⁻¹ - y) := by field_simp
  rw [this, norm_mul, norm_of_mem hq hx, one_mul]

end Basic

section Main

variable {q : ℕ} {ζ : ℂ}

lemma Cs_eq (q : ℕ) (a : ℂ) :
    Cs q a = ∏ x ∈ (mu q).erase a, ∏ y ∈ (mu q).erase a, hh x y := by
  unfold Cs
  refine prod_congr rfl fun x _ => ?_
  rw [prod_filter]; rfl

lemma Ds_eq (q : ℕ) (a : ℂ) : Ds q a = ∏ x ∈ (mu q).erase a, hh x x := by
  unfold Ds
  rw [prod_filter]
  refine prod_congr rfl fun x _ => ?_
  simp only [hh, sq]

lemma Dfull_eq (q : ℕ) : Dfull q = ∏ x ∈ mu q, hh x x := by
  unfold Dfull
  rw [prod_filter]
  refine prod_congr rfl fun x _ => ?_
  simp only [hh, sq]

/-- **Step S2.** The Vandermonde of `μ_q` minus one point: `V_a = q^(q-2)`, for every `a ∈ μ_q`. -/
theorem vandermonde_punctured (hζ : IsPrimitiveRoot ζ q) (hq : 2 ≤ q) {a : ℂ} (ha : a ∈ mu q) :
    Vs q a = (q : ℝ) ^ (q - 2) := by
  classical
  have hq0 : 0 < q := by omega
  have hcard : ((mu q).erase a).card = q - 1 := by
    rw [card_erase_of_mem ha, card_mu hζ]
  -- inner product: `‖x - a‖ * ∏_{y ∈ U_a ∖ x} ‖x - y‖ = q`
  have hin : ∀ x ∈ (mu q).erase a,
      ‖x - a‖ * ∏ y ∈ ((mu q).erase a).erase x, ‖x - y‖ = q := by
    intro x hx
    have hxa : x ≠ a := ne_of_mem_erase hx
    have hxm : x ∈ mu q := mem_of_mem_erase hx
    have hax : a ∈ (mu q).erase x := mem_erase.2 ⟨hxa.symm, ha⟩
    have e : ((mu q).erase a).erase x = ((mu q).erase x).erase a := erase_right_comm
    rw [e, ← prod_norm_sub_erase hζ hq0 hxm, ← mul_prod_erase _ _ hax]
  have hA : ∏ x ∈ (mu q).erase a, ‖x - a‖ = q := by
    rw [← prod_norm_sub_erase hζ hq0 ha]
    exact prod_congr rfl fun x _ => norm_sub_rev _ _
  have hprod : Vs q a * ∏ x ∈ (mu q).erase a, ‖x - a‖ = (q : ℝ) ^ (q - 1) := by
    unfold Vs
    rw [← prod_mul_distrib]
    have h' : ∀ x ∈ (mu q).erase a,
        (∏ y ∈ ((mu q).erase a).erase x, ‖x - y‖) * ‖x - a‖ = q := fun x hx => by
      rw [mul_comm]; exact hin x hx
    rw [prod_congr rfl h', prod_const, hcard]
  rw [hA] at hprod
  have hqr : (q : ℝ) ≠ 0 := by positivity
  have : (q : ℝ) ^ (q - 1) = (q : ℝ) ^ (q - 2) * q := by
    rw [← pow_succ]; congr 1; omega
  rw [this] at hprod
  exact mul_right_cancel₀ hqr hprod

/-- **Steps S3–S6.** `C_a · D_a = q^(q-2) · D`, for every `a ∈ μ_q`. -/
theorem CD_punctured (hζ : IsPrimitiveRoot ζ q) (hq : 2 ≤ q) {a : ℂ} (ha : a ∈ mu q) :
    Cs q a * Ds q a = (q : ℝ) ^ (q - 2) * Dfull q := by
  classical
  have hq0 : 0 < q := by omega
  have hcard : ((mu q).erase a).card = q - 1 := by
    rw [card_erase_of_mem ha, card_mu hζ]
  have hin : ∀ x ∈ (mu q).erase a,
      (∏ y ∈ (mu q).erase a, hh x y) * hh x a = q := by
    intro x hx
    have hxm : x ∈ mu q := mem_of_mem_erase hx
    rw [mul_comm, mul_prod_erase _ _ ha]
    exact prod_hh hζ hq0 hxm
  set P := ∏ x ∈ (mu q).erase a, hh x a with hP
  have hPpos : 0 < P := prod_pos fun x _ => hh_pos x a
  have hP2 : hh a a * P = q := by
    rw [hP, mul_prod_erase _ (fun x => hh x a) ha]
    rw [prod_congr rfl (fun x _ => hh_symm x a)]
    exact prod_hh hζ hq0 ha
  have hC : Cs q a * P = (q : ℝ) ^ (q - 1) := by
    rw [Cs_eq, hP, ← prod_mul_distrib]
    rw [prod_congr rfl hin, prod_const, hcard]
  have hqr : (q : ℝ) ≠ 0 := by positivity
  have hC2 : Cs q a = (q : ℝ) ^ (q - 2) * hh a a := by
    refine mul_right_cancel₀ hPpos.ne' ?_
    rw [hC, mul_assoc, hP2, ← pow_succ]; congr 1; omega
  have hD : hh a a * Ds q a = Dfull q := by
    rw [Ds_eq, Dfull_eq, mul_prod_erase _ (fun x => hh x x) ha]
  rw [hC2, mul_assoc, hD]

/-- **`prop:Ms`** (Proposition 8.2 of the note), ordered form `M_s² = M_0²`:
`V_a · C_a · D_a` does not depend on the removed root `a ∈ μ_q`.  The statement is about moduli;
the complex product without absolute values does depend on `s`. -/
theorem prop_Ms (hζ : IsPrimitiveRoot ζ q) (hq : 2 ≤ q) {a b : ℂ} (ha : a ∈ mu q)
    (hb : b ∈ mu q) :
    Vs q a * Cs q a * Ds q a = Vs q b * Cs q b * Ds q b := by
  rw [mul_assoc, mul_assoc, CD_punctured hζ hq ha, CD_punctured hζ hq hb,
    vandermonde_punctured hζ hq ha, vandermonde_punctured hζ hq hb]

/-- `prop:Ms` with `a = ζ^s`, `s ∈ ℤ/q`: `M_s² = M_0²`. -/
theorem prop_Ms_zmod [NeZero q] (hζ : IsPrimitiveRoot ζ q) (hq : 2 ≤ q) (s : ZMod q) :
    Vs q (ζ ^ s.val) * Cs q (ζ ^ s.val) * Ds q (ζ ^ s.val) =
      Vs q (ζ ^ (0 : ZMod q).val) * Cs q (ζ ^ (0 : ZMod q).val) * Ds q (ζ ^ (0 : ZMod q).val) := by
  have hq0 : 0 < q := by omega
  have hmem : ∀ n : ℕ, ζ ^ n ∈ mu q := fun n => by
    rw [mem_mu hq0, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  exact prop_Ms hζ hq (hmem _) (hmem _)

end Main

end WeylProductMs
