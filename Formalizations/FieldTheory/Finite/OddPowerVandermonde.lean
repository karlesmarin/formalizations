/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Int.Interval

/-!
# Four finite-field facts: Fermat series, residue classes, monomial isolation, odd powers

Auxiliary facts over `ZMod p`, `p` prime.

## Main results

* `ConjeturaC.fermat_series`: `(k : ZMod p)^(p−1) = if p ∣ k then 0 else 1`.
* `ConjeturaC.crt_Xc`: for `2m + 1 = p n` with `gcd(p, n) = 1` and `n ∤ c`, the set
  `X_c = {x ∈ [−m, m] | x ≡ c (mod n)}` has `p` elements, does not contain `0`, and reduction
  modulo `p` is a bijection from `X_c` onto `ZMod p`.
* `ConjeturaC.isolate_monomial_fin`, `ConjeturaC.isolate_monomial`: `p` distinct points of
  `ZMod p` carry weights `λ` with `∑_x λ x · x^i = δ_ij` for all `i < p` (Vandermonde).
* `ConjeturaC.det_oddChar_ne_zero`: `det [l^e]_{l = 1..(p−1)/2, e = 1, 3, …, p−2} ≠ 0` in
  `ZMod p` (a diagonal times a Vandermonde matrix in `l²`).
-/

@[expose] public section

open Finset Matrix

namespace ConjeturaC

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### The Fermat series -/
theorem fermat_series (k : ℤ) :
    (k : ZMod p) ^ (p - 1) = if (p : ℤ) ∣ k then 0 else 1 := by
  simp only [ZMod.pow_card_sub_one, ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd, ite_not]

/-! ### Residue classes in `[−m, m]` -/
/-- `X_c = {x ∈ [-m, m] : x ≡ c [ZMOD n]}`. -/
def Xc (m n : ℕ) (c : ℤ) : Finset ℤ :=
  (Finset.Icc (-(m : ℤ)) m).filter (fun x => x ≡ c [ZMOD n])

theorem crt_Xc (n m : ℕ) (hn : 1 ≤ n) (hcop : Nat.Coprime p n) (hm : 2 * m + 1 = p * n)
    (c : ℤ) (hc : ¬ (n : ℤ) ∣ c) :
    (Xc m n c).card = p ∧ (0 : ℤ) ∉ Xc m n c ∧
    Set.InjOn (fun x : ℤ => (x : ZMod p)) (Xc m n c) ∧
    ∀ r : ZMod p, ∃ x ∈ Xc m n c, (x : ZMod p) = r := by
  have hmZ : (2 * (m : ℤ) + 1) = (p : ℤ) * n := by exact_mod_cast hm
  -- injectivity
  have hinj : Set.InjOn (fun x : ℤ => (x : ZMod p)) (Xc m n c) := by
    intro x hx y hy hxy
    simp only [Xc, Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hx hy
    have h1 : (p : ℤ) ∣ y - x := (ZMod.intCast_eq_intCast_iff_dvd_sub x y p).1 hxy
    have h2 : (n : ℤ) ∣ y - x := Int.modEq_iff_dvd.1 (hx.2.trans hy.2.symm)
    have hco : IsCoprime (p : ℤ) (n : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]; exact hcop
    have h3 : (p : ℤ) * n ∣ y - x := hco.mul_dvd h1 h2
    have h4 : |y - x| < (p : ℤ) * n := by
      rw [abs_lt]; constructor <;> linarith [hx.1.1, hx.1.2, hy.1.1, hy.1.2]
    have := Int.eq_zero_of_abs_lt_dvd h3 h4
    linarith
  -- surjectivity (Chinese remainder + choice of the representative in [-m, m])
  have hsurj : ∀ r : ZMod p, ∃ x ∈ Xc m n c, (x : ZMod p) = r := by
    intro r
    obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop r.val (c % n).toNat
    obtain ⟨N, hN⟩ : ∃ N : ℤ, N = 2 * m + 1 := ⟨_, rfl⟩
    have hNpos : 0 < N := by omega
    have hmodN : ((k : ℤ) + m) % N - m ≡ k [ZMOD N] := by
      have := Int.mod_modEq ((k : ℤ) + m) N
      simpa using this.sub_right (m : ℤ)
    have hmodpn : ((k : ℤ) + m) % N - m ≡ k [ZMOD (p : ℤ) * n] := by
      rw [← hmZ, ← hN]; exact hmodN
    refine ⟨((k : ℤ) + m) % N - m, ?_, ?_⟩
    · have hmodn : ((k : ℤ) + m) % N - m ≡ k [ZMOD n] := hmodpn.of_mul_left _
      have hkn : (k : ℤ) ≡ c [ZMOD n] := by
        have h := congrArg (Nat.cast : ℕ → ℤ) hk2
        push_cast at h
        have hnn : 0 ≤ c % (n : ℤ) := Int.emod_nonneg c (by exact_mod_cast (by omega : n ≠ 0))
        rw [Int.toNat_of_nonneg hnn, Int.emod_emod] at h
        exact h
      simp only [Xc, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, hmodn.trans hkn⟩
      · have := Int.emod_nonneg ((k : ℤ) + m) hNpos.ne'; linarith
      · have := Int.emod_lt_of_pos ((k : ℤ) + m) hNpos; linarith
    · have hmodp : ((k : ℤ) + m) % N - m ≡ k [ZMOD p] := hmodpn.of_mul_right _
      rw [(ZMod.intCast_eq_intCast_iff _ _ p).2 hmodp, Int.cast_natCast,
        (ZMod.natCast_eq_natCast_iff _ _ p).2 hk1, ZMod.natCast_zmod_val]
  refine ⟨?_, ?_, hinj, hsurj⟩
  · rw [← ZMod.card p, ← Finset.card_univ]
    exact Finset.card_nbij _ (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) hinj
      fun r _ => hsurj r
  · intro h0
    simp only [Xc, Finset.mem_filter] at h0
    exact hc (by simpa using Int.modEq_iff_dvd.1 h0.2)

/-! ### Isolating a monomial -/
/-- Vandermonde core: `n` distinct points of a field, weights isolating the monomial `X^j`. -/
theorem isolate_monomial_fin {K : Type*} [Field K] {n : ℕ} (v : Fin n → K)
    (hv : Function.Injective v) (j : Fin n) :
    ∃ μ : Fin n → K, ∀ i : Fin n, ∑ k, μ k * v k ^ (i : ℕ) = if i = j then 1 else 0 := by
  classical
  obtain ⟨μ, hμ⟩ := vecMul_surjective_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2
    (isUnit_iff_ne_zero.2 (det_vandermonde_ne_zero_iff.2 hv))) (Pi.single j 1)
  exact ⟨μ, fun i => by simpa [vecMul, dotProduct, Pi.single_apply] using congrFun hμ i⟩

/-- Isolating a monomial, as used: `S ⊆ ZMod p` with `p` points (i.e. the reductions of `X_c`). -/
theorem isolate_monomial (S : Finset (ZMod p)) (hS : S.card = p) (j : ℕ) (hj : j < p) :
    ∃ lam : ZMod p → ZMod p, ∀ i < p,
      ∑ x ∈ S, lam x * x ^ i = if i = j then 1 else 0 := by
  classical
  let e : S ≃ Fin p := Finset.equivFinOfCardEq hS
  let v : Fin p → ZMod p := fun k => (e.symm k : ZMod p)
  have hv : Function.Injective v := Subtype.val_injective.comp e.symm.injective
  obtain ⟨μ, hμ⟩ := isolate_monomial_fin v hv ⟨j, hj⟩
  refine ⟨fun x => if h : x ∈ S then μ (e ⟨x, h⟩) else 0, fun i hi => ?_⟩
  rw [← Finset.sum_coe_sort S, ← e.symm.sum_comp]
  have := hμ ⟨i, hi⟩
  simp only [Fin.mk.injEq] at this
  rw [← this]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [v]

/-! ### Odd powers -/
/-- Rows `l = a+1 ∈ {1..(p-1)/2}`, columns `e = 2b+1 ∈ {1,3,..,p-2}`, entry `l^e`. -/
def oddCharMat (p : ℕ) : Matrix (Fin ((p - 1) / 2)) (Fin ((p - 1) / 2)) (ZMod p) :=
  Matrix.of fun a b => (((a : ℕ) + 1 : ℕ) : ZMod p) ^ (2 * (b : ℕ) + 1)

theorem det_oddChar_ne_zero : (oddCharMat p).det ≠ 0 := by
  have hp2 := hp.out.two_le
  have hne : ∀ a : Fin ((p - 1) / 2), (((a : ℕ) + 1 : ℕ) : ZMod p) ≠ 0 := by
    intro a h
    have hd := (ZMod.natCast_eq_zero_iff _ _).1 h
    have := Nat.le_of_dvd (by omega) hd
    have := a.2; omega
  have hfac : oddCharMat p = diagonal (fun a : Fin ((p - 1) / 2) => (((a : ℕ) + 1 : ℕ) : ZMod p)) *
      vandermonde (fun a : Fin ((p - 1) / 2) => (((a : ℕ) + 1 : ℕ) : ZMod p) ^ 2) := by
    ext a b
    simp only [oddCharMat, of_apply, diagonal_mul, vandermonde_apply]
    rw [pow_succ, pow_mul]; ring
  have hinj : Function.Injective
      (fun a : Fin ((p - 1) / 2) => (((a : ℕ) + 1 : ℕ) : ZMod p) ^ 2) := by
    intro a b h
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
    · rw [ZMod.natCast_eq_natCast_iff'] at h
      rw [Nat.mod_eq_of_lt (by have := a.2; omega), Nat.mod_eq_of_lt (by have := b.2; omega)] at h
      exact Fin.ext (by omega)
    · exfalso
      have h0 : ((((a : ℕ) + 1) + ((b : ℕ) + 1) : ℕ) : ZMod p) = 0 := by
        push_cast at h ⊢; rw [h]; ring
      have hd := (ZMod.natCast_eq_zero_iff _ _).1 h0
      have := Nat.le_of_dvd (by omega) hd
      have := a.2; have := b.2; omega
  rw [hfac, det_mul, det_diagonal]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun a _ => hne a)
    (det_vandermonde_ne_zero_iff.2 hinj)

end ConjeturaC
