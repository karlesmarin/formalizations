/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Combinatorial core of `κ(F_q(x)) = ω²`

The combinatorial core of the lower bound `κ(F_q(x)) = ω²` for the length of the DGH
stratification.

Let `L` be a prime, `G` an additive commutative group, and `f : ℤ → G` an `L`-periodic function
that is a finite sum of `k` arithmetic-progression indicators,
`f n = ∑ i, [n ≡ m i (mod N i)] • c i`. Then `f` is constant on all residues mod `L` except at
most `k` of them.

## Proof sketch

* `M := ∏_{i : L ∤ N i} N i` is coprime to `L`; pick `b` with `b·M ≡ 1 (mod L)`.
* For `r : ℤ`, `n := b·M·r ≡ r (mod L)`, so `f r = f n`. Terms with `L ∤ N i` are evaluated at a
  multiple of `N i`, hence equal the constant `c₀`. So `f r ≠ c₀` forces some `i` with `L ∣ N i`.
* Such an `i` determines `r mod L`, so the bad residues inject into `Fin k`.

The hypotheses `k < L` and `N i ≥ 1` are not needed.

## Main results

* `card_ne_const_le`, `card_ne_const_le_of_lt`.
-/

open Finset

namespace DGH.FqLower

/-- Core counting lemma (no `k < L`, no `N i ≥ 1` needed). -/
theorem card_ne_const_le {G : Type*} [AddCommGroup G] [DecidableEq G] (L : ℕ) (hL : L.Prime) (k : ℕ)
    (N : Fin k → ℕ) (m : Fin k → ℤ) (c : Fin k → G) (f : ℤ → G)
    (hper : ∀ n, f (n + L) = f n)
    (hf : ∀ n, f n = ∑ i, if n ≡ m i [ZMOD (N i)] then c i else 0) :
    ∃ c₀ : G, ((Finset.range L).filter (fun r : ℕ => f r ≠ c₀)).card ≤ k := by
  classical
  set S := (Finset.univ : Finset (Fin k)).filter (fun i => ¬ L ∣ N i) with hS
  set M : ℤ := ∏ i ∈ S, (N i : ℤ) with hM
  have hcop : IsCoprime (L : ℤ) M := by
    refine IsCoprime.prod_right fun i hi => ?_
    have : ¬ L ∣ N i := (Finset.mem_filter.1 hi).2
    exact Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hL).2 this)
  obtain ⟨a, b, hab⟩ := hcop
  have hNM : ∀ i, ¬ L ∣ N i → (N i : ℤ) ∣ M := fun i hi =>
    Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
  have hP : Function.Periodic f (L : ℤ) := hper
  set c₀ : G := ∑ i, if (¬ L ∣ N i ∧ (0 : ℤ) ≡ m i [ZMOD (N i)]) then c i else 0 with hc₀
  -- key claim: a value different from `c₀` is witnessed by a term with `L ∣ N i`
  have key : ∀ r : ℤ, f r ≠ c₀ →
      ∃ i, L ∣ N i ∧ ∃ s : ℤ, s ≡ r [ZMOD L] ∧ s ≡ m i [ZMOD (N i)] := by
    intro r hr
    by_contra hno
    push Not at hno
    apply hr
    have hn : f (b * M * r) = f r := by
      have : b * M * r = r + (-(a * r)) * (L : ℤ) := by linear_combination r * hab
      rw [this]; simpa using hP.int_mul (-(a * r)) r
    have hnr : b * M * r ≡ r [ZMOD L] :=
      Int.modEq_iff_dvd.2 ⟨a * r, by linear_combination (-r) * hab⟩
    rw [← hn, hf]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : L ∣ N i
    · have h1 : ¬ (b * M * r ≡ m i [ZMOD (N i)]) := hno i hi _ hnr
      simp [h1, hi]
    · have h0 : b * M * r ≡ 0 [ZMOD (N i)] :=
        Int.modEq_zero_iff_dvd.2 (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (hNM i hi) b) r)
      have h2 : (b * M * r ≡ m i [ZMOD (N i)]) ↔ ((0 : ℤ) ≡ m i [ZMOD (N i)]) :=
        ⟨fun h => h0.symm.trans h, fun h => h0.trans h⟩
      simp [hi, h2]
  refine ⟨c₀, ?_⟩
  have hcard := Finset.card_le_card_of_forall_subsingleton
    (s := (Finset.range L).filter (fun r : ℕ => f r ≠ c₀))
    (t := (Finset.univ : Finset (Fin k)))
    (fun (r : ℕ) (i : Fin k) => L ∣ N i ∧ ∃ s : ℤ, s ≡ (r : ℤ) [ZMOD L] ∧ s ≡ m i [ZMOD (N i)])
    (fun r hr => by
      obtain ⟨i, hi⟩ := key r (Finset.mem_filter.1 hr).2
      exact ⟨i, Finset.mem_univ _, hi⟩)
    (fun i _ => by
      rintro x ⟨hx, -, s, hs, hsm⟩ y ⟨hy, hiL, s', hs', hsm'⟩
      have hxL : x < L := Finset.mem_range.1 (Finset.mem_filter.1 hx).1
      have hyL : y < L := Finset.mem_range.1 (Finset.mem_filter.1 hy).1
      have hss : s ≡ s' [ZMOD (N i)] := hsm.trans hsm'.symm
      have hssL : s ≡ s' [ZMOD L] := hss.of_dvd (Int.natCast_dvd_natCast.2 hiL)
      have hxy : (x : ℤ) ≡ y [ZMOD L] := (hs.symm.trans hssL).trans hs'
      have hxy' : x % L = y % L := Int.natCast_modEq_iff.1 hxy
      rwa [Nat.mod_eq_of_lt hxL, Nat.mod_eq_of_lt hyL] at hxy')
  simpa using hcard

/-- The statement in the form requested (with the unused hypotheses `k < L`, `1 ≤ N i`). -/
theorem card_ne_const_le_of_lt {G : Type*} [AddCommGroup G] [DecidableEq G] (L : ℕ) (hL : L.Prime) (k : ℕ)
    (_hk : k < L) (N : Fin k → ℕ) (_hN : ∀ i, 1 ≤ N i) (m : Fin k → ℤ) (c : Fin k → G)
    (f : ℤ → G) (hper : ∀ n, f (n + L) = f n)
    (hf : ∀ n, f n = ∑ i, if n ≡ m i [ZMOD (N i)] then c i else 0) :
    ∃ c₀ : G, ((Finset.range L).filter (fun r : ℕ => f r ≠ c₀)).card ≤ k :=
  card_ne_const_le L hL k N m c f hper hf

end DGH.FqLower
