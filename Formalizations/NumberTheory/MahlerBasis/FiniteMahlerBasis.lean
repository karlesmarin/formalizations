/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Nat.Choose.Basic

/-!
# The finite Mahler basis of `ZMod N → R`

The functions `x ↦ C(x.val, i)`, `i < N`, on `ZMod N` with values in a nontrivial commutative
ring `R` are linearly independent (the matrix `[C(x, i)]_{x, i < N}` is lower unitriangular);
over a field they form a basis of `ZMod N → K`.

## Main results

* `ConjeturaC.linearIndependent_choose`: linear independence over `R`.
* `ConjeturaC.chooseBasis`, `ConjeturaC.coe_chooseBasis`: the basis over a field.
* `ConjeturaC.linearIndependent_choose_sq`: the case `N = p²`, `R = ZMod p`.

## References

* C. Marín, *Reading Iwasawa λ-invariants from Mahler matrices modulo p: programs, data and Lean
  files*, Zenodo (2026), doi:10.5281/zenodo.23085315.
-/

@[expose] public section

namespace ConjeturaC

/-- Binomial functions on `ZMod N`. -/
def chooseFun (N : ℕ) (R : Type*) [CommRing R] (i : Fin N) : ZMod N → R :=
  fun x => ((x.val.choose i : ℕ) : R)

theorem linearIndependent_choose (N : ℕ) [NeZero N] (R : Type*) [CommRing R] [Nontrivial R] :
    LinearIndependent R (chooseFun N R) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have key : ∀ n : ℕ, ∀ i : Fin N, i.val = n → g i = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hi
      have h := congrFun hg (i.val : ZMod N)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, chooseFun,
        ZMod.val_natCast_of_lt i.isLt] at h
      rw [Finset.sum_eq_single i] at h
      · simpa using h
      · intro j _ hji
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hji) with hlt | hgt
        · rw [ih j.val (by omega) j rfl, zero_mul]
        · rw [Nat.choose_eq_zero_of_lt hgt, Nat.cast_zero, mul_zero]
      · simp
  exact fun i => key i.val i rfl

/-- Over a field, the binomial functions are a basis of `ZMod N → K`. -/
noncomputable def chooseBasis (N : ℕ) [NeZero N] (K : Type*) [Field K] :
    Module.Basis (Fin N) K (ZMod N → K) :=
  have : Nonempty (Fin N) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩⟩
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_choose N K)
    (by rw [Module.finrank_fintype_fun_eq_card, ZMod.card, Fintype.card_fin])

theorem coe_chooseBasis (N : ℕ) [NeZero N] (K : Type*) [Field K] :
    ⇑(chooseBasis N K) = chooseFun N K := by
  simp [chooseBasis]

/-- The case of the paper: `N = p²`, values in `ZMod p`. -/
theorem linearIndependent_choose_sq (p : ℕ) [Fact p.Prime] :
    haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (Fact.out : p.Prime).ne_zero⟩
    LinearIndependent (ZMod p)
      (fun i : Fin (p ^ 2) => fun x : ZMod (p ^ 2) => ((x.val.choose i : ℕ) : ZMod p)) :=
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (Fact.out : p.Prime).ne_zero⟩
  linearIndependent_choose (p ^ 2) (ZMod p)

end ConjeturaC
