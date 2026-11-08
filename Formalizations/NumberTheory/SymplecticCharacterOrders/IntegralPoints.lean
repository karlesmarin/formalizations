/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.NumberTheory.SymplecticCharacterOrders.Segments
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.RingTheory.RootsOfUnity.Minpoly
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.FieldTheory.Galois.Basic

/-!
# Integrality of the spectrum of `g_{1/q}` (Theorem 5.1, arithmetic part)

The spectrum of `g_{1/q}` in the natural representation of `Sp(2m)` is the multiset
`spec q m = {±j mod q : j = 1..m}` of `ZMod q`.

## Main results

* `Segmentos.stable_iff_cond`: for `q ≥ 2`, `m ≥ 1`, `spec q m` is stable under every unit of
  `ZMod q` iff `q ∣ 2m`, `q ∣ 2m+1`, `q ∣ 2m+2`, or `q = 6 ∧ m ≡ 1 (mod 3)`.
-/

@[expose] public section

open Finset

namespace Segmentos

/-- The multiset `{±j : j = 1..m}` of `ZMod q` (`2m` elements). -/
def spec (q m : ℕ) : Multiset (ZMod q) :=
  (Icc 1 m).val.map (fun j : ℕ => (j : ZMod q)) + (Icc 1 m).val.map (fun j : ℕ => -(j : ZMod q))

/-- Condition (I) of Theorem 5.1. -/
def CondI (q m : ℕ) : Prop := D q m ∨ (q = 6 ∧ m % 3 = 1)

instance (q m : ℕ) : Decidable (CondI q m) := by unfold CondI; infer_instance

/-- Multiplicity in `spec` versus the count `N`: elements with `c = -c` count twice. -/
lemma count_spec (q m : ℕ) (c : ZMod q) :
    (spec q m).count c = (if c = -c then 2 else 1) * N q m c := by
  unfold spec N
  rw [Multiset.count_add, Multiset.count_map, Multiset.count_map]
  have e1 : Multiset.card (Multiset.filter (fun j : ℕ => c = (j : ZMod q)) (Icc 1 m).val) =
      ((Icc 1 m).filter (fun j : ℕ => c = (j : ZMod q))).card := rfl
  have e2 : Multiset.card (Multiset.filter (fun j : ℕ => c = -(j : ZMod q)) (Icc 1 m).val) =
      ((Icc 1 m).filter (fun j : ℕ => c = -(j : ZMod q))).card := rfl
  rw [e1, e2]
  split_ifs with h
  · have f1 : (Icc 1 m).filter (fun j : ℕ => c = (j : ZMod q)) =
        (Icc 1 m).filter (fun j : ℕ => (j : ZMod q) = c ∨ (j : ZMod q) = -c) := by
      apply filter_congr; intro j _
      constructor
      · intro hj; exact Or.inl hj.symm
      · rintro (hj | hj)
        · exact hj.symm
        · rw [hj]; exact h
    have f2 : (Icc 1 m).filter (fun j : ℕ => c = -(j : ZMod q)) =
        (Icc 1 m).filter (fun j : ℕ => (j : ZMod q) = c ∨ (j : ZMod q) = -c) := by
      apply filter_congr; intro j _
      constructor
      · intro hj; exact Or.inr (by rw [hj, neg_neg])
      · rintro (hj | hj)
        · rw [hj]; exact h
        · rw [hj]; exact (neg_neg c).symm
    rw [f1, f2]; ring
  · rw [one_mul, ← card_union_of_disjoint]
    · congr 1
      ext j
      simp only [mem_union, mem_filter]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, Or.inl h2.symm⟩
        · refine ⟨h1, Or.inr ?_⟩; rw [h2, neg_neg]
      · rintro ⟨h1, h2 | h2⟩
        · exact Or.inl ⟨h1, h2.symm⟩
        · refine Or.inr ⟨h1, ?_⟩; rw [h2, neg_neg]
    · rw [disjoint_left]
      intro j h1 h2
      simp only [mem_filter] at h1 h2
      exact h (h2.2.trans (by rw [h1.2]))

/-- Bridge: `spec` is stable under a unit iff `N` is (`Stable`). -/
lemma map_mul_spec_iff (q m : ℕ) (u : (ZMod q)ˣ) :
    (spec q m).map (fun x => (u : ZMod q) * x) = spec q m ↔ Stable q m u := by
  have hinj : Function.Injective (fun x : ZMod q => (u : ZMod q) * x) :=
    fun x y h => (Units.mul_right_inj u).mp h
  rw [Multiset.ext]
  have key : ∀ c : ZMod q, ((spec q m).map (fun x => (u : ZMod q) * x)).count ((u : ZMod q) * c) =
      (spec q m).count c := fun c => Multiset.count_map_eq_count' _ _ hinj c
  have hsurj : ∀ y : ZMod q, ∃ c, (u : ZMod q) * c = y := fun y =>
    ⟨((u⁻¹ : (ZMod q)ˣ) : ZMod q) * y, by rw [← mul_assoc, Units.mul_inv, one_mul]⟩
  have hsym : ∀ c : ZMod q, ((u : ZMod q) * c = -((u : ZMod q) * c)) ↔ (c = -c) := by
    intro c
    rw [← mul_neg, Units.mul_right_inj]
  constructor
  · intro H c
    have h1 := H ((u : ZMod q) * c)
    rw [key c, count_spec, count_spec] at h1
    simp only [hsym] at h1
    have : 0 < (if c = -c then 2 else 1) := by split_ifs <;> omega
    exact (Nat.eq_of_mul_eq_mul_left this h1).symm
  · intro H y
    obtain ⟨c, rfl⟩ := hsurj y
    rw [key c, count_spec, count_spec]
    simp only [hsym]
    rw [H c]

/-! ## A unit different from `±1` -/

lemma unit_aux {q x : ℕ} (hx : Nat.Coprime x q) (hx1 : 1 ≤ x) (h1 : ¬ q ∣ x - 1)
    (h2 : ¬ q ∣ x + 1) : ∃ u : (ZMod q)ˣ, (u : ZMod q) ≠ 1 ∧ (u : ZMod q) ≠ -1 := by
  refine ⟨ZMod.unitOfCoprime x hx, ?_, ?_⟩
  · rw [ZMod.coe_unitOfCoprime]
    intro h
    apply h1
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hx1, h, Nat.cast_one, sub_self]
  · rw [ZMod.coe_unitOfCoprime]
    intro h
    apply h2
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, h, Nat.cast_one, neg_add_cancel]

/-- For `q ≥ 3`, `q ∉ {3, 4, 6}` there is a unit of `ZMod q` different from `±1`. -/
lemma exists_unit_ne {q : ℕ} (hq : 3 ≤ q) (h3 : q ≠ 3) (h4 : q ≠ 4) (h6 : q ≠ 6) :
    ∃ u : (ZMod q)ˣ, (u : ZMod q) ≠ 1 ∧ (u : ZMod q) ≠ -1 := by
  by_cases hodd : q % 2 = 1
  · refine unit_aux (x := 2) ?_ (by norm_num) ?_ ?_
    · rw [Nat.coprime_two_left]; exact Nat.odd_iff.mpr hodd
    · intro h; have := Nat.le_of_dvd (by norm_num) h; omega
    · intro h; have := Nat.le_of_dvd (by norm_num) h; omega
  · by_cases h40 : q % 4 = 0
    · obtain ⟨j, rfl⟩ : ∃ j, q = 4 * j := ⟨q / 4, by omega⟩
      refine unit_aux (x := 2 * j + 1) ?_ (by omega) ?_ ?_
      · have h1 : Nat.Coprime (2*j+1) 4 := by
          have : Nat.Coprime (2*j+1) 2 := by simp
          simpa using Nat.Coprime.pow_right 2 this
        have h2 : Nat.Coprime (2*j+1) j := by simp
        exact Nat.Coprime.mul_right h1 h2
      · intro h; have := Nat.le_of_dvd (by omega) h; omega
      · intro h; have := Nat.le_of_dvd (by omega) h; omega
    · obtain ⟨k, rfl⟩ : ∃ k, q = 2 * k := ⟨q / 2, by omega⟩
      have hk : Odd k := Nat.odd_iff.mpr (by omega)
      refine unit_aux (x := k + 2) ?_ (by omega) ?_ ?_
      · refine Nat.Coprime.mul_right ?_ ?_
        · rw [Nat.coprime_two_right]; exact hk.add_even even_two
        · rw [add_comm, Nat.coprime_add_self_left, Nat.coprime_two_left]; exact hk
      · intro h; have := Nat.le_of_dvd (by omega) h; omega
      · intro h; have := Nat.le_of_dvd (by omega) h; omega

/-- For `q ∈ {2, 3, 4, 6}` every unit of `ZMod q` is `±1`. -/
lemma unit_pm {q : ℕ} (hs : q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 6) (u : (ZMod q)ˣ) :
    (u : ZMod q) = 1 ∨ (u : ZMod q) = -1 := by
  have h2 : ∀ a b : ZMod 2, a * b = 1 → a = 1 ∨ a = -1 := by decide
  have h3 : ∀ a b : ZMod 3, a * b = 1 → a = 1 ∨ a = -1 := by decide
  have h4 : ∀ a b : ZMod 4, a * b = 1 → a = 1 ∨ a = -1 := by decide
  have h6 : ∀ a b : ZMod 6, a * b = 1 → a = 1 ∨ a = -1 := by decide
  rcases hs with rfl | rfl | rfl | rfl
  · exact h2 _ _ u.mul_inv
  · exact h3 _ _ u.mul_inv
  · exact h4 _ _ u.mul_inv
  · exact h6 _ _ u.mul_inv

/-- For `q ∈ {2, 3, 4, 6}`, condition (I) always holds. -/
lemma condI_small {q : ℕ} (m : ℕ) (hs : q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 6) : CondI q m := by
  unfold CondI D
  simp only [Nat.dvd_iff_mod_eq_zero]
  have h3 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  have h4 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
  rcases hs with rfl | rfl | rfl | rfl <;> rcases h3 with h3 | h3 | h3 <;> omega

/-- **Theorem 5.1, integer arithmetic.** For `q ≥ 2`, the spectrum `{±j mod q : j = 1..m}` is
stable under every unit of `ZMod q` iff `q ∣ 2m`, `q ∣ 2m+1`, `q ∣ 2m+2`, or
`q = 6 ∧ m ≡ 1 (mod 3)` (the last clause is needed: for `q = 6` the units are `±1`, so the
spectrum is always stable). -/
theorem stable_iff_cond {q m : ℕ} (hq : 2 ≤ q) :
    (∀ u : (ZMod q)ˣ, (spec q m).map (fun x => (u : ZMod q) * x) = spec q m) ↔ CondI q m := by
  simp only [map_mul_spec_iff]
  by_cases hs : q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 6
  · refine ⟨fun _ => condI_small m hs, fun _ u => ?_⟩
    intro c
    rcases unit_pm hs u with h | h
    · rw [h, one_mul]
    · rw [h, neg_mul, one_mul, N_neg]
  · simp only [not_or] at hs
    obtain ⟨hs2, hs3, hs4, hs6⟩ := hs
    have hq3 : 3 ≤ q := by omega
    obtain ⟨a, ha1, ha2⟩ := exists_unit_ne hq3 hs3 hs4 hs6
    constructor
    · intro H
      exact Or.inl ((lem_seg hq3 a ha1 ha2).mp (H a))
    · rintro (hD | ⟨h6, _⟩)
      · exact fun u => seg_stable_of_dvd hq3 hD u
      · exact absurd h6 hs6

/-! ## Integrality and Galois stability -/

open Polynomial

/-- `esymm` commutes with ring homomorphisms. -/
lemma esymm_map {R S F : Type*} [CommSemiring R] [CommSemiring S] [FunLike F R S]
    [RingHomClass F R S] (f : F) (s : Multiset R) (k : ℕ) :
    f (s.esymm k) = (s.map f).esymm k := by
  simp only [Multiset.esymm, map_multiset_sum, Multiset.map_map, Multiset.powersetCard_map,
    Function.comp_def, map_multiset_prod]

section Cyclotomic

variable {q : ℕ} [NeZero q] {K : Type*} [Field K] [Algebra ℚ K] {ζ : K}

omit [Algebra ℚ K] in
/-- `a ↦ ζ ^ a.val` is injective on `ZMod q`. -/
lemma pow_val_injective (hζ : IsPrimitiveRoot ζ q) :
    Function.Injective (fun a : ZMod q => ζ ^ a.val) := by
  intro a b h
  exact ZMod.val_injective q (hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h)

omit [NeZero q] [Algebra ℚ K] in
lemma pow_val_mul (hζ : IsPrimitiveRoot ζ q) (a b : ZMod q) :
    ζ ^ (a * b).val = (ζ ^ a.val) ^ b.val := by
  rw [ZMod.val_mul, ← pow_mul, ← pow_eq_pow_mod _ hζ.pow_eq_one]

/-- An automorphism `σ` with `σ ζ = ζ ^ v` acts on `{ζ^a}_{a ∈ A}` as `a ↦ v a` on `A`. -/
lemma map_aut_pow (hζ : IsPrimitiveRoot ζ q) (σ : K ≃ₐ[ℚ] K) (A : Multiset (ZMod q)) :
    (A.map (fun a => ζ ^ a.val)).map σ =
      (A.map (fun a => ((hζ.autToPow ℚ σ : (ZMod q)ˣ) : ZMod q) * a)).map (fun a => ζ ^ a.val) := by
  rw [Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro a _
  simp only [Function.comp_apply, map_pow]
  rw [← hζ.autToPow_spec ℚ σ, pow_val_mul hζ, ← pow_mul]

/-- Over a cyclotomic field: the `esymm` of `{ζ^a}_{a ∈ A}` are all rational iff `A` is stable
under all units. -/
theorem esymm_rat_iff_stable [IsCyclotomicExtension {q} ℚ K] (hζ : IsPrimitiveRoot ζ q)
    (A : Multiset (ZMod q)) :
    (∀ k, ∃ r : ℚ, (A.map (fun a => ζ ^ a.val)).esymm k = algebraMap ℚ K r) ↔
      ∀ u : (ZMod q)ˣ, A.map (fun a => (u : ZMod q) * a) = A := by
  have hinj := pow_val_injective hζ
  have : FiniteDimensional ℚ K := IsCyclotomicExtension.finiteDimensional ({q} : Set ℕ) ℚ K
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {q} ℚ K
  constructor
  · -- (⇒)
    intro H u
    have hirr : Irreducible (Polynomial.cyclotomic q ℚ) :=
      Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_ne_zero (NeZero.ne q))
    have hμ : IsPrimitiveRoot (ζ ^ (u : ZMod q).val) q :=
      hζ.pow_of_coprime _ (ZMod.val_coe_unit_coprime u)
    have hmin : minpoly ℚ (hζ.powerBasis ℚ).gen = minpoly ℚ (hμ.powerBasis ℚ).gen := by
      rw [hζ.powerBasis_gen ℚ, hμ.powerBasis_gen ℚ]
      exact (hζ.minpoly_eq_cyclotomic_of_irreducible hirr).symm.trans
        (hμ.minpoly_eq_cyclotomic_of_irreducible hirr)
    set σ := (hζ.powerBasis ℚ).equivOfMinpoly (hμ.powerBasis ℚ) hmin with hσ
    have hσζ : σ ζ = ζ ^ (u : ZMod q).val := by
      have := PowerBasis.equivOfMinpoly_gen (hζ.powerBasis ℚ) (hμ.powerBasis ℚ) hmin
      rwa [hζ.powerBasis_gen ℚ, hμ.powerBasis_gen ℚ] at this
    have hv : hζ.autToPow ℚ σ = u := by
      apply Units.ext
      apply ZMod.val_injective q
      apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
      rw [hζ.autToPow_spec ℚ σ, hσζ]
    -- the polynomial `∏ (X - ζ^a)` has rational coefficients, hence is fixed by `σ`
    set SK : Multiset K := A.map (fun a => ζ ^ a.val) with hSK
    have hfix : ∀ j, σ (SK.esymm j) = SK.esymm j := by
      intro j
      obtain ⟨r, hr⟩ := H j
      rw [hr]
      exact σ.commutes r
    have hP : (SK.map fun t => X - C t).prod =
        ∑ j ∈ Finset.range (Multiset.card SK + 1),
          (-1) ^ j * (C (SK.esymm j) * X ^ (Multiset.card SK - j)) :=
      Multiset.prod_X_sub_X_eq_sum_esymm SK
    have hmapP : ((SK.map fun t => X - C t).prod).map (σ : K →+* K) =
        (SK.map fun t => X - C t).prod := by
      conv_rhs => rw [hP]
      rw [hP, Polynomial.map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg, Polynomial.map_one,
        Polynomial.map_C, Polynomial.map_X]
      congr 3
      exact hfix j
    have he : ((SK.map σ).map fun t => X - C t) =
        (SK.map fun t => X - C t).map (Polynomial.map (σ : K →+* K)) := by
      simp only [hSK, Multiset.map_map]
      apply Multiset.map_congr rfl
      intro t _
      simp
    have hprod : (((SK.map σ)).map fun t => X - C t).prod = (SK.map fun t => X - C t).prod := by
      rw [he, ← Polynomial.map_multiset_prod]
      exact hmapP
    have hroots := congrArg Polynomial.roots hprod
    rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hroots
    have h2 := map_aut_pow hζ σ A
    rw [hv] at h2
    rw [hroots] at h2
    exact Multiset.map_injective hinj h2.symm
  · -- (⇐)
    intro H k
    have hmem : ∀ σ : K ≃ₐ[ℚ] K, σ ((A.map (fun a => ζ ^ a.val)).esymm k) =
        (A.map (fun a => ζ ^ a.val)).esymm k := by
      intro σ
      rw [esymm_map σ, map_aut_pow hζ σ A, H]
    obtain ⟨r, hr⟩ := (IsGalois.mem_range_algebraMap_iff_fixed
      ((A.map (fun a => ζ ^ a.val)).esymm k)).mpr hmem
    exact ⟨r, hr.symm⟩

end Cyclotomic

/-- The `esymm` of roots of unity are algebraic integers. -/
lemma esymm_isIntegral {q : ℕ} (hq : 0 < q) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ q)
    (A : Multiset (ZMod q)) (k : ℕ) :
    IsIntegral ℤ ((A.map (fun a => ζ ^ a.val)).esymm k) := by
  have key : (A.map (fun a => ζ ^ a.val)).esymm k ∈ integralClosure ℤ ℂ := by
    unfold Multiset.esymm
    apply Subalgebra.multiset_sum_mem
    intro y hy
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hy
    apply Subalgebra.multiset_prod_mem
    intro z hz
    have hz' := Multiset.mem_of_le (Multiset.mem_powersetCard.mp ht).1 hz
    obtain ⟨a, _, rfl⟩ := Multiset.mem_map.mp hz'
    exact (mem_integralClosure_iff ℤ ℂ).mpr ((hζ.isIntegral hq).pow _)
  exact (mem_integralClosure_iff ℤ ℂ).mp key

/-- **Integrality and Galois stability.** Let `ζ ∈ ℂ` be a primitive `q`-th root of unity and `A`
a finite multiset of `ZMod q`. All elementary symmetric functions of `{ζ^a}_{a ∈ A}` are integers
iff `A` is stable under multiplication by every unit of `ZMod q`. -/
theorem esymm_int_iff_stable {q : ℕ} (hq : 1 ≤ q) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ q)
    (A : Multiset (ZMod q)) :
    (∀ k, ∃ n : ℤ, (A.map (fun a => ζ ^ a.val)).esymm k = n) ↔
      ∀ u : (ZMod q)ˣ, A.map (fun a => (u : ZMod q) * a) = A := by
  have : NeZero q := ⟨by omega⟩
  have hint : IsIntegral ℚ ζ := (hζ.isIntegral (by omega)).tower_top
  let K := IntermediateField.adjoin ℚ {ζ}
  have : IsCyclotomicExtension {q} ℚ K := by
    change IsCyclotomicExtension {q} ℚ (IntermediateField.adjoin ℚ {ζ}).toSubalgebra
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hζ.adjoin_isCyclotomicExtension ℚ
  let ζK : K := IntermediateField.AdjoinSimple.gen ℚ ζ
  have hζK : IsPrimitiveRoot ζK q := by
    refine IsPrimitiveRoot.of_map_of_injective (f := (IntermediateField.val K)) ?_
      (IntermediateField.val K).toRingHom.injective
    exact hζ
  rw [← esymm_rat_iff_stable hζK A]
  have hS : ∀ k, (IntermediateField.val K) ((A.map (fun a => ζK ^ a.val)).esymm k) =
      (A.map (fun a => ζ ^ a.val)).esymm k := by
    intro k
    rw [esymm_map, Multiset.map_map]
    congr 2
  refine forall_congr' fun k => ⟨?_, ?_⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, (IntermediateField.val K).toRingHom.injective ?_⟩
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [hS, hn]
    simp
  · rintro ⟨r, hr⟩
    have h1 : (A.map (fun a => ζ ^ a.val)).esymm k = algebraMap ℚ ℂ r := by
      rw [← hS, hr]
      exact AlgHom.commutes _ r
    have h2 : IsIntegral ℤ (algebraMap ℚ ℂ r) := h1 ▸ esymm_isIntegral (by omega) hζ A k
    have h3 : IsIntegral ℤ r := (isIntegral_algebraMap_iff (A := ℚ) (B := ℂ)).mp h2
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h3
    refine ⟨y, ?_⟩
    rw [h1, ← hy]
    simp

/-! ## The final statement -/

lemma pow_val_natCast {q : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ q) (j : ℕ) :
    ζ ^ ((j : ZMod q).val) = ζ ^ j := by
  rw [ZMod.val_natCast]
  exact (pow_eq_pow_mod j hζ.pow_eq_one).symm

lemma pow_val_neg_natCast {q : ℕ} [NeZero q] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ q) (j : ℕ) :
    ζ ^ ((-(j : ZMod q)).val) = (ζ ^ j)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_add, hζ.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]
  push_cast
  simp

/-- The spectrum of `g_{1/q}` on the natural representation, as complex numbers:
`{ζ^j, ζ^{-j} : j = 1..m}`. -/
lemma spec_map {q : ℕ} [NeZero q] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ q) (m : ℕ) :
    (spec q m).map (fun a => ζ ^ a.val) =
      (Icc 1 m).val.map (fun j : ℕ => ζ ^ j) + (Icc 1 m).val.map (fun j : ℕ => (ζ ^ j)⁻¹) := by
  unfold spec
  rw [Multiset.map_add, Multiset.map_map, Multiset.map_map]
  congr 1
  · apply Multiset.map_congr rfl
    intro j _
    exact pow_val_natCast hζ j
  · apply Multiset.map_congr rfl
    intro j _
    exact pow_val_neg_natCast hζ j

/-- **Theorem 5.1 (`thm:clasif`), spectral form.** Let `m ≥ 1`, `q ≥ 2` and `ζ ∈ ℂ` a primitive
`q`-th root of unity. All elementary symmetric functions of the spectrum `{ζ^{±j} : j = 1..m}` of
`g_{1/q}` are integers iff `q ∣ 2m`, `q ∣ 2m+1`, `q ∣ 2m+2`, or `q = 6 ∧ m ≡ 1 (mod 3)`.

NOT formalized here: the step "all characters of `Sp(2m)` are integers at `g_{1/q}` iff the
`esymm` of the spectrum are". It is the representation ring of `Sp(2m)`, generated by the exterior
powers of the natural representation, whose characters at `g` are these `esymm`. That step is
certified exactly in `anc/certificar_exacto.py` (C2: 455 characters, 44 of 44 pairs `m ≤ 5`,
`q ≤ 12`). -/
theorem thm_clasif_spectral {q m : ℕ} (hq : 2 ≤ q) (hm : 1 ≤ m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ q) :
    (∀ k, ∃ n : ℤ, ((spec q m).map (fun a => ζ ^ a.val)).esymm k = n) ↔
      (q ∣ 2 * m ∨ q ∣ 2 * m + 1 ∨ q ∣ 2 * m + 2 ∨ (q = 6 ∧ m % 3 = 1)) := by
  have := hm
  rw [esymm_int_iff_stable (by omega) hζ, stable_iff_cond hq]
  simp only [CondI, D, or_assoc]

/-- Sanity checks. -/
example : CondI 6 4 := by decide
example : CondI 5 4 := by decide  -- 5 ∣ 10 = 2·4+2 (the brief's "false" was a slip)
example : ¬ CondI 5 3 := by decide
example : CondI 9 4 := by decide
example : ¬ D 6 4 := by decide

end Segmentos
