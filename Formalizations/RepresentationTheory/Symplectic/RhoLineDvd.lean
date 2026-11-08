/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
-- encaje: F_ρ ∣ F_ℓ en Sp(2m) (cierra la hipótesis hQ de thm:crit, thm:valgen, thm:signo de characters_at_aP.tex)
module

public import Formalizations.RepresentationTheory.Symplectic.RhoLine
public import Formalizations.RepresentationTheory.Symplectic.RhoLineSign
public import Formalizations.RepresentationTheory.Symplectic.SurvivorCount
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# The ρ-line of `Sp(2m)`: `F_ρ ∣ F_ℓ`

`ρ` minimises `N_d` over all `d ≥ 1` (`SurvivorCount`, the marginal-cost argument), and
`1 - X^a = -∏_{d ∣ a} Φ_d`, so the multiplicity of `Φ_d` in `F_x` is `N_d x`.  Hence `F_ρ ∣ F_ℓ`
and the hypothesis `F_ρ · Q = F_ℓ` of `thm_crit`, `thm_valgen`, `thm_signo` can be discharged.

## Main results

* `RhoLine.N_rho_le`: `N_d ρ ≤ N_d ℓ` for `d ≥ 1`, `ℓ` of length `m`.
* `RhoLine.dvd_rho`: `∃ Q, F_ρ * Q = F_ℓ`.
* `RhoLine.thm_crit'`, `RhoLine.thm_valgen'`, `RhoLine.thm_signo'`: the theorems without `hQ`.
-/

@[expose] public section

open Polynomial Finset

namespace RhoLine

section Bound

open ResidueCapacity SurvivorCount

/-- `ρ` minimises `N_q` over all vectors of the same length (every `q ≥ 1`). -/
lemma Nq_rho_le {q : ℕ} [NeZero q] (L : List (ZMod q)) : Nq (rho q L.length) ≤ Nq L := by
  have key : ∀ (m : ℕ) (x : Fin m → ZMod q), Nq (rho q m) ≤ Nq (List.ofFn x) := by
    intro m x
    rcases le_or_gt (m % q) (aq q) with hv | hv
    · have hρ : ∀ k : Cls (ZMod q), Al (2 * (m / q)) (m / q) 0 (wt (cls (G := ZMod q)) k)
          (prof (cls (G := ZMod q)) (rhoV q m) k) := by
        intro k
        obtain ⟨g, rfl⟩ := cls_surj k
        rw [wt_cls, ← occ_ofFn, occ_rhoV]
        exact rho_Al_case1 m hv g
      have hcg := cost_ge (t := 2 * (m / q)) (b := m / q) (ε := 0) (Nat.zero_le 1) (by ring)
        (wt (cls (G := ZMod q))) (prof (cls (G := ZMod q)) x)
        (prof (cls (G := ZMod q)) (rhoV q m))
        ((prof_sum _ x).trans (prof_sum _ _).symm) hρ
      have h1 := hcg.1
      rw [cost_eq_two_Nq, cost_eq_two_Nq] at h1
      rw [Nq_rho_eq]
      omega
    · have hρ : ∀ k : Cls (ZMod q), Al (2 * (m / q) + 1) (m / q) 1 (wt (cls (G := ZMod q)) k)
          (prof (cls (G := ZMod q)) (rhoV q m) k) := by
        intro k
        obtain ⟨g, rfl⟩ := cls_surj k
        rw [wt_cls, ← occ_ofFn, occ_rhoV]
        exact rho_Al_case2 m hv g
      have hcg := cost_ge (t := 2 * (m / q) + 1) (b := m / q) (ε := 1) le_rfl (by ring)
        (wt (cls (G := ZMod q))) (prof (cls (G := ZMod q)) x)
        (prof (cls (G := ZMod q)) (rhoV q m))
        ((prof_sum _ x).trans (prof_sum _ _).symm) hρ
      have h1 := hcg.1
      rw [cost_eq_two_Nq, cost_eq_two_Nq] at h1
      rw [Nq_rho_eq]
      omega
  have := key L.length L.get
  rwa [List.ofFn_get] at this

/-- **`N_rho_le`.**  For `d ≥ 1` and `ℓ` of length `m`: `N_d ρ ≤ N_d ℓ`. -/
theorem N_rho_le {d m : ℕ} (hd : 0 < d) (l : List ℤ) (hl : l.length = m) :
    N d (rhoZ m) ≤ N d l := by
  have : NeZero d := ⟨hd.ne'⟩
  have h := Nq_rho_le (q := d) (l.map (Int.castAddHom (ZMod d)))
  rw [List.length_map, hl, ← rhoZ_cast d m, Nq_cast, Nq_cast] at h
  exact h

end Bound

section Cyclo

variable {R : Type*} [CommRing R]

/-- `F`-type product as a signed product of cyclotomic polynomials with multiplicity `N_d`. -/
lemma Fl_cyclo (B : ℕ) (L : List ℤ) (hL : ∀ a ∈ L, 0 < a ∧ a.natAbs ≤ B) :
    Fl R L = (-1) ^ L.length *
      ∏ d ∈ Icc 1 B, (cyclotomic d R) ^ Ncount d L := by
  induction L with
  | nil => simp [Fl, Ncount]
  | cons a L ih =>
    have ih := ih fun b hb => hL b (List.mem_cons_of_mem _ hb)
    obtain ⟨ha, haB⟩ := hL a (List.mem_cons_self ..)
    have hapos : 0 < a.natAbs := Int.natAbs_pos.2 ha.ne'
    have hc : ∀ d : ℕ, Ncount d (a :: L) = Ncount d L + if d ∣ a.natAbs then 1 else 0 := by
      intro d
      simp only [Ncount, List.countP_cons, decide_eq_true_eq]
      congr 1
      simp [Int.natCast_dvd]
    have hdiv : ∏ d ∈ Icc 1 B, (cyclotomic d R) ^ (if d ∣ a.natAbs then 1 else 0) =
        X ^ a.natAbs - 1 := by
      rw [← prod_cyclotomic_eq_X_pow_sub_one hapos]
      have : ∏ d ∈ Icc 1 B, (cyclotomic d R) ^ (if d ∣ a.natAbs then 1 else 0) =
          ∏ d ∈ (Icc 1 B).filter (· ∣ a.natAbs), cyclotomic d R := by
        rw [Finset.prod_filter]
        refine Finset.prod_congr rfl fun d _ => ?_
        split_ifs <;> simp
      rw [this]
      congr 1
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨_, h⟩; exact ⟨h, hapos.ne'⟩
      · rintro ⟨h, _⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos h hapos, (Nat.le_of_dvd hapos h).trans haB⟩, h⟩
    rw [Fl_cons, ih, List.length_cons]
    have : ∏ d ∈ Icc 1 B, (cyclotomic d R) ^ Ncount d (a :: L) =
        (∏ d ∈ Icc 1 B, (cyclotomic d R) ^ (if d ∣ a.natAbs then 1 else 0)) *
          ∏ d ∈ Icc 1 B, (cyclotomic d R) ^ Ncount d L := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun d _ => ?_
      rw [hc, pow_add, mul_comm]
    rw [this, hdiv]
    ring

lemma exists_bound (L : List ℤ) : ∃ B : ℕ, ∀ a ∈ L, a.natAbs ≤ B := by
  induction L with
  | nil => exact ⟨0, by simp⟩
  | cons a L ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨max a.natAbs B, fun b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact le_max_left _ _
    · exact (hB b hb).trans (le_max_right _ _)

/-- **`dvd_rho`.**  With all pairs of `ℓ` positive (those of `ρ` always are) and `ℓ` of length `m`,
`F_ρ ∣ F_ℓ` over any commutative ring. -/
theorem dvd_rho_ring (R : Type*) [CommRing R] {m : ℕ} (l : List ℤ) (hl : l.length = m)
    (hpl : ∀ a ∈ pairs l, 0 < a) : ∃ Q : R[X], F R (rhoZ m) * Q = F R l := by
  obtain ⟨B1, h1⟩ := exists_bound (pairs l)
  obtain ⟨B2, h2⟩ := exists_bound (pairs (rhoZ m))
  set B := max B1 B2
  have e1 := Fl_cyclo (R := R) B (pairs l)
    (fun a ha => ⟨hpl a ha, (h1 a ha).trans (le_max_left _ _)⟩)
  have e2 := Fl_cyclo (R := R) B (pairs (rhoZ m))
    (fun a ha => ⟨rhoZ_pairs_pos m a ha, (h2 a ha).trans (le_max_right _ _)⟩)
  set n1 := (pairs l).length
  set n2 := (pairs (rhoZ m)).length
  let T : R[X] := ∏ d ∈ Icc 1 B, (cyclotomic d R) ^ (N d l - N d (rhoZ m))
  have hT : (∏ d ∈ Icc 1 B, (cyclotomic d R) ^ Ncount d (pairs (rhoZ m))) * T =
      ∏ d ∈ Icc 1 B, (cyclotomic d R) ^ Ncount d (pairs l) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun d hd => ?_
    have hd1 : 0 < d := (Finset.mem_Icc.1 hd).1
    have := N_rho_le hd1 l hl
    rw [← pow_add]
    congr 1
    show N d (rhoZ m) + (N d l - N d (rhoZ m)) = N d l
    omega
  refine ⟨(-1) ^ n1 * (-1) ^ n2 * T, ?_⟩
  have hsq : ((-1 : R[X]) ^ n2) * (-1) ^ n2 = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  unfold F
  rw [e1, e2]
  calc (-1 : R[X]) ^ n2 * (∏ d ∈ Icc 1 B, (cyclotomic d R) ^ Ncount d (pairs (rhoZ m))) *
        ((-1) ^ n1 * (-1) ^ n2 * T)
      = ((-1 : R[X]) ^ n2 * (-1) ^ n2) * (-1) ^ n1 *
        ((∏ d ∈ Icc 1 B, (cyclotomic d R) ^ Ncount d (pairs (rhoZ m))) * T) := by ring
    _ = _ := by rw [hsq, hT]; ring

end Cyclo

/-- **`dvd_rho`** in characteristic `0` (the field case of `dvd_rho_ring`). -/
theorem dvd_rho (K : Type*) [Field K] [CharZero K] {m : ℕ} (l : List ℤ) (hl : l.length = m)
    (hpl : ∀ a ∈ pairs l, 0 < a) : ∃ Q : K[X], F K (rhoZ m) * Q = F K l :=
  dvd_rho_ring K l hl hpl

section Corollaries

variable {K : Type*} [Field K] [CharZero K]

/-- **Theorem 3.1 (`thm:crit`) without `hQ`.** -/
theorem thm_crit' (q : ℕ) (hq : 0 < q) (ζ : K) (hζ : IsPrimitiveRoot ζ q) {m : ℕ} (l : List ℤ)
    (hl : l.length = m) (hpl : ∀ a ∈ pairs l, 0 < a) :
    ∃ Q : K[X], F K (rhoZ m) * Q = F K l ∧
      (N q (rhoZ m) ≤ N q l ∧ (Q.eval ζ ≠ 0 ↔ N q l = N q (rhoZ m))) := by
  obtain ⟨Q, hQ⟩ := dvd_rho K l hl hpl
  exact ⟨Q, hQ, thm_crit q hq ζ hζ l (rhoZ m) hpl (rhoZ_pairs_pos m) Q hQ⟩

/-- **Theorem 8.3 (`thm:valgen`) without `hQ`.** -/
theorem thm_valgen' {q m d : ℕ} (hq : 0 < q) (hd : d * q = 2 * m + 2) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ q) (l : List ℤ) (hl : l.length = m)
    (hpl : ∀ a ∈ pairs l, 0 < a) (hN : N q l = N q (rhoZ m)) :
    ∃ Q : ℂ[X], F ℂ (rhoZ m) * Q = F ℂ l ∧
      ‖Q.eval ζ‖ = (((pairs l).filter fun a => (q : ℤ) ∣ a).map fun a : ℤ => (a : ℝ)).prod /
        (((pairs (rhoZ m)).filter fun b => (q : ℤ) ∣ b).map fun b : ℤ => (b : ℝ)).prod := by
  obtain ⟨Q, hQ⟩ := dvd_rho ℂ l hl hpl
  exact ⟨Q, hQ, thm_valgen hq hd hζ l hl hpl hN Q hQ⟩

/-- **Theorem 7.1 (`thm:signo`) without `hQ`.** -/
theorem thm_signo' {q m d p : ℕ} (hq : 0 < q) (hd : d * q = 2 * m + 2) (hpq : p.Coprime q)
    {ζ : ℂ} (hζ : ζ = Complex.exp (2 * Real.pi * Complex.I * ((p : ℂ) / q)))
    (l : List ℤ) (hl : l.length = m) (hpl : ∀ a ∈ pairs l, 0 < a)
    (hN : N q l = N q (rhoZ m)) :
    ∃ Q : ℂ[X], F ℂ (rhoZ m) * Q = F ℂ l ∧
      ζ ^ (-(List.zipWith (fun a b => (a - b) * b) l (rhoZ m)).sum) * Q.eval ζ =
        (-1 : ℂ) ^ (((pairs l).map fun a => (p : ℤ) * a / q).sum -
            ((pairs (rhoZ m)).map fun a => (p : ℤ) * a / q).sum) *
          ((((pairs l).filter fun a => (q : ℤ) ∣ a).map fun a : ℤ => (a : ℂ)).prod /
            (((pairs (rhoZ m)).filter fun b => (q : ℤ) ∣ b).map fun b : ℤ => (b : ℂ)).prod) := by
  obtain ⟨Q, hQ⟩ := dvd_rho ℂ l hl hpl
  exact ⟨Q, hQ, thm_signo hq hd hpq hζ l hl hpl hN Q hQ⟩

end Corollaries

end RhoLine
