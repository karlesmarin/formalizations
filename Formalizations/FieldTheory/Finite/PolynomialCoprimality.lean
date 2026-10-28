/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.GCDMonoid.Finset

/-!
# The polynomial coprimality theorem over finite fields

Over a finite field with `q` elements, the number of `m`-tuples of monic polynomials of degrees
`n₁, …, n_m ≥ 1` with no non-unit common divisor is `q^N − q^(N − m + 1)`, `N = Σ nᵢ`; with equal
degrees, the proportion of tuples with a non-trivial common factor is `1/q^(m−1)` (Theorem of the
Day). Proof: every tuple factors uniquely as `d · (g₁, …, g_m)` with `d` the monic gcd and the `gᵢ`
coprime, so `q^N = Σ_k q^k · C(n − k)`, and strong induction on `min nᵢ` solves for `C`.

## Main results

* `PolynomialCoprimality.card_monic_natDegree`: there are q^n monic polynomials of degree n
* `PolynomialCoprimality.card_coprime_tuples`: coprime m-tuples of monic polynomials of degrees nᵢ ≥ 1: q^N − q^(N−m+1)
* `PolynomialCoprimality.card_not_coprime_equal_degree`: equal degrees: q^(mn − m + 1) tuples share a non-trivial factor (proportion 1/q^(m−1))

## References

* R. Whitty, Theorem of the Day, «The Polynomial Coprimality Theorem» (CombinatorialTheory/Coprimality).
* S. Corteel, C. D. Savage, H. S. Wilf, D. Zeilberger, A pentagonal number sieve, J. Combin. Theory Ser. A 82 (1998).
* A. T. Benjamin, C. D. Bennett, The probability of relatively prime polynomials, Math. Mag. 80 (2007).
-/

@[expose] public section

open Polynomial

namespace PolynomialCoprimality

variable (K : Type*) [Field K]

/-- Monic polynomials of natural degree `n`. -/
abbrev MonicDeg (n : ℕ) := {f : K[X] // f.Monic ∧ f.natDegree = n}

noncomputable def monicEquiv (n : ℕ) : MonicDeg K n ≃ degreeLT K n where
  toFun f := ⟨f.1 - X ^ n, by
    rw [mem_degreeLT]
    have h1 : f.1.degree = (n : WithBot ℕ) := by rw [degree_eq_natDegree f.2.1.ne_zero, f.2.2]
    have h2 : (X ^ n : K[X]).degree = n := degree_X_pow n
    have := degree_sub_lt_left (p := f.1) (q := X ^ n) (h1.trans h2.symm) f.2.1.ne_zero
      (by rw [f.2.1.leadingCoeff, leadingCoeff_X_pow])
    rwa [h1] at this⟩
  invFun g := ⟨X ^ n + g.1, monic_X_pow_add (mem_degreeLT.1 g.2), by
    rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
    rw [degree_X_pow]; exact mem_degreeLT.1 g.2⟩
  left_inv f := Subtype.ext (by simp)
  right_inv g := Subtype.ext (by simp)

theorem card_monic_natDegree [Fintype K] (n : ℕ) :
    Nat.card {f : K[X] // f.Monic ∧ f.natDegree = n} = Fintype.card K ^ n := by
  rw [Nat.card_congr ((monicEquiv K n).trans (degreeLTEquiv K n).toEquiv)]
  simp

instance finMonicDeg [Finite K] (n : ℕ) : Finite (MonicDeg K n) :=
  Finite.of_equiv _ ((monicEquiv K n).trans (degreeLTEquiv K n).toEquiv).symm

/-- Tuples of monic polynomials with prescribed degrees. -/
abbrev TupDeg (m : ℕ) (n : Fin m → ℕ) :=
  {t : Fin m → K[X] // ∀ i, (t i).Monic ∧ (t i).natDegree = n i}

/-- Such tuples with no non-unit common divisor. -/
abbrev CopDeg (m : ℕ) (n : Fin m → ℕ) :=
  {t : Fin m → K[X] // (∀ i, (t i).Monic ∧ (t i).natDegree = n i) ∧
    ∀ d : K[X], (∀ i, d ∣ t i) → IsUnit d}

variable {K}

noncomputable def tupEquiv {m : ℕ} (n : Fin m → ℕ) : TupDeg K m n ≃ ∀ i, MonicDeg K (n i) :=
  Equiv.subtypePiEquivPi (p := fun i (f : K[X]) => f.Monic ∧ f.natDegree = n i)

instance finTup [Finite K] {m : ℕ} (n : Fin m → ℕ) : Finite (TupDeg K m n) :=
  Finite.of_equiv _ (tupEquiv n).symm

instance finCop [Finite K] {m : ℕ} (n : Fin m → ℕ) : Finite (CopDeg K m n) :=
  Finite.of_injective (fun t : CopDeg K m n => (⟨t.1, t.2.1⟩ : TupDeg K m n))
    (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))

theorem card_tup [Fintype K] {m : ℕ} (n : Fin m → ℕ) :
    Nat.card (TupDeg K m n) = Fintype.card K ^ (∑ i, n i) := by
  rw [Nat.card_congr (tupEquiv n), Nat.card_pi]
  simp [card_monic_natDegree, Finset.prod_pow_eq_pow_sum]

/-- A normalized gcd on `K[X]`, local to this file (Mathlib has no global instance for a bare field). -/
noncomputable local instance instNGCD [DecidableEq K] : NormalizedGCDMonoid K[X] :=
  UniqueFactorizationMonoid.toNormalizedGCDMonoid _

theorem gcd_mul_cop [DecidableEq K] {m : ℕ} (d : K[X]) (hd : d.Monic) (g : Fin m → K[X])
    (hg : ∀ c : K[X], (∀ i, c ∣ g i) → IsUnit c) :
    Finset.univ.gcd (fun i => d * g i) = d := by
  have h1 : Finset.univ.gcd g = 1 := by
    rw [← Finset.normalize_gcd, normalize_eq_one]
    exact hg _ (fun i => Finset.gcd_dvd (Finset.mem_univ i))
  have h2 := Finset.gcd_mul_left' Finset.univ g d
  rw [h1, mul_one] at h2
  calc _ = normalize (Finset.univ.gcd fun i => d * g i) := (Finset.normalize_gcd ..).symm
    _ = normalize d := normalize_eq_normalize h2.dvd h2.symm.dvd
    _ = d := hd.normalize_eq_self

theorem exists_decomp [DecidableEq K] {m : ℕ} (hm : 0 < m) (t : Fin m → K[X]) (ht : ∀ i, (t i).Monic) :
    ∃ (d : K[X]) (s : Fin m → K[X]), d.Monic ∧ (∀ i, (s i).Monic) ∧ (∀ i, t i = d * s i) ∧
      ∀ c : K[X], (∀ i, c ∣ s i) → IsUnit c := by
  obtain ⟨s, hs, hg⟩ := Finset.extract_gcd t (Finset.univ_nonempty_iff.2 ⟨⟨0, hm⟩⟩)
  obtain ⟨d, hd⟩ : ∃ d, d = Finset.univ.gcd t := ⟨_, rfl⟩
  rw [← hd] at hs
  have hd0 : d ≠ 0 := by
    intro h0
    have := hs ⟨0, hm⟩ (Finset.mem_univ _)
    rw [h0, zero_mul] at this
    exact (ht _).ne_zero this
  have hdm : d.Monic := by
    have := monic_normalize hd0
    rwa [hd, Finset.normalize_gcd, ← hd] at this
  refine ⟨d, s, hdm, fun i => hdm.of_mul_monic_left (by rw [← hs i (Finset.mem_univ i)]; exact ht i),
    fun i => hs i (Finset.mem_univ i), fun c hc => ?_⟩
  have := Finset.dvd_gcd (s := Finset.univ) (f := s) (fun i _ => hc i)
  rw [hg] at this
  exact isUnit_of_dvd_one this

/-- Decomposition data: a monic `d` of degree `k ≤ L` and a coprime tuple of degrees `nᵢ - k`. -/
abbrev Dec (K : Type*) [Field K] (m : ℕ) (n : Fin m → ℕ) (L : ℕ) :=
  Σ k : Fin (L + 1), MonicDeg K k × CopDeg K m (fun i => n i - k)

theorem decMap_prop {m : ℕ} (n : Fin m → ℕ) (L : ℕ) (hL : ∀ i, L ≤ n i) (x : Dec K m n L) (i : Fin m) :
    (x.2.1.1 * x.2.2.1 i).Monic ∧ (x.2.1.1 * x.2.2.1 i).natDegree = n i := by
  obtain ⟨k, ⟨d, hd, hdk⟩, ⟨g, hg, -⟩⟩ := x
  have hk : (k : ℕ) ≤ n i := le_trans (Nat.lt_succ_iff.1 k.2) (hL i)
  show (d * g i).Monic ∧ (d * g i).natDegree = n i
  refine ⟨hd.mul (hg i).1, ?_⟩
  rw [hd.natDegree_mul (hg i).1, hdk, (hg i).2]
  show (k : ℕ) + (n i - k) = n i
  omega

/-- The multiplication map `(d, g) ↦ d • g`. -/
noncomputable def decMap {m : ℕ} (n : Fin m → ℕ) (L : ℕ) (hL : ∀ i, L ≤ n i) :
    Dec K m n L → TupDeg K m n :=
  fun x => ⟨fun i => x.2.1.1 * x.2.2.1 i, decMap_prop n L hL x⟩

theorem decMap_bijective [DecidableEq K] {m : ℕ} (hm : 0 < m) (n : Fin m → ℕ) (L : ℕ)
    (hL : ∀ i, L ≤ n i) (hL' : ∃ i, n i = L) : Function.Bijective (decMap (K := K) n L hL) := by
  constructor
  · intro x y h
    obtain ⟨k, ⟨d, hd, hdk⟩, ⟨g, hg, hgc⟩⟩ := x
    obtain ⟨k', ⟨d', hd', hdk'⟩, ⟨g', hg', hgc'⟩⟩ := y
    have h' : ∀ i, d * g i = d' * g' i := fun i => congrFun (congrArg Subtype.val h) i
    have hfun : (fun i => d * g i) = fun i => d' * g' i := funext h'
    have e1 : d = d' :=
      calc d = Finset.univ.gcd (fun i => d * g i) := (gcd_mul_cop d hd g hgc).symm
        _ = Finset.univ.gcd (fun i => d' * g' i) := by rw [hfun]
        _ = d' := gcd_mul_cop d' hd' g' hgc'
    subst e1
    have hk : k = k' := Fin.ext (hdk.symm.trans hdk')
    subst hk
    have hgg : g = g' := funext fun i => mul_left_cancel₀ hd.ne_zero (h' i)
    subst hgg
    rfl
  · intro t
    obtain ⟨d, s, hd, hs, hts, hcop⟩ := exists_decomp hm t.1 (fun i => (t.2 i).1)
    have hdn : ∀ i, d.natDegree + (s i).natDegree = n i := fun i => by
      rw [← hd.natDegree_mul (hs i), ← hts i]; exact (t.2 i).2
    obtain ⟨i0, hi0⟩ := hL'
    have hdL : d.natDegree ≤ L := by have := hdn i0; omega
    refine ⟨⟨⟨d.natDegree, Nat.lt_succ_of_le hdL⟩, ⟨d, hd, rfl⟩,
      ⟨s, fun i => ⟨hs i, ?_⟩, hcop⟩⟩, ?_⟩
    · show (s i).natDegree = n i - d.natDegree
      have := hdn i; omega
    · apply Subtype.ext; funext i; exact (hts i).symm

/-- `q ^ N = ∑_{k ≤ L} q ^ k * C(n - k)`. -/
theorem card_decomp [Fintype K] [DecidableEq K] {m : ℕ} (hm : 0 < m) (n : Fin m → ℕ) (L : ℕ)
    (hL : ∀ i, L ≤ n i) (hL' : ∃ i, n i = L) :
    Fintype.card K ^ (∑ i, n i) = ∑ k ∈ Finset.range (L + 1),
      Fintype.card K ^ k * Nat.card (CopDeg K m (fun i => n i - k)) := by
  rw [← card_tup n, ← Nat.card_congr (Equiv.ofBijective _ (decMap_bijective hm n L hL hL')),
    Nat.card_sigma, ← Fin.sum_univ_eq_sum_range
      (fun k => Fintype.card K ^ k * Nat.card (CopDeg K m (fun i => n i - k))) (L + 1)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Nat.card_prod, card_monic_natDegree]

/-- Pure telescoping step. -/
theorem telescope (f a : ℕ → ℕ) (L : ℕ) (hL : 1 ≤ L)
    (h1 : ∀ j, 1 ≤ j → j < L → f j + a (j + 1) = a j) (h2 : f L = a L) :
    ∑ k ∈ Finset.range L, f (k + 1) = a 1 := by
  have key : ∀ t, t < L → ∑ k ∈ Finset.range t, f (k + 1) + a (t + 1) = a 1 := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
      intro ht
      have := ih (by omega)
      have h := h1 (t + 1) (by omega) ht
      rw [Finset.sum_range_succ]
      omega
  obtain ⟨t, rfl⟩ : ∃ t, L = t + 1 := ⟨L - 1, by omega⟩
  rw [Finset.sum_range_succ, h2]
  exact key t (by omega)

theorem count_ind [Fintype K] [DecidableEq K] {m : ℕ} (hm : 0 < m) :
    ∀ N : ℕ, ∀ n : Fin m → ℕ, ∑ i, n i = N →
      ((∃ i, n i = 0) → Nat.card (CopDeg K m n) = Fintype.card K ^ N) ∧
      ((∀ i, 1 ≤ n i) →
        Nat.card (CopDeg K m n) + Fintype.card K ^ (N - m + 1) = Fintype.card K ^ N) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro n hN
  constructor
  · rintro ⟨i0, hi0⟩
    have := card_decomp (K := K) hm n 0 (fun i => Nat.zero_le _) ⟨i0, hi0⟩
    simpa [hN] using this.symm
  · intro hpos
    obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ n
      ⟨⟨0, hm⟩, Finset.mem_univ _⟩
    have hL : ∀ i, n i0 ≤ n i := fun i => hi0 i (Finset.mem_univ i)
    have hL1 : 1 ≤ n i0 := hpos i0
    have hdec := card_decomp (K := K) hm n (n i0) hL ⟨i0, rfl⟩
    rw [hN, Finset.sum_range_succ'] at hdec
    simp only [Nat.sub_zero, pow_zero, one_mul] at hdec
    have hmN : m ≤ N := by
      have := Finset.sum_le_sum (s := Finset.univ) (f := fun _ : Fin m => 1) (g := n)
        (fun i _ => hpos i)
      simp at this; omega
    have hsum : ∑ k ∈ Finset.range (n i0), Fintype.card K ^ (k + 1) *
        Nat.card (CopDeg K m (fun i => n i - (k + 1))) = Fintype.card K ^ (N - m + 1) := by
      have hmain := telescope
        (fun j => Fintype.card K ^ j * Nat.card (CopDeg K m (fun i => n i - j)))
        (fun j => Fintype.card K ^ (N + j - m * j)) (n i0) hL1 ?_ ?_
      · have e : N + 1 - m * 1 = N - m + 1 := by omega
        simp only [e] at hmain
        exact hmain
      · intro j hj1 hjL
        have hj : ∀ i, j ≤ n i := fun i => by have := hL i; omega
        have hs : ∑ i, (n i - j) = N - m * j := by
          rw [Finset.sum_tsub_distrib _ (fun i _ => hj i), hN]; simp
        have hmj : m * j ≤ N := by
          have := Finset.sum_le_sum (s := Finset.univ) (f := fun _ : Fin m => j) (g := n)
            (fun i _ => hj i)
          simp at this; omega
        have hge : m ≤ N - m * j := by
          have := Finset.sum_le_sum (s := Finset.univ) (f := fun _ : Fin m => 1)
            (g := fun i => n i - j) (fun i _ => by have := hL i; omega)
          simp at this; omega
        have hpos' : 0 < m * j := Nat.mul_pos hm hj1
        have := (ih (N - m * j) (by omega) (fun i => n i - j) hs).2
          (fun i => by have := hL i; omega)
        have h3 := congrArg (fun x => Fintype.card K ^ j * x) this
        simp only [mul_add, ← pow_add] at h3
        have e1 : j + (N - m * j - m + 1) = N + (j + 1) - m * (j + 1) := by
          rw [Nat.mul_succ]; omega
        have e2 : j + (N - m * j) = N + j - m * j := by omega
        rw [e1, e2] at h3
        exact h3
      · have hj : ∀ i, n i0 ≤ n i := hL
        have hs : ∑ i, (n i - n i0) = N - m * n i0 := by
          rw [Finset.sum_tsub_distrib _ (fun i _ => hj i), hN]; simp
        have hmj : m * n i0 ≤ N := by
          have := Finset.sum_le_sum (s := Finset.univ) (f := fun _ : Fin m => n i0) (g := n)
            (fun i _ => hj i)
          simp at this; omega
        have hpos' : 0 < m * n i0 := Nat.mul_pos hm hL1
        have := (ih (N - m * n i0) (by omega) (fun i => n i - n i0) hs).1
          ⟨i0, by simp⟩
        show Fintype.card K ^ n i0 * Nat.card (CopDeg K m (fun i => n i - n i0)) =
          Fintype.card K ^ (N + n i0 - m * n i0)
        rw [this, ← pow_add]
        congr 1; omega
    rw [hsum] at hdec
    have e : Nat.card (CopDeg K m fun i => n i) = Nat.card (CopDeg K m n) := rfl
    rw [e] at hdec
    omega

/-- **The polynomial coprimality theorem** (general degrees). -/
theorem card_coprime_tuples (K : Type*) [Field K] [Fintype K] (m : ℕ) (hm : 1 ≤ m) (n : Fin m → ℕ)
    (hn : ∀ i, 1 ≤ n i) :
    Nat.card {t : Fin m → K[X] // (∀ i, (t i).Monic ∧ (t i).natDegree = n i) ∧
        ∀ d : K[X], (∀ i, d ∣ t i) → IsUnit d} =
      Fintype.card K ^ (∑ i, n i) - Fintype.card K ^ (∑ i, n i - m + 1) := by
  classical
  have h := (count_ind (K := K) hm (∑ i, n i) n rfl).2 hn
  show Nat.card (CopDeg K m n) = _
  omega

/-- Equal degrees: `q ^ (m * n - m + 1)` tuples of monic polynomials of degree `n` share a
non-trivial common factor. -/
theorem card_not_coprime_equal_degree (K : Type*) [Field K] [Fintype K] (m : ℕ) (hm : 1 ≤ m)
    (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {t : Fin m → K[X] // (∀ i, (t i).Monic ∧ (t i).natDegree = n) ∧
        ∃ d : K[X], (∀ i, d ∣ t i) ∧ ¬ IsUnit d} =
      Fintype.card K ^ (m * n - m + 1) := by
  classical
  have hsum : ∑ _i : Fin m, n = m * n := by simp
  have h := (count_ind (K := K) hm (∑ _i : Fin m, n) (fun _ => n) rfl).2 (fun _ => hn)
  rw [hsum] at h
  have hcop : Nat.card (CopDeg K m (fun _ => n)) =
      Nat.card {x : TupDeg K m (fun _ => n) // ∀ d : K[X], (∀ i, d ∣ x.1 i) → IsUnit d} :=
    Nat.card_congr
      { toFun := fun t => ⟨⟨t.1, t.2.1⟩, t.2.2⟩
        invFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have e1 : {t : Fin m → K[X] // (∀ i, (t i).Monic ∧ (t i).natDegree = n) ∧
        ∃ d : K[X], (∀ i, d ∣ t i) ∧ ¬ IsUnit d} ≃
      {x : TupDeg K m (fun _ => n) // ¬ ∀ d : K[X], (∀ i, d ∣ x.1 i) → IsUnit d} :=
    { toFun := fun t => ⟨⟨t.1, t.2.1⟩, by
        obtain ⟨d, hd1, hd2⟩ := t.2.2
        exact fun hc => hd2 (hc d hd1)⟩
      invFun := fun x => ⟨x.1.1, x.1.2, by
        have := x.2
        push Not at this
        obtain ⟨d, hd1, hd2⟩ := this
        exact ⟨d, hd1, hd2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let _ : Fintype (TupDeg K m (fun _ => n)) := Fintype.ofFinite _
  rw [Nat.card_congr e1, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← hcop, card_tup]
  simp only [hsum]
  omega


end PolynomialCoprimality
