/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Zify
public import Mathlib.Tactic.Linarith

/-!
# The rank profile of a Mahler matrix modulo `p`: the arithmetic

For an odd prime `p`, row `J > 0` of the Mahler matrix of a measure depends on the rows above it
exactly when `u < p r_b`, where `J + 1 = p^s u` with `p ∤ u`, `b ≡ J (mod p − 1)`, and `r_b` is
the `λ`-invariant of the `ω^b`-branch. This file formalizes the arithmetic of that criterion and
of its consequences. The criterion itself enters as the explicit hypothesis `ThmA p r Dep`, and
the comparison with the graded layers as the explicit hypothesis `hB`; neither is proved here.

## Main results

* `FilasIII.crit_iff_seed`, `FilasIII.seed_injective`, `FilasIII.thmA_seeds`: the seed form of
  the criterion, rows `Φ^s(d_b(i))` for `i < r_b`, pairwise distinct.
* `FilasIII.cor_low`, `FilasIII.cor_phi`, `FilasIII.cor_phi_top`, `FilasIII.Jk_Phi`,
  `FilasIII.kstar_count`, `FilasIII.cor_rank`: the corollaries on low rows, the map `Φ`, the
  indices `k*` and the rank.
* `FilasIII.cor_C`, `FilasIII.cor_D`, `FilasIII.jD_zero_strictMono`, `FilasIII.jD_zero_range`,
  `FilasIII.cor_D_first`: the arithmetic of the two corollaries on graded layers, given both
  hypotheses.

## References

* C. Marín, *Reading Iwasawa λ-invariants from Mahler matrices modulo p: programs, data and Lean
  files*, Zenodo (2026), doi:10.5281/zenodo.23085315.
-/

@[expose] public section

open Finset

namespace FilasIII

/-! ## Objects -/

/-- `Φ(J) = p(J+1) - 1`. -/
def Phi (p J : ℕ) : ℕ := p * (J + 1) - 1

/-- `[b-i]_{p-1}`: least nonnegative residue of `b - i` modulo `p - 1`. -/
def brk (p b i : ℕ) : ℕ := (((b : ℤ) - i) % ((p : ℤ) - 1)).toNat

/-- `d_b(i) = p i + [b-i]_{p-1}`. -/
def dseed (p b i : ℕ) : ℕ := p * i + brk p b i

/-- `u(J)`: the prime-to-`p` part of `J + 1`. -/
def uPart (p J : ℕ) : ℕ := ordCompl[p] (J + 1)

/-- The criterion of Theorem A: `u < p r_b`, `b ≡ J (mod p-1)`, `b ∈ [0,p-2]`. -/
def Crit (p : ℕ) (r : ℕ → ℕ∞) (J : ℕ) : Prop := (uPart p J : ℕ∞) < p * r (J % (p - 1))

/-- Theorem A (measure part), taken as a hypothesis: for `0 < J < p^a`, row `J` at resolution
`p^a` is dependent iff `u < p r_b`. `Dep a J` = "row `J` of `B` at level `p^a` is dependent". -/
def ThmA (p : ℕ) (r : ℕ → ℕ∞) (Dep : ℕ → ℕ → Prop) : Prop :=
  ∀ a J, 0 < J → J < p ^ a → (Dep a J ↔ Crit p r J)

/-! ## Basic arithmetic -/

lemma Phi_add_one {p : ℕ} (hp : 0 < p) (J : ℕ) : Phi p J + 1 = p * (J + 1) := by
  unfold Phi
  have : 1 ≤ p * (J + 1) := Nat.mul_pos hp (Nat.succ_pos J)
  omega

lemma Phi_iter_add_one {p : ℕ} (hp : 0 < p) (s d : ℕ) :
    (Phi p)^[s] d + 1 = p ^ s * (d + 1) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Function.iterate_succ_apply', Phi_add_one hp, ih]
    ring

lemma Phi_iter {p : ℕ} (hp : 0 < p) (s d : ℕ) : (Phi p)^[s] d = p ^ s * (d + 1) - 1 := by
  have := Phi_iter_add_one hp s d
  omega

/-- Uniqueness of the decomposition `n = p^s u`, `p ∤ u`. -/
lemma factor_unique {p : ℕ} (hp : p.Prime) {s u : ℕ} (hu : ¬ p ∣ u) :
    (p ^ s * u).factorization p = s ∧ ordCompl[p] (p ^ s * u) = u := by
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (dvd_zero p)
  refine ⟨?_, Nat.ordCompl_pow_mul_of_not_dvd s hp hu⟩
  rw [Nat.factorization_mul (pow_ne_zero s hp.ne_zero) hu0, Finsupp.add_apply,
    hp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hu]
  simp

lemma not_dvd_mul_add {p i e : ℕ} (he0 : 0 < e) (he : e < p) : ¬ p ∣ p * i + e := by
  intro h
  have : p ∣ e := (Nat.dvd_add_right (dvd_mul_right p i)).mp h
  exact absurd (Nat.le_of_dvd he0 this) (by omega)

lemma brk_cast {p : ℕ} (hp : 2 ≤ p) (b i : ℕ) :
    (brk p b i : ℤ) = ((b : ℤ) - i) % ((p : ℤ) - 1) := by
  unfold brk
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))

lemma brk_lt {p : ℕ} (hp : 2 ≤ p) (b i : ℕ) : brk p b i < p - 1 := by
  have h := brk_cast hp b i
  have : ((b : ℤ) - i) % ((p : ℤ) - 1) < (p : ℤ) - 1 := Int.emod_lt_of_pos _ (by omega)
  omega

/-- `[b-i]_{p-1}` is the unique `δ ∈ [0,p-2]` with `δ ≡ b - i (mod p-1)`. -/
lemma brk_eq_of {p b i δ : ℕ} (hp : 2 ≤ p) (hδ : δ < p - 1)
    (h : ((p : ℤ) - 1) ∣ (δ : ℤ) - ((b : ℤ) - i)) : brk p b i = δ := by
  have h1 : ((b : ℤ) - i) % ((p : ℤ) - 1) = (δ : ℤ) % ((p : ℤ) - 1) :=
    (Int.modEq_iff_dvd.mpr h)
  have h2 : (δ : ℤ) % ((p : ℤ) - 1) = δ := Int.emod_eq_of_lt (by omega) (by omega)
  have := brk_cast hp b i
  omega

lemma brk_dvd {p : ℕ} (hp : 2 ≤ p) (b i : ℕ) :
    ((p : ℤ) - 1) ∣ (brk p b i : ℤ) - ((b : ℤ) - i) := by
  rw [brk_cast hp, Int.emod_def]
  exact ⟨-(((b : ℤ) - i) / ((p : ℤ) - 1)), by ring⟩

/-- `p i + e < p r ↔ i < r` in `ℕ∞` for `e < p`. -/
lemma key_lt {p i e : ℕ} (hp : 0 < p) (he : e < p) (r : ℕ∞) :
    ((p * i + e : ℕ) : ℕ∞) < p * r ↔ (i : ℕ∞) < r := by
  induction r using ENat.recTopCoe with
  | top =>
    simp only [ENat.natCast_lt_top, iff_true]
    rw [ENat.mul_top (by exact_mod_cast hp.ne')]
    exact ENat.natCast_lt_top _
  | coe n =>
    rw [← Nat.cast_mul, Nat.cast_lt, Nat.cast_lt]
    constructor
    · intro h
      by_contra hc
      have : p * n ≤ p * i := Nat.mul_le_mul_left p (by omega)
      omega
    · intro h
      have : p * (i + 1) ≤ p * n := Nat.mul_le_mul_left p h
      rw [mul_add] at this
      omega

lemma dseed_succ_not_dvd {p : ℕ} (hp : 2 ≤ p) (b i : ℕ) : ¬ p ∣ dseed p b i + 1 := by
  unfold dseed
  have := brk_lt hp b i
  rw [add_assoc]
  exact not_dvd_mul_add (by omega) (by omega)

lemma dseed_div {p : ℕ} (hp : 2 ≤ p) (b i : ℕ) : (dseed p b i + 1) / p = i := by
  unfold dseed
  have := brk_lt hp b i
  rw [add_assoc, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), add_zero]

/-- `Φ^s(d_b(i)) + 1 = p^s (d_b(i)+1)`, so `v_p = s` and `u = d_b(i)+1`. -/
lemma seed_decomp {p : ℕ} (hp : p.Prime) (b s i : ℕ) :
    ((Phi p)^[s] (dseed p b i) + 1).factorization p = s ∧
      uPart p ((Phi p)^[s] (dseed p b i)) = dseed p b i + 1 := by
  unfold uPart
  rw [Phi_iter_add_one hp.pos]
  exact factor_unique hp (dseed_succ_not_dvd hp.two_le b i)

/-- `Φ^s(d_b(i)) ≡ b (mod p-1)`. -/
lemma seed_mod {p : ℕ} (hp : 2 ≤ p) {b : ℕ} (hb : b < p - 1) (s i : ℕ) :
    (Phi p)^[s] (dseed p b i) % (p - 1) = b := by
  have hcast : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ p)]; ring
  have hX := Phi_iter_add_one (by omega : 0 < p) s (dseed p b i)
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (p : ℤ) 1 s
  obtain ⟨e, he⟩ := brk_dvd hp b i
  have hX' : (((Phi p)^[s] (dseed p b i) : ℕ) : ℤ) + 1 = (p : ℤ) ^ s * ((dseed p b i : ℤ) + 1) := by
    exact_mod_cast hX
  have hd : (dseed p b i : ℤ) = p * i + brk p b i := by unfold dseed; push_cast; ring
  have hdvd : ((p - 1 : ℕ) : ℤ) ∣ (((Phi p)^[s] (dseed p b i) : ℕ) : ℤ) - b := by
    rw [hcast]
    refine ⟨c * ((dseed p b i : ℤ) + 1) + i + e, ?_⟩
    simp only [one_pow] at hc
    linear_combination hX' + hc * ((dseed p b i : ℤ) + 1) + hd + he
  have := (Nat.modEq_iff_dvd.mpr hdvd)
  unfold Nat.ModEq at this
  rw [Nat.mod_eq_of_lt hb] at this
  exact this.symm

/-- Every `J` is `Φ^s(d_b(i))` with `s = v_p(J+1)`, `b = J mod (p-1)`, `i = ⌊u/p⌋`, and
`u = d_b(i) + 1`. -/
lemma decomp {p : ℕ} (hp : p.Prime) (J : ℕ) :
    uPart p J = dseed p (J % (p - 1)) (uPart p J / p) + 1 ∧
      J = (Phi p)^[(J + 1).factorization p] (dseed p (J % (p - 1)) (uPart p J / p)) := by
  have hp2 := hp.two_le
  set s := (J + 1).factorization p with hs
  set u := uPart p J with hu
  set b := J % (p - 1) with hb
  set i := u / p with hi
  have hJu : p ^ s * u = J + 1 := Nat.ordProj_mul_ordCompl_eq_self (J + 1) p
  have hu0 : 0 < u := Nat.ordCompl_pos p (by omega)
  have hnd : ¬ p ∣ u := Nat.not_dvd_ordCompl hp (by omega)
  set δ := u % p - 1 with hδ
  have hmod : u % p ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
  have hmodlt : u % p < p := Nat.mod_lt _ hp.pos
  have hudec : u = p * i + δ + 1 := by
    have := Nat.div_add_mod u p
    rw [← hi] at this
    omega
  have hδlt : δ < p - 1 := by omega
  -- δ ≡ b - i
  have hbrk : brk p b i = δ := by
    apply brk_eq_of hp2 hδlt
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (p : ℤ) 1 s
    have hJb : ((p - 1 : ℕ) : ℤ) ∣ (J : ℤ) - b := by
      have : b ≡ J [MOD p - 1] := Nat.mod_modEq J (p - 1)
      exact Nat.modEq_iff_dvd.mp this
    have hcast : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ p)]; ring
    rw [hcast] at hJb
    obtain ⟨q, hq⟩ := hJb
    have hJu' : (p : ℤ) ^ s * u = J + 1 := by exact_mod_cast hJu
    have hud' : (u : ℤ) = p * i + δ + 1 := by exact_mod_cast hudec
    simp only [one_pow] at hc
    exact ⟨q - c * u - i, by linear_combination hq - hc * (u : ℤ) + hJu' - hud'⟩
  have hdseed : dseed p b i + 1 = u := by unfold dseed; rw [hbrk]; omega
  refine ⟨hdseed.symm, ?_⟩
  have := Phi_iter_add_one hp.pos s (dseed p b i)
  rw [hdseed, hJu] at this
  omega

/-! ## Theorem A: the seed form and distinctness -/

/-- Arithmetic core of Theorem A: for `J ≡ b (mod p-1)`, `b ∈ [0,p-2]`,
`u(J) < p r ↔ J = Φ^s(d_b(i))` for some `s ≥ 0` and `i < r`. (Valid for every `J`, including
`J = 0`, which is `Φ^0(d_0(0))`.) -/
theorem crit_iff_seed {p : ℕ} (hp : p.Prime) {b J : ℕ}
    (hJb : J % (p - 1) = b) (r : ℕ∞) :
    (uPart p J : ℕ∞) < p * r ↔ ∃ s i : ℕ, (i : ℕ∞) < r ∧ J = (Phi p)^[s] (dseed p b i) := by
  have hp2 := hp.two_le
  constructor
  · intro h
    obtain ⟨hu, hJ⟩ := decomp hp J
    refine ⟨(J + 1).factorization p, uPart p J / p, ?_, by rw [← hJb]; exact hJ⟩
    rw [hu, hJb] at h
    unfold dseed at h
    have := brk_lt hp2 b (uPart p J / p)
    rw [add_assoc] at h
    exact (key_lt hp.pos (by omega) r).mp h
  · rintro ⟨s, i, hi, rfl⟩
    rw [(seed_decomp hp b s i).2]
    unfold dseed
    have := brk_lt hp2 b i
    rw [add_assoc]
    exact (key_lt hp.pos (by omega) r).mpr hi

/-- Distinctness in Theorem A: `(s,i) ↦ Φ^s(d_b(i))` is injective. -/
theorem seed_injective {p : ℕ} (hp : p.Prime) (b : ℕ) :
    Function.Injective (fun x : ℕ × ℕ => (Phi p)^[x.1] (dseed p b x.2)) := by
  rintro ⟨s, i⟩ ⟨s', i'⟩ h
  simp only at h
  have h1 := seed_decomp hp b s i
  have h2 := seed_decomp hp b s' i'
  rw [h] at h1
  have hs : s = s' := h1.1.symm.trans h2.1
  have hd : dseed p b i + 1 = dseed p b i' + 1 := h1.2.symm.trans h2.2
  have hi : i = i' := by
    rw [← dseed_div hp.two_le b i, ← dseed_div hp.two_le b i', hd]
  rw [hs, hi]

/-- **Theorem A, seed form** (thm:A, "Equivalently"), with the criterion `u < p r_b` as
hypothesis `hA`: the positive rows `J < p^a`, `J ≡ b (mod p-1)`, that are dependent are exactly
the `Φ^s(d_b(i))` with `0 < Φ^s(d_b(i)) < p^a`, `s ≥ 0`, `i < r_b`. -/
theorem thmA_seeds {p : ℕ} (hp : p.Prime) {r : ℕ → ℕ∞} {Dep : ℕ → ℕ → Prop}
    (hA : ThmA p r Dep) (a : ℕ) {b : ℕ} (hb : b < p - 1) (J : ℕ) :
    (0 < J ∧ J < p ^ a ∧ J % (p - 1) = b ∧ Dep a J) ↔
      (0 < J ∧ J < p ^ a ∧ ∃ s i : ℕ, (i : ℕ∞) < r b ∧ J = (Phi p)^[s] (dseed p b i)) := by
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨h0, h1, ?_⟩
    have := (hA a J h0 h1).mp h3
    unfold Crit at this
    rw [h2] at this
    exact (crit_iff_seed hp h2 (r b)).mp this
  · rintro ⟨h0, h1, s, i, hi, rfl⟩
    have h2 := seed_mod hp.two_le hb s i
    refine ⟨h0, h1, h2, ?_⟩
    rw [hA a _ h0 h1]
    unfold Crit
    rw [h2]
    exact (crit_iff_seed hp h2 (r b)).mpr ⟨s, i, hi, rfl⟩

/-! ## Corollary 3.2 (cor:phi) -/

lemma Phi_eq {p : ℕ} (hp : 0 < p) (J : ℕ) : Phi p J = J + (p - 1) * (J + 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  unfold Phi
  simp only [Nat.add_sub_cancel]
  have : (q + 1) * (J + 1) = J + q * (J + 1) + 1 := by ring
  omega

lemma Crit_Phi {p : ℕ} (hp : p.Prime) (r : ℕ → ℕ∞) (J : ℕ) :
    Crit p r (Phi p J) ↔ Crit p r J := by
  unfold Crit uPart
  have h1 : Phi p J + 1 = p ^ 1 * (J + 1) := by rw [pow_one]; exact Phi_add_one hp.pos J
  have h2 : Phi p J % (p - 1) = J % (p - 1) := by
    rw [Phi_eq hp.pos, Nat.add_mul_mod_self_left]
  rw [h1, Nat.ordCompl_self_pow_mul _ _ hp, h2]

/-- **Corollary 3.2** (cor:phi), first part: for `0 < J < p^a`, row `J` is dependent at
resolution `p^a` iff row `Φ(J)` is dependent at resolution `p^{a+1}`. -/
theorem cor_phi {p : ℕ} (hp : p.Prime) {r : ℕ → ℕ∞} {Dep : ℕ → ℕ → Prop}
    (hA : ThmA p r Dep) {a J : ℕ} (h0 : 0 < J) (hJ : J < p ^ a) :
    Dep a J ↔ Dep (a + 1) (Phi p J) := by
  have h1 := Phi_add_one hp.pos J
  have hlt : Phi p J < p ^ (a + 1) := by
    have : p * (J + 1) ≤ p * p ^ a := Nat.mul_le_mul_left p hJ
    rw [pow_succ]
    have : p * p ^ a = p ^ a * p := mul_comm _ _
    omega
  have hpos : 0 < Phi p J := by
    have : p * (J + 1) ≥ 2 * 2 := Nat.mul_le_mul hp.two_le (by omega)
    omega
  rw [hA a J h0 hJ, hA (a + 1) _ hpos hlt, Crit_Phi hp]

/-- **Corollary 3.2** (cor:phi), second part: row `p^a - 1` is dependent iff `r_0 > 0`. -/
theorem cor_phi_top {p : ℕ} (hp : p.Prime) {r : ℕ → ℕ∞} {Dep : ℕ → ℕ → Prop}
    (hA : ThmA p r Dep) {a : ℕ} (ha : 1 ≤ a) :
    Dep a (p ^ a - 1) ↔ 0 < r 0 := by
  have hpa : p ≤ p ^ a := by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ a := Nat.pow_le_pow_right hp.pos ha
  have h2 := hp.two_le
  rw [hA a _ (by omega) (by omega)]
  unfold Crit uPart
  have hsub : p ^ a - 1 + 1 = p ^ a := by omega
  have hmod : (p ^ a - 1) % (p - 1) = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    simpa using Nat.sub_dvd_pow_sub_pow p 1 a
  rw [hsub, Nat.ordCompl_self_pow hp, hmod]
  have := key_lt (i := 0) (e := 1) hp.pos (by omega) (r 0)
  simpa using this

/-! ## Corollary 3.1 (cor:low) -/

lemma dseed_zero_zero {p : ℕ} (hp : 2 ≤ p) : dseed p 0 0 = 0 := by
  unfold dseed
  rw [brk_eq_of (δ := 0) hp (by omega) (by simp)]; simp

lemma dseed_zero {p : ℕ} (hp : 2 ≤ p) {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ p - 2) :
    dseed p 0 i = (i + 1) * (p - 1) := by
  unfold dseed
  rw [brk_eq_of (δ := p - 1 - i) hp (by omega) ⟨1, by
    push_cast [Nat.cast_sub (by omega : i ≤ p - 1), Nat.cast_sub (by omega : 1 ≤ p)]; ring⟩]
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  zify [(by omega : i ≤ q)]
  ring

/-- **Corollary 3.1** (cor:low), with Theorem A as hypothesis: if `1 ≤ r_0 = n ≤ p - 1`, the
dependent rows `0 < J < p^a` with `J ≡ 0 (mod p-1)` are
`{p^s - 1 : 1 ≤ s ≤ a} ∪ {p^s((i+1)(p-1)+1) - 1 : 0 ≤ s ≤ a-2, 1 ≤ i ≤ r_0 - 1}`
(`s ≤ a - 2` written `s + 2 ≤ a`, which is empty for `a < 2`, as in the paper). -/
theorem cor_low {p : ℕ} (hp : p.Prime) {r : ℕ → ℕ∞} {Dep : ℕ → ℕ → Prop}
    (hA : ThmA p r Dep) (a : ℕ) {n : ℕ} (hr : r 0 = n) (hn1 : 1 ≤ n) (hn : n ≤ p - 1)
    (J : ℕ) :
    (0 < J ∧ J < p ^ a ∧ J % (p - 1) = 0 ∧ Dep a J) ↔
      ((∃ s, 1 ≤ s ∧ s ≤ a ∧ J = p ^ s - 1) ∨
        (∃ s i, s + 2 ≤ a ∧ 1 ≤ i ∧ i ≤ n - 1 ∧ J = p ^ s * ((i + 1) * (p - 1) + 1) - 1)) := by
  have h2 := hp.two_le
  have h1 := hp.one_lt
  rw [thmA_seeds hp hA a (b := 0) (by omega) J, hr]
  constructor
  · rintro ⟨h0, hlt, s, i, hi, rfl⟩
    rw [Nat.cast_lt] at hi
    rcases Nat.eq_zero_or_pos i with rfl | hi1
    · left
      rw [Phi_iter hp.pos, dseed_zero_zero h2] at h0 hlt ⊢
      simp only [zero_add, mul_one] at h0 hlt ⊢
      refine ⟨s, ?_, ?_, rfl⟩
      · rcases Nat.eq_zero_or_pos s with rfl | hs
        · simp at h0
        · exact hs
      · have : p ^ s ≤ p ^ a := by omega
        exact (Nat.pow_le_pow_iff_right h1).mp this
    · right
      rw [Phi_iter hp.pos, dseed_zero h2 hi1 (by omega)] at hlt ⊢
      refine ⟨s, i, ?_, hi1, by omega, rfl⟩
      by_contra hc
      have hX : p < (i + 1) * (p - 1) + 1 := by
        have : 2 * (p - 1) ≤ (i + 1) * (p - 1) := Nat.mul_le_mul_right _ (by omega)
        omega
      have hps : 0 < p ^ s := pow_pos hp.pos s
      have h3 : p ^ s * p < p ^ s * ((i + 1) * (p - 1) + 1) := Nat.mul_lt_mul_of_pos_left hX hps
      have h4 : p ^ a ≤ p ^ s * p := by
        rw [← pow_succ]; exact Nat.pow_le_pow_right hp.pos (by omega)
      omega
  · rintro (⟨s, hs1, hsa, rfl⟩ | ⟨s, i, hsa, hi1, hin, rfl⟩)
    · have hps : 1 < p ^ s := Nat.one_lt_pow (by omega) h1
      have hpa : p ^ s ≤ p ^ a := Nat.pow_le_pow_right hp.pos hsa
      refine ⟨by omega, by omega, s, 0, by exact_mod_cast hn1, ?_⟩
      rw [Phi_iter hp.pos, dseed_zero_zero h2]; simp
    · have hps : 0 < p ^ s := pow_pos hp.pos s
      have hX : (i + 1) * (p - 1) + 1 < p ^ 2 := by
        have : (i + 1) * (p - 1) ≤ (p - 1) * (p - 1) := Nat.mul_le_mul_right _ (by omega)
        obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
        simp only [Nat.add_sub_cancel] at this ⊢
        nlinarith
      have hX2 : 2 ≤ (i + 1) * (p - 1) + 1 := by
        have : 1 * 1 ≤ (i + 1) * (p - 1) := Nat.mul_le_mul (by omega) (by omega)
        omega
      have h3 : p ^ s * ((i + 1) * (p - 1) + 1) < p ^ s * p ^ 2 :=
        Nat.mul_lt_mul_of_pos_left hX hps
      have h4 : p ^ s * p ^ 2 ≤ p ^ a := by
        rw [← pow_add]; exact Nat.pow_le_pow_right hp.pos hsa
      have h5 : p ^ s * 2 ≤ p ^ s * ((i + 1) * (p - 1) + 1) := Nat.mul_le_mul_left _ hX2
      refine ⟨by omega, by omega, s, i, by exact_mod_cast (show i < n by omega), ?_⟩
      rw [Phi_iter hp.pos, dseed_zero h2 hi1 (by omega)]

/-! ## Corollary 3.3 (cor:kstar) -/

/-- `J^{(a_0)}_k = p^{a_0-2}(k(p-1)+1) - 1`. -/
def Jk (p a0 k : ℕ) : ℕ := p ^ (a0 - 2) * (k * (p - 1) + 1) - 1

/-- `k* = ⌈p n/(p-1)⌉`, written in `ℕ` (see `kstar_spec`). -/
def kstar (p n : ℕ) : ℕ := (p * n + (p - 2)) / (p - 1)

/-- `kstar p n` is the ceiling of `p n/(p-1)`: `(k*-1)(p-1) < p n ≤ k*(p-1)`. -/
lemma kstar_spec {p : ℕ} (hp : 2 ≤ p) (n : ℕ) :
    p * n ≤ kstar p n * (p - 1) ∧ kstar p n * (p - 1) < p * n + (p - 1) := by
  unfold kstar
  have h1 := Nat.div_add_mod (p * n + (p - 2)) (p - 1)
  have h2 := Nat.mod_lt (p * n + (p - 2)) (show 0 < p - 1 by omega)
  rw [mul_comm ((p * n + (p - 2)) / (p - 1))]
  omega

lemma Jk_add_one {p : ℕ} (hp : 0 < p) (a0 k : ℕ) :
    Jk p a0 k + 1 = p ^ (a0 - 2) * (k * (p - 1) + 1) := by
  unfold Jk
  have : 0 < p ^ (a0 - 2) * (k * (p - 1) + 1) := Nat.mul_pos (pow_pos hp _) (Nat.succ_pos _)
  omega

/-- First claim of cor:kstar: `J_{pj+1} = Φ(J_j)`. (Holds for every `j`, also `j = 0`.) -/
theorem Jk_Phi {p : ℕ} (hp : 0 < p) (a0 j : ℕ) : Jk p a0 (p * j + 1) = Phi p (Jk p a0 j) := by
  suffices h : Jk p a0 (p * j + 1) + 1 = Phi p (Jk p a0 j) + 1 by omega
  rw [Jk_add_one hp, Phi_add_one hp, Jk_add_one hp]
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

lemma Jk_pos {p : ℕ} (hp : 2 ≤ p) (a0 : ℕ) {k : ℕ} (hk : 1 ≤ k) : 0 < Jk p a0 k := by
  have h := Jk_add_one (by omega : 0 < p) a0 k
  have h1 : 1 * 1 ≤ k * (p - 1) := Nat.mul_le_mul hk (by omega)
  have h2 : 1 ≤ p ^ (a0 - 2) := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 * 2 ≤ p ^ (a0 - 2) * (k * (p - 1) + 1) := Nat.mul_le_mul h2 (by omega)
  omega

lemma Jk_mono {p : ℕ} (hp : 0 < p) (a0 : ℕ) {k k' : ℕ} (h : k ≤ k') : Jk p a0 k ≤ Jk p a0 k' := by
  have h1 := Jk_add_one hp a0 k
  have h2 := Jk_add_one hp a0 k'
  have : p ^ (a0 - 2) * (k * (p - 1) + 1) ≤ p ^ (a0 - 2) * (k' * (p - 1) + 1) :=
    Nat.mul_le_mul_left _ (by have := Nat.mul_le_mul_right (p - 1) h; omega)
  omega

lemma Jk_mod {p : ℕ} (hp : 2 ≤ p) (a0 k : ℕ) : Jk p a0 k % (p - 1) = 0 := by
  have h := Jk_add_one (by omega : 0 < p) a0 k
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (p : ℤ) 1 (a0 - 2)
  have h' : ((Jk p a0 k : ℕ) : ℤ) + 1 = (p : ℤ) ^ (a0 - 2) * ((k : ℤ) * ((p : ℤ) - 1) + 1) := by
    have := congrArg (fun x : ℕ => (x : ℤ)) h
    push_cast [Nat.cast_sub (by omega : 1 ≤ p)] at this
    exact this
  have hdvd : ((p - 1 : ℕ) : ℤ) ∣ ((Jk p a0 k : ℕ) : ℤ) - (0 : ℕ) := by
    rw [show ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 by push_cast [Nat.cast_sub (by omega : 1 ≤ p)]; ring]
    simp only [one_pow] at hc
    exact ⟨c * ((k : ℤ) * ((p : ℤ) - 1) + 1) + k,
      by push_cast; linear_combination h' + hc * ((k : ℤ) * ((p : ℤ) - 1) + 1)⟩
  have := (Nat.modEq_iff_dvd.mpr hdvd)
  unfold Nat.ModEq at this
  rw [Nat.zero_mod] at this
  exact this.symm

lemma Crit_Jk {p : ℕ} (hp : p.Prime) (r : ℕ → ℕ∞) (a0 k : ℕ) :
    Crit p r (Jk p a0 k) ↔ (ordCompl[p] (k * (p - 1) + 1) : ℕ∞) < p * r 0 := by
  unfold Crit uPart
  rw [Jk_add_one hp.pos, Nat.ordCompl_self_pow_mul _ _ hp, Jk_mod hp.two_le]

/-- **Corollary 3.3** (cor:kstar), case `r_0 = 0`: row `J_1` is new (so `k* = 1`). -/
theorem cor_kstar_zero {p : ℕ} (hp : p.Prime) {r : ℕ → ℕ∞} {Dep : ℕ → ℕ → Prop}
    (hA : ThmA p r Dep) {a0 a1 : ℕ} (hr : r 0 = 0) (hlt : Jk p a0 1 < p ^ a1) :
    ¬ Dep a1 (Jk p a0 1) := by
  rw [hA a1 _ (Jk_pos hp.two_le a0 le_rfl) hlt, Crit_Jk hp, hr]
  simp

/-- **Corollary 3.3** (cor:kstar), case `r_0 = ∞`: every row of the progression is dependent. -/
theorem cor_kstar_top {p : ℕ} (hp : p.Prime) {r : ℕ → ℕ∞} {Dep : ℕ → ℕ → Prop}
    (hA : ThmA p r Dep) {a0 a1 : ℕ} (hr : r 0 = ⊤) {k : ℕ} (hk : 1 ≤ k)
    (hlt : Jk p a0 k < p ^ a1) : Dep a1 (Jk p a0 k) := by
  rw [hA a1 _ (Jk_pos hp.two_le a0 hk) hlt, Crit_Jk hp, hr,
    ENat.mul_top (by exact_mod_cast hp.ne_zero)]
  exact ENat.natCast_lt_top _

/-- **Corollary 3.3** (cor:kstar), case `1 ≤ r_0 = n < ∞`, rows before `k*`: every `J_k` with
`1 ≤ k < k* = ⌈p n/(p-1)⌉` (read at a resolution containing it) is dependent. -/
theorem cor_kstar_below {p : ℕ} (hp : p.Prime) {r : ℕ → ℕ∞} {Dep : ℕ → ℕ → Prop}
    (hA : ThmA p r Dep) {a0 a1 n : ℕ} (hr : r 0 = n) (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k)
    (hks : k < kstar p n) (hlt : Jk p a0 k < p ^ a1) : Dep a1 (Jk p a0 k) := by
  have h2 := hp.two_le
  rw [hA a1 _ (Jk_pos h2 a0 hk) hlt, Crit_Jk hp, hr, ← Nat.cast_mul, Nat.cast_lt]
  obtain ⟨_, hs2⟩ := kstar_spec h2 n
  have h3 : k * (p - 1) + (p - 1) ≤ kstar p n * (p - 1) := by
    have := Nat.mul_le_mul_right (p - 1) (show k + 1 ≤ kstar p n by omega)
    rw [add_mul, one_mul] at this
    exact this
  -- `k(p-1) + 1 ≤ p n`
  rcases Nat.lt_or_ge (k * (p - 1) + 1) (p * n) with hX | hX
  · exact lt_of_le_of_lt (Nat.ordCompl_le _ _) hX
  · have hX' : k * (p - 1) + 1 = p ^ 1 * n := by rw [pow_one]; omega
    rw [hX', Nat.ordCompl_self_pow_mul _ _ hp]
    have : n < p * n := by
      have := Nat.mul_le_mul_right n h2
      omega
    exact lt_of_le_of_lt (Nat.ordCompl_le _ _) this

/-- **Corollary 3.3** (cor:kstar), case `1 ≤ r_0 = n < ∞`, the row `k*`: if `J_{k*}` lies below
the resolution, it is new. With `cor_kstar_below`, `k* = ⌈p r_0/(p-1)⌉` is the least `k ≥ 1`
with `J_k` new; it depends neither on `a_0` nor on `a_1`. -/
theorem cor_kstar_new {p : ℕ} (hp : p.Prime) {r : ℕ → ℕ∞} {Dep : ℕ → ℕ → Prop}
    (hA : ThmA p r Dep) {a0 a1 n : ℕ} (hr : r 0 = n) (hn : 1 ≤ n)
    (hlt : Jk p a0 (kstar p n) < p ^ a1) : ¬ Dep a1 (Jk p a0 (kstar p n)) := by
  have h2 := hp.two_le
  obtain ⟨hs1, hs2⟩ := kstar_spec h2 n
  have hk1 : 1 ≤ kstar p n := by
    rcases Nat.eq_zero_or_pos (kstar p n) with h | h
    · rw [h, zero_mul] at hs1
      have := Nat.mul_le_mul_left p hn
      omega
    · exact h
  rw [hA a1 _ (Jk_pos h2 a0 hk1) hlt, Crit_Jk hp, hr, ← Nat.cast_mul, Nat.cast_lt]
  set k := kstar p n with hk
  -- `p ∤ k(p-1)+1`
  have hnd : ¬ p ∣ k * (p - 1) + 1 := by
    intro hd
    have hsum : k * (p - 1) + 1 + (k - 1) = k * p := by
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      rw [hm]
      simp only [Nat.add_sub_cancel]
      ring
    have hd' : p ∣ k - 1 := (Nat.dvd_add_right hd).mp (by rw [hsum]; exact dvd_mul_left p k)
    obtain ⟨j, hj⟩ := hd'
    have e1 : k * (p - 1) = p * (j * (p - 1)) + (p - 1) := by
      have : k = p * j + 1 := by omega
      rw [this, add_mul, one_mul, mul_assoc]
    have i1 : j * (p - 1) < n := by
      have : p * (j * (p - 1)) < p * n := by omega
      exact Nat.lt_of_mul_lt_mul_left this
    have i2 : n < j * (p - 1) + 1 := by
      have : p * n < p * (j * (p - 1) + 1) := by rw [mul_add, mul_one]; omega
      exact Nat.lt_of_mul_lt_mul_left this
    omega
  rw [(Nat.ordCompl_eq_self_iff_zero_or_not_dvd _ hp).mpr (Or.inr hnd)]
  omega

/-- **Corollary 3.3** (cor:kstar), last sentence: if `J_{k*} ≥ p^{a_1}`, every row of the
progression below `p^{a_1}` is dependent. -/
theorem cor_kstar_beyond {p : ℕ} (hp : p.Prime) {r : ℕ → ℕ∞} {Dep : ℕ → ℕ → Prop}
    (hA : ThmA p r Dep) {a0 a1 n : ℕ} (hr : r 0 = n) (hn : 1 ≤ n)
    (hge : p ^ a1 ≤ Jk p a0 (kstar p n)) {k : ℕ} (hk : 1 ≤ k) (hlt : Jk p a0 k < p ^ a1) :
    Dep a1 (Jk p a0 k) := by
  have hks : k < kstar p n := by
    by_contra hc
    have := Jk_mono hp.pos a0 (show kstar p n ≤ k by omega)
    omega
  exact cor_kstar_below hp hA hr hn hk hks hlt

/-! ## Corollary 3.4 (cor:rank) -/

lemma sum_count (N : ℕ) (r : ℕ∞) :
    ∑ i ∈ range N, (if (i : ℕ∞) < r then 0 else 1) = (((N : ℕ) : ℕ∞) - r).toNat := by
  induction r using ENat.recTopCoe with
  | top => simp
  | coe n =>
    rw [← ENat.natCast_sub, ENat.toNat_natCast]
    simp only [Nat.cast_lt]
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ, ih]
      split_ifs <;> omega

open Classical in
/-- **Corollary 3.4** (cor:rank), with Theorem A as hypothesis: the number of new rows of `B`
at level `p^a` is `[μ(ℤ_p) ≠ 0] + Σ_{b=0}^{p-2} Σ_{t=0}^{a-1} max(p^t - r_b, 0)`
(`max(p^t - ∞, 0) = 0` is the truncated subtraction of `ℕ∞`). `M0` stands for `μ(ℤ_p) = 0`, and
`h0` is the row-0 clause of thm:A. -/
theorem cor_rank {p : ℕ} (hp : p.Prime) {r : ℕ → ℕ∞} {Dep : ℕ → ℕ → Prop}
    (hA : ThmA p r Dep) {a : ℕ} (ha : 1 ≤ a) (M0 : Prop) (h0 : Dep a 0 ↔ M0) :
    ((range (p ^ a)).filter (fun J => ¬ Dep a J)).card =
      (if M0 then 0 else 1) +
        ∑ b ∈ range (p - 1), ∑ t ∈ range a, (((p ^ t : ℕ) : ℕ∞) - r b).toNat := by
  have h2 := hp.two_le
  have hpa : p ≤ p ^ a := by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ a := Nat.pow_le_pow_right hp.pos ha
  set P := p ^ a with hP
  set g : ℕ → ℕ := fun J => if Crit p r J then 0 else 1 with hg
  -- Step 1: split off row 0 and use Theorem A on the positive rows.
  have step1 : ((range P).filter (fun J => ¬ Dep a J)).card =
      ∑ J ∈ range (P - 1), g (J + 1) + (if M0 then 0 else 1) := by
    rw [card_filter, show P = (P - 1) + 1 by omega, sum_range_succ']
    congr 1
    · refine sum_congr rfl (fun J hJ => ?_)
      rw [mem_range] at hJ
      rw [hA a (J + 1) (Nat.succ_pos J) (by omega)]
      simp only [hg]
      by_cases h : Crit p r (J + 1) <;> simp [h]
    · by_cases h : M0 <;> simp [h0, h]
  -- Step 2: `g (P-1) = g 0`, so shifting the window does not change the sum.
  have hgP : g (P - 1) = g 0 := by
    have hsub : P - 1 + 1 = p ^ a := by omega
    have hmod : (P - 1) % (p - 1) = 0 := by
      apply Nat.mod_eq_zero_of_dvd
      simpa using Nat.sub_dvd_pow_sub_pow p 1 a
    have hc : Crit p r (P - 1) ↔ Crit p r 0 := by
      unfold Crit uPart
      rw [hsub, Nat.ordCompl_self_pow hp, hmod]
      simp
    simp only [hg]
    by_cases h : Crit p r 0
    · rw [ite_eq_left (hc.mpr h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (hc.mp h')), ite_eq_right h]
  have step2 : ∑ J ∈ range (P - 1), g (J + 1) = ∑ J ∈ range (P - 1), g J := by
    have e1 := sum_range_succ' g (P - 1)
    have e2 := sum_range_succ g (P - 1)
    rw [hgP] at e2
    omega
  -- Step 3: reindex the rows `J < P - 1` by `(b, s, i)`, `J = Φ^s(d_b(i))`.
  set T : Finset (Σ _ : ℕ, Σ _ : ℕ, ℕ) :=
    (range (p - 1)).sigma (fun _ => (range a).sigma (fun s => range (p ^ (a - s - 1)))) with hT
  have step3 : ∑ J ∈ range (P - 1), g J =
      ∑ x ∈ T, (if (x.2.2 : ℕ∞) < r x.1 then 0 else 1) := by
    refine sum_nbij' (fun J => ⟨J % (p - 1), ⟨(J + 1).factorization p, uPart p J / p⟩⟩)
      (fun x => (Phi p)^[x.2.1] (dseed p x.1 x.2.2)) ?_ ?_ ?_ ?_ ?_
    · intro J hJ
      rw [mem_range] at hJ
      simp only [hT, mem_sigma, mem_range]
      have hJu : p ^ (J + 1).factorization p * uPart p J = J + 1 :=
        Nat.ordProj_mul_ordCompl_eq_self (J + 1) p
      have hu0 : 0 < uPart p J := Nat.ordCompl_pos p (by omega)
      set s := (J + 1).factorization p
      have hs : s < a := by
        by_contra hc
        have : p ^ a ≤ p ^ s := Nat.pow_le_pow_right hp.pos (by omega)
        have : p ^ s ≤ p ^ s * uPart p J := Nat.le_mul_of_pos_right _ hu0
        omega
      refine ⟨Nat.mod_lt _ (by omega), hs, ?_⟩
      rw [Nat.div_lt_iff_lt_mul hp.pos, ← pow_succ, show a - s - 1 + 1 = a - s by omega]
      have : p ^ s * uPart p J < p ^ s * p ^ (a - s) := by
        rw [← pow_add, show s + (a - s) = a by omega]; omega
      exact Nat.lt_of_mul_lt_mul_left this
    · rintro ⟨b, s, i⟩ hx
      simp only [hT, mem_sigma, mem_range] at hx
      obtain ⟨hb, hs, hi⟩ := hx
      rw [mem_range]
      have h1 := Phi_iter_add_one hp.pos s (dseed p b i)
      have hbl := brk_lt h2 b i
      have hd : dseed p b i + 1 < p * p ^ (a - s - 1) := by
        have : p * (i + 1) ≤ p * p ^ (a - s - 1) := Nat.mul_le_mul_left p hi
        unfold dseed
        rw [mul_add, mul_one] at this
        omega
      have : p ^ s * (dseed p b i + 1) < p ^ s * (p * p ^ (a - s - 1)) :=
        Nat.mul_lt_mul_of_pos_left hd (pow_pos hp.pos s)
      rw [← pow_succ', ← pow_add, show s + (a - s - 1 + 1) = a by omega] at this
      simp only
      omega
    · intro J _
      exact (decomp hp J).2.symm
    · rintro ⟨b, s, i⟩ hx
      simp only [hT, mem_sigma, mem_range] at hx
      obtain ⟨hb, -⟩ := hx
      obtain ⟨hfs, hu⟩ := seed_decomp hp b s i
      simp only
      rw [hfs, hu, dseed_div h2, seed_mod h2 hb]
    · intro J _
      simp only [hg]
      have hu := (decomp hp J).1
      have hc : Crit p r J ↔ ((uPart p J / p : ℕ) : ℕ∞) < r (J % (p - 1)) := by
        unfold Crit
        have := brk_lt h2 (J % (p - 1)) (uPart p J / p)
        generalize uPart p J / p = i at hu this ⊢
        rw [hu]
        unfold dseed
        rw [add_assoc]
        exact key_lt hp.pos (by omega) _
      by_cases h : Crit p r J
      · rw [ite_eq_left h, ite_eq_left (hc.mp h)]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h (hc.mpr h'))]
  -- Step 4: evaluate the sum over `T`.
  have step4 : ∑ x ∈ T, (if (x.2.2 : ℕ∞) < r x.1 then 0 else 1) =
      ∑ b ∈ range (p - 1), ∑ t ∈ range a, (((p ^ t : ℕ) : ℕ∞) - r b).toNat := by
    rw [hT, sum_sigma]
    refine sum_congr rfl (fun b _ => ?_)
    rw [sum_sigma]
    refine Eq.trans ?_ (sum_range_reflect (fun t => (((p ^ t : ℕ) : ℕ∞) - r b).toNat) a)
    refine sum_congr rfl (fun s hs => ?_)
    rw [mem_range] at hs
    rw [show a - 1 - s = a - s - 1 by omega]
    show (∑ i ∈ range (p ^ (a - s - 1)), if (i : ℕ∞) < r b then 0 else 1) = _
    exact sum_count _ _
  rw [step1, step2, step3, step4, add_comm]

/-! ## cor:kstar, "Equivalently": `r_0 = (k* - 1) - #{j ≥ 1 : pj + 1 < k*}` -/

theorem kstar_count {p : ℕ} (hp : 2 ≤ p) {n : ℕ} (hn : 1 ≤ n) :
    n = (kstar p n - 1) -
      ((range (kstar p n)).filter (fun j => 1 ≤ j ∧ p * j + 1 < kstar p n)).card := by
  obtain ⟨hs1, hs2⟩ := kstar_spec hp n
  set K := kstar p n with hK
  have hK2 : 2 ≤ K := by
    by_contra hc
    have : K * (p - 1) ≤ 1 * (p - 1) := Nat.mul_le_mul_right _ (by omega)
    have : p * 1 ≤ p * n := Nat.mul_le_mul_left p hn
    omega
  set c := (K - 2) / p with hc
  set ρ := (K - 2) % p with hρ
  have hρlt : ρ < p := Nat.mod_lt _ (by omega)
  have hKdec : K = p * c + ρ + 2 := by
    have := Nat.div_add_mod (K - 2) p
    rw [← hc, ← hρ] at this
    omega
  -- the filtered set is `Icc 1 c`
  have hset : (range K).filter (fun j => 1 ≤ j ∧ p * j + 1 < K) = Icc 1 c := by
    ext j
    simp only [mem_filter, mem_range, mem_Icc]
    have hdiv : j ≤ c ↔ j * p ≤ K - 2 := Nat.le_div_iff_mul_le (by omega)
    have hjp : j ≤ p * j := Nat.le_mul_of_pos_left j (by omega)
    rw [hdiv, mul_comm j p]
    omega
  rw [hset, Nat.card_Icc, Nat.add_sub_cancel]
  set m := (p - 1) * c + ρ + 1 with hm
  have hid : K * (p - 1) + ρ + 2 = p * m + p := by
    rw [hKdec, hm]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have h1 : m ≤ n := by
    have e1 : p * (n + 1) = p * n + p := by ring
    have : p * m < p * (n + 1) := by omega
    have := Nat.lt_of_mul_lt_mul_left this
    omega
  have h2 : n ≤ m := by
    have e1 : p * (m + 1) = p * m + p := by ring
    have : p * n < p * (m + 1) := by omega
    have := Nat.lt_of_mul_lt_mul_left this
    omega
  have hpc : (p - 1) * c + c = p * c := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  omega

/-! ## Arithmetic of Corollaries C and D (thm:B as hypothesis) -/

lemma ordCompl_prime_self {p : ℕ} (hp : p.Prime) : ordCompl[p] p = 1 := by
  simpa using Nat.ordCompl_self_pow (k := 1) hp

/-- **Corollary C** (cor:C), with thm:A and thm:B as hypotheses. `Vanish j` = "the
`χ`-component of `G_{P+j}` vanishes"; `hB` is thm:B (= lem:M1 + lem:bridge, not formalized);
`r 0 = r_{χ,0}`, which lem:R (not formalized) identifies with `λ̃(χ)`. For `1 ≤ k ≤ p - 1`,
the component at `P + J_k` vanishes iff `k ≤ r_{χ,0}`. -/
theorem cor_C {p : ℕ} (hp : p.Prime) {r : ℕ → ℕ∞} {Dep : ℕ → ℕ → Prop}
    (hA : ThmA p r Dep) {a : ℕ} (ha : 2 ≤ a) {Vanish : ℕ → Prop}
    (hB : ∀ j, j < p ^ a - p ^ (a - 1) → (Vanish j ↔ Dep a j))
    {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ p - 1) :
    Vanish (Jk p a k) ↔ (k : ℕ∞) ≤ r 0 := by
  have h2 := hp.two_le
  -- `J_k < P - p^{a-1}`
  have hJ1 := Jk_add_one hp.pos a k
  have hPa : p ^ a = p ^ (a - 2) * (p * p) := by
    rw [← pow_two, ← pow_add, show a - 2 + 2 = a by omega]
  have hPa1 : p ^ (a - 1) = p ^ (a - 2) * p := by
    rw [← pow_succ, show a - 2 + 1 = a - 1 by omega]
  have hX : k * (p - 1) + 1 + p ≤ p * p := by
    have : k * (p - 1) ≤ (p - 1) * (p - 1) := Nat.mul_le_mul_right _ hk
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at this ⊢
    nlinarith
  have hlt : Jk p a k < p ^ a - p ^ (a - 1) := by
    have := Nat.mul_le_mul_left (p ^ (a - 2)) hX
    rw [mul_add, mul_add] at this
    rw [mul_add, mul_one] at hJ1
    rw [hPa, hPa1, Nat.lt_sub_iff_add_lt]
    omega
  have hltP : Jk p a k < p ^ a := lt_of_lt_of_le hlt (Nat.sub_le _ _)
  rw [hB _ hlt, hA a _ (Jk_pos h2 a hk1) hltP, Crit_Jk hp]
  induction r 0 using ENat.recTopCoe with
  | top =>
    simp only [le_top, iff_true]
    rw [ENat.mul_top (by exact_mod_cast hp.ne_zero)]
    exact ENat.natCast_lt_top _
  | coe n =>
    rw [← Nat.cast_mul, Nat.cast_lt, Nat.cast_le]
    rcases Nat.eq_or_lt_of_le hk1 with rfl | hk2
    · rw [one_mul, Nat.sub_add_cancel (by omega : 1 ≤ p), ordCompl_prime_self hp]
      constructor
      · intro h; by_contra hc; simp_all
      · intro h; have := Nat.mul_le_mul h2 h; omega
    · have hnd : ¬ p ∣ k * (p - 1) + 1 := by
        have e : k * (p - 1) + 1 = p * (k - 1) + (p - k + 1) := by
          obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
          obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          rw [show q + 1 - (m + 1) + 1 = q - m + 1 by omega]
          zify [(by omega : m ≤ q)]
          ring
        rw [e]
        exact not_dvd_mul_add (by omega) (by omega)
      rw [(Nat.ordCompl_eq_self_iff_zero_or_not_dvd _ hp).mpr (Or.inr hnd)]
      constructor
      · intro h
        by_contra hc
        have : p * n ≤ p * (k - 1) := Nat.mul_le_mul_left p (by omega)
        have e : p * (k - 1) ≤ k * (p - 1) + 1 := by
          obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
          obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
          simp only [Nat.add_sub_cancel] at hk ⊢
          nlinarith
        omega
      · intro h
        have h3 : k * (p - 1) ≤ n * (p - 1) := Nat.mul_le_mul_right _ h
        have e : n * (p - 1) + n = p * n := by
          obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          ring
        omega

/-- `j_{b,i} = p i + [b-i]_{p-1}`, except `j_{0,0} = p - 1` (cor:D). -/
def jD (p b i : ℕ) : ℕ := if b = 0 ∧ i = 0 then p - 1 else dseed p b i

lemma brk_self {p b : ℕ} (hp : 2 ≤ p) (hb : b < p - 1) : brk p b 0 = b :=
  brk_eq_of hp hb (by simp)

/-- Arithmetic of cor:D: `j_{b,i} > 0`, `j_{b,i} ≡ b`, and `u(j_{b,i}) < p r ↔ i < r`. -/
lemma jD_crit {p : ℕ} (hp : p.Prime) (r : ℕ → ℕ∞) {b : ℕ} (hb : b < p - 1) (i : ℕ) :
    0 < jD p b i ∧ jD p b i % (p - 1) = b ∧ (Crit p r (jD p b i) ↔ (i : ℕ∞) < r b) := by
  have h2 := hp.two_le
  unfold jD
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    refine ⟨by omega, Nat.mod_self _, ?_⟩
    unfold Crit uPart
    rw [Nat.sub_add_cancel (by omega : 1 ≤ p), ordCompl_prime_self hp, Nat.mod_self]
    have := key_lt (i := 0) (e := 1) hp.pos (by omega) (r 0)
    simpa using this
  · have hm := seed_mod h2 hb 0 i
    simp only [Function.iterate_zero, id] at hm
    refine ⟨?_, hm, ?_⟩
    · unfold dseed
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · rw [brk_self h2 hb]; omega
      · have : p * 1 ≤ p * i := Nat.mul_le_mul_left p hi
        omega
    · unfold Crit
      have hu := (seed_decomp hp b 0 i).2
      simp only [Function.iterate_zero, id] at hu
      rw [hu, hm]
      unfold dseed
      have := brk_lt h2 b i
      rw [add_assoc]
      exact key_lt hp.pos (by omega) _

/-- **Corollary D** (cor:D), first statement, with thm:A and thm:B (`hB`) as hypotheses:
if `j_{b,i} < P - p^{a-1}`, the `χ`-component of `G_{P + j_{b,i}}` vanishes iff `i < r_{χ,b}`.
(Stated for every `b ∈ [0,p-2]`; the paper restricts to even `b`.) -/
theorem cor_D {p : ℕ} (hp : p.Prime) {r : ℕ → ℕ∞} {Dep : ℕ → ℕ → Prop}
    (hA : ThmA p r Dep) {a : ℕ} {Vanish : ℕ → Prop}
    (hB : ∀ j, j < p ^ a - p ^ (a - 1) → (Vanish j ↔ Dep a j))
    {b : ℕ} (hb : b < p - 1) {i : ℕ} (hj : jD p b i < p ^ a - p ^ (a - 1)) :
    Vanish (jD p b i) ↔ (i : ℕ∞) < r b := by
  obtain ⟨h0, hm, hc⟩ := jD_crit hp r hb i
  rw [hB _ hj, hA a _ h0 (lt_of_lt_of_le hj (Nat.sub_le _ _)), hc]

lemma jD_zero_lt {p : ℕ} (hp : 2 ≤ p) (i : ℕ) : jD p 0 i < p * (i + 1) := by
  unfold jD
  split_ifs with h
  · obtain ⟨-, rfl⟩ := h; omega
  · unfold dseed
    have := brk_lt hp 0 i
    rw [mul_add, mul_one]
    omega

/-- cor:D: the `j_{0,i}` increase with `i`. -/
theorem jD_zero_strictMono {p : ℕ} (hp : 2 ≤ p) : StrictMono (jD p 0) := by
  apply strictMono_nat_of_lt_succ
  intro i
  have h1 := jD_zero_lt hp i
  have h2 : p * (i + 1) ≤ jD p 0 (i + 1) := by
    unfold jD
    rw [ite_eq_right (by omega)]
    unfold dseed
    omega
  omega

/-- cor:D: `j_{0,i} < P - p^{a-1}` for `i ≤ p^{a-1} - p^{a-2} - 1`. -/
theorem jD_zero_range {p : ℕ} (hp : 2 ≤ p) {a : ℕ} (ha : 2 ≤ a) {i : ℕ}
    (hi : i < p ^ (a - 1) - p ^ (a - 2)) : jD p 0 i < p ^ a - p ^ (a - 1) := by
  have h1 := jD_zero_lt hp i
  have e : p ^ a - p ^ (a - 1) = p * (p ^ (a - 1) - p ^ (a - 2)) := by
    rw [Nat.mul_sub, ← pow_succ', ← pow_succ', show a - 1 + 1 = a by omega,
      show a - 2 + 1 = a - 1 by omega]
  have : p * (i + 1) ≤ p * (p ^ (a - 1) - p ^ (a - 2)) := Nat.mul_le_mul_left p hi
  omega

/-- **Corollary D** (cor:D), "in particular": if `r_{χ,0} = n < p^{a-1} - p^{a-2}`, then among
the indices `0 ≤ i ≤ p^{a-1} - p^{a-2} - 1` (all within the range of thm:B) the components at
`P + j_{0,i}` vanish exactly for the first `n` of them: the vanishing set is `{0, …, n-1}`. -/
theorem cor_D_first {p : ℕ} (hp : p.Prime) {r : ℕ → ℕ∞} {Dep : ℕ → ℕ → Prop}
    (hA : ThmA p r Dep) {a : ℕ} (ha : 2 ≤ a) {Vanish : ℕ → Prop} [DecidablePred Vanish]
    (hB : ∀ j, j < p ^ a - p ^ (a - 1) → (Vanish j ↔ Dep a j))
    {n : ℕ} (hr : r 0 = n) (hn : n < p ^ (a - 1) - p ^ (a - 2)) :
    (range (p ^ (a - 1) - p ^ (a - 2))).filter (fun i => Vanish (jD p 0 i)) = range n := by
  have h2 := hp.two_le
  ext i
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨hi, hv⟩
    have := (cor_D hp hA hB (by omega : 0 < p - 1) (jD_zero_range h2 ha hi)).mp hv
    rw [hr] at this
    exact_mod_cast this
  · intro hi
    refine ⟨by omega, ?_⟩
    rw [cor_D hp hA hB (by have := hp.two_le; omega) (jD_zero_range hp.two_le ha (by omega)), hr]
    exact_mod_cast hi

/-! ## Checks against Remark rem:scope (`p = 5`, `r_0 = 6`) -/

/-- `k* = ⌈5·6/4⌉ = 8`. -/
example : kstar 5 6 = 8 := by decide

/-- The seeds `j_{0,i}`, `i = 0, …, 6`, for `p = 5`: `4, 8, 12, 16, 20, 28, 32`. -/
example : (List.range 7).map (jD 5 0) = [4, 8, 12, 16, 20, 28, 32] := by decide


end FilasIII
