/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.Ring

/-!
# Melody Chan's theorem on distinguishing GL_n(F)

For a field `F`, infinite or finite with `|F| > n + 1`, the vectors of `Fⁿ` can be coloured Green or
Blue so that every invertible `n × n` matrix other than the identity sends some Green vector to a
Blue one (Theorem of the Day; Chan 2006). Construction: take `α` with `α^r ≠ 1` for `1 ≤ r ≤ n` (a
generator of `F^×`, or an element avoiding the roots of unity of order `≤ n`), and colour Blue the
vectors `α^i e_j`, `0 ≤ i < j ≤ n`; a matrix preserving this set fixes every basis vector.

## Main results

* `Chan.blue_stable_eq_one`: an invertible matrix preserving Chan Blue set is the identity
* `Chan.exists_blue`: Chan: a Green/Blue colouring of Fⁿ that no non-identity invertible matrix respects

## References

* R. Whitty, Theorem of the Day, «A Theorem of Melody Chan on Group Actions» (GroupTheory/MChan).
* M. Chan, The maximum distinguishing number of a group, Electron. J. Combin. 13 (2006) R70.
-/

@[expose] public section

open Matrix

namespace Chan

/-- Existence of `α` of multiplicative order `> n`. -/
theorem exists_alpha (F : Type*) [Field F] (n : ℕ)
    (hF : Infinite F ∨ ∃ _ : Fintype F, n + 1 < Fintype.card F) :
    ∃ α : F, α ≠ 0 ∧ ∀ r : ℕ, 1 ≤ r → r ≤ n → α ^ r ≠ 1 := by
  classical
  rcases hF with hinf | ⟨hfin, hcard⟩
  · let bad : Finset F := insert 0 ((Finset.Icc 1 n).biUnion
      fun r => ((Polynomial.X ^ r - 1 : Polynomial F)).roots.toFinset)
    obtain ⟨α, hα⟩ := Infinite.exists_notMem_finset bad
    refine ⟨α, fun h => hα (by simp [bad, h]), fun r hr1 hrn h => hα ?_⟩
    simp only [bad, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_Icc, Multiset.mem_toFinset]
    right
    refine ⟨r, ⟨hr1, hrn⟩, ?_⟩
    have hne : (Polynomial.X ^ r - 1 : Polynomial F) ≠ 0 := by
      simpa using Polynomial.X_pow_sub_C_ne_zero (by omega : 0 < r) (1 : F)
    rw [Polynomial.mem_roots hne]
    simp [h]
  · obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
    have hord : orderOf g = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers hg
    rw [Nat.card_eq_fintype_card, Fintype.card_units] at hord
    refine ⟨(g : F), g.ne_zero, fun r hr1 hrn h => ?_⟩
    have h1 : g ^ r = 1 := Units.ext (by simpa using h)
    have := orderOf_le_of_pow_eq_one (by omega) h1
    omega

/-- The Blue set. -/
def Blue (F : Type*) [Field F] (n : ℕ) (α : F) : Set (Fin n → F) :=
  {v | ∃ j : Fin n, ∃ i : ℕ, i < j.val + 1 ∧ v = Pi.single j (α ^ i)}

section
variable {F : Type*} [Field F] {n : ℕ} {α : F}

theorem single_inj {j j' : Fin n} {a b : F} (ha : a ≠ 0) (h : (Pi.single j a : Fin n → F) = Pi.single j' b) :
    j = j' ∧ a = b := by
  by_cases hj : j = j'
  · subst hj
    exact ⟨rfl, by simpa using congrFun h j⟩
  · exfalso
    apply ha
    simpa [Pi.single_apply, hj] using congrFun h j

theorem pow_inj (hα : ∀ r : ℕ, 1 ≤ r → r ≤ n → α ^ r ≠ 1) (h0 : α ≠ 0) {r i : ℕ}
    (hr : r ≤ n) (hi : i ≤ n) (h : α ^ r = α ^ i) : r = i := by
  rcases lt_trichotomy r i with hlt | rfl | hgt
  · exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have h1 : α ^ (d + 1) = 1 := by
      have hne : α ^ r ≠ 0 := pow_ne_zero _ h0
      apply mul_left_cancel₀ hne
      have e : r + (d + 1) = r + d + 1 := by omega
      rw [← pow_add, mul_one, e, ← h]
    exact hα (d + 1) (by omega) (by omega) h1
  · rfl
  · exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hgt
    have h1 : α ^ (d + 1) = 1 := by
      have hne : α ^ i ≠ 0 := pow_ne_zero _ h0
      apply mul_left_cancel₀ hne
      have e : i + (d + 1) = i + d + 1 := by omega
      rw [← pow_add, mul_one, e, h]
    exact hα (d + 1) (by omega) (by omega) h1

theorem single_mem_iff (hα : ∀ r : ℕ, 1 ≤ r → r ≤ n → α ^ r ≠ 1) (h0 : α ≠ 0) (j : Fin n)
    {r : ℕ} (hr : r ≤ n) : Pi.single j (α ^ r) ∈ Blue F n α ↔ r < j.val + 1 := by
  constructor
  · rintro ⟨j', i, hi, h⟩
    obtain ⟨rfl, h2⟩ := single_inj (pow_ne_zero _ h0) h
    have := pow_inj hα h0 hr (by omega) h2
    omega
  · intro h
    exact ⟨j, r, h, rfl⟩

theorem inv_not_mem (hα : ∀ r : ℕ, 1 ≤ r → r ≤ n → α ^ r ≠ 1) (h0 : α ≠ 0) (j : Fin n) :
    Pi.single j α⁻¹ ∉ Blue F n α := by
  rintro ⟨j', i, hi, h⟩
  obtain ⟨rfl, h2⟩ := single_inj (inv_ne_zero h0) h
  apply hα (i + 1) (by omega) (by omega)
  rw [pow_succ, ← h2]
  exact inv_mul_cancel₀ h0

theorem smul_single (j : Fin n) (c a : F) :
    c • (Pi.single j a : Fin n → F) = Pi.single j (c * a) := by
  ext l
  by_cases hl : l = j
  · subst hl; simp
  · simp [hl]

theorem smul_single_one (j : Fin n) (a : F) :
    a • (Pi.single j 1 : Fin n → F) = Pi.single j a := by
  rw [smul_single, mul_one]

theorem mulVec_single_smul (B : Matrix (Fin n) (Fin n) F) (k : Fin n) (a : F) :
    B *ᵥ Pi.single k a = a • (B *ᵥ Pi.single k 1) := by
  ext i
  simp [mul_comm]

/-- An invertible matrix preserving the Blue set is the identity. -/
theorem blue_stable_eq_one (hα : ∀ r : ℕ, 1 ≤ r → r ≤ n → α ^ r ≠ 1) (h0 : α ≠ 0)
    (B : GL (Fin n) F)
    (hB : ∀ v, v ∈ Blue F n α ↔ (B : Matrix (Fin n) (Fin n) F) *ᵥ v ∈ Blue F n α) :
    B = 1 := by
  classical
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin n) (Fin n) F, M = (B : Matrix (Fin n) (Fin n) F) :=
    ⟨_, rfl⟩
  rw [← hM] at hB
  have key : ∀ k : Fin n, M *ᵥ Pi.single k 1 = Pi.single k 1 := by
    intro k
    have hk : (Pi.single k 1 : Fin n → F) ∈ Blue F n α :=
      ⟨k, 0, by omega, by simp⟩
    obtain ⟨j, i, hi, hji⟩ := (hB _).1 hk
    have hi0 : i = 0 := by
      by_contra hne
      have h1 := (hB (Pi.single k α⁻¹)).not.1 (inv_not_mem hα h0 k)
      apply h1
      rw [mulVec_single_smul, hji, smul_single]
      refine ⟨j, i - 1, by omega, ?_⟩
      congr 1
      obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hne
      rw [pow_succ', ← mul_assoc, inv_mul_cancel₀ h0, one_mul]
      rfl
    subst hi0
    simp only [pow_zero] at hji
    have hmul : ∀ a : F, M *ᵥ Pi.single k a = Pi.single j a := fun a => by
      rw [mulVec_single_smul, hji, smul_single_one]
    have hjk : j = k := by
      have e1 : j.val < k.val + 1 := by
        by_contra hlt
        have h1 := (hB (Pi.single k (α ^ (k.val + 1)))).2 (by
          rw [hmul]
          exact (single_mem_iff hα h0 j (by omega)).2 (by omega))
        have := (single_mem_iff hα h0 k (by omega)).1 h1
        omega
      have e2 : k.val < j.val + 1 := by
        by_contra hlt
        have h1 : Pi.single j (α ^ (j.val + 1)) ∉ Blue F n α := fun h =>
          absurd ((single_mem_iff hα h0 j (by omega)).1 h) (by omega)
        apply h1
        rw [← hmul (α ^ (j.val + 1))]
        have h2 := (hB (Pi.single k (α ^ (j.val + 1)))).1
        apply h2
        exact (single_mem_iff hα h0 k (by omega)).2 (by omega)
      exact Fin.ext (by omega)
    subst hjk
    simpa using hji
  apply Units.ext
  ext i k
  have := congrFun (key k) i
  rw [mulVec_single_one] at this
  rw [← hM]
  simpa [Matrix.one_apply, Pi.single_apply] using this

theorem blue_finite (F : Type*) [Field F] (n : ℕ) (α : F) : (Blue F n α).Finite := by
  classical
  refine (Set.finite_range (fun p : Fin n × Fin (n + 1) => (Pi.single p.1 (α ^ p.2.val) : Fin n → F))).subset ?_
  rintro v ⟨j, i, hi, rfl⟩
  exact ⟨(j, ⟨i, by omega⟩), rfl⟩

end

/-- **Melody Chan's theorem.** Let `F` be a field, infinite or finite with `|F| > n + 1`. Then the vectors of `Fⁿ` can be
coloured Green or Blue (`Blue` a set, `Green` its complement) so that for every invertible `n × n` matrix `B` other than
the identity there is a Green vector `v` with `B v` Blue. -/
theorem exists_blue (F : Type*) [Field F] (n : ℕ) (hF : Infinite F ∨ ∃ _ : Fintype F, n + 1 < Fintype.card F) :
    ∃ Blue : Set (Fin n → F), ∀ B : GL (Fin n) F, B ≠ 1 →
      ∃ v : Fin n → F, v ∉ Blue ∧ (B : Matrix (Fin n) (Fin n) F) *ᵥ v ∈ Blue := by
  obtain ⟨α, h0, hα⟩ := exists_alpha F n hF
  refine ⟨Blue F n α, fun B hB1 => ?_⟩
  by_contra hcon
  push Not at hcon
  apply hB1
  apply blue_stable_eq_one hα h0 B
  intro v
  have hsub : ((fun w => (B : Matrix (Fin n) (Fin n) F) *ᵥ w) ⁻¹' Blue F n α) ⊆ Blue F n α := by
    intro w hw
    by_contra hw'
    exact hcon w hw' hw
  have hinj : Function.Injective (fun w : Fin n → F => (B : Matrix (Fin n) (Fin n) F) *ᵥ w) := by
    intro a b hab
    have := congrArg (fun w => ((B⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ w) hab
    simpa [Matrix.mulVec_mulVec] using this
  have hrange : Blue F n α ⊆ Set.range (fun w : Fin n → F => (B : Matrix (Fin n) (Fin n) F) *ᵥ w) := by
    intro w _
    refine ⟨((B⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ w, ?_⟩
    simp [Matrix.mulVec_mulVec]
  have hcard := Set.ncard_preimage_of_injective_subset_range hinj hrange
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard.ge (blue_finite F n α)
  constructor
  · intro hv
    rw [← heq] at hv
    exact hv
  · intro hv
    exact hsub hv

end Chan
