/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Combinatorics.Additive.SubsetSum
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.IntervalCases

/-!
# Intervals of subset sums and the parity of a signed half sum

Two small statements on weighted sums of a sign sequence: how an interval of subset sums grows
when an element is adjoined, and the parity of `∑_{c ≤ m} c ε(c)` for a sequence of signs.

## Main results

* `IntervalosFilas.intervalos_a`: if the subset sums `Σ(A)` contain `[α, β]` and
  `0 < x ≤ β − α + 1`, `x ∉ A`, then `Σ(A ∪ {x}) ⊇ [α, β + x]`.
* `IntervalosFilas.SS_symm`, `IntervalosFilas.intervalos_a_sym`: `Σ(A)` is symmetric under
  `y ↦ P_A − y` (`P_A` the sum of `A`), so an interval reaching `P_A / 2` extends to
  `[α, P_A − α]`.
* `IntervalosFilas.filas_parity`: for signs `ε(c) = ±1`, `∑_{c ≤ m} c ε(c) ≡ (n² − 1)/8 (mod 2)`
  with `n = 2m + 1`.
* `IntervalosFilas.filas_vanish`: the sum vanishes only if the Jacobi symbol `(2/n)` is `1`.
* `IntervalosFilas.filas_char`: the same for `T(m, χ)`, `χ` a quadratic character modulo `f`
  with `gcd(f, m!) = 1`.

## References

* C. Marín, *Zeros of weighted partial sums of completely multiplicative functions: Dirichlet
  characters, the Euler factor at 2 and Conrey's sine series*, Zenodo (2026),
  doi:10.5281/zenodo.22847374.
-/

@[expose] public section

open Finset

namespace IntervalosFilas

/-! ## `lem:intervalos` (a) -/

/-- `Σ(A)`: the set of subset sums of a finite set `A ⊆ ℕ`. -/
abbrev SS (A : Finset ℕ) : Finset ℕ := A.subsetSum

lemma mem_SS {A : Finset ℕ} {y : ℕ} : y ∈ SS A ↔ ∃ B ⊆ A, ∑ b ∈ B, b = y :=
  mem_subsetSum_iff

lemma SS_mono {A A' : Finset ℕ} (h : A ⊆ A') {y : ℕ} (hy : y ∈ SS A) : y ∈ SS A' :=
  subsetSum_mono h hy

/-- **`lem:intervalos` (a), first sentence.** If `Σ(A) ⊇ [α, β]`, `x ∉ A` and
`0 < x ≤ β − α + 1`, then `Σ(A ∪ {x}) ⊇ [α, β + x]`. -/
theorem intervalos_a {A : Finset ℕ} {α β x : ℕ} (hA : ∀ y ∈ Icc α β, y ∈ SS A) (hx : x ∉ A)
    (_hx0 : 0 < x) (hxb : x + α ≤ β + 1) : ∀ y ∈ Icc α (β + x), y ∈ SS (insert x A) := by
  intro y hy
  rw [mem_Icc] at hy
  by_cases hyb : y ≤ β
  · exact SS_mono (subset_insert x A) (hA y (mem_Icc.mpr ⟨hy.1, hyb⟩))
  · obtain ⟨B, hB, hBs⟩ := mem_SS.mp (hA (y - x) (mem_Icc.mpr ⟨by omega, by omega⟩))
    refine mem_SS.mpr ⟨insert x B, insert_subset_insert x hB, ?_⟩
    rw [sum_insert (fun h => hx (hB h)), hBs]
    omega

/-- **`lem:intervalos` (a): "`Σ(A)` is symmetric under `x ↦ P_A − x`"**, `P_A = ∑_{a∈A} a`. -/
theorem SS_symm {A : Finset ℕ} {y : ℕ} (hy : y ∈ SS A) :
    y ≤ ∑ a ∈ A, a ∧ (∑ a ∈ A, a) - y ∈ SS A := by
  obtain ⟨B, hB, rfl⟩ := mem_SS.mp hy
  have h : ∑ b ∈ A \ B, b + ∑ b ∈ B, b = ∑ a ∈ A, a := sum_sdiff hB
  refine ⟨by omega, mem_SS.mpr ⟨A \ B, sdiff_subset, by omega⟩⟩

/-- **`lem:intervalos` (a), second sentence.** `Σ(A) ⊇ [α, β]` with `β ≥ P_A/2` implies
`Σ(A) ⊇ [α, P_A − α]`. -/
theorem intervalos_a_sym {A : Finset ℕ} {α β : ℕ} (hA : ∀ y ∈ Icc α β, y ∈ SS A)
    (hβ : ∑ a ∈ A, a ≤ 2 * β) : ∀ y ∈ Icc α ((∑ a ∈ A, a) - α), y ∈ SS A := by
  intro y hy
  rw [mem_Icc] at hy
  by_cases hyb : y ≤ β
  · exact hA y (mem_Icc.mpr ⟨hy.1, hyb⟩)
  · have h1 := hA ((∑ a ∈ A, a) - y) (mem_Icc.mpr ⟨by omega, by omega⟩)
    have h2 := (SS_symm h1).2
    rwa [show (∑ a ∈ A, a) - ((∑ a ∈ A, a) - y) = y by omega] at h2

/-! ## `prop:filas` -/

/-- `∑_{c=1}^{m} c = m(m+1)/2`, in the form `2 ∑ c = m(m+1)`. -/
lemma two_mul_sum_id (m : ℕ) : 2 * ∑ c ∈ Icc 1 m, (c : ℤ) = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_Icc_succ_top (by omega), mul_add, ih]; push_cast; ring

/-- `(n² − 1)/8 = m(m+1)/2` for `n = 2m+1`. -/
lemma eighth (m : ℕ) : (((2 * m + 1 : ℕ) : ℤ) ^ 2 - 1) / 8 = ∑ c ∈ Icc 1 m, (c : ℤ) := by
  have h := two_mul_sum_id m
  rw [show (((2 * m + 1 : ℕ) : ℤ) ^ 2 - 1) = 8 * ∑ c ∈ Icc 1 m, (c : ℤ) by push_cast; linarith]
  exact Int.mul_ediv_cancel_left _ (by norm_num)

/-- **`prop:filas`, the congruence.** For `n = 2m+1` and any `ε` with values `±1` on `1, …, m`,
`∑_{c=1}^{m} c ε(c) ≡ (n² − 1)/8 (mod 2)`. -/
theorem filas_parity (m : ℕ) (ε : ℕ → ℤ) (hε : ∀ c ∈ Icc 1 m, ε c = 1 ∨ ε c = -1) :
    ∑ c ∈ Icc 1 m, (c : ℤ) * ε c ≡ (((2 * m + 1 : ℕ) : ℤ) ^ 2 - 1) / 8 [ZMOD 2] := by
  rw [eighth, Int.modEq_iff_dvd]
  rw [← sum_sub_distrib]
  apply dvd_sum
  intro c hc
  rcases hε c hc with h | h <;> rw [h]
  · exact ⟨0, by ring⟩
  · exact ⟨c, by ring⟩

/-- `(n² − 1)/8` even, for `n = 2m+1`, iff `n ≡ ±1 (mod 8)`. -/
lemma even_eighth_iff (m : ℕ) :
    (2 : ℤ) ∣ ∑ c ∈ Icc 1 m, (c : ℤ) ↔ (2 * m + 1) % 8 = 1 ∨ (2 * m + 1) % 8 = 7 := by
  have h := two_mul_sum_id m
  constructor
  · rintro ⟨t, ht⟩
    rw [ht] at h
    have h4 : (4 : ℤ) ∣ (m : ℤ) * (m + 1) := ⟨t, by linarith⟩
    have h4' : 4 ∣ m * (m + 1) := by exact_mod_cast h4
    have hm : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
    rw [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.add_mod] at h4'
    interval_cases hh : m % 4 <;> simp_all <;> omega
  · intro h8
    have hm : m % 4 = 0 ∨ m % 4 = 3 := by omega
    have h4 : (4 : ℤ) ∣ (m : ℤ) * (m + 1) := by
      rcases hm with hm | hm
      · obtain ⟨s, hs⟩ : 4 ∣ m := Nat.dvd_of_mod_eq_zero hm
        exact ⟨s * (m + 1), by rw [hs]; push_cast; ring⟩
      · obtain ⟨s, hs⟩ : 4 ∣ m + 1 := by omega
        have hs' : (m : ℤ) + 1 = 4 * s := by exact_mod_cast hs
        exact ⟨m * s, by rw [hs']; ring⟩
    obtain ⟨t, ht⟩ := h4
    exact ⟨t, by linarith⟩

/-- **`prop:filas`, "so it can vanish only if `(2/n) = 1`"** (Jacobi symbol, `n = 2m+1`), through
the second supplementary law `J(2 | n) = χ₈(n)` (`jacobiSym.at_two`). -/
theorem filas_vanish (m : ℕ) (ε : ℕ → ℤ) (hε : ∀ c ∈ Icc 1 m, ε c = 1 ∨ ε c = -1)
    (h0 : ∑ c ∈ Icc 1 m, (c : ℤ) * ε c = 0) : jacobiSym 2 (2 * m + 1) = 1 := by
  have hp := filas_parity m ε hε
  rw [h0, eighth] at hp
  have h2 : (2 : ℤ) ∣ ∑ c ∈ Icc 1 m, (c : ℤ) := by
    have := (Int.modEq_iff_dvd.mp hp); simpa using this
  have h8 := (even_eighth_iff m).mp h2
  rw [jacobiSym.at_two ⟨m, rfl⟩, ZMod.χ₈_nat_eq_if_mod_eight]
  rw [ite_eq_right (by omega), ite_eq_left h8]

/-- `T(m, χ) = ∑_{c=1}^{m} c χ(c)` for a character `χ` modulo `f`. -/
def T {f : ℕ} (m : ℕ) (χ : MulChar (ZMod f) ℤ) : ℤ := ∑ c ∈ Icc 1 m, (c : ℤ) * χ (c : ZMod f)

/-- A quadratic character takes the values `±1` at the residues prime to its modulus. -/
lemma quad_unit {f c : ℕ} (χ : MulChar (ZMod f) ℤ) (hχ : χ.IsQuadratic) (hc : Nat.Coprime c f) :
    χ (c : ZMod f) = 1 ∨ χ (c : ZMod f) = -1 := by
  rcases hχ (c : ZMod f) with h | h | h
  · exfalso
    set u := ZMod.unitOfCoprime c hc
    have hu : ((u : ZMod f)) = (c : ZMod f) := ZMod.coe_unitOfCoprime c hc
    have h1 : χ (u : ZMod f) * χ ((u⁻¹ : (ZMod f)ˣ) : ZMod f) = 1 := by
      rw [← map_mul, Units.mul_inv, MulChar.map_one]
    rw [hu, h, zero_mul] at h1
    exact zero_ne_one h1
  · exact Or.inl h
  · exact Or.inr h

/-- **`prop:filas`, "In particular".** If `χ` is a quadratic character modulo `f` with
`gcd(f, m!) = 1`, then `T(m, χ) = 0` forces `(2/n) = 1`, `n = 2m+1`. (Primitivity is not used.) -/
theorem filas_char {f m : ℕ} (χ : MulChar (ZMod f) ℤ) (hχ : χ.IsQuadratic)
    (hf : Nat.Coprime f m.factorial) (h0 : T m χ = 0) : jacobiSym 2 (2 * m + 1) = 1 := by
  apply filas_vanish m (fun c => χ (c : ZMod f)) _ h0
  intro c hc
  rw [mem_Icc] at hc
  apply quad_unit χ hχ
  exact (Nat.Coprime.coprime_dvd_right (Nat.dvd_factorial hc.1 hc.2) hf).symm

/-! ## Controls -/

/-- The paper's remark: at `f = 35`, `m = 6` the values `1, −1, 1, 1, 0, −1` give
`1 − 2 + 3 + 4 + 0 − 6 = 0` although `n = 13 ≢ ±1 (mod 8)`: the hypothesis `gcd(f, m!) = 1`
(through the values `±1`) is needed. -/
example : (1 : ℤ) * 1 + 2 * (-1) + 3 * 1 + 4 * 1 + 5 * 0 + 6 * (-1) = 0 ∧ 13 % 8 = 5 := by
  decide

/-- `m = 3`: `1 + 2 − 3 = 0`, and `n = 7 ≡ −1 (mod 8)`. -/
example : jacobiSym 2 (2 * 3 + 1) = 1 :=
  filas_vanish 3 (fun c => if c = 3 then -1 else 1) (by decide) (by decide)

end IntervalosFilas

