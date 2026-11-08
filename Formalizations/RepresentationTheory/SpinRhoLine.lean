/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
-- encaje: identidades de producto de senos y valores espinoriales en la recta de ρ (tipos B, D)
module

public import Mathlib.RingTheory.RootsOfUnity.Lemmas
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Sine products and the spin values on the ρ-line of types B and D

Classical trigonometric identities (the product of sines `∏_{k=1}^{n-1} 2 sin(kπ/n) = n`, the
Dirichlet kernel, the index shift of `sin`) and their consequences for the spin values on the
ρ-line: the spin representation of `B_m` gives `∏_{j=1}^{m} 2 sin(jπ/(2m+1)) = √(2m+1)` (and its
cosine form) and the half-spin representations of `D_m` give `∏_{j=1}^{m-1} 2 sin(jπ/(2m)) = √m`.
The values `√(2m+1)` and `√m` are known in the literature as level-2 quantum dimensions
(Gannon; Gannon–Schopieray); the formalization is ours. The product of sines is derived from
`IsPrimitiveRoot.prod_pow_sub_one_eq_order` via `|e^{2πik/n} - 1| = 2 sin(πk/n)`.

## Main results

* `SpinRhoLine.prod_two_sin`: `∏_{k=1}^{n-1} 2 sin(kπ/n) = n` for `n ≥ 1`
* `SpinRhoLine.spin_B`, `SpinRhoLine.spin_B_cos`: the type-B spin value `√(2m+1)`
* `SpinRhoLine.halfspin_D`: the type-D half-spin value `√m`
* `SpinRhoLine.dirichlet`: `1 + ∑_{j=1}^{m} 2 cos(2πj/q) = sin((2m+1)π/q) / sin(π/q)`
* `SpinRhoLine.index_shift`, `SpinRhoLine.index_shift_div`: `sin((hq+r)π/q) = (-1)^h sin(rπ/q)`
* `SpinRhoLine.sqrt_two_mul_add_one_eq_nat_iff`, `SpinRhoLine.sqrt_eq_nat_iff`: `√(2m+1)`
  (resp. `√m`) is a natural number iff `2m+1` (resp. `m`) is a perfect square
-/

@[expose] public section

open Real Finset

namespace SpinRhoLine

/-- `|e^{2πik/n} - 1| = |2 sin(kπ/n)|`. -/
lemma norm_exp_pow_sub_one (n k : ℕ) :
    ‖Complex.exp (2 * π * Complex.I / n) ^ k - 1‖ = ‖2 * Real.sin (k * π / n)‖ := by
  rw [← Complex.exp_nat_mul]
  have : (k : ℂ) * (2 * π * Complex.I / n) = Complex.I * ((2 * k * π / n : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, Complex.norm_exp_I_mul_ofReal_sub_one, show 2 * k * π / n / 2 = k * π / n by ring]

lemma sin_nat_pos {k n : ℕ} (hk : 0 < k) (hkn : k < n) : 0 < Real.sin (k * π / n) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hkn' : (k : ℝ) < n := by exact_mod_cast hkn
  have hn' : (0 : ℝ) < n := by linarith
  apply sin_pos_of_pos_of_lt_pi (by positivity)
  rw [div_lt_iff₀ hn']
  nlinarith [pi_pos]

/-- Reflection `sin(aπ/D) = sin(bπ/D)` when `a + b = D`. -/
lemma sin_reflect {a b D : ℕ} (h : a + b = D) (hD : D ≠ 0) :
    Real.sin (a * π / D) = Real.sin (b * π / D) := by
  rw [← sin_pi_sub]
  congr 1
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  have hab : (a : ℝ) = D - b := by rw [← h]; push_cast; ring
  rw [hab]
  field_simp
  ring

/-- Product of sines, `range` form: `∏_{k<N} 2 sin((k+1)π/(N+1)) = N+1`. -/
theorem prod_two_sin_range (N : ℕ) :
    ∏ k ∈ range N, 2 * Real.sin (((k + 1 : ℕ) : ℝ) * π / ((N + 1 : ℕ) : ℝ)) =
      ((N + 1 : ℕ) : ℝ) := by
  have hμ := Complex.isPrimitiveRoot_exp (N + 1) (Nat.succ_ne_zero N)
  have h := congrArg norm (hμ.prod_pow_sub_one_eq_order)
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_prod] at h
  have h2 : ‖((N : ℂ) + 1)‖ = ((N + 1 : ℕ) : ℝ) := by
    rw [show ((N : ℂ) + 1) = ((N + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
  rw [h2] at h
  refine Eq.trans ?_ h
  refine prod_congr rfl (fun k hk => ?_)
  rw [mem_range] at hk
  rw [norm_exp_pow_sub_one, Real.norm_eq_abs, abs_of_pos]
  exact mul_pos two_pos (sin_nat_pos (n := N + 1) (Nat.succ_pos k) (by omega))

/-- **Product of sines.** For `n ≥ 1`, `∏_{k=1}^{n-1} 2 sin(kπ/n) = n`. -/
theorem prod_two_sin (n : ℕ) (hn : 1 ≤ n) :
    ∏ k ∈ Ico 1 n, 2 * Real.sin (k * π / n) = n := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  rw [prod_Ico_eq_prod_range, Nat.add_sub_cancel]
  refine Eq.trans ?_ (prod_two_sin_range N)
  refine prod_congr rfl (fun k _ => ?_)
  rw [add_comm 1 k]

/-- Type B, squared form, in `range` notation. -/
lemma spin_B_range_sq (m : ℕ) :
    (∏ k ∈ range m, 2 * Real.sin (((k + 1 : ℕ) : ℝ) * π / ((2 * m + 1 : ℕ) : ℝ))) ^ 2 =
      ((2 * m + 1 : ℕ) : ℝ) := by
  set f : ℕ → ℝ := fun j => 2 * Real.sin ((j : ℝ) * π / ((2 * m + 1 : ℕ) : ℝ)) with hf
  have h := prod_two_sin_range (2 * m)
  have hsplit : ∏ k ∈ range (2 * m), f (k + 1) =
      (∏ k ∈ range m, f (k + 1)) * ∏ k ∈ range m, f (m + k + 1) := by
    rw [two_mul, prod_range_add]
  have hrefl : ∏ k ∈ range m, f (m + k + 1) = ∏ k ∈ range m, f (k + 1) := by
    refine Eq.trans ?_ (prod_range_reflect (fun k => f (k + 1)) m)
    refine prod_congr rfl (fun k hk => ?_)
    rw [mem_range] at hk
    simp only [hf]
    rw [sin_reflect (a := m + k + 1) (b := m - 1 - k + 1) (by omega) (by omega)]
  have : ∏ k ∈ range (2 * m), f (k + 1) = ((2 * m + 1 : ℕ) : ℝ) := h
  rw [hsplit, hrefl] at this
  rw [sq]
  exact this

lemma spin_B_range (m : ℕ) :
    ∏ k ∈ range m, 2 * Real.sin (((k + 1 : ℕ) : ℝ) * π / ((2 * m + 1 : ℕ) : ℝ)) =
      Real.sqrt ((2 * m + 1 : ℕ) : ℝ) := by
  have hnn : 0 ≤ ∏ k ∈ range m,
      2 * Real.sin (((k + 1 : ℕ) : ℝ) * π / ((2 * m + 1 : ℕ) : ℝ)) := by
    refine prod_nonneg (fun k hk => ?_)
    rw [mem_range] at hk
    exact (mul_pos two_pos (sin_nat_pos (n := 2 * m + 1) (Nat.succ_pos k) (by omega))).le
  conv_rhs => rw [← spin_B_range_sq m]
  rw [Real.sqrt_sq hnn]

/-- **Type B spin value.** `∏_{j=1}^{m} 2 sin(jπ/(2m+1)) = √(2m+1)` (also true for `m = 0`). -/
theorem spin_B (m : ℕ) :
    ∏ j ∈ Ico 1 (m + 1), 2 * Real.sin (j * π / (2 * m + 1)) = Real.sqrt (2 * m + 1) := by
  have h := spin_B_range m
  push_cast at h
  rw [prod_Ico_eq_prod_range, Nat.add_sub_cancel, ← h]
  refine prod_congr rfl (fun k _ => ?_)
  push_cast
  ring_nf

/-- **Type B spin value, cosine form.** `∏_{i=1}^{m} 2 cos((2i-1)π/(4m+2)) = √(2m+1)`. -/
theorem spin_B_cos (m : ℕ) :
    ∏ i ∈ Ico 1 (m + 1), 2 * Real.cos ((2 * i - 1) * π / (4 * m + 2)) =
      Real.sqrt (2 * m + 1) := by
  have h := spin_B_range m
  rw [← prod_range_reflect] at h
  push_cast at h
  rw [prod_Ico_eq_prod_range, Nat.add_sub_cancel, ← h]
  refine prod_congr rfl (fun k hk => ?_)
  rw [mem_range] at hk
  have hc : ((m - 1 - k : ℕ) : ℝ) = m - 1 - k := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  rw [hc, ← sin_pi_div_two_sub]
  congr 2
  have hm : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
  have hm' : (4 * (m : ℝ) + 2) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **Type D half-spin value.** For `m ≥ 1`, `∏_{j=1}^{m-1} 2 sin(jπ/(2m)) = √m`. -/
theorem halfspin_D (m : ℕ) (hm : 1 ≤ m) :
    ∏ j ∈ Ico 1 m, 2 * Real.sin (j * π / (2 * m)) = Real.sqrt m := by
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
  set f : ℕ → ℝ := fun j => 2 * Real.sin ((j : ℝ) * π / ((2 * M + 1 + 1 : ℕ) : ℝ)) with hf
  have h : ∏ k ∈ range (2 * M + 1), f (k + 1) = ((2 * M + 1 + 1 : ℕ) : ℝ) :=
    prod_two_sin_range (2 * M + 1)
  have hsplit : ∏ k ∈ range (2 * M + 1), f (k + 1) =
      (∏ k ∈ range M, f (k + 1)) * ((∏ k ∈ range M, f (M + k + 2)) * f (M + 1)) := by
    rw [show 2 * M + 1 = M + (M + 1) by ring, prod_range_add, prod_range_succ']
    rfl
  have hmid : f (M + 1) = 2 := by
    simp only [hf]
    have : ((M + 1 : ℕ) : ℝ) * π / ((2 * M + 1 + 1 : ℕ) : ℝ) = π / 2 := by
      push_cast; field_simp; ring
    rw [this, sin_pi_div_two, mul_one]
  have hrefl : ∏ k ∈ range M, f (M + k + 2) = ∏ k ∈ range M, f (k + 1) := by
    refine Eq.trans ?_ (prod_range_reflect (fun k => f (k + 1)) M)
    refine prod_congr rfl (fun k hk => ?_)
    rw [mem_range] at hk
    simp only [hf]
    rw [sin_reflect (a := M + k + 2) (b := M - 1 - k + 1) (by omega) (by omega)]
  rw [hsplit, hrefl, hmid] at h
  have hsq : (∏ k ∈ range M, f (k + 1)) ^ 2 = ((M + 1 : ℕ) : ℝ) := by
    push_cast at h ⊢; nlinarith [h]
  have hnn : 0 ≤ ∏ k ∈ range M, f (k + 1) := by
    refine prod_nonneg (fun k hk => ?_)
    rw [mem_range] at hk
    exact (mul_pos two_pos (sin_nat_pos (n := 2 * M + 1 + 1) (Nat.succ_pos k) (by omega))).le
  conv_rhs => rw [← hsq]
  rw [Real.sqrt_sq hnn, prod_Ico_eq_prod_range, Nat.add_sub_cancel]
  refine prod_congr rfl (fun k _ => ?_)
  simp only [hf]
  push_cast
  ring_nf

/-- Dirichlet kernel, multiplied form, for any `x`. -/
lemma sin_mul_dirichlet (x : ℝ) (m : ℕ) :
    Real.sin x * (1 + ∑ j ∈ range m, 2 * Real.cos (2 * ((j : ℝ) + 1) * x)) =
      Real.sin ((2 * m + 1) * x) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ← add_assoc, mul_add, ih]
    push_cast
    rw [show (2 * (m : ℝ) + 1) * x = (2 * m + 2) * x - x by ring,
      show (2 * ((m : ℝ) + 1) + 1) * x = (2 * m + 2) * x + x by ring,
      show 2 * ((m : ℝ) + 1) * x = (2 * m + 2) * x by ring, sin_add, sin_sub]
    ring

/-- **Dirichlet kernel.** For `q ≥ 2`, `1 + ∑_{j=1}^{m} 2 cos(2πj/q) = sin((2m+1)π/q)/sin(π/q)`. -/
theorem dirichlet (q m : ℕ) (hq : 2 ≤ q) :
    1 + ∑ j ∈ Icc 1 m, 2 * Real.cos (2 * π * j / q) =
      Real.sin ((2 * m + 1) * π / q) / Real.sin (π / q) := by
  have hs : 0 < Real.sin (π / q) := by
    have := sin_nat_pos (k := 1) (n := q) one_pos (by omega)
    simpa using this
  have hIcc : Icc 1 m = Ico 1 (m + 1) := by ext; simp only [mem_Icc, mem_Ico]; omega
  rw [eq_div_iff hs.ne', hIcc, sum_Ico_eq_sum_range, Nat.add_sub_cancel, mul_comm,
    show (2 * (m : ℝ) + 1) * π / q = (2 * m + 1) * (π / q) by ring, ← sin_mul_dirichlet]
  congr 2
  refine sum_congr rfl (fun k _ => ?_)
  push_cast
  ring_nf

/-- **Index shift.** For `q ≥ 1`, `sin((hq+r)π/q) = (-1)^h sin(rπ/q)`. -/
theorem index_shift (q h r : ℕ) (hq : 1 ≤ q) :
    Real.sin ((h * q + r) * π / q) = (-1) ^ h * Real.sin (r * π / q) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  rw [show ((h : ℝ) * q + r) * π / q = r * π / q + h * π by field_simp; ring]
  exact sin_add_nat_mul_pi _ _

/-- **Index shift, divided form.** -/
theorem index_shift_div (q h r : ℕ) (hq : 1 ≤ q) :
    Real.sin ((h * q + r) * π / q) / Real.sin (π / q) =
      (-1) ^ h * (Real.sin (r * π / q) / Real.sin (π / q)) := by
  rw [index_shift q h r hq, mul_div_assoc]

/-- `√n` is a natural number iff `n` is a perfect square. -/
theorem sqrt_eq_nat_iff (n : ℕ) : (∃ k : ℕ, Real.sqrt n = k) ↔ IsSquare n := by
  constructor
  · rintro ⟨k, hk⟩
    have : (n : ℝ) = k * k := by
      rw [← hk]; exact (Real.mul_self_sqrt (Nat.cast_nonneg n)).symm
    exact ⟨k, by exact_mod_cast this⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, by rw [hr]; push_cast; exact Real.sqrt_mul_self (Nat.cast_nonneg r)⟩

/-- **Corollary (type B).** `√(2m+1)` is a natural number iff `2m+1` is a perfect square. -/
theorem sqrt_two_mul_add_one_eq_nat_iff (m : ℕ) :
    (∃ k : ℕ, Real.sqrt (2 * m + 1) = k) ↔ IsSquare (2 * m + 1) := by
  have := sqrt_eq_nat_iff (2 * m + 1)
  push_cast at this
  exact this

/-- **Corollary (type B), product form.** The spin value is an integer iff `2m+1` is a square. -/
theorem spin_B_eq_nat_iff (m : ℕ) :
    (∃ k : ℕ, ∏ j ∈ Ico 1 (m + 1), 2 * Real.sin (j * π / (2 * m + 1)) = k) ↔
      IsSquare (2 * m + 1) := by
  rw [spin_B]; exact sqrt_two_mul_add_one_eq_nat_iff m

/-- **Corollary (type D), product form.** The half-spin value is an integer iff `m` is a square. -/
theorem halfspin_D_eq_nat_iff (m : ℕ) (hm : 1 ≤ m) :
    (∃ k : ℕ, ∏ j ∈ Ico 1 m, 2 * Real.sin (j * π / (2 * m)) = k) ↔ IsSquare m := by
  rw [halfspin_D m hm]; exact sqrt_eq_nat_iff m

end SpinRhoLine
