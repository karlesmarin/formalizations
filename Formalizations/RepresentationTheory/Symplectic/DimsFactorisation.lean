/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.RepresentationTheory.Symplectic.RhoLine
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Vandermonde

/-!
# The value on the ρ-line at `k = 2` (Theorem 8.1, `conj:val`), by pairs

Arithmetic of integers on the right-hand side of `RhoLine.thm_valgen`.  For `q = m + 1`
(`d = 2`) every pair of `ρ` divisible by `q` equals `q`, hence
`∏_{q ∣ b} b = q ^ N_q ρ` and the ratio of `thm_valgen` is `∏_{q ∣ a} (a / q)`.

Stage A of the commission only; the form "one factor per folded class `D_c`" is NOT done here.
-/

@[expose] public section

namespace RhoLine

open ResidueCapacity

/-- Every pair of `ρ_m` lies in `(0, 2m]`. -/
lemma rhoZ_pairs_le (m : ℕ) : ∀ a ∈ pairs (rhoZ m), a ≤ 2 * (m : ℤ) := by
  induction m with
  | zero => simp [pairs, rhoZ, posRootVals]
  | succ m ih =>
    intro a ha
    rw [pairs, rhoZ_succ] at ha
    simp only [posRootVals, List.mem_cons, List.mem_append, List.mem_flatMap] at ha
    rcases ha with (rfl | ⟨b, hb, hab⟩) | ha
    · rw [two_nsmul]; push_cast; omega
    · have := mem_rhoZ hb
      simp only [List.not_mem_nil, or_false] at hab
      rcases hab with rfl | rfl <;> push_cast <;> omega
    · have := ih a ha
      push_cast; omega

/-- `rho_div_pairs_eq_q`: for `q = m + 1`, every pair of `ρ` divisible by `q` equals `q`. -/
theorem rho_div_pairs_eq_q (m : ℕ) {q : ℕ} (hq : q = m + 1) :
    ∀ b ∈ pairs (rhoZ m), (q : ℤ) ∣ b → b = q := by
  intro b hb hd
  have h1 := rhoZ_pairs_pos m b hb
  have h2 := rhoZ_pairs_le m b hb
  obtain ⟨c, rfl⟩ := hd
  subst hq
  push_cast at h1 h2 ⊢
  have hc1 : 0 < c := by nlinarith
  have hc2 : c < 2 := by nlinarith
  have : c = 1 := by omega
  subst this; ring

lemma prod_const_of_forall (L : List ℤ) (q : ℤ) (h : ∀ b ∈ L, b = q) :
    (L.map fun b : ℤ => (b : ℚ)).prod = (q : ℚ) ^ L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha := h a (List.mem_cons_self ..)
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ, ha]
    rw [ih fun b hb => h b (List.mem_cons_of_mem _ hb)]
    ring

lemma prod_div_const (L : List ℤ) (q : ℚ) :
    (L.map fun a : ℤ => (a : ℚ) / q).prod = (L.map fun a : ℤ => (a : ℚ)).prod / q ^ L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ, ih]
    rw [div_mul_div_comm]; ring

lemma length_filter_eq_N (q : ℕ) (x : List ℤ) :
    ((pairs x).filter fun a => (q : ℤ) ∣ a).length = N q x := by
  unfold N Ncount
  rw [List.countP_eq_length_filter]

/-- `∏_{q ∣ b} b = q ^ N_q ρ` for `q = m + 1`. -/
theorem prod_rho_div (m : ℕ) {q : ℕ} (hq : q = m + 1) :
    (((pairs (rhoZ m)).filter fun b => (q : ℤ) ∣ b).map fun b : ℤ => (b : ℚ)).prod =
      (q : ℚ) ^ N q (rhoZ m) := by
  have := prod_const_of_forall ((pairs (rhoZ m)).filter fun b => (q : ℤ) ∣ b) q
    (fun b hb => by
      obtain ⟨hb1, hb2⟩ := List.mem_filter.1 hb
      exact rho_div_pairs_eq_q m hq b hb1 (by simpa using hb2))
  rw [this, length_filter_eq_N]
  simp

/-- **Theorem 8.1 (`conj:val`), `k = 2`, by pairs.**  `q = m + 1`, `N_q ℓ = N_q ρ`:
`∏_{q ∣ a} a / ∏_{q ∣ b} b = ∏_{q ∣ a} (a / q)` in `ℚ`. -/
theorem thm_val_k2 (m : ℕ) {q : ℕ} (hq : q = m + 1) (l : List ℤ)
    (hN : N q l = N q (rhoZ m)) :
    (((pairs l).filter fun a => (q : ℤ) ∣ a).map fun a : ℤ => (a : ℚ)).prod /
        (((pairs (rhoZ m)).filter fun b => (q : ℤ) ∣ b).map fun b : ℤ => (b : ℚ)).prod =
      (((pairs l).filter fun a => (q : ℤ) ∣ a).map fun a : ℤ => (a : ℚ) / q).prod := by
  rw [prod_rho_div m hq, prod_div_const, length_filter_eq_N, hN]

/-- **Theorem 8.1 (`conj:val`), `k = 2`, on the modulus.**  `d = 2`, `q = m + 1`:
`‖Q(ζ)‖ = ∏_{a ∈ pairs ℓ, q ∣ a} (a / q)` in `ℝ`. -/
theorem thm_val_k2_norm {q m : ℕ} (hq : q = m + 1) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ q)
    (l : List ℤ) (hl : l.length = m) (hpl : ∀ a ∈ pairs l, 0 < a)
    (hN : N q l = N q (rhoZ m)) (Q : Polynomial ℂ)
    (hQ : F ℂ (rhoZ m) * Q = F ℂ l) :
    ‖Q.eval ζ‖ = (((pairs l).filter fun a => (q : ℤ) ∣ a).map
      fun a : ℤ => (a : ℝ) / q).prod := by
  have hqpos : 0 < q := by omega
  have hd : 2 * q = 2 * m + 2 := by omega
  rw [thm_valgen hqpos hd hζ l hl hpl hN Q hQ]
  have h := thm_val_k2 m hq l hN
  have h' := congrArg (fun r : ℚ => (r : ℝ)) h
  simp only [Rat.cast_div, Rat.cast_list_prod, List.map_map, Function.comp_def,
    Rat.cast_intCast, Rat.cast_natCast] at h'
  exact h'

/-! ## Stage B (partial): the dimension formulas and the Weyl-shift identities

Index-based transcription (0-indexed) of `dim_gl`, `dim_sp`, `dim_so_odd` of `anc/dims_recuento.py`,
valued in `ℚ`.  Only the algebraic core of Stage B is done here (B1-B3 as shift identities);
the combinatorial assembly over folded classes (B4) is NOT done. -/

/-- `∏_{i<j<n} (l_i - l_j)`. -/
def vdm (n : ℕ) (l : ℕ → ℚ) : ℚ :=
  ∏ i ∈ Finset.range n, ∏ j ∈ Finset.Ico (i + 1) n, (l i - l j)

/-- Type-`C`/`B` Weyl numerator `∏_i l_i ∏_{i<j} (l_i - l_j)(l_i + l_j)`. -/
def weylC (n : ℕ) (l : ℕ → ℚ) : ℚ :=
  ∏ i ∈ Finset.range n, (l i * ∏ j ∈ Finset.Ico (i + 1) n, ((l i - l j) * (l i + l j)))

/-- `dim_gl`: `∏_{i<j}(ν_i - ν_j + j - i) / ∏_{j<n} j!`. -/
def dimGl (n : ℕ) (ν : ℕ → ℤ) : ℚ :=
  vdm n (fun i => ((ν i : ℚ) + ((n : ℚ) - i - 1))) / ∏ j ∈ Finset.range n, ((j.factorial : ℕ) : ℚ)

/-- `dim_sp`: Weyl numerator at `ν + ρ_C`, `ρ_C = (n, …, 1)`, over that at `ρ_C`. -/
def dimSp (n : ℕ) (ν : ℕ → ℤ) : ℚ :=
  weylC n (fun i => (ν i : ℚ) + ((n : ℚ) - i)) / weylC n (fun i => (n : ℚ) - i)

/-- `dim_so_odd`: Weyl numerator at `ν + ρ_B`, `ρ_B = (n - ½, …, ½)`, over that at `ρ_B`;
`ν` may be half-integral, hence valued in `ℚ`. -/
def dimSoOdd (n : ℕ) (ν : ℕ → ℚ) : ℚ :=
  weylC n (fun i => ν i + (2 * ((n : ℚ) - i) - 1) / 2) /
    weylC n (fun i => (2 * ((n : ℚ) - i) - 1) / 2)

def pad (L : List ℤ) : ℕ → ℤ := fun i => L.getD i 0
def padQ (L : List ℚ) : ℕ → ℚ := fun i => L.getD i 0

-- sanity values: GL_3 (1,0,0) = 3, (2,1,0) = 8; Sp(4) (1,0) = 4, (1,1) = 5;
-- SO(5) (1/2,1/2) = 4, (1,0) = 5.
example : dimGl 3 (pad [1, 0, 0]) = 3 := by
  norm_num [dimGl, vdm, pad, Finset.prod_Ico_eq_prod_range, Finset.prod_range_succ,
    Nat.factorial]
example : dimGl 3 (pad [2, 1, 0]) = 8 := by
  norm_num [dimGl, vdm, pad, Finset.prod_Ico_eq_prod_range, Finset.prod_range_succ,
    Nat.factorial]
example : dimSp 2 (pad [1, 0]) = 4 := by
  norm_num [dimSp, weylC, pad, Finset.prod_range_succ]
example : dimSp 2 (pad [1, 1]) = 5 := by
  norm_num [dimSp, weylC, pad, Finset.prod_range_succ]
example : dimSoOdd 2 (padQ [1 / 2, 1 / 2]) = 4 := by
  norm_num [dimSoOdd, weylC, padQ, Finset.prod_range_succ]
example : dimSoOdd 2 (padQ [1, 0]) = 5 := by
  norm_num [dimSoOdd, weylC, padQ, Finset.prod_range_succ]

/-- **B1 (non-fixed class), shift identity.**  If `ν_i = y_i - y_{n-1} - (n-1-i)` (the note's
`ν^{(c)}`, 0-indexed), then `dim_gl ν = ∏_{i<j}(y_i - y_j) / ∏_{j<n} j!`: the divisible pairs of
the class are `q (y_i - y_j)` and the factor `q^{#}` cancels against `ρ`. -/
theorem dimGl_shift (n : ℕ) (ν : ℕ → ℤ) (y : ℕ → ℤ)
    (hν : ∀ i < n, ν i = y i - y (n - 1) - ((n : ℤ) - 1 - i)) :
    dimGl n ν = vdm n (fun i => (y i : ℚ)) / ∏ j ∈ Finset.range n, ((j.factorial : ℕ) : ℚ) := by
  unfold dimGl
  congr 1
  unfold vdm
  refine Finset.prod_congr rfl fun i hi => Finset.prod_congr rfl fun j hj => ?_
  have hi' := Finset.mem_range.1 hi
  have hj' := (Finset.mem_Ico.1 hj).2
  have hn : 1 ≤ n := by omega
  beta_reduce
  rw [hν i hi', hν j hj']
  push_cast; ring

lemma vdm_congr (n : ℕ) (l l' : ℕ → ℚ) (h : ∀ i < n, l i = l' i) : vdm n l = vdm n l' := by
  unfold vdm
  refine Finset.prod_congr rfl fun i hi => Finset.prod_congr rfl fun j hj => ?_
  rw [h i (Finset.mem_range.1 hi), h j (Finset.mem_Ico.1 hj).2]

/-- Number of pairs `i < j < n`. -/
def npairs (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, (n - (i + 1))

lemma vdm_scale (n : ℕ) (a : ℚ) (y : ℕ → ℚ) :
    vdm n (fun i => a * y i) = a ^ npairs n * vdm n y := by
  unfold vdm npairs
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Nat.card_Ico (i + 1) n, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  ring

/-- **B-block (one non-fixed class), ratio form.**  Rows `e_i = c + q y_i` of a non-fixed class
(`e_i = ε_i ℓ_i`, `c` the class representative): the divisible pairs are `e_i - e_j = q (y_i - y_j)`,
and the ratio of their product to the one of the `ρ`-block (`q^{#pairs} ∏_{j<n} j!`, i.e.
`y = (n-1, …, 0)`) is `dim_gl ν^{(c)}`. -/
theorem block_ratio (n q : ℕ) (hq : 0 < q) (e y ν : ℕ → ℤ) (c : ℤ)
    (hy : ∀ i < n, e i = c + q * y i)
    (hν : ∀ i < n, ν i = y i - y (n - 1) - ((n : ℤ) - 1 - i)) :
    vdm n (fun i => (e i : ℚ)) /
        ((q : ℚ) ^ npairs n * ∏ j ∈ Finset.range n, ((j.factorial : ℕ) : ℚ)) =
      dimGl n ν := by
  rw [dimGl_shift n ν y hν]
  have h1 : vdm n (fun i => (e i : ℚ)) = vdm n (fun i => (c : ℚ) + q * y i) :=
    vdm_congr n _ _ fun i hi => by rw [hy i hi]; push_cast; ring
  have h2 : vdm n (fun i => (c : ℚ) + q * y i) = vdm n (fun i => (q : ℚ) * y i) := by
    unfold vdm
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    ring
  rw [h1, h2, vdm_scale, div_mul_eq_div_div, mul_div_assoc]
  have : ((q : ℚ) ^ npairs n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq.ne')
  field_simp

/-! ### (1) Pairs and folded classes -/

/-- Product of the `q`-divisible pairs of `x`. -/
def prodDiv (q : ℕ) (x : List ℤ) : ℚ :=
  (((pairs x).filter fun a => (q : ℤ) ∣ a).map fun a : ℤ => (a : ℚ)).prod

/-- Contribution of the two roots `e_i ∓ e_j` of the pair of rows `(a, b)`. -/
def fpair (q : ℕ) (a b : ℤ) : ℚ :=
  (if (q : ℤ) ∣ a - b then ((a - b : ℤ) : ℚ) else 1) *
    (if (q : ℤ) ∣ a + b then ((a + b : ℤ) : ℚ) else 1)

/-- Contribution of the long root `2 e_i`. -/
def gdiag (q : ℕ) (a : ℤ) : ℚ := if (q : ℤ) ∣ 2 * a then ((2 * a : ℤ) : ℚ) else 1

lemma flatMap_prod_div (q : ℕ) (a : ℤ) (xs : List ℤ) :
    ((((xs.flatMap fun b => [a - b, a + b]).filter fun c => (q : ℤ) ∣ c).map
      fun c : ℤ => (c : ℚ))).prod = (xs.map (fpair q a)).prod := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    simp only [List.flatMap_cons, List.filter_append, List.map_append, List.prod_append,
      List.map_cons, List.prod_cons, ih, fpair]
    by_cases h1 : (q : ℤ) ∣ a - b <;> by_cases h2 : (q : ℤ) ∣ a + b <;>
      simp [h1, h2]

/-- Recursion for the divisible-pair product. -/
lemma prodDiv_cons (q : ℕ) (a : ℤ) (xs : List ℤ) :
    prodDiv q (a :: xs) = gdiag q a * (xs.map (fpair q a)).prod * prodDiv q xs := by
  unfold prodDiv
  have e : pairs (a :: xs) = (2 * a) :: (xs.flatMap fun b => [a - b, a + b]) ++ pairs xs := by
    simp [pairs, ResidueCapacity.posRootVals]
  rw [e, List.filter_append, List.map_append, List.prod_append, List.filter_cons,
    ← flatMap_prod_div q a xs]
  unfold gdiag
  by_cases h : (q : ℤ) ∣ 2 * a
  · simp [h, mul_assoc]
  · simp [h]

lemma dvd_iff_zmod (q : ℕ) (a : ℤ) : (q : ℤ) ∣ a ↔ (a : ZMod q) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd a q).symm

/-- Rows in different folded classes contribute nothing. -/
lemma fpair_diff_class {q : ℕ} (a b : ℤ) (h1 : (a : ZMod q) ≠ b) (h2 : (a : ZMod q) ≠ -b) :
    fpair q a b = 1 := by
  have n1 : ¬ (q : ℤ) ∣ a - b := by
    rw [dvd_iff_zmod]; push_cast; exact fun h => h1 (sub_eq_zero.1 h)
  have n2 : ¬ (q : ℤ) ∣ a + b := by
    rw [dvd_iff_zmod]; push_cast; exact fun h => h2 (eq_neg_of_add_eq_zero_left h)
  simp [fpair, n1, n2]

/-- Same non-fixed class, `a ≡ b`: only `a - b` is divisible. -/
lemma fpair_same_nonfixed_sub {q : ℕ} (a b : ℤ) (h : (a : ZMod q) = b)
    (hfix : 2 * (a : ZMod q) ≠ 0) : fpair q a b = ((a - b : ℤ) : ℚ) := by
  have d1 : (q : ℤ) ∣ a - b := by
    rw [dvd_iff_zmod]; push_cast; rw [h, sub_self]
  have n2 : ¬ (q : ℤ) ∣ a + b := by
    rw [dvd_iff_zmod]; push_cast; intro h0
    apply hfix; rw [two_mul]; nth_rewrite 2 [h]; exact h0
  simp [fpair, d1, n2]

/-- Same non-fixed class, `a ≡ -b`: only `a + b` is divisible. -/
lemma fpair_same_nonfixed_add {q : ℕ} (a b : ℤ) (h : (a : ZMod q) = -b)
    (hfix : 2 * (a : ZMod q) ≠ 0) : fpair q a b = ((a + b : ℤ) : ℚ) := by
  have d2 : (q : ℤ) ∣ a + b := by
    rw [dvd_iff_zmod]; push_cast; rw [h, neg_add_cancel]
  have n1 : ¬ (q : ℤ) ∣ a - b := by
    rw [dvd_iff_zmod]; push_cast; intro h0
    apply hfix
    have hab : (a : ZMod q) = b := sub_eq_zero.1 h0
    have := congrArg₂ (· + ·) hab h
    rw [add_neg_cancel] at this
    rw [two_mul]; exact this
  simp [fpair, d2, n1]

/-- Fixed class (`2a ≡ 0`) and same class: both roots `a ∓ b` are divisible. -/
lemma fpair_fixed {q : ℕ} (a b : ℤ) (hfix : 2 * (a : ZMod q) = 0)
    (h : (a : ZMod q) = b ∨ (a : ZMod q) = -b) :
    fpair q a b = ((a - b : ℤ) : ℚ) * ((a + b : ℤ) : ℚ) := by
  have hneg : (a : ZMod q) = -a := by
    rw [eq_neg_iff_add_eq_zero, ← two_mul]; exact hfix
  have hb : (a : ZMod q) = b ∧ (a : ZMod q) = -b := by
    rcases h with h | h
    · exact ⟨h, by rw [← h]; exact hneg⟩
    · have hb' : (b : ZMod q) = -a := by rw [h, neg_neg]
      exact ⟨by rw [hb']; exact hneg, h⟩
  have d1 : (q : ℤ) ∣ a - b := by
    rw [dvd_iff_zmod]; push_cast; rw [hb.1, sub_self]
  have d2 : (q : ℤ) ∣ a + b := by
    rw [dvd_iff_zmod]; push_cast; rw [hb.2, neg_add_cancel]
  simp [fpair, d1, d2]

/-- The long root contributes `2a` exactly on fixed classes. -/
lemma gdiag_fixed {q : ℕ} (a : ℤ) (hfix : 2 * (a : ZMod q) = 0) :
    gdiag q a = ((2 * a : ℤ) : ℚ) := by
  have : (q : ℤ) ∣ 2 * a := by rw [dvd_iff_zmod]; push_cast; exact hfix
  simp [gdiag, this]

lemma gdiag_nonfixed {q : ℕ} (a : ℤ) (hfix : 2 * (a : ZMod q) ≠ 0) : gdiag q a = 1 := by
  have : ¬ (q : ℤ) ∣ 2 * a := by rw [dvd_iff_zmod]; push_cast; exact hfix
  simp [gdiag, this]

/-! ### (a) Grouping the pair product by class -/

/-- **Class grouping.**  If `f i j = 1` whenever `cl i ≠ cl j`, then `∏_{i<j} f i j` is the
product over the classes `c ∈ T` of the same product restricted to the rows of class `c`. -/
theorem prod_pairs_by_class {β : Type*} [DecidableEq β] (n : ℕ) (cl : ℕ → β) (f : ℕ → ℕ → ℚ)
    (hf : ∀ i j, cl i ≠ cl j → f i j = 1) (T : Finset β) (hT : ∀ i < n, cl i ∈ T) :
    ∏ i ∈ Finset.range n, ∏ j ∈ Finset.Ico (i + 1) n, f i j =
      ∏ c ∈ T, ∏ i ∈ (Finset.range n).filter (fun i => cl i = c),
        ∏ j ∈ (Finset.Ico (i + 1) n).filter (fun j => cl j = c), f i j := by
  have h1 : ∀ i ∈ Finset.range n, ∏ j ∈ Finset.Ico (i + 1) n, f i j =
      ∏ j ∈ (Finset.Ico (i + 1) n).filter (fun j => cl j = cl i), f i j := by
    intro i _
    symm
    apply Finset.prod_filter_of_ne
    intro j _ hne
    by_contra hc
    exact hne (hf i j (fun h => hc h.symm))
  rw [Finset.prod_congr rfl h1,
    ← Finset.prod_fiberwise_of_maps_to (s := Finset.range n) (t := T) (g := cl)
      (fun i hi => hT i (Finset.mem_range.1 hi))]
  refine Finset.prod_congr rfl fun c _ => Finset.prod_congr rfl fun i hi => ?_
  have : cl i = c := (Finset.mem_filter.1 hi).2
  rw [this]

lemma list_map_prod_range (f : ℤ → ℚ) (xs : List ℤ) :
    (xs.map f).prod = ∏ j ∈ Finset.range xs.length, f (xs.getD j 0) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    rw [List.map_cons, List.prod_cons, ih, List.length_cons, Finset.prod_range_succ']
    simp [mul_comm]

/-- The divisible-pair product as an indexed double product over the rows. -/
theorem prodDiv_idx (q : ℕ) (x : List ℤ) :
    prodDiv q x = (∏ i ∈ Finset.range x.length, gdiag q (x.getD i 0)) *
      ∏ i ∈ Finset.range x.length, ∏ j ∈ Finset.Ico (i + 1) x.length,
        fpair q (x.getD i 0) (x.getD j 0) := by
  induction x with
  | nil => simp [prodDiv, pairs, ResidueCapacity.posRootVals]
  | cons a xs ih =>
    rw [prodDiv_cons, ih, list_map_prod_range, List.length_cons,
      Finset.prod_range_succ' _ xs.length, Finset.prod_range_succ' _ xs.length]
    have hI : ∀ i : ℕ, ∏ j ∈ Finset.Ico (i + 1 + 1) (xs.length + 1),
        fpair q ((a :: xs).getD (i + 1) 0) ((a :: xs).getD j 0) =
        ∏ j ∈ Finset.Ico (i + 1) xs.length, fpair q (xs.getD i 0) (xs.getD j 0) := by
      intro i
      rw [← Finset.prod_Ico_add' (fun j => fpair q ((a :: xs).getD (i + 1) 0)
        ((a :: xs).getD j 0)) (i + 1) xs.length 1]
      simp
    have h0 : ∏ j ∈ Finset.Ico (0 + 1) (xs.length + 1), fpair q ((a :: xs).getD 0 0)
        ((a :: xs).getD j 0) = ∏ j ∈ Finset.range xs.length, fpair q a (xs.getD j 0) := by
      rw [Finset.range_eq_Ico, ← Finset.prod_Ico_add' (fun j => fpair q ((a :: xs).getD 0 0)
        ((a :: xs).getD j 0)) 0 xs.length 1]
      simp
    simp only [hI, h0]
    simp [mul_comm, mul_left_comm, mul_assoc]

/-! ### (b) Permutation invariance of `|vdm|` -/

/-- `∏_{i<j} |l_i - l_j|` over `range n`. -/
def avdm (n : ℕ) (l : ℕ → ℚ) : ℚ :=
  ∏ i ∈ Finset.range n, ∏ j ∈ Finset.Ico (i + 1) n, |l i - l j|

lemma abs_vdm (n : ℕ) (l : ℕ → ℚ) : |vdm n l| = avdm n l := by
  unfold vdm avdm
  rw [Finset.abs_prod]
  exact Finset.prod_congr rfl fun i _ => by rw [Finset.abs_prod]

lemma avdm_fin (n : ℕ) (l : ℕ → ℚ) :
    avdm n l = |Matrix.det (Matrix.vandermonde (fun i : Fin n => l i))| := by
  rw [Matrix.det_vandermonde, Finset.abs_prod]
  unfold avdm
  rw [← Fin.prod_univ_eq_prod_range (fun i => ∏ j ∈ Finset.Ico (i + 1) n, |l i - l j|) n]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.abs_prod]
  have e : ∏ j ∈ Finset.Ico ((i : ℕ) + 1) n, |l i - l j| =
      ∏ j ∈ Finset.Ioi i, |l i - l j| := by
    have h := Finset.prod_map (Finset.Ioi i) Fin.valEmbedding (fun j : ℕ => |l i - l j|)
    rw [Fin.map_valEmbedding_Ioi] at h
    simp only [Fin.valEmbedding_apply] at h
    rw [← h]
    refine Finset.prod_congr ?_ fun _ _ => rfl
    ext j
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  rw [e]
  exact Finset.prod_congr rfl fun j _ => abs_sub_comm _ _

/-- **Permutation invariance (b).**  Reordering the entries (a permutation `σ` of `range n`
given as a function `s` with `s` a bijection of `Fin n`) leaves `|vdm|` unchanged. -/
theorem avdm_perm (n : ℕ) (l : ℕ → ℚ) (σ : Equiv.Perm (Fin n)) :
    avdm n (fun i => if h : i < n then l (σ ⟨i, h⟩) else 0) = avdm n l := by
  rw [avdm_fin, avdm_fin]
  have : (Matrix.vandermonde (fun i : Fin n =>
      (fun i => if h : i < n then l (σ ⟨i, h⟩) else 0) (i : ℕ))) =
      (Matrix.vandermonde (fun i : Fin n => l i)).submatrix σ id := by
    ext i j
    simp [Matrix.vandermonde_apply]
  rw [this, Matrix.det_permute, abs_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

/-- **(c) core.**  Consecutive `y`-values: `∏_{i<j<n} |i − j| = ∏_{j<n} j!`.  (Via
`Matrix.det_vandermonde_id_eq_superFactorial`.) -/
theorem avdm_id (n : ℕ) :
    avdm n (fun i => (i : ℚ)) = ∏ j ∈ Finset.range n, ((j.factorial : ℕ) : ℚ) := by
  cases n with
  | zero => simp [avdm]
  | succ k =>
    rw [avdm_fin]
    have h := Matrix.det_vandermonde_id_eq_superFactorial (R := ℚ) k
    have e : (fun i : Fin (k + 1) => ((i : ℕ) : ℚ)) = fun i : Fin (k + 1) => (i : ℚ) := rfl
    rw [e, h, Finset.prod_range_succ']
    simp only [Nat.factorial_zero, Nat.cast_one, mul_one]
    rw [← Nat.prod_range_factorial_succ k, abs_of_nonneg (by positivity)]
    push_cast
    rfl

/-- Shift invariance: the `y`'s may start at any rational `t`. -/
lemma avdm_shift (n : ℕ) (l : ℕ → ℚ) (t : ℚ) : avdm n (fun i => l i + t) = avdm n l := by
  unfold avdm
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  congr 1; ring

lemma avdm_congr(n: ℕ) (l l' : ℕ → ℚ) (h : ∀ i < n, l i = l' i) : avdm n l = avdm n l' := by
  unfold avdm
  refine Finset.prod_congr rfl fun i hi => Finset.prod_congr rfl fun j hj => ?_
  rw [h i (Finset.mem_range.1 hi), h j (Finset.mem_Ico.1 hj).2]

lemma weylC_eq (n : ℕ) (l : ℕ → ℚ) :
    weylC n l = (∏ i ∈ Finset.range n, l i) * vdm n (fun i => l i ^ 2) := by
  unfold weylC vdm
  rw [Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  ring

/-- **(b) for `weylC`:** a permutation of the entries changes `weylC` at most by a sign. -/
theorem abs_weylC_perm (n : ℕ) (l : ℕ → ℚ) (σ : Equiv.Perm (Fin n)) :
    |weylC n (fun i => if h : i < n then l (σ ⟨i, h⟩) else 0)| = |weylC n l| := by
  rw [weylC_eq, weylC_eq, abs_mul, abs_mul, abs_vdm, abs_vdm]
  congr 1
  · have e1 : ∏ i ∈ Finset.range n, (if h : i < n then l (σ ⟨i, h⟩) else 0) =
        ∏ i : Fin n, l (σ i) := by
      rw [← Fin.prod_univ_eq_prod_range (fun i => if h : i < n then l (σ ⟨i, h⟩) else 0) n]
      exact Finset.prod_congr rfl fun i _ => by simp
    have e2 : ∏ i : Fin n, l (σ i) = ∏ i : Fin n, l i := Equiv.prod_comp σ (fun i => l i)
    rw [e1, e2, ← Fin.prod_univ_eq_prod_range (fun i => l i) n]
  · rw [← avdm_perm n (fun i => l i ^ 2) σ]
    exact avdm_congr n _ _ fun i hi => by simp [hi]

lemma weylC_congr(n: ℕ) (l l' : ℕ → ℚ) (h : ∀ i < n, l i = l' i) :
    weylC n l = weylC n l' := by
  unfold weylC
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  rw [h i hi']
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [h j (Finset.mem_Ico.1 hj).2]

/-- **B2 (class 0), shift identity.**  If `ν_i = L_i - (n - i)` (the note's `ν^{(0)}`, with
`L_i = ℓ_i / q`), then `dim_sp ν = weylC(L) / weylC(ρ_C)`. -/
theorem dimSp_shift (n : ℕ) (ν L : ℕ → ℤ) (hν : ∀ i < n, ν i = L i - ((n : ℤ) - i)) :
    dimSp n ν = weylC n (fun i => (L i : ℚ)) / weylC n (fun i => (n : ℚ) - i) := by
  unfold dimSp
  congr 1
  exact weylC_congr n _ _ fun i hi => by
    rw [hν i hi]; push_cast; ring

/-- **B3 (class `q/2`), shift identity.**  If `ν_i = L_i - (2(n-i)-1)/2` (the note's
`ν^{(q/2)}`, `L_i = ℓ_i / q`), then `dim_so_odd ν = weylC(L) / weylC(ρ_B)`. -/
theorem dimSoOdd_shift (n : ℕ) (ν L : ℕ → ℚ)
    (hν : ∀ i < n, ν i = L i - (2 * ((n : ℚ) - i) - 1) / 2) :
    dimSoOdd n ν = weylC n L / weylC n (fun i => (2 * ((n : ℚ) - i) - 1) / 2) := by
  unfold dimSoOdd
  congr 1
  exact weylC_congr n _ _ fun i hi => by
    rw [hν i hi]; ring

/-! ### (i) List version of `avdm` and its invariance under `List.Perm` -/

/-- `∏_{i<j} |L_i − L_j|` by recursion on the list. -/
def avdmL : List ℚ → ℚ
  | [] => 1
  | a :: L => (L.map fun b => |a - b|).prod * avdmL L

lemma avdmL_perm {L L' : List ℚ} (h : L.Perm L') : avdmL L = avdmL L' := by
  induction h with
  | nil => rfl
  | cons a hp ih =>
    simp only [avdmL, ih]
    rw [(List.Perm.map (fun b => |a - b|) hp).prod_eq]
  | swap x y l =>
    simp only [avdmL, List.map_cons, List.prod_cons]
    rw [abs_sub_comm y x]
    ring
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

lemma avdmL_idx (L : List ℚ) : avdmL L = avdm L.length (fun i => L.getD i 0) := by
  induction L with
  | nil => simp [avdmL, avdm]
  | cons a xs ih =>
    rw [avdmL, ih]
    unfold avdm
    rw [List.length_cons, Finset.prod_range_succ']
    have hI : ∀ i : ℕ, ∏ j ∈ Finset.Ico (i + 1 + 1) (xs.length + 1),
        |(a :: xs).getD (i + 1) 0 - (a :: xs).getD j 0| =
        ∏ j ∈ Finset.Ico (i + 1) xs.length, |xs.getD i 0 - xs.getD j 0| := by
      intro i
      rw [← Finset.prod_Ico_add' (fun j => |(a :: xs).getD (i + 1) 0 - (a :: xs).getD j 0|)
        (i + 1) xs.length 1]
      simp
    have h0 : ∏ j ∈ Finset.Ico (0 + 1) (xs.length + 1), |(a :: xs).getD 0 0 - (a :: xs).getD j 0| =
        ∏ j ∈ Finset.range xs.length, |a - xs.getD j 0| := by
      rw [Finset.range_eq_Ico, ← Finset.prod_Ico_add'
        (fun j => |(a :: xs).getD 0 0 - (a :: xs).getD j 0|) 0 xs.length 1]
      simp
    have hm : ∀ ys : List ℚ, (ys.map fun b => |a - b|).prod =
        ∏ j ∈ Finset.range ys.length, |a - ys.getD j 0| := by
      intro ys
      induction ys with
      | nil => simp
      | cons b ys ih' =>
        rw [List.map_cons, List.prod_cons, ih', List.length_cons, Finset.prod_range_succ']
        simp [mul_comm]
    simp only [hI, h0, hm xs]
    simp [mul_comm]

/-! ### Orientation of the rows of a non-fixed class -/

/-- Orientation `ε_i ℓ_i ≡ c`: keep `v` if `v ≡ c`, otherwise (`v ≡ -c`) take `-v`. -/
def orient (q : ℕ) (c : ZMod q) (v : ℤ) : ℤ := if (v : ZMod q) = c then v else -v

lemma abs_fpair_nonfixed {q : ℕ} (c : ZMod q) (hc : 2 * c ≠ 0) (a b : ℤ)
    (ha : (a : ZMod q) = c ∨ (a : ZMod q) = -c) (hb : (b : ZMod q) = c ∨ (b : ZMod q) = -c) :
    |fpair q a b| = |((orient q c a : ℤ) : ℚ) - ((orient q c b : ℤ) : ℚ)| := by
  have hneg : (c : ZMod q) ≠ -c := by
    intro h; apply hc; rw [two_mul]; nth_rewrite 2 [h]; exact add_neg_cancel c
  have hfa : 2 * (a : ZMod q) ≠ 0 := by
    rcases ha with h | h
    · rw [h]; exact hc
    · rw [h, mul_neg]; exact neg_ne_zero.2 hc
  by_cases h1 : (a : ZMod q) = c <;> by_cases h2 : (b : ZMod q) = c
  · rw [fpair_same_nonfixed_sub a b (h1.trans h2.symm) hfa]
    simp [orient, h1, h2]
  · have hb' : (b : ZMod q) = -c := hb.resolve_left h2
    rw [fpair_same_nonfixed_add a b (by rw [hb', neg_neg]; exact h1) hfa]
    simp [orient, h1, h2]
  · have ha' : (a : ZMod q) = -c := ha.resolve_left h1
    rw [fpair_same_nonfixed_add a b (by rw [ha', h2]) hfa]
    simp only [orient, h1, h2, ite_true, ite_false, Int.cast_add, Int.cast_neg]
    rw [← abs_neg]; congr 1; ring
  · have ha' : (a : ZMod q) = -c := ha.resolve_left h1
    have hb' : (b : ZMod q) = -c := hb.resolve_left h2
    rw [fpair_same_nonfixed_sub a b (ha'.trans hb'.symm) hfa]
    simp only [orient, h1, h2, ite_false, Int.cast_sub, Int.cast_neg]
    rw [← abs_neg]; congr 1; ring

/-- Product of `|fpair|` over the pairs of a block of rows. -/
def pairProdL (q : ℕ) : List ℤ → ℚ
  | [] => 1
  | a :: L => (L.map fun b => |fpair q a b|).prod * pairProdL q L

/-- **Block pair product = list Vandermonde of the oriented rows.** -/
theorem pairProdL_eq_avdmL {q : ℕ} (c : ZMod q) (hc : 2 * c ≠ 0) (L : List ℤ)
    (hL : ∀ v ∈ L, (v : ZMod q) = c ∨ (v : ZMod q) = -c) :
    pairProdL q L = avdmL (L.map fun v => ((orient q c v : ℤ) : ℚ)) := by
  induction L with
  | nil => simp [pairProdL, avdmL]
  | cons a L ih =>
    have hL' : ∀ v ∈ L, (v : ZMod q) = c ∨ (v : ZMod q) = -c :=
      fun v hv => hL v (List.mem_cons_of_mem _ hv)
    have ha := hL a (List.mem_cons_self ..)
    rw [pairProdL, List.map_cons, avdmL, ih hL', List.map_map]
    congr 1
    congr 1
    refine List.map_congr_left fun b hb => ?_
    simp only [Function.comp_apply]
    exact abs_fpair_nonfixed c hc a b ha (hL' b hb)

/-- Block pair product as `|vdm|` of the oriented rows (indexed form). -/
lemma pairProdL_eq_abs_vdm {q : ℕ} (c : ZMod q) (hc : 2 * c ≠ 0) (L : List ℤ)
    (hL : ∀ v ∈ L, (v : ZMod q) = c ∨ (v : ZMod q) = -c) :
    pairProdL q L = |vdm L.length (fun i => ((orient q c (L.getD i 0) : ℤ) : ℚ))| := by
  rw [pairProdL_eq_avdmL c hc L hL, avdmL_idx, abs_vdm, List.length_map]
  refine avdm_congr _ _ _ fun i hi => ?_
  simp [List.getD_eq_getElem?_getD, hi]

/-- **`D_c` for a non-fixed class (ratio form).**  If the `ℓ`-block `Lℓ` and the `ρ`-block `Lρ`
of a non-fixed class `c` both have `n` rows, the `ρ`-block product is `q^{npairs n} ∏_{j<n} j!`
(the consecutive-`y` fact `hρ`), and the oriented `ℓ`-rows are `c₀ + q y_i` with
`ν_i = y_i - y_{n-1} - (n-1-i)`, then the ratio of the two block products is `|dim_gl ν|`. -/
theorem D_nonfixed {q : ℕ} (hq : 0 < q) (c : ZMod q) (hc : 2 * c ≠ 0) (c₀ : ℤ)
    (n : ℕ) (Lℓ Lρ : List ℤ) (hℓn : Lℓ.length = n)
    (hℓ : ∀ v ∈ Lℓ, (v : ZMod q) = c ∨ (v : ZMod q) = -c)
    (hρ : pairProdL q Lρ = (q : ℚ) ^ npairs n * ∏ j ∈ Finset.range n, ((j.factorial : ℕ) : ℚ))
    (y ν : ℕ → ℤ) (hy : ∀ i < n, orient q c (Lℓ.getD i 0) = c₀ + q * y i)
    (hν : ∀ i < n, ν i = y i - y (n - 1) - ((n : ℤ) - 1 - i)) :
    pairProdL q Lℓ / pairProdL q Lρ = |dimGl n ν| := by
  have hpos : 0 < (q : ℚ) ^ npairs n * ∏ j ∈ Finset.range n, ((j.factorial : ℕ) : ℚ) := by
    apply mul_pos (pow_pos (by exact_mod_cast hq) _)
    exact Finset.prod_pos fun j _ => by exact_mod_cast Nat.factorial_pos j
  rw [hρ, pairProdL_eq_abs_vdm c hc Lℓ hℓ, hℓn, ← block_ratio n q hq
    (fun i => orient q c (Lℓ.getD i 0)) y ν c₀ hy hν, abs_div, abs_of_pos hpos]

/-! ### (i) The `ρ`-block of a non-fixed class: oriented rows `c₀ + q y`, `y = -s, …, s` -/

lemma cls_iff_c (q : ℕ) (v c₀ : ℤ) : (v : ZMod q) = (c₀ : ZMod q) ↔ (q : ℤ) ∣ v - c₀ := by
  rw [dvd_iff_zmod]; push_cast; exact sub_eq_zero.symm

lemma cls_iff_negc (q : ℕ) (v c₀ : ℤ) : (v : ZMod q) = -(c₀ : ZMod q) ↔ (q : ℤ) ∣ v + c₀ := by
  rw [dvd_iff_zmod]; push_cast; exact eq_neg_iff_add_eq_zero

lemma mem_rhoZ_of {m : ℕ} {b : ℤ} (h1 : 1 ≤ b) (h2 : b ≤ m) : b ∈ rhoZ m := by
  simp only [rhoZ, List.mem_map, List.mem_reverse, List.mem_range]
  refine ⟨(b - 1).toNat, by omega, by omega⟩

/-- `2 c₀ ≢ 0 (mod 2h)` for `0 < c₀ < h`. -/
lemma two_c_ne_zero {h : ℕ} (c₀ : ℤ) (h1 : 1 ≤ c₀) (h2 : c₀ ≤ (h : ℤ) - 1) :
    2 * (c₀ : ZMod (2 * h)) ≠ 0 := by
  intro hz
  have : ((2 * c₀ : ℤ) : ZMod (2 * h)) = 0 := by push_cast; exact hz
  rw [← dvd_iff_zmod] at this
  push_cast at this
  obtain ⟨k, hk⟩ := this
  have hk0 : 0 < k := by nlinarith
  have hk1 : k < 1 := by nlinarith
  omega

lemma c_ne_neg_c {h : ℕ} (c₀ : ℤ) (h1 : 1 ≤ c₀) (h2 : c₀ ≤ (h : ℤ) - 1) :
    (c₀ : ZMod (2 * h)) ≠ -(c₀ : ZMod (2 * h)) := by
  intro he
  apply two_c_ne_zero c₀ h1 h2
  calc 2 * (c₀ : ZMod (2 * h)) = c₀ + c₀ := two_mul _
    _ = c₀ + -(c₀ : ZMod (2 * h)) := by rw [← he]
    _ = 0 := add_neg_cancel _

/-- Oriented rows of `ρ_m` in the class of `c₀`, for `q = 2h`, `m + 1 = (2s+1) h`: exactly
`c₀ + q y`, `y ∈ [-s, s]`. -/
theorem rho_orient_mem {h s m : ℕ} (hm : m + 1 = (2 * s + 1) * h) (c₀ : ℤ) (h1 : 1 ≤ c₀)
    (h2 : c₀ ≤ (h : ℤ) - 1) (a : ℤ) :
    (∃ v ∈ rhoZ m, ((v : ZMod (2 * h)) = (c₀ : ZMod (2 * h)) ∨
        (v : ZMod (2 * h)) = -(c₀ : ZMod (2 * h))) ∧
      orient (2 * h) (c₀ : ZMod (2 * h)) v = a) ↔
    ∃ t : ℕ, t < 2 * s + 1 ∧ a = c₀ + ((2 * h : ℕ) : ℤ) * ((t : ℤ) - s) := by
  have hmZ : (m : ℤ) + 1 = (2 * s + 1) * h := by exact_mod_cast hm
  have hh : (2 : ℤ) ≤ h := by omega
  have hqZ : ((2 * h : ℕ) : ℤ) = 2 * h := by push_cast; ring
  have hneg := c_ne_neg_c (h := h) c₀ h1 h2
  constructor
  · rintro ⟨v, hv, hcl, rfl⟩
    obtain ⟨hv1, hv2⟩ := mem_rhoZ hv
    rcases hcl with hvc | hvn
    · have hor : orient (2 * h) (c₀ : ZMod (2 * h)) v = v := by simp [orient, hvc]
      rw [hor]
      obtain ⟨y, hy⟩ := (cls_iff_c _ v c₀).1 hvc
      rw [hqZ] at hy
      have hy0 : 0 ≤ y := by
        by_contra hn; push Not at hn
        nlinarith
      have hy1 : y ≤ s := by
        by_contra hn; push Not at hn
        nlinarith
      refine ⟨(y + s).toNat, by omega, ?_⟩
      rw [hqZ, show (((y + s).toNat : ℕ) : ℤ) = y + s by omega]
      linarith
    · have hne : ¬ (v : ZMod (2 * h)) = (c₀ : ZMod (2 * h)) := fun he => hneg (he.symm.trans hvn)
      have hor : orient (2 * h) (c₀ : ZMod (2 * h)) v = -v := by simp [orient, hne]
      rw [hor]
      obtain ⟨k, hk⟩ := (cls_iff_negc _ v c₀).1 hvn
      rw [hqZ] at hk
      have hk0 : 1 ≤ k := by
        by_contra hn; push Not at hn
        nlinarith
      have hk1 : k ≤ s := by
        by_contra hn; push Not at hn
        nlinarith
      refine ⟨(s - k).toNat, by omega, ?_⟩
      rw [hqZ, show (((s - k).toNat : ℕ) : ℤ) = s - k by omega]
      linarith
  · rintro ⟨t, ht, rfl⟩
    rw [hqZ]
    by_cases hts : s ≤ t
    · have hY0 : 0 ≤ (t : ℤ) - s := by omega
      have hY1 : (t : ℤ) - s ≤ s := by omega
      have e1 : 0 ≤ (h : ℤ) * ((t : ℤ) - s) := mul_nonneg (by omega) hY0
      have e2 : (h : ℤ) * ((t : ℤ) - s) ≤ h * s := mul_le_mul_of_nonneg_left hY1 (by omega)
      have hmem : c₀ + 2 * h * ((t : ℤ) - s) ∈ rhoZ m :=
        mem_rhoZ_of (by nlinarith) (by nlinarith)
      have hcl : ((c₀ + 2 * h * ((t : ℤ) - s) : ℤ) : ZMod (2 * h)) = (c₀ : ZMod (2 * h)) := by
        rw [cls_iff_c, hqZ.symm]
        exact ⟨(t : ℤ) - s, by push_cast; ring⟩
      exact ⟨_, hmem, Or.inl hcl, by simp [orient, hcl]⟩
    · push Not at hts
      have hk : 1 ≤ (s : ℤ) - t := by omega
      have hk1 : (s : ℤ) - t ≤ s := by omega
      have e1 : (h : ℤ) ≤ h * ((s : ℤ) - t) := by nlinarith
      have e2 : (h : ℤ) * ((s : ℤ) - t) ≤ h * s := mul_le_mul_of_nonneg_left hk1 (by omega)
      have hmem : -(c₀ + 2 * h * ((t : ℤ) - s)) ∈ rhoZ m :=
        mem_rhoZ_of (by nlinarith) (by nlinarith)
      have hcl : ((-(c₀ + 2 * h * ((t : ℤ) - s)) : ℤ) : ZMod (2 * h)) =
          -(c₀ : ZMod (2 * h)) := by
        rw [cls_iff_negc, hqZ.symm]
        exact ⟨(s : ℤ) - t, by push_cast; ring⟩
      have hne : ¬ ((-(c₀ + 2 * h * ((t : ℤ) - s)) : ℤ) : ZMod (2 * h)) =
          (c₀ : ZMod (2 * h)) := fun he => hneg (he.symm.trans hcl)
      exact ⟨_, hmem, Or.inr hcl, by unfold orient; simp only [hne, ↓reduceIte]; ring⟩

lemma rhoZ_nodup (m : ℕ) : (rhoZ m).Nodup := by
  unfold rhoZ
  refine List.Nodup.map (fun a b hab => ?_) (List.nodup_reverse.2 (List.nodup_range))
  have : (a : ℤ) + 1 = b + 1 := by exact_mod_cast hab
  omega

lemma avdm_scale (n : ℕ) (a : ℚ) (l : ℕ → ℚ) :
    avdm n (fun i => a * l i) = |a| ^ npairs n * avdm n l := by
  rw [← abs_vdm, ← abs_vdm, vdm_scale, abs_mul, abs_pow]

/-- **(i) `ρ`-block of a non-fixed class.**  For `q = 2h`, `m + 1 = (2s+1) h` (`d = 2s+1` odd)
and `0 < c₀ < h`, the block of `ρ_m` in the folded class of `c₀` has pair product
`q^{npairs d} ∏_{j<d} j!` (its oriented rows are `c₀ + q y`, `y = -s..s`). -/
theorem rho_block_prod {h s m : ℕ} (hm : m + 1 = (2 * s + 1) * h) (c₀ : ℤ) (h1 : 1 ≤ c₀)
    (h2 : c₀ ≤ (h : ℤ) - 1) :
    pairProdL (2 * h) ((rhoZ m).filter fun v : ℤ => decide ((v : ZMod (2 * h)) = (c₀ : ZMod (2 * h)) ∨
        (v : ZMod (2 * h)) = -(c₀ : ZMod (2 * h)))) =
      ((2 * h : ℕ) : ℚ) ^ npairs (2 * s + 1) *
        ∏ j ∈ Finset.range (2 * s + 1), ((j.factorial : ℕ) : ℚ) := by
  have hh : (1 : ℤ) ≤ h - 1 := le_trans h1 h2
  have hq0 : 0 < (2 * h : ℕ) := by omega
  have hneg := c_ne_neg_c (h := h) c₀ h1 h2
  have hc := two_c_ne_zero (h := h) c₀ h1 h2
  set L := (rhoZ m).filter fun v : ℤ => decide ((v : ZMod (2 * h)) = (c₀ : ZMod (2 * h)) ∨
        (v : ZMod (2 * h)) = -(c₀ : ZMod (2 * h))) with hL
  have hLc : ∀ v ∈ L, (v : ZMod (2 * h)) = (c₀ : ZMod (2 * h)) ∨
      (v : ZMod (2 * h)) = -(c₀ : ZMod (2 * h)) := fun v hv => by
    simpa using (List.mem_filter.1 hv).2
  rw [pairProdL_eq_avdmL (c₀ : ZMod (2 * h)) hc L hLc]
  -- the oriented rows are a permutation of `c₀ + q (t - s)`, `t < 2s+1`
  have hperm : (L.map (orient (2 * h) (c₀ : ZMod (2 * h)))).Perm
      ((List.range (2 * s + 1)).map fun t : ℕ => c₀ + ((2 * h : ℕ) : ℤ) * ((t : ℤ) - s)) := by
    rw [List.perm_ext_iff_of_nodup]
    · intro a
      rw [List.mem_map, List.mem_map]
      have := rho_orient_mem hm c₀ h1 h2 a
      constructor
      · rintro ⟨v, hv, rfl⟩
        obtain ⟨hv1, hv2⟩ := List.mem_filter.1 hv
        obtain ⟨t, ht, e⟩ := this.1 ⟨v, hv1, by simpa using hv2, rfl⟩
        exact ⟨t, List.mem_range.2 ht, e.symm⟩
      · rintro ⟨t, ht, rfl⟩
        obtain ⟨v, hv, hcl, e⟩ := this.2 ⟨t, List.mem_range.1 ht, rfl⟩
        exact ⟨v, List.mem_filter.2 ⟨hv, by simpa using hcl⟩, e⟩
    · refine List.Nodup.map_on (fun v hv w hw hvw => ?_) ((rhoZ_nodup m).filter _)
      obtain ⟨hv1, hv2⟩ := List.mem_filter.1 hv
      obtain ⟨hw1, hw2⟩ := List.mem_filter.1 hw
      have hvp := (mem_rhoZ hv1).1
      have hwp := (mem_rhoZ hw1).1
      have hv3 : (v : ZMod (2 * h)) = c₀ ∨ (v : ZMod (2 * h)) = -(c₀ : ZMod (2 * h)) := by
        simpa using hv2
      have hw3 : (w : ZMod (2 * h)) = c₀ ∨ (w : ZMod (2 * h)) = -(c₀ : ZMod (2 * h)) := by
        simpa using hw2
      by_cases a1 : (v : ZMod (2 * h)) = c₀ <;> by_cases a2 : (w : ZMod (2 * h)) = c₀ <;>
        simp only [orient, a1, a2, ↓reduceIte] at hvw <;> omega
    · refine List.Nodup.map (fun t t' htt => ?_) (List.nodup_range)
      have h0 : ((2 * h : ℕ) : ℤ) * ((t : ℤ) - s) = ((2 * h : ℕ) : ℤ) * ((t' : ℤ) - s) := by
        linarith
      have := mul_left_cancel₀ (by exact_mod_cast hq0.ne' : ((2 * h : ℕ) : ℤ) ≠ 0) h0
      omega
  have e1 : L.map (fun v => ((orient (2 * h) (c₀ : ZMod (2 * h)) v : ℤ) : ℚ)) =
      (L.map (orient (2 * h) (c₀ : ZMod (2 * h)))).map (Int.cast : ℤ → ℚ) := by
    rw [List.map_map]; rfl
  rw [e1, avdmL_perm (hperm.map (Int.cast : ℤ → ℚ)), List.map_map, avdmL_idx, List.length_map,
    List.length_range]
  have e2 : avdm (2 * s + 1) (fun i => (List.map ((Int.cast : ℤ → ℚ) ∘ fun t : ℕ =>
      c₀ + ((2 * h : ℕ) : ℤ) * ((t : ℤ) - s)) (List.range (2 * s + 1))).getD i 0) =
      avdm (2 * s + 1) (fun i => ((2 * h : ℕ) : ℚ) * (i : ℚ) + ((c₀ : ℚ) - ((2 * h : ℕ) : ℚ) * s)) :=
    avdm_congr _ _ _ fun i hi => by
      simp [List.getD_eq_getElem?_getD, hi]
      ring
  rw [e2, avdm_shift (2 * s + 1) (fun i => ((2 * h : ℕ) : ℚ) * (i : ℚ)),
    avdm_scale (2 * s + 1) _ (fun i => (i : ℚ)), avdm_id, abs_of_nonneg (by positivity)]

/-- **`D_c` for a non-fixed class, `d` odd (complete).**  `q = 2h`, `m + 1 = (2s+1) h`,
`0 < c₀ < h`.  If the `ℓ`-block `Lℓ` of the class of `c₀` has `d = 2s+1` rows whose oriented
values are `c₀ + q y_i` (`ν_i = y_i - y_{d-1} - (d-1-i)`), then the product of the divisible
pairs inside the class for `ℓ`, divided by the same for `ρ`, is `|dim_gl ν|` (modulus form). -/
theorem D_c_nonfixed_odd {h s m : ℕ} (hm : m + 1 = (2 * s + 1) * h) (c₀ : ℤ) (h1 : 1 ≤ c₀)
    (h2 : c₀ ≤ (h : ℤ) - 1) (Lℓ : List ℤ) (hℓn : Lℓ.length = 2 * s + 1)
    (hℓ : ∀ v ∈ Lℓ, (v : ZMod (2 * h)) = (c₀ : ZMod (2 * h)) ∨
      (v : ZMod (2 * h)) = -(c₀ : ZMod (2 * h)))
    (y ν : ℕ → ℤ)
    (hy : ∀ i < 2 * s + 1, orient (2 * h) (c₀ : ZMod (2 * h)) (Lℓ.getD i 0) =
      c₀ + ((2 * h : ℕ) : ℤ) * y i)
    (hν : ∀ i < 2 * s + 1, ν i = y i - y (2 * s + 1 - 1) - (((2 * s + 1 : ℕ) : ℤ) - 1 - i)) :
    pairProdL (2 * h) Lℓ /
        pairProdL (2 * h) ((rhoZ m).filter fun v : ℤ =>
          decide ((v : ZMod (2 * h)) = (c₀ : ZMod (2 * h)) ∨
            (v : ZMod (2 * h)) = -(c₀ : ZMod (2 * h)))) =
      |dimGl (2 * s + 1) ν| :=
  D_nonfixed (by omega) (c₀ : ZMod (2 * h)) (two_c_ne_zero c₀ h1 h2) c₀ (2 * s + 1) Lℓ _ hℓn hℓ
    (rho_block_prod hm c₀ h1 h2) y ν hy hν


end RhoLine
