/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.RepresentationTheory.Symplectic.RhoLine
public import Mathlib.Data.Nat.Factorial.Basic

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

lemma weylC_congr (n : ℕ) (l l' : ℕ → ℚ) (h : ∀ i < n, l i = l' i) :
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

end RhoLine
