/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.RepresentationTheory.Symplectic.SurvivorCount
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
# The difference of two residue histograms is another group's (Proposition `prop:resid`)

In `ℤ[ZMod q]`, let `ℛ_x` be the residue histogram of type `C` (`ResidueCapacity.R`).  When the
folded occupancies of `ℓ` depart from the flat profile only on `r` classes (the minimal profiles
of `SurvivorCount.min_profile_case1/2`), `P_ℓ = 2u T + P_L` (`v ≤ a`) or `P_ℓ = 2(u+1) T - P_L`
(`v > a`), with `L` a list of `r` class representatives, and the same holds for `ρ` with its own
departure list `ρ_H`.  Then `ℛ_ℓ - ℛ_ρ = ℛ^H_L - ℛ^H_{ρ_H}`, `H = C_r` or `D_r`.

## Main results

* `ResidualHistogram.RD`, `ResidualHistogram.eq_res_D`: the type-`D` histogram and its identity
  `2 ℛ^D_x + 2r = P_x² - P_x(X²)`.
* `ResidualHistogram.resid_core`: the algebraic core (no profiles).
* `ResidualHistogram.resid_C`, `ResidualHistogram.resid_D`: the difference, as `ℛ^C` / `ℛ^D`.
* `ResidualHistogram.P_shape_case1`, `ResidualHistogram.P_shape_case2`: the shape of `P_ℓ`.
* `ResidualHistogram.prop_resid_case1`, `ResidualHistogram.prop_resid_case2`: Proposition 9.2.

## References

* C. Marín, *Integer character values on the ρ-line of Sp(2m)*, Zenodo (2026),
  doi:10.5281/zenodo.22683560; `characters_at_aP.tex`, Proposition 9.2.
-/

@[expose] public section

open Finset ResidueCapacity SurvivorCount

namespace ResidualHistogram

section Core

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

omit [DecidableEq G] in
lemma T_mul_P (L : List G) :
    (∑ g : G, s g) * P L = ((2 * L.length : ℕ) : AddMonoidAlgebra ℤ G) * ∑ g : G, s g := by
  induction L with
  | nil => simp [P]
  | cons a xs ih =>
    simp only [P, mul_add, T_mul_s, ih, List.length_cons]
    push_cast; ring

lemma P_of_o (x L : List G) (k σ : ℤ) (h : ∀ g, o x g = k + σ * o L g) :
    P x = (k : AddMonoidAlgebra ℤ G) * ∑ g : G, s g + (σ : AddMonoidAlgebra ℤ G) * P L := by
  rw [P_eq_sum x, P_eq_sum L]
  simp only [h, add_smul, mul_smul, Finset.sum_add_distrib, zsmul_eq_mul,
    ← Finset.mul_sum]

lemma P2_of_o (x L : List G) (k σ : ℤ) (h : ∀ g, o x g = k + σ * o L g) :
    P (x.map fun a => 2 • a) = (k : AddMonoidAlgebra ℤ G) * ∑ g : G, s (2 • g) +
      (σ : AddMonoidAlgebra ℤ G) * P (L.map fun a => 2 • a) := by
  rw [P2_eq_sum x, P2_eq_sum L]
  simp only [h, add_smul, mul_smul, Finset.sum_add_distrib, zsmul_eq_mul,
    ← Finset.mul_sum]

/-- **The algebraic core.**  If `o_x = k + σ o_L` and `o_y = k + σ o_{L₀}` with `σ = ±1` and `x`,
`y` of the same length, then `|L| = |L₀|` and
`2 (ℛ_x - ℛ_y) = (P_L² + σ P_L(X²)) - (P_{L₀}² + σ P_{L₀}(X²))`. -/
theorem resid_core (x y L L0 : List G) (k σ : ℤ) (hσ : σ = 1 ∨ σ = -1)
    (hxy : x.length = y.length)
    (hx : ∀ g, o x g = k + σ * o L g) (hy : ∀ g, o y g = k + σ * o L0 g) :
    L.length = L0.length ∧
      (2 : AddMonoidAlgebra ℤ G) * (R x - R y) =
        ((P L ^ 2 + (σ : AddMonoidAlgebra ℤ G) * P (L.map fun a => 2 • a)) -
          (P L0 ^ 2 + (σ : AddMonoidAlgebra ℤ G) * P (L0.map fun a => 2 • a))) := by
  have hlen : L.length = L0.length := by
    have h1 := o_sum x
    have h2 := o_sum y
    have h3 := o_sum L
    have h4 := o_sum L0
    simp only [hx, Finset.sum_add_distrib, ← Finset.mul_sum, h3, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul] at h1
    simp only [hy, Finset.sum_add_distrib, ← Finset.mul_sum, h4, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul] at h2
    have h5 : σ * (L.length : ℤ) = σ * (L0.length : ℤ) := by
      have : (2 * x.length : ℤ) = 2 * y.length := by rw [hxy]
      nlinarith
    have h6 : (L.length : ℤ) = L0.length := by
      rcases hσ with rfl | rfl <;> linarith
    exact_mod_cast h6
  refine ⟨hlen, ?_⟩
  have E1 := eq_res x
  have E2 := eq_res y
  rw [P_of_o x L k σ hx, P2_of_o x L k σ hx] at E1
  rw [P_of_o y L0 k σ hy, P2_of_o y L0 k σ hy] at E2
  simp only [nsmul_eq_mul (α := AddMonoidAlgebra ℤ G), Nat.cast_ofNat, Nat.cast_mul] at E1 E2
  rw [hxy] at E1
  have hTL := T_mul_P L
  have hTL0 := T_mul_P L0
  rw [← hlen] at hTL0
  have hσσ : (σ : AddMonoidAlgebra ℤ G) * σ = 1 := by
    rcases hσ with rfl | rfl <;> simp
  linear_combination E1 - E2 + 2 * (k : AddMonoidAlgebra ℤ G) * σ * (hTL - hTL0) +
    (P L ^ 2 - P L0 ^ 2) * hσσ

/-! ### The type-`D` histogram -/

/-- Values `(x, α)` on the positive roots `e_i ± e_j` of `D_m` (no long roots `2 e_i`). -/
def posRootValsD : List G → List G
  | [] => []
  | a :: xs => (xs.flatMap fun b => [a - b, a + b]) ++ posRootValsD xs

/-- `ℛ^D_x = Σ_{α ∈ Φ(D_m)} X^{(x,α)}`: the same as `ℛ_x` without the long roots. -/
noncomputable def RD (x : List G) : AddMonoidAlgebra ℤ G :=
  ((posRootValsD x).map fun v => s v + s (-v)).sum

omit [DecidableEq G] [Fintype G] in
lemma R_eq_RD (x : List G) : R x = RD x + P (x.map fun a => 2 • a) := by
  induction x with
  | nil => simp [R, RD, P, posRootVals, posRootValsD]
  | cons a xs ih =>
    have h1 : R (a :: xs) = s (2 • a) + s (-(2 • a)) +
        ((xs.flatMap fun b => [a - b, a + b]).map fun v => s v + s (-v)).sum + R xs := by
      simp [R, posRootVals, List.sum_append, add_assoc]
    have h2 : RD (a :: xs) =
        ((xs.flatMap fun b => [a - b, a + b]).map fun v => s v + s (-v)).sum + RD xs := by
      simp [RD, posRootValsD, List.sum_append]
    rw [h1, h2, ih]
    simp only [List.map_cons, P]
    abel

omit [DecidableEq G] [Fintype G] in
/-- The identity of `ResidueCapacity.eq_res` without the long roots:
`2 ℛ^D_x + 2m = P_x² - P_x(X²)`. -/
theorem eq_res_D (x : List G) :
    (2 : AddMonoidAlgebra ℤ G) * RD x + ((2 * x.length : ℕ) : AddMonoidAlgebra ℤ G) =
      P x ^ 2 - P (x.map fun a => 2 • a) := by
  have E := eq_res x
  rw [R_eq_RD] at E
  simp only [nsmul_eq_mul (α := AddMonoidAlgebra ℤ G), Nat.cast_ofNat, Nat.cast_mul] at E
  push_cast
  linear_combination E

omit [DecidableEq G] [Fintype G] in
lemma eq_res_C (x : List G) :
    (2 : AddMonoidAlgebra ℤ G) * R x + ((2 * x.length : ℕ) : AddMonoidAlgebra ℤ G) =
      P x ^ 2 + P (x.map fun a => 2 • a) := by
  have E := eq_res x
  simp only [nsmul_eq_mul (α := AddMonoidAlgebra ℤ G), Nat.cast_ofNat, Nat.cast_mul] at E
  push_cast
  linear_combination E

omit [DecidableEq G] [Fintype G] in
lemma cancel2 {a b : AddMonoidAlgebra ℤ G} (h : (2 : AddMonoidAlgebra ℤ G) * a = 2 * b) :
    a = b := by
  apply two_smul_cancel
  rw [two_nsmul, two_nsmul]
  linear_combination h

/-- **Proposition `prop:resid`, algebraic form, `σ = +1`.**  `ℛ_x - ℛ_y = ℛ^{C}_L - ℛ^{C}_{L₀}`. -/
theorem resid_C (x y L L0 : List G) (k : ℤ)
    (hxy : x.length = y.length)
    (hx : ∀ g, o x g = k + o L g) (hy : ∀ g, o y g = k + o L0 g) :
    R x - R y = R L - R L0 := by
  have hx' : ∀ g, o x g = k + (1 : ℤ) * o L g := fun g => by rw [hx]; ring
  have hy' : ∀ g, o y g = k + (1 : ℤ) * o L0 g := fun g => by rw [hy]; ring
  obtain ⟨hlen, hc⟩ := resid_core x y L L0 k 1 (Or.inl rfl) hxy hx' hy'
  apply cancel2
  have e1 := eq_res_C L
  have e2 := eq_res_C L0
  rw [hlen] at e1
  simp only [Int.cast_one, one_mul] at hc
  linear_combination hc - e1 + e2

/-- **Proposition `prop:resid`, algebraic form, `σ = -1`.**  `ℛ_x - ℛ_y = ℛ^{D}_L - ℛ^{D}_{L₀}`. -/
theorem resid_D (x y L L0 : List G) (k : ℤ)
    (hxy : x.length = y.length)
    (hx : ∀ g, o x g = k - o L g) (hy : ∀ g, o y g = k - o L0 g) :
    R x - R y = RD L - RD L0 := by
  have hx' : ∀ g, o x g = k + (-1 : ℤ) * o L g := fun g => by rw [hx]; ring
  have hy' : ∀ g, o y g = k + (-1 : ℤ) * o L0 g := fun g => by rw [hy]; ring
  obtain ⟨hlen, hc⟩ := resid_core x y L L0 k (-1) (Or.inr rfl) hxy hx' hy'
  apply cancel2
  have e1 := eq_res_D L
  have e2 := eq_res_D L0
  rw [hlen] at e1
  simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul] at hc
  linear_combination hc - e1 + e2

end Core

/-! ## Part 2: `G = ZMod q`, the shape of `P_ℓ` and of `P_ρ` -/

section ZModq

variable {q : ℕ} [NeZero q]

lemma occ_neg {G : Type*} [AddCommGroup G] [DecidableEq G] (x : List G) (g : G) :
    occ x (-g) = occ x g := by
  unfold occ
  congr 1
  funext a
  simp only [neg_neg, or_comm]

lemma o_toList {G : Type*} [AddCommGroup G] [DecidableEq G] (S : Finset G) (g : G) :
    o S.toList g = ∑ c ∈ S, bump c g := by
  unfold o bump
  exact Finset.sum_map_toList S
    (fun b => (if b = g then (1 : ℤ) else 0) + (if -b = g then 1 else 0))

/-- The folded classes of `ZMod q` have the representatives `c` with `2 c.val ≤ q`; summing the
bumps `[g = c] + [g = -c]` over the representatives satisfying a class-invariant condition gives
the indicator of the condition, doubled on fixed classes. -/
lemma sum_bump_rep (cond : ZMod q → Prop) [DecidablePred cond] (hc : ∀ g, cond (-g) ↔ cond g)
    (g : ZMod q) :
    ∑ c ∈ (Finset.univ.filter fun c : ZMod q => 2 * c.val ≤ q ∧ cond c), bump c g =
      if cond g then (if 2 • g = 0 then 2 else 1) else 0 := by
  unfold bump
  rw [Finset.sum_add_distrib]
  simp only [neg_eq_iff_eq_neg]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hc]
  have hlt := ZMod.val_lt g
  have hD := two_smul_eq_zero_iff g
  by_cases hcg : cond g
  · simp only [hcg, and_true, ite_true]
    rw [val_neg']
    by_cases hfix : 2 • g = 0
    · have := hD.1 hfix
      simp only [hfix, ite_true]
      split_ifs <;> omega
    · have := mt hD.2 hfix
      simp only [hfix, ite_false]
      split_ifs <;> omega
  · simp [hcg]

lemma card_eq_of_o {x L : List (ZMod q)} (k : ℤ) (σ : ℤ) (_hσ : σ = 1 ∨ σ = -1)
    (hx : ∀ g, o x g = k + σ * o L g) :
    (q : ℤ) * k + σ * (2 * L.length) = 2 * x.length := by
  have h1 := o_sum x
  have h3 := o_sum L
  simp only [hx, Finset.sum_add_distrib, ← Finset.mul_sum, h3, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ZMod.card] at h1
  linarith

/-- **Objective 1, case `v ≤ a`.**  If `N_q(x) = N_q(ρ)` and `m = u q + v` with `v ≤ a`, there are
`v` non-fixed folded classes (represented by `c` with `2 c.val ≤ q`, collected in the list `L`)
such that `o_x = 2u + o_L`, i.e. `P_x = 2u T + C_S`. -/
theorem P_shape_case1 (x : List (ZMod q)) (hv : x.length % q ≤ aq q)
    (h : Nq x = Nq (rho q x.length)) :
    ∃ L : List (ZMod q), L.length = x.length % q ∧ L.Nodup ∧
      (∀ c ∈ L, 2 * c.val ≤ q ∧ 2 • c ≠ 0) ∧
      (∀ g, o x g = ((2 * (x.length / q) : ℕ) : ℤ) + o L g) ∧
      P x = ((2 * (x.length / q) : ℕ) : AddMonoidAlgebra ℤ (ZMod q)) * ∑ g : ZMod q, s g + P L := by
  have hmin := (min_profile_case1 (q := q) x.length hv x.get).1 (by rw [List.ofFn_get]; exact h)
  rw [List.ofFn_get] at hmin
  have hdm := Nat.div_add_mod x.length q
  generalize hu : x.length / q = u at *
  generalize hw : x.length % q = w at *
  let cond : ZMod q → Prop := fun g => occ x g = 2 * u + 1
  have hc : ∀ g, cond (-g) ↔ cond g := fun g => by simp only [cond, occ_neg]
  set S : Finset (ZMod q) := Finset.univ.filter fun c : ZMod q => 2 * c.val ≤ q ∧ cond c with hS
  have key : ∀ g, o x g = ((2 * u : ℕ) : ℤ) + o S.toList g := by
    intro g
    rw [o_toList, hS, sum_bump_rep cond hc g, o_eq_occ]
    have hg := hmin g
    by_cases hf : 2 • g = 0
    · have hg' : occ x g = u := by
        unfold Al at hg; rw [ite_eq_left hf] at hg; simpa using hg
      simp only [cond, hf, ite_true]
      split_ifs <;> omega
    · have hg' : occ x g = 2 * u ∨ occ x g = 2 * u + 1 := by
        unfold Al at hg; rw [ite_eq_right hf] at hg; simpa using hg
      simp only [cond, hf, ite_false]
      split_ifs <;> omega
  have hcard := card_eq_of_o (x := x) (L := S.toList) (((2 * u : ℕ) : ℤ)) 1 (Or.inl rfl)
    (fun g => by rw [key]; ring)
  have hlen : S.toList.length = w := by
    rw [Finset.length_toList]
    rw [Finset.length_toList] at hcard
    push_cast at hcard
    have hdm' : (q : ℤ) * u + w = x.length := by exact_mod_cast hdm
    have : (S.card : ℤ) = w := by linarith
    exact_mod_cast this
  refine ⟨S.toList, hlen, S.nodup_toList, ?_, key, ?_⟩
  · intro c hcm
    rw [Finset.mem_toList, hS, Finset.mem_filter] at hcm
    refine ⟨hcm.2.1, fun hf => ?_⟩
    have := hmin c
    unfold Al at this
    have h2 := hcm.2.2
    simp only [cond] at h2
    simp only [hf, ite_true] at this
    omega
  · have := P_of_o x S.toList ((2 * u : ℕ) : ℤ) 1 (fun g => by rw [key]; ring)
    simpa using this

/-- **Objective 1, case `v > a`.**  If `N_q(x) = N_q(ρ)` and `m = u q + v` with `v > a`, there are
`q - v` folded classes (fixed ones allowed, represented by `c` with `2 c.val ≤ q`) that are one
row short of the flat profile: `o_x = 2(u+1) - o_L`, i.e. `P_x = 2(u+1) T - C_S`. -/
theorem P_shape_case2 (x : List (ZMod q)) (hv : aq q < x.length % q)
    (h : Nq x = Nq (rho q x.length)) :
    ∃ L : List (ZMod q), L.length = q - x.length % q ∧ L.Nodup ∧
      (∀ c ∈ L, 2 * c.val ≤ q) ∧
      (∀ g, o x g = ((2 * (x.length / q + 1) : ℕ) : ℤ) - o L g) ∧
      P x = ((2 * (x.length / q + 1) : ℕ) : AddMonoidAlgebra ℤ (ZMod q)) * ∑ g : ZMod q, s g
        - P L := by
  have hmin := (min_profile_case2 (q := q) x.length hv x.get).1 (by rw [List.ofFn_get]; exact h)
  rw [List.ofFn_get] at hmin
  have hdm := Nat.div_add_mod x.length q
  have hwq : x.length % q < q := Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne q))
  generalize hu : x.length / q = u at *
  generalize hw : x.length % q = w at *
  let cond : ZMod q → Prop := fun g => occ x g = if 2 • g = 0 then u else 2 * u + 1
  have hc : ∀ g, cond (-g) ↔ cond g := fun g => by
    simp only [cond, occ_neg, smul_neg, neg_eq_zero]
  set S : Finset (ZMod q) := Finset.univ.filter fun c : ZMod q => 2 * c.val ≤ q ∧ cond c with hS
  have key : ∀ g, o x g = ((2 * (u + 1) : ℕ) : ℤ) - o S.toList g := by
    intro g
    rw [o_toList, hS, sum_bump_rep cond hc g, o_eq_occ]
    have hg := hmin g
    by_cases hf : 2 • g = 0
    · have hg' : occ x g = u ∨ occ x g = u + 1 := by
        unfold Al at hg; rw [ite_eq_left hf] at hg; simpa using hg
      simp only [cond, hf, ite_true]
      split_ifs <;> omega
    · have hg' : occ x g = 2 * u + 1 ∨ occ x g = 2 * u + 2 := by
        unfold Al at hg; rw [ite_eq_right hf] at hg; simpa using hg
      simp only [cond, hf, ite_false]
      split_ifs <;> omega
  have hcard := card_eq_of_o (x := x) (L := S.toList) (((2 * (u + 1) : ℕ) : ℤ)) (-1)
    (Or.inr rfl) (fun g => by rw [key]; ring)
  have hlen : S.toList.length = q - w := by
    rw [Finset.length_toList]
    rw [Finset.length_toList] at hcard
    push_cast at hcard
    have hdm' : (q : ℤ) * u + w = x.length := by exact_mod_cast hdm
    have : (S.card : ℤ) = q - w := by linarith
    omega
  refine ⟨S.toList, hlen, S.nodup_toList, ?_, key, ?_⟩
  · intro c hcm
    rw [Finset.mem_toList, hS, Finset.mem_filter] at hcm
    exact hcm.2.1
  · have := P_of_o x S.toList ((2 * (u + 1) : ℕ) : ℤ) (-1) (fun g => by rw [key]; ring)
    simpa [sub_eq_add_neg] using this

/-! ### `ρ` -/

lemma Ncnt_mod (m : ℕ) (g : ZMod q) :
    Ncnt q (m % q) g = if g ≠ 0 ∧ g.val ≤ m % q then 1 else 0 := by
  have hq := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [Ncnt_eq, Nat.div_eq_of_lt (Nat.mod_lt m hq), Nat.mod_mod, zero_add]

/-- `ρ = (m, …, 1)` splits into `u` full periods and the tail `ρ_v`:
`o_{ρ_m} = 2u + o_{ρ_v}` (all `m`, no case distinction). -/
lemma o_rho_split (m : ℕ) (g : ZMod q) :
    o (rho q m) g = ((2 * (m / q) : ℕ) : ℤ) + o (rho q (m % q)) g := by
  rw [o_rho_Ncnt, o_rho_Ncnt, Ncnt_eq, Ncnt_eq, Ncnt_mod, Ncnt_mod]
  push_cast
  split_ifs <;> omega

/-- The half-sum of `D_r`, `ρ_{D_r} = (r-1, …, 1, 0)`, reduced modulo `q`. -/
def rhoD (q r : ℕ) : List (ZMod q) :=
  ((List.range r).reverse).map fun i => ((i : ℕ) : ZMod q)

omit [NeZero q] in
lemma rhoD_succ (r : ℕ) : rhoD q (r + 1) = ((r : ℕ) : ZMod q) :: rhoD q r := by
  simp [rhoD, List.range_succ]

omit [NeZero q] in
lemma rhoD_length (r : ℕ) : (rhoD q r).length = r := by simp [rhoD]

lemma natCast_eq_iff_val {r : ℕ} (hr : r < q) (g : ZMod q) : ((r : ℕ) : ZMod q) = g ↔ g.val = r := by
  constructor
  · intro h
    rw [← h, ZMod.val_natCast, Nat.mod_eq_of_lt hr]
  · intro h
    have := ZMod.natCast_zmod_val g
    rw [h] at this
    exact this

lemma o_rhoD (r : ℕ) (hr : r ≤ q) (g : ZMod q) :
    o (rhoD q r) g = (if g.val < r then 1 else 0) + (if (-g).val < r then 1 else 0) := by
  induction r with
  | zero => simp [rhoD]
  | succ r ih =>
    rw [rhoD_succ, o_cons, ih (by omega)]
    have hA : ((r : ℕ) : ZMod q) = g ↔ g.val = r := natCast_eq_iff_val (by omega) g
    have hB : -((r : ℕ) : ZMod q) = g ↔ (-g).val = r := by
      rw [neg_eq_iff_eq_neg, natCast_eq_iff_val (by omega)]
    simp only [hA, hB]
    split_ifs <;> omega

lemma o_rho_add_rhoD (m : ℕ) (g : ZMod q) :
    o (rho q (m % q)) g + o (rhoD q (q - m % q)) g = 2 := by
  have hwq : m % q < q := Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne q))
  have hlt := ZMod.val_lt g
  rw [o_rho_Ncnt, Ncnt_mod, Ncnt_mod, o_rhoD _ (by omega)]
  have hg0 : g = 0 ↔ g.val = 0 := (ZMod.val_eq_zero g).symm
  simp only [ne_eq, neg_eq_zero, hg0, val_neg']
  push_cast
  split_ifs <;> omega

/-- `ρ` in the `D` regime: `o_{ρ_m} = 2(u+1) - o_{ρ_{D_{q-v}}}` (all `m`). -/
lemma o_rho_splitD (m : ℕ) (g : ZMod q) :
    o (rho q m) g = ((2 * (m / q + 1) : ℕ) : ℤ) - o (rhoD q (q - m % q)) g := by
  have := o_rho_split m g
  have h2 := o_rho_add_rhoD m g
  push_cast at this ⊢
  linarith

/-! ### Proposition 9.2 -/

/-- **Proposition `prop:resid` (9.2), case `v ≤ a`, type `C`.**  Let `x` have length `m = u q + v`,
`v ≤ a`, and `N_q(x) = N_q(ρ)`.  Then there is a list `L` of `v` pairwise inequivalent non-fixed
folded classes with `P_x = 2u T + P_L`, `P_ρ = 2u T + P_{ρ_v}` (`ρ_H = ρ_v = (v, …, 1)`), and
`ℛ_x - ℛ_ρ = ℛ^{C_v}_L - ℛ^{C_v}_{ρ_v}`. -/
theorem prop_resid_case1 (x : List (ZMod q)) (hv : x.length % q ≤ aq q)
    (h : Nq x = Nq (rho q x.length)) :
    ∃ L : List (ZMod q), L.length = x.length % q ∧ L.Nodup ∧
      (∀ c ∈ L, 2 * c.val ≤ q ∧ 2 • c ≠ 0) ∧
      P x = ((2 * (x.length / q) : ℕ) : AddMonoidAlgebra ℤ (ZMod q)) * ∑ g : ZMod q, s g + P L ∧
      P (rho q x.length) = ((2 * (x.length / q) : ℕ) : AddMonoidAlgebra ℤ (ZMod q)) *
        ∑ g : ZMod q, s g + P (rho q (x.length % q)) ∧
      R x - R (rho q x.length) = R L - R (rho q (x.length % q)) := by
  obtain ⟨L, hlen, hnd, hmem, hkey, hP⟩ := P_shape_case1 x hv h
  refine ⟨L, hlen, hnd, hmem, hP, ?_, ?_⟩
  · have := P_of_o (rho q x.length) (rho q (x.length % q)) ((2 * (x.length / q) : ℕ) : ℤ) 1
      (fun g => by rw [o_rho_split]; ring)
    simpa only [Int.cast_natCast, Int.cast_one, one_mul] using this
  · exact resid_C x (rho q x.length) L (rho q (x.length % q)) ((2 * (x.length / q) : ℕ) : ℤ)
      (by rw [rho_length]) hkey (fun g => o_rho_split _ g)

/-- **Proposition `prop:resid` (9.2), case `v > a`, type `D`.**  Let `x` have length `m = u q + v`,
`v > a`, and `N_q(x) = N_q(ρ)`.  Then there is a list `L` of `r = q - v` pairwise inequivalent
folded classes (fixed ones allowed) with `P_x = 2(u+1) T - P_L`,
`P_ρ = 2(u+1) T - P_{ρ_{D_r}}` (`ρ_H = (r-1, …, 0)`), and
`ℛ_x - ℛ_ρ = ℛ^{D_r}_L - ℛ^{D_r}_{ρ_{D_r}}`. -/
theorem prop_resid_case2 (x : List (ZMod q)) (hv : aq q < x.length % q)
    (h : Nq x = Nq (rho q x.length)) :
    ∃ L : List (ZMod q), L.length = q - x.length % q ∧ L.Nodup ∧
      (∀ c ∈ L, 2 * c.val ≤ q) ∧
      P x = ((2 * (x.length / q + 1) : ℕ) : AddMonoidAlgebra ℤ (ZMod q)) * ∑ g : ZMod q, s g
        - P L ∧
      P (rho q x.length) = ((2 * (x.length / q + 1) : ℕ) : AddMonoidAlgebra ℤ (ZMod q)) *
        ∑ g : ZMod q, s g - P (rhoD q (q - x.length % q)) ∧
      R x - R (rho q x.length) = RD L - RD (rhoD q (q - x.length % q)) := by
  obtain ⟨L, hlen, hnd, hmem, hkey, hP⟩ := P_shape_case2 x hv h
  refine ⟨L, hlen, hnd, hmem, hP, ?_, ?_⟩
  · have := P_of_o (rho q x.length) (rhoD q (q - x.length % q))
      ((2 * (x.length / q + 1) : ℕ) : ℤ) (-1) (fun g => by rw [o_rho_splitD]; ring)
    simpa only [Int.cast_natCast, Int.cast_neg, Int.cast_one, neg_mul, one_mul,
      ← sub_eq_add_neg] using this
  · exact resid_D x (rho q x.length) L (rhoD q (q - x.length % q))
      ((2 * (x.length / q + 1) : ℕ) : ℤ) (by rw [rho_length]) hkey (fun g => o_rho_splitD _ g)

end ZModq

end ResidualHistogram
