/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Formalizations.LinearAlgebra.Matrix.Rank.Kronecker

/-!
# The product orbifold `(S¹/ℤ₂)^k`: the counts behind its semigroup

The affine semigroup of boundary conditions of `(S¹/ℤ₂)^k` (Part IX-B of the orbifold series) has one generator per
label; a label is a choice of two parity bits per circle, and each of the `2^k` fixed points (one reflection per
circle) reads one bit per circle. This file proves the counts the paper uses and the arithmetic that decides it.

## Main results

* `marginal_injective`, `card_labels`: distinct labels have distinct readouts, and there are `4^k` labels, so the
  semigroup has `n = 4^k` generators.
* `sum_choose_mul_two_pow`: `∑ C(k, j) 2^j = 3^k`, the number of faces of the boundary complex of the cross-polytope,
  which is `dim S`.
* `fms_bound_met`, `fms_bound_violated`: `4^k = 2·3^k − 2` for `k = 1, 2` and `4^k > 2·3^k − 2` for `k ≥ 3`.
* `not_completeIntersection_of_fms`: Proposition 2 of the paper, with the cited Corollary 3.4 of Fischer, Morris and
  Shapiro (a complete intersection of dimension `d ≥ 2` has at most `2d − 2` extreme rays) as a hypothesis.
* `cut_vertices`, `edges_exceed`: the count showing that `(S¹/ℤ₂)^k` is not a cut ideal for `k ≥ 3` (equation (5)).
* `not_cone_of_others`, `generator_extreme`: a one-hot block vector of a family of distinct choices is not a
  non-negative combination of the others, so every generator of `(S¹/ℤ₂)^k` spans an extreme ray of the cone (the
  first step of the proof of Proposition 2).
* `rank_circle`, `generators_eq`, `rank_generators`: the generator matrix of `(S¹/ℤ₂)^k` is, up to reindexing, the
  `k`-th Kronecker power of a `4 × 4` matrix of rank `3`, so it has rank `3^k`: `dim S = 3^k` (the rank part of
  Proposition 2).

## References

* C. Marín, *An Affine Semigroup from Orbifold Boundary Conditions* (Part IX-B), Zenodo (2026),
  doi:10.5281/zenodo.22254864, §8.
* K. G. Fischer, W. Morris, J. Shapiro, *Affine semigroup rings that are complete intersections*,
  Proc. Amer. Math. Soc. 125 (1997), Corollary 3.4.
-/

@[expose] public section

namespace OrbifoldProduct

/-- A label of `(S¹/ℤ₂)^k`: two parity bits per circle (one for each of its two reflections). -/
abbrev Label (k : ℕ) := Fin k → Bool × Bool

/-- A fixed point of `(S¹/ℤ₂)^k`: one of the two reflections of each circle. -/
abbrev FixedPoint (k : ℕ) := Fin k → Bool

/-- What a fixed point reads from a label: on each circle, the bit of the reflection it chose. -/
def readout {k : ℕ} (t : Label k) (c : FixedPoint k) : Fin k → Bool :=
  fun i => if c i then (t i).2 else (t i).1

/-- The marginal datum of a label: its readout at every fixed point (the generator of the semigroup, as the
indicator blocks of the paper encode it). -/
def marginal {k : ℕ} (t : Label k) : FixedPoint k → Fin k → Bool := fun c => readout t c

/-- The two fixed points «all first reflections» and «all second reflections» already recover the label: distinct
labels give distinct generators. -/
theorem marginal_injective (k : ℕ) : Function.Injective (marginal (k := k)) := by
  intro s t h
  funext i
  have h1 := congrFun (congrFun h (fun _ => false)) i
  have h2 := congrFun (congrFun h (fun _ => true)) i
  simp only [marginal, readout, Bool.false_eq_true, ↓reduceIte] at h1 h2
  exact Prod.ext h1 h2

/-- There are `4^k` labels, hence `n = 4^k` generators. -/
theorem card_labels (k : ℕ) : Fintype.card (Label k) = 4 ^ k := by
  simp [Label]

/-- `∑_{j ≤ k} C(k, j) 2^j = 3^k`: the faces of the boundary complex of the `k`-dimensional cross-polytope, which is
`dim S` for `(S¹/ℤ₂)^k`. -/
theorem sum_choose_mul_two_pow (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), k.choose j * 2 ^ j = 3 ^ k := by
  have h := (add_pow (2 : ℕ) 1 k).symm
  rw [show (2 : ℕ) + 1 = 3 by norm_num] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [one_pow, mul_comm]

/-- At `k = 1, 2` the extreme rays meet the bound `2d − 2` exactly. -/
theorem fms_bound_met : 4 ^ 1 = 2 * 3 ^ 1 - 2 ∧ 4 ^ 2 = 2 * 3 ^ 2 - 2 := by norm_num

/-- For `k ≥ 3`, `4^k > 2·3^k − 2`: the extreme rays exceed the bound of Fischer, Morris and Shapiro. -/
theorem fms_bound_violated {k : ℕ} (hk : 3 ≤ k) : 2 * 3 ^ k - 2 < 4 ^ k := by
  suffices h : 2 * 3 ^ k < 4 ^ k + 2 by
    have hp : 0 < 4 ^ k := by positivity
    omega
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h4 : 4 ≤ 4 ^ k := by
      calc 4 = 4 ^ 1 := by norm_num
        _ ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ, pow_succ]
    nlinarith

/-- **Proposition 2**, from the cited bound: if a complete intersection must have at most `2d − 2` extreme rays
(Fischer–Morris–Shapiro, Corollary 3.4, taken as the hypothesis `hfms`), then with `n = 4^k` extreme rays and
`d = 3^k` the semigroup of `(S¹/ℤ₂)^k` is not a complete intersection for any `k ≥ 3`. -/
theorem not_completeIntersection_of_fms {CI : Prop} {n d k : ℕ} (hfms : CI → n ≤ 2 * d - 2) (hn : n = 4 ^ k)
    (hd : d = 3 ^ k) (hk : 3 ≤ k) : ¬ CI := by
  intro hci
  have := hfms hci
  subst hn hd
  have := fms_bound_violated hk
  omega

/-- A cut ideal with `4^k` coordinates needs a graph with `2^(m−1) = 4^k` cuts, so `m = 2k + 1` vertices. -/
theorem cut_vertices {m k : ℕ} (hm : 1 ≤ m) (h : 2 ^ (m - 1) = 4 ^ k) : m = 2 * k + 1 := by
  have : (2 : ℕ) ^ (m - 1) = 2 ^ (2 * k) := by rw [h, pow_mul]; norm_num
  have := Nat.pow_right_injective (le_refl 2) this
  omega

/-- **Equation (5)**: for `k ≥ 3` the `3^k − 1` edges a cut model would need exceed the `k(2k+1)` edges of the
complete graph on `2k + 1` vertices, so `(S¹/ℤ₂)^k` is not a cut ideal. -/
theorem edges_exceed {k : ℕ} (hk : 3 ≤ k) : k * (2 * k + 1) < 3 ^ k - 1 := by
  suffices h : k * (2 * k + 1) + 1 < 3 ^ k by omega
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    nlinarith

section Extreme

open Finset

/-- The one-hot block vector of a choice `f : B → P`: in block `b`, a `1` at position `f b`. A generator of the
semigroup is the one-hot vector of its readouts (one indicator block per fixed point). -/
def oneHot {B P : Type*} [DecidableEq P] (f : B → P) : B × P → ℚ := fun bp => if f bp.1 = bp.2 then 1 else 0

theorem sum_oneHot {B P : Type*} [Fintype B] [Fintype P] [DecidableEq P] (f : B → P) :
    ∑ bp, oneHot f bp = Fintype.card B := by
  rw [Fintype.sum_prod_type]
  simp [oneHot]

/-- A one-hot block vector is not a non-negative combination of the other ones of a family of distinct choices: it
spans an extreme ray of their cone. (Summing all coordinates forces the coefficients to add up to `1`; in each block
a vector with a positive coefficient must have its `1` where `v i` has it, so it is `v i`.) -/
theorem not_cone_of_others {ι B P : Type*} [Fintype ι] [DecidableEq ι] [Fintype B] [Nonempty B] [Fintype P]
    [DecidableEq P] (v : ι → B → P) (hv : Function.Injective v) (i : ι) (c : ι → ℚ) (hc : ∀ j, 0 ≤ c j)
    (h : ∀ bp, ∑ j ∈ univ.erase i, c j * oneHot (v j) bp = oneHot (v i) bp) : False := by
  set S := ∑ j ∈ univ.erase i, c j with hS
  have hB : (0 : ℚ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  have hsum : S = 1 := by
    have := congrArg (fun g : B × P → ℚ => ∑ bp, g bp) (funext h)
    rw [Finset.sum_comm] at this
    simp only [← Finset.mul_sum, sum_oneHot] at this
    rw [← Finset.sum_mul] at this
    have : S * Fintype.card B = 1 * Fintype.card B := by rw [one_mul]; exact this
    exact mul_right_cancel₀ (ne_of_gt hB) this
  have hblock : ∀ b, ∀ j ∈ univ.erase i, c j ≠ 0 → v j b = v i b := by
    intro b
    have hb := h (b, v i b)
    simp only [oneHot, ↓reduceIte] at hb
    have hzero : ∑ j ∈ univ.erase i, c j * (1 - (if v j b = v i b then 1 else 0)) = 0 := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hb, ← hS, hsum, sub_self]
    have hnn : ∀ j ∈ univ.erase i, 0 ≤ c j * (1 - (if v j b = v i b then (1 : ℚ) else 0)) := by
      intro j _
      apply mul_nonneg (hc j)
      split_ifs <;> norm_num
    intro j hj hcj
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hzero j hj
    by_contra hne
    simp [hne, hcj] at this
  have hall : ∀ j ∈ univ.erase i, c j = 0 := by
    intro j hj
    by_contra hcj
    exact (Finset.ne_of_mem_erase hj) (hv (funext fun b => hblock b j hj hcj))
  have : S = 0 := Finset.sum_eq_zero hall
  rw [hsum] at this
  exact one_ne_zero this

/-- **Every generator of `(S¹/ℤ₂)^k` spans an extreme ray**: the one-hot vector of a label's readouts is not a
non-negative combination of those of the other labels. -/
theorem generator_extreme (k : ℕ) (t : Label k) (c : Label k → ℚ) (hc : ∀ s, 0 ≤ c s)
    (h : ∀ bp, ∑ s ∈ univ.erase t, c s * oneHot (marginal s) bp = oneHot (marginal t) bp) : False :=
  not_cone_of_others marginal (marginal_injective k) t c hc h

end Extreme

section Rank

open Matrix

/-- One circle: rows are (fixed point, bit read), columns are labels `(t₁, t₂)`. -/
def circle : Matrix (Bool × Bool) (Bool × Bool) ℚ :=
  fun cb t => if (if cb.1 then t.2 else t.1) = cb.2 then 1 else 0

/-- Rows `(false, false)`, `(false, true)`, `(true, false)` of `circle`. -/
def circleRows : Matrix (Fin 3) (Bool × Bool) ℚ :=
  circle.submatrix ![(false, false), (false, true), (true, false)] id

/-- Coefficients of the rows of `circle` in `circleRows`: row `(true, true)` is the first two minus the third. -/
def circleCoeffs : Matrix (Bool × Bool) (Fin 3) ℚ := fun cb =>
  match cb with
  | (false, false) => ![1, 0, 0]
  | (false, true) => ![0, 1, 0]
  | (true, false) => ![0, 0, 1]
  | (true, true) => ![1, 1, -1]

theorem circle_eq_mul : circle = circleCoeffs * circleRows := by
  ext ⟨c, b⟩ ⟨t₁, t₂⟩
  rw [mul_apply, Fin.sum_univ_three]
  cases c <;> cases b <;> cases t₁ <;> cases t₂ <;> norm_num [circleCoeffs, circleRows, circle]

theorem rank_circle : circle.rank = 3 := by
  apply le_antisymm
  · rw [circle_eq_mul]
    exact (rank_mul_le_left _ _).trans ((rank_le_card_width circleCoeffs).trans (by simp))
  · let r : Fin 3 → Bool × Bool := ![(false, false), (false, true), (true, false)]
    let c : Fin 3 → Bool × Bool := ![(false, false), (true, false), (false, true)]
    have hdet : (circle.submatrix r c).det ≠ 0 := by
      rw [det_fin_three]
      simp [r, c, circle]
    have hu : IsUnit (circle.submatrix r c) := (isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
    have := rank_submatrix_le circle r c
    rwa [rank_of_isUnit _ hu, Fintype.card_fin] at this

/-- The generator matrix of `(S¹/ℤ₂)^k`: column `t` is the one-hot vector of the readouts of label `t`. -/
def generators (k : ℕ) : Matrix (FixedPoint k × (Fin k → Bool)) (Label k) ℚ :=
  fun cb t => oneHot (marginal t) cb

theorem generators_eq (k : ℕ) :
    generators k = (piKronecker k circle).submatrix (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Bool) (fun _ => Bool)).symm (Equiv.refl _) := by
  ext ⟨c, b⟩ t
  simp only [generators, oneHot, marginal, piKronecker, circle, submatrix_apply]
  rw [Finset.prod_boole]
  simp only [funext_iff, Equiv.arrowProdEquivProdArrow, readout, Equiv.coe_fn_symm_mk]
  congr
  simp only [Finset.mem_univ, true_imp_iff, Equiv.refl_apply]
  exact propext (forall_congr' fun i => by rcases Bool.eq_false_or_eq_true (c i) with hc | hc <;> simp [hc])

/-- **`dim S = 3^k`**: the generators of `(S¹/ℤ₂)^k` span a space of dimension `3^k`. -/
theorem rank_generators (k : ℕ) : (generators k).rank = 3 ^ k := by
  rw [generators_eq, rank_submatrix _ _ (Equiv.refl _), rank_piKronecker, rank_circle]

end Rank

end OrbifoldProduct
