/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

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

end OrbifoldProduct
