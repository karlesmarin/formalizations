/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination

/-!
# Cayley and Segre cubics, Newton's identities, and subsets of `𝔽_p` with `e₁ = e₃ = 0`

* Models: over a field with `6 ≠ 0`, the matrix of the four nodes has determinant `−8` and turns
  the cubic `F = 2x₀³ + x₁³ + x₂³ + x₃³ − (2x₀ + x₁ + x₂ + x₃)³` into `24 σ₃`; the singular points
  of `F = 0` are exactly the four columns. The ten `±1` points of the Segre cubic are nodes, and
  they are all its singular points.
* Newton: over `ZMod p` (`p > 3`), and over any domain with `3 ≠ 0`, the first and third power
  sums of `T` vanish iff the coefficients `e₁` and `e₃` of `∏_{t ∈ T} (X − t)` do (Mathlib's
  `MvPolynomial.mul_esymm_eq_sum`).
* Counts: for `#T ≤ 4`, `e₁ = e₃ = 0` iff `T = −T`; the number `C(n, p)` of `n`-subsets of
  `ZMod p` with both moments zero is `(p − 1)/2` for `n = 3` and `(p − 1)(p − 3)/8` for `n = 4`.

## Main results

* `P3c.prop_modelos_cayley`, `P3c.prop_modelos_cayley_nodes`, `P3c.prop_modelos_segre`.
* `P3c.lem_newton`, `P3c.lem_newton_domain`.
* `P3c.n34_esym_iff_symm`, `P3c.prop_n34_three`, `P3c.prop_n34_four`.

## References

* C. Marín, *Subsets of F_p with two prescribed moments, Part I: the pair (1,3)*, Zenodo (2026),
  doi:10.5281/zenodo.22886540.
-/

@[expose] public section

open Finset

namespace P3c

/-! ## Part 1: prop:modelos -/

section Modelos

open MvPolynomial

variable {R : Type*} [CommRing R]

/-! ### Part (2): Cayley's nodal cubic -/

/-- `F = 2x₁³+x₂³+x₃³+x₄³-(2x₁+x₂+x₃+x₄)³` (indices `0..3`). -/
noncomputable def cayleyF : MvPolynomial (Fin 4) R :=
  C 2 * X 0 ^ 3 + X 1 ^ 3 + X 2 ^ 3 + X 3 ^ 3 - (C 2 * X 0 + X 1 + X 2 + X 3) ^ 3

noncomputable def cayleyStd : MvPolynomial (Fin 4) R :=
  X 0 * X 1 * X 2 + X 0 * X 1 * X 3 + X 0 * X 2 * X 3 + X 1 * X 2 * X 3

/-- Matrix whose columns are the four nodes. -/
def nodeMat : Matrix (Fin 4) (Fin 4) R :=
  !![1, 1, 1, 1; -1, -1, -1, 1; -1, -1, 1, -1; -1, 1, -1, -1]

theorem cayley_identity :
    aeval (R := R) (S₁ := MvPolynomial (Fin 4) R) (fun i => ∑ j, C (nodeMat i j) * X j) cayleyF
      = 24 * cayleyStd := by
  have h2 : (C 2 : MvPolynomial (Fin 4) R) = 2 := map_ofNat C 2
  simp [cayleyF, cayleyStd, nodeMat, Fin.sum_univ_four, h2]
  ring

theorem det_nodeMat : (nodeMat : Matrix (Fin 4) (Fin 4) R).det = -8 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, nodeMat, Fin.succAbove]
  ring

theorem node_singular (j : Fin 4) :
    eval (fun i => (nodeMat : Matrix (Fin 4) (Fin 4) R) i j) cayleyF = 0 ∧
    ∀ i, eval (fun i => (nodeMat : Matrix (Fin 4) (Fin 4) R) i j) (pderiv i cayleyF) = 0 := by
  constructor
  · fin_cases j <;> simp [cayleyF, nodeMat] <;> ring
  · intro i
    fin_cases j <;> fin_cases i <;> simp [cayleyF, nodeMat, pderiv_X] <;> ring

lemma eval_pderiv_cayleyF (x : Fin 4 → R) :
    eval x (pderiv 0 (cayleyF : MvPolynomial (Fin 4) R)) =
      6 * x 0 ^ 2 - 6 * (2 * x 0 + x 1 + x 2 + x 3) ^ 2 ∧
    ∀ i : Fin 4, i ≠ 0 → eval x (pderiv i (cayleyF : MvPolynomial (Fin 4) R)) =
      3 * x i ^ 2 - 3 * (2 * x 0 + x 1 + x 2 + x 3) ^ 2 := by
  refine ⟨?_, fun i hi => ?_⟩
  · simp [cayleyF, pderiv_X]; ring
  · fin_cases i
    · exact absurd rfl hi
    all_goals simp [cayleyF, pderiv_X]

/-- The singular points of `F = 0` in `ℙ³` (`char k ∤ 6`) are exactly the four nodes. -/
theorem cayley_sing_classification {k : Type*} [Field k] (h6 : (6 : k) ≠ 0)
    (x : Fin 4 → k) (hx : x ≠ 0) (hsing : ∀ i, eval x (pderiv i (cayleyF : MvPolynomial (Fin 4) k)) = 0) :
    ∃ j : Fin 4, ∃ c : k, c ≠ 0 ∧ x = c • (fun i => (nodeMat : Matrix (Fin 4) (Fin 4) k) i j) := by
  have h2 : (2 : k) ≠ 0 := fun h => h6 (by
    have : (6 : k) = 2 * 3 := by norm_num
    rw [this, h, zero_mul])
  have h3 : (3 : k) ≠ 0 := fun h => h6 (by
    have : (6 : k) = 2 * 3 := by norm_num
    rw [this, h, mul_zero])
  have h4 : (4 : k) ≠ 0 := by
    have : (4 : k) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  obtain ⟨hd0, hdi⟩ := eval_pderiv_cayleyF x
  obtain ⟨s, hs⟩ : ∃ s, s = 2 * x 0 + x 1 + x 2 + x 3 := ⟨_, rfl⟩
  rw [← hs] at hd0 hdi
  have hsq : ∀ i, x i ^ 2 = s ^ 2 := by
    intro i
    by_cases hi : i = 0
    · subst hi
      have h := hsing 0
      rw [hd0] at h
      have : 6 * (x 0 ^ 2 - s ^ 2) = 0 := by linear_combination h
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h6)
    · have h := hsing i
      rw [hdi i hi] at h
      have : 3 * (x i ^ 2 - s ^ 2) = 0 := by linear_combination h
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h3)
  have hpm : ∀ i, x i = s ∨ x i = -s := fun i => sq_eq_sq_iff_eq_or_eq_neg.mp (hsq i)
  have hs0 : s ≠ 0 := by
    intro h0
    apply hx
    funext i
    have := hsq i
    rw [h0] at this
    simpa using this
  have kill : ∀ c : k, c ≠ 0 → c * s = 0 → False := fun c hc h =>
    hs0 ((mul_eq_zero.mp h).resolve_left hc)
  rcases hpm 0 with e0 | e0 <;> rcases hpm 1 with e1 | e1 <;> rcases hpm 2 with e2 | e2 <;>
    rcases hpm 3 with e3 | e3 <;> rw [e0, e1, e2, e3] at hs
  all_goals try first
    | exact (kill 2 h2 (by linear_combination hs)).elim
    | exact (kill 2 h2 (by linear_combination -hs)).elim
    | exact (kill 4 h4 (by linear_combination hs)).elim
    | exact (kill 4 h4 (by linear_combination -hs)).elim
    | exact (kill 6 h6 (by linear_combination hs)).elim
  · refine ⟨3, s, hs0, ?_⟩; funext i; fin_cases i <;> simp [nodeMat, e0, e1, e2, e3]
  · refine ⟨2, s, hs0, ?_⟩; funext i; fin_cases i <;> simp [nodeMat, e0, e1, e2, e3]
  · refine ⟨1, s, hs0, ?_⟩; funext i; fin_cases i <;> simp [nodeMat, e0, e1, e2, e3]
  · refine ⟨0, -s, neg_ne_zero.mpr hs0, ?_⟩; funext i; fin_cases i <;> simp [nodeMat, e0, e1, e2, e3]

/-- `F` is the cubic of `V_(2,1^4)` after eliminating `x₅ = -(2x₁+x₂+x₃+x₄)`. -/
theorem cayleyF_eq_elim (x : Fin 4 → R) :
    2 * x 0 ^ 3 + x 1 ^ 3 + x 2 ^ 3 + x 3 ^ 3 + (-(2 * x 0 + x 1 + x 2 + x 3)) ^ 3 =
      eval x (cayleyF : MvPolynomial (Fin 4) R) := by
  simp [cayleyF]; ring

/-- **prop:modelos (2)**: over a field with `char k ∤ 6`, `M` is invertible (`det M = -8 ≠ 0`)
and `F ∘ M = 24 · (u₀u₁u₂ + u₀u₁u₃ + u₀u₂u₃ + u₁u₂u₃)` with `24 ≠ 0`: `V_(2,1^4)` is
projectively equivalent over `k` to Cayley's cubic, with no rescaling. -/
theorem prop_modelos_cayley {k : Type*} [Field k] (h6 : (6 : k) ≠ 0) :
    (nodeMat : Matrix (Fin 4) (Fin 4) k).det = -8 ∧ (-8 : k) ≠ 0 ∧ (24 : k) ≠ 0 ∧
    aeval (R := k) (S₁ := MvPolynomial (Fin 4) k) (fun i => ∑ j, C (nodeMat i j) * X j) cayleyF
      = 24 * cayleyStd := by
  have h2 : (2 : k) ≠ 0 := fun h => h6 (by
    have : (6 : k) = 2 * 3 := by norm_num
    rw [this, h, zero_mul])
  have h3 : (3 : k) ≠ 0 := fun h => h6 (by
    have : (6 : k) = 2 * 3 := by norm_num
    rw [this, h, mul_zero])
  refine ⟨det_nodeMat, ?_, ?_, cayley_identity⟩
  · have : (-8 : k) = -(2 * 2 * 2) := by norm_num
    rw [this, neg_ne_zero]
    exact mul_ne_zero (mul_ne_zero h2 h2) h2
  · have : (24 : k) = 2 * 2 * 2 * 3 := by norm_num
    rw [this]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h3

/-- **prop:modelos (2)**, the nodes: over a field with `char k ∤ 6`, the singular points of
`F = 0` in `ℙ³` are exactly the four columns of `M` (up to a nonzero scalar). -/
theorem prop_modelos_cayley_nodes {k : Type*} [Field k] (h6 : (6 : k) ≠ 0)
    (x : Fin 4 → k) (hx : x ≠ 0) :
    (∀ i, eval x (pderiv i (cayleyF : MvPolynomial (Fin 4) k)) = 0) ↔
    ∃ j : Fin 4, ∃ c : k, c ≠ 0 ∧ x = c • (fun i => (nodeMat : Matrix (Fin 4) (Fin 4) k) i j) := by
  constructor
  · exact cayley_sing_classification h6 x hx
  · rintro ⟨j, c, -, rfl⟩ i
    fin_cases j <;> fin_cases i <;> simp [cayleyF, nodeMat, pderiv_X] <;> ring

/-! ### Part (1): the Segre cubic -/

/-- Linear form `Σ yᵢ` of the Segre cubic. -/
noncomputable def segreL : MvPolynomial (Fin 6) R := ∑ i, X i

/-- Cubic form `Σ yᵢ³` of the Segre cubic. -/
noncomputable def segreG : MvPolynomial (Fin 6) R := ∑ i, X i ^ 3

/-- The sign vector with `+1` on `A` and `-1` off `A`. -/
def segreNode (A : Finset (Fin 6)) : Fin 6 → R := fun i => if i ∈ A then 1 else -1

lemma eval_pderiv_segreL (y : Fin 6 → R) (i : Fin 6) : eval y (pderiv i segreL) = 1 := by
  classical
  simp [segreL, pderiv_X, Pi.single_apply]

lemma eval_pderiv_segreG (y : Fin 6 → R) (i : Fin 6) :
    eval y (pderiv i segreG) = 3 * y i ^ 2 := by
  classical
  simp [segreG, pderiv_X, Pi.single_apply]

lemma sum_segreNode (A : Finset (Fin 6)) :
    ∑ i, (segreNode A i : R) = 2 * (#A : R) - 6 := by
  have : ∀ i, (segreNode A i : R) = 2 * (if i ∈ A then 1 else 0) - 1 := by
    intro i; unfold segreNode; split_ifs <;> ring
  simp only [this, sum_sub_distrib, ← mul_sum, sum_boole]
  simp

theorem segre_node_singular (A : Finset (Fin 6)) (hA : #A = 3) :
    eval (segreNode A) (segreL : MvPolynomial (Fin 6) R) = 0 ∧
    eval (segreNode A) (segreG : MvPolynomial (Fin 6) R) = 0 ∧
    ∀ i, eval (segreNode A) (pderiv i (segreG : MvPolynomial (Fin 6) R))
      = 3 * eval (segreNode A) (pderiv i segreL) := by
  have hc : ∀ i, (segreNode A i : R) ^ 3 = segreNode A i := by
    intro i; unfold segreNode; split_ifs <;> ring
  have hs : ∀ i, (segreNode A i : R) ^ 2 = 1 := by
    intro i; unfold segreNode; split_ifs <;> ring
  refine ⟨?_, ?_, ?_⟩
  · simp [segreL, sum_segreNode, hA]; norm_num
  · simp [segreG, hc, sum_segreNode, hA]; norm_num
  · intro i
    rw [eval_pderiv_segreG, eval_pderiv_segreL, hs]

theorem segre_sing_classification {k : Type*} [Field k] (h6 : (6 : k) ≠ 0)
    (y : Fin 6 → k) (hy : y ≠ 0)
    (hL : eval y (segreL : MvPolynomial (Fin 6) k) = 0)
    (hrank : ∃ a b : k, (a ≠ 0 ∨ b ≠ 0) ∧
      ∀ i, a * eval y (pderiv i segreL) + b * eval y (pderiv i segreG) = 0) :
    ∃ s : k, s ≠ 0 ∧ ∃ A : Finset (Fin 6), #A = 3 ∧ y = s • segreNode A := by
  classical
  have h2 : (2 : k) ≠ 0 := fun h => h6 (by
    have : (6 : k) = 2 * 3 := by norm_num
    rw [this, h, zero_mul])
  have h3 : (3 : k) ≠ 0 := fun h => h6 (by
    have : (6 : k) = 2 * 3 := by norm_num
    rw [this, h, mul_zero])
  obtain ⟨a, b, hab, hi⟩ := hrank
  simp only [eval_pderiv_segreL, eval_pderiv_segreG, mul_one] at hi
  have hb : b ≠ 0 := by
    rintro rfl
    have := hi 0
    simp at this
    rcases hab with h | h
    · exact h this
    · exact h rfl
  -- all squares equal
  have hsq : ∀ i j, y i ^ 2 = y j ^ 2 := by
    intro i j
    have hi' := hi i
    have hj' := hi j
    have : b * 3 * (y i ^ 2 - y j ^ 2) = 0 := by linear_combination hi' - hj'
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (mul_ne_zero hb h3)
    · exact sub_eq_zero.mp h
  obtain ⟨i0, hi0⟩ : ∃ i, y i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hy (funext h)
  refine ⟨y i0, hi0, univ.filter (fun i => y i = y i0), ?_, ?_⟩
  · have hy' : y = y i0 • segreNode (univ.filter (fun i => y i = y i0)) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, segreNode, mem_filter, mem_univ, true_and]
      split_ifs with h
      · rw [h, mul_one]
      · rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hsq i i0) with h' | h'
        · exact absurd h' h
        · rw [h']; ring
    have hsum : ∑ i, y i = y i0 * (2 * (#(univ.filter (fun i => y i = y i0)) : k) - 6) := by
      conv_lhs => rw [hy']
      simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum, sum_segreNode]
    have hL' : ∑ i, y i = 0 := by simpa [segreL] using hL
    rw [hL'] at hsum
    have hz : (2 * (#(univ.filter (fun i => y i = y i0)) : k) - 6) = 0 := by
      rcases mul_eq_zero.mp hsum.symm with h | h
      · exact absurd h hi0
      · exact h
    have hle : #(univ.filter (fun i => y i = y i0)) ≤ 6 := by
      calc _ ≤ #(univ : Finset (Fin 6)) := card_filter_le _ _
        _ = 6 := by simp
    have h4 : (4 : k) ≠ 0 := by
      have : (4 : k) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2
    interval_cases hc : #(univ.filter (fun i => y i = y i0))
    · exact absurd (by linear_combination -hz) h6
    · exact absurd (by linear_combination -hz) h4
    · exact absurd (by linear_combination -hz) h2
    · rfl
    · exact absurd (by linear_combination hz) h2
    · exact absurd (by linear_combination hz) h4
    · exact absurd (by linear_combination hz) h6
  · funext i
    simp only [Pi.smul_apply, smul_eq_mul, segreNode, mem_filter, mem_univ, true_and]
    split_ifs with h
    · rw [h, mul_one]
    · rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hsq i i0) with h' | h'
      · exact absurd h' h
      · rw [h']; ring

/-- The nodes come in antipodal pairs `A ↔ Aᶜ` (same projective point). -/
lemma segreNode_compl (A : Finset (Fin 6)) :
    (segreNode Aᶜ : Fin 6 → R) = -segreNode A := by
  funext i
  simp only [segreNode, mem_compl, Pi.neg_apply]
  split_ifs <;> simp_all

/-- `#{A ⊆ [6] : #A = 3} = 20`, i.e. ten projective nodes after `A ~ Aᶜ`. -/
lemma card_three_subsets : #(powersetCard 3 (univ : Finset (Fin 6))) = 20 := by
  simp [card_powersetCard]; rfl

/-- **prop:modelos (1)**: over a field with `char k ∤ 6`, the singular points of
`{Σyᵢ = Σyᵢ³ = 0} ⊂ ℙ⁵` (points where the `2×6` Jacobian has rank `< 2`) are exactly the
multiples of the sign vectors with three `+1` and three `-1`. -/
theorem prop_modelos_segre {k : Type*} [Field k] (h6 : (6 : k) ≠ 0) (y : Fin 6 → k) (hy : y ≠ 0) :
    (eval y (segreL : MvPolynomial (Fin 6) k) = 0 ∧ eval y (segreG : MvPolynomial (Fin 6) k) = 0 ∧
      ∃ a b : k, (a ≠ 0 ∨ b ≠ 0) ∧
        ∀ i, a * eval y (pderiv i segreL) + b * eval y (pderiv i segreG) = 0) ↔
    ∃ s : k, s ≠ 0 ∧ ∃ A : Finset (Fin 6), #A = 3 ∧ y = s • segreNode A := by
  constructor
  · rintro ⟨hL, -, hrank⟩
    exact segre_sing_classification h6 y hy hL hrank
  · rintro ⟨s, -, A, hA, rfl⟩
    obtain ⟨hL, hG, hJ⟩ := segre_node_singular (R := k) A hA
    have hcube : ∀ i, (s • segreNode A : Fin 6 → k) i ^ 3 = s ^ 3 * segreNode A i := by
      intro i
      have : (segreNode A i : k) ^ 3 = segreNode A i := by
        unfold segreNode; split_ifs <;> ring
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow, this]
    have hL' : ∑ i, (segreNode A i : k) = 0 := by simpa [segreL] using hL
    refine ⟨?_, ?_, 3 * s ^ 2, -1, Or.inr (by norm_num), fun i => ?_⟩
    · simp only [segreL, map_sum, eval_X, Pi.smul_apply, smul_eq_mul, ← mul_sum]
      rw [hL', mul_zero]
    · simp only [segreG, map_sum, map_pow, eval_X, hcube, ← mul_sum]
      rw [hL', mul_zero]
    · rw [eval_pderiv_segreL, eval_pderiv_segreG]
      have : (segreNode A i : k) ^ 2 = 1 := by
        unfold segreNode; split_ifs <;> ring
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow, this]
      ring

end Modelos

/-! ## Part 2: lem:newton and prop:n34 -/

section Newton

variable {R : Type*} [CommRing R]

/-- Power sum `M_j(T) = Σ_{t∈T} t^j`. -/
def moment (j : ℕ) (T : Finset R) : R := ∑ t ∈ T, t ^ j

/-- Elementary symmetric function `e_j(T)`. -/
def esym (j : ℕ) (T : Finset R) : R := T.val.esymm j

theorem newton_three (T : Finset R) :
    3 * esym 3 T = moment 3 T - esym 1 T * moment 2 T + esym 2 T * moment 1 T := by
  classical
  have h := MvPolynomial.mul_esymm_eq_sum {x // x ∈ T} R 3
  have h' := congrArg (MvPolynomial.aeval (R := R) (fun x : {x // x ∈ T} => (x : R))) h
  have hval : (univ : Finset {x // x ∈ T}).val.map (fun x : {x // x ∈ T} => (x : R)) = T.val := by
    rw [univ_eq_attach, attach_val]; exact Multiset.attach_map_val T.val
  have he : ∀ j, MvPolynomial.aeval (fun x : {x // x ∈ T} => (x : R))
      (MvPolynomial.esymm {x // x ∈ T} R j) = esym j T := by
    intro j
    rw [MvPolynomial.aeval_esymm_eq_multiset_esymm, hval]; rfl
  have hp : ∀ j, MvPolynomial.aeval (fun x : {x // x ∈ T} => (x : R))
      (MvPolynomial.psum {x // x ∈ T} R j) = moment j T := by
    intro j
    simp [MvPolynomial.psum, moment, sum_attach T (fun t => t ^ j)]
  simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum, he, hp] at h'
  have hanti : (antidiagonal 3).filter (fun a : ℕ × ℕ => a.1 < 3) =
      {(0, 3), (1, 2), (2, 1)} := by decide
  rw [hanti] at h'
  simp [sum_insert, esym, Multiset.esymm, Multiset.powersetCard_zero_left] at h'
  simp only [esym, Multiset.esymm]
  linear_combination h'

lemma esym_one (T : Finset R) : esym 1 T = moment 1 T := by
  simp [esym, moment, Multiset.esymm, Multiset.powersetCard_one]

/-- `M₁ = M₃ = 0 ⇔ e₁ = e₃ = 0` when `3 ≠ 0` in a domain. -/
theorem moments_iff_esym [IsDomain R] (h3 : (3 : R) ≠ 0) (T : Finset R) :
    (moment 1 T = 0 ∧ moment 3 T = 0) ↔ (esym 1 T = 0 ∧ esym 3 T = 0) := by
  have hN := newton_three T
  rw [esym_one] at hN ⊢
  constructor
  · rintro ⟨h1, h3'⟩
    refine ⟨h1, ?_⟩
    simp only [h1, h3', mul_zero, zero_mul, sub_zero, add_zero] at hN
    rcases mul_eq_zero.mp hN with h | h
    · exact absurd h h3
    · exact h
  · rintro ⟨h1, he3⟩
    refine ⟨h1, ?_⟩
    rw [h1, he3, mul_zero, mul_zero, zero_mul, add_zero, sub_zero] at hN
    exact hN.symm

/-- Value of `∏_{t∈T} (x - t)` in terms of the `e_j`. -/
lemma prod_sub_eq_sum_esym (T : Finset R) (x : R) :
    ∏ t ∈ T, (x - t) =
      ∑ j ∈ range (#T + 1), (-1) ^ j * esym j T * x ^ (#T - j) := by
  have h := congrArg (Polynomial.eval x) (Multiset.prod_X_sub_X_eq_sum_esymm T.val)
  simp only [Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_def,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one] at h
  rw [prod_eq_multiset_prod, h]
  simp [esym, card_val, mul_assoc]

open Polynomial in
/-- Coefficient of `X^m` for an integer exponent `m` (zero when `m < 0`), so that
"the coefficient of `X^{n-3}`" is meaningful for every `n`. -/
noncomputable def coeffZ (P : R[X]) (m : ℤ) : R := if m < 0 then 0 else P.coeff m.toNat

open Polynomial in
lemma coeffZ_prod (T : Finset R) (j : ℕ) :
    coeffZ (∏ t ∈ T, (X - C t)) ((#T : ℤ) - j) = (-1) ^ j * esym j T := by
  unfold coeffZ
  by_cases hj : j ≤ #T
  · rw [ite_eq_right (by omega)]
    have hk : ((#T : ℤ) - j).toNat = #T - j := by omega
    rw [hk, prod_eq_multiset_prod, Multiset.prod_X_sub_C_coeff T.val (by simp)]
    simp only [card_val, Nat.sub_sub_self hj, esym]
  · rw [ite_eq_left (by omega)]
    have : esym j T = 0 := by
      simp only [esym, Multiset.esymm]
      rw [Multiset.powersetCard_eq_empty j (by simp; omega)]
      simp
    rw [this, mul_zero]

open Polynomial in
/-- **lem:newton**, over any domain in which `3 ≠ 0`. -/
theorem lem_newton_domain [IsDomain R] (h3 : (3 : R) ≠ 0) (T : Finset R) :
    (moment 1 T = 0 ∧ moment 3 T = 0) ↔
      (coeffZ (∏ t ∈ T, (X - C t)) ((#T : ℤ) - 1) = 0 ∧
       coeffZ (∏ t ∈ T, (X - C t)) ((#T : ℤ) - 3) = 0) := by
  rw [moments_iff_esym h3]
  have h1 := coeffZ_prod T 1
  have h3' := coeffZ_prod T 3
  push_cast at h1 h3'
  rw [h1, h3']
  simp

end Newton

section N34

variable {p : ℕ}

/-- `T = -T` (as a property: `T` is stable under negation). -/
def SymmNeg {R : Type*} [Ring R] (T : Finset R) : Prop := ∀ x ∈ T, -x ∈ T

instance {R : Type*} [Ring R] [DecidableEq R] (T : Finset R) : Decidable (SymmNeg T) := by
  unfold SymmNeg; infer_instance

lemma two_ne_zero_zmod (hp3 : 3 < p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  have := Nat.le_of_dvd (by norm_num) this
  omega

lemma three_ne_zero_zmod (hp3 : 3 < p) : (3 : ZMod p) ≠ 0 := by
  intro h
  have : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  have := Nat.le_of_dvd (by norm_num) this
  omega

/-- A set stable under negation has vanishing odd power sums (`p` odd). -/
lemma moment_odd_eq_zero [Fact p.Prime] (hp3 : 3 < p) {T : Finset (ZMod p)} (hT : SymmNeg T)
    {j : ℕ} (hj : Odd j) : moment j T = 0 := by
  have h : moment j T = - moment j T := by
    unfold moment
    rw [← sum_neg_distrib]
    refine sum_nbij' (fun x => -x) (fun x => -x) (fun x hx => hT x hx) (fun x hx => hT x hx)
      (fun x _ => neg_neg x) (fun x _ => neg_neg x) (fun x _ => ?_)
    rw [hj.neg_pow, neg_neg]
  have h2 : (2 : ZMod p) * moment j T = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h' | h'
  · exact absurd h' (two_ne_zero_zmod hp3)
  · exact h'

/-- prop:n34, first claim: for `p > 3` and `#T ≤ 4`, `e₁ = e₃ = 0 ⇔ T = -T`. -/
theorem n34_esym_iff_symm [Fact p.Prime] (hp3 : 3 < p) (T : Finset (ZMod p)) (hn : #T ≤ 4) :
    (esym 1 T = 0 ∧ esym 3 T = 0) ↔ SymmNeg T := by
  constructor
  · rintro ⟨h1, h3⟩ x hx
    have hfx : ∏ t ∈ T, (x - t) = 0 := prod_eq_zero hx (sub_self x)
    have hneg : ∏ t ∈ T, (-x - t) = (-1) ^ #T * ∏ t ∈ T, (x - t) := by
      rw [prod_sub_eq_sum_esym, prod_sub_eq_sum_esym]
      interval_cases h : #T <;> simp [sum_range_succ, h1, h3] <;> ring
    rw [hfx, mul_zero] at hneg
    obtain ⟨t, ht, h0⟩ := prod_eq_zero_iff.mp hneg
    have : t = -x := by linear_combination -h0
    rw [← this]; exact ht
  · intro hT
    rw [← moments_iff_esym (three_ne_zero_zmod hp3)]
    exact ⟨moment_odd_eq_zero hp3 hT odd_one, moment_odd_eq_zero hp3 hT (by decide)⟩

open Polynomial in
/-- **lem:newton** (`p > 3`): `M₁(T) = M₃(T) = 0` iff the coefficients of `X^{n-1}` and
`X^{n-3}` in `∏_{t∈T} (X - t)` vanish, `n = #T`. -/
theorem lem_newton [Fact p.Prime] (hp3 : 3 < p) (T : Finset (ZMod p)) :
    (moment 1 T = 0 ∧ moment 3 T = 0) ↔
      (coeffZ (∏ t ∈ T, (X - C t)) ((#T : ℤ) - 1) = 0 ∧
       coeffZ (∏ t ∈ T, (X - C t)) ((#T : ℤ) - 3) = 0) :=
  lem_newton_domain (three_ne_zero_zmod hp3) T

/-- `C(n,p)`: number of `n`-subsets `T ⊆ 𝔽_p` with `M₁(T) = M₃(T) = 0`. -/
def C13 (n p : ℕ) [NeZero p] : ℕ :=
  #((powersetCard n (univ : Finset (ZMod p))).filter (fun T => moment 1 T = 0 ∧ moment 3 T = 0))

/-- Representatives of the antipodal pairs: `{x : 1 ≤ val x ≤ p/2}`. -/
def halfReps (p : ℕ) [NeZero p] : Finset (ZMod p) :=
  univ.filter (fun x => 1 ≤ x.val ∧ x.val ≤ p / 2)

lemma card_halfReps (p : ℕ) [NeZero p] : #(halfReps p) = p / 2 := by
  have hp0 : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hI : #(Icc 1 (p / 2)) = p / 2 := by simp
  rw [← hI]
  refine card_nbij' (fun x => x.val) (fun k => (k : ZMod p)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [halfReps, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
    simpa using hx
  · intro k hk
    simp only [coe_Icc, Set.mem_Icc] at hk
    simp only [halfReps, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    exact hk
  · intro x _
    exact ZMod.natCast_zmod_val x
  · intro k hk
    simp only [coe_Icc, Set.mem_Icc] at hk
    simp only
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]

lemma zero_notMem_halfReps (p : ℕ) [NeZero p] : (0 : ZMod p) ∉ halfReps p := by
  simp [halfReps]

/-- For `x ≠ 0` and `p` odd, exactly one of `x`, `-x` is a representative. -/
lemma halfReps_xor [Fact p.Prime] (hodd : p % 2 = 1) {x : ZMod p} (hx : x ≠ 0) :
    (x ∈ halfReps p ↔ -x ∉ halfReps p) := by
  have hv : (-x).val = p - x.val := by rw [ZMod.neg_val, ite_eq_right hx]
  have hlt := ZMod.val_lt x
  have hpos : x.val ≠ 0 := fun h => hx ((ZMod.val_eq_zero x).mp h)
  simp only [halfReps, mem_filter, mem_univ, true_and, hv]
  omega

/-- Cardinality of a negation-stable set: `#T = 2·#(T ∩ H) + [0 ∈ T]`. -/
lemma card_symm [Fact p.Prime] (hodd : p % 2 = 1) {T : Finset (ZMod p)} (hT : SymmNeg T) :
    #T = 2 * #(T.filter (· ∈ halfReps p)) + (if (0 : ZMod p) ∈ T then 1 else 0) := by
  have hsplit := card_filter_add_card_filter_not (s := T) (· ∈ halfReps p)
  have himg : (T.filter (· ∉ halfReps p)).erase 0 =
      (T.filter (· ∈ halfReps p)).image (fun x => -x) := by
    ext y
    simp only [mem_erase, mem_filter, mem_image]
    constructor
    · rintro ⟨hy0, hyT, hyH⟩
      refine ⟨-y, ⟨hT y hyT, ?_⟩, neg_neg y⟩
      by_contra h
      exact hyH ((halfReps_xor hodd hy0).mpr h)
    · rintro ⟨z, ⟨hzT, hzH⟩, rfl⟩
      have hz0 : z ≠ 0 := fun h => zero_notMem_halfReps p (h ▸ hzH)
      exact ⟨neg_ne_zero.mpr hz0, hT z hzT, (halfReps_xor hodd hz0).mp hzH⟩
  have hcimg : #((T.filter (· ∈ halfReps p)).image (fun x => -x)) =
      #(T.filter (· ∈ halfReps p)) := card_image_of_injective _ neg_injective
  rw [← himg] at hcimg
  split_ifs with h0
  · have h0' : (0 : ZMod p) ∈ T.filter (· ∉ halfReps p) :=
      mem_filter.mpr ⟨h0, zero_notMem_halfReps p⟩
    have := card_erase_add_one h0'
    omega
  · have h0' : (0 : ZMod p) ∉ T.filter (· ∉ halfReps p) := fun h => h0 (mem_filter.mp h).1
    rw [erase_eq_of_notMem h0'] at hcimg
    omega

/-- The negation-stable set generated by `S ⊆ H`, with `0` added iff `b`. -/
def symmOf (b : Bool) (S : Finset (ZMod p)) : Finset (ZMod p) :=
  (if b then {0} else ∅) ∪ (S ∪ S.image (fun x => -x))

lemma symmOf_symm (b : Bool) (S : Finset (ZMod p)) : SymmNeg (symmOf b S) := by
  intro x hx
  simp only [symmOf, mem_union, mem_image] at hx ⊢
  rcases hx with h | h | ⟨z, hz, rfl⟩
  · left; split_ifs at h ⊢ with hb
    · simp only [mem_singleton] at h ⊢; rw [h, neg_zero]
    · simp at h
  · right; right; exact ⟨x, h, rfl⟩
  · right; left; rw [neg_neg]; exact hz

lemma symmOf_filter [Fact p.Prime] (hodd : p % 2 = 1) (b : Bool) {S : Finset (ZMod p)}
    (hS : S ⊆ halfReps p) : (symmOf b S).filter (· ∈ halfReps p) = S := by
  ext x
  simp only [symmOf, mem_filter, mem_union, mem_image]
  constructor
  · rintro ⟨h | h | ⟨z, hz, rfl⟩, hxH⟩
    · split_ifs at h
      · simp only [mem_singleton] at h; subst h; exact absurd hxH (zero_notMem_halfReps p)
      · simp at h
    · exact h
    · have hz0 : z ≠ 0 := fun h => zero_notMem_halfReps p (h ▸ hS hz)
      exact absurd hxH ((halfReps_xor hodd hz0).mp (hS hz))
  · intro hx
    exact ⟨Or.inr (Or.inl hx), hS hx⟩

lemma zero_mem_symmOf_iff [Fact p.Prime] (b : Bool) {S : Finset (ZMod p)}
    (hS : S ⊆ halfReps p) : (0 : ZMod p) ∈ symmOf b S ↔ b = true := by
  simp only [symmOf, mem_union, mem_image]
  constructor
  · rintro (h | h | ⟨z, hz, hz0⟩)
    · split_ifs at h with hb
      · exact hb
      · simp at h
    · exact absurd (hS h) (zero_notMem_halfReps p)
    · have : z = 0 := neg_eq_zero.mp hz0
      exact absurd (this ▸ hS hz) (zero_notMem_halfReps p)
  · intro hb; left; simp [hb]

/-- Two negation-stable sets with the same representatives and the same `0`-status coincide. -/
lemma symm_ext [Fact p.Prime] (hodd : p % 2 = 1) {T T' : Finset (ZMod p)} (hT : SymmNeg T)
    (hT' : SymmNeg T') (h0 : (0 : ZMod p) ∈ T ↔ (0 : ZMod p) ∈ T')
    (hf : T.filter (· ∈ halfReps p) = T'.filter (· ∈ halfReps p)) : T = T' := by
  have key : ∀ y ∈ halfReps p, (y ∈ T ↔ y ∈ T') := by
    intro y hy
    have := congrArg (y ∈ ·) hf
    simpa [mem_filter, hy] using this
  ext x
  by_cases hx0 : x = 0
  · subst hx0; exact h0
  by_cases hxH : x ∈ halfReps p
  · exact key x hxH
  · have hnx : -x ∈ halfReps p := by
      by_contra h
      exact hxH ((halfReps_xor hodd hx0).mpr h)
    constructor
    · intro hx
      have := (key _ hnx).mp (hT x hx)
      simpa using hT' _ this
    · intro hx
      have := (key _ hnx).mpr (hT' x hx)
      simpa using hT _ this

/-- Counting negation-stable `n`-sets with prescribed `0`-status:
they are in bijection with `k`-subsets of `H`, `n = 2k + [b]`. -/
lemma card_symm_sets [Fact p.Prime] (hodd : p % 2 = 1) (b : Bool) (k : ℕ) :
    #((powersetCard (2 * k + (if b then 1 else 0)) (univ : Finset (ZMod p))).filter
        (fun T => SymmNeg T ∧ ((0 : ZMod p) ∈ T ↔ b = true))) =
      (p / 2).choose k := by
  rw [← card_halfReps p, ← card_powersetCard]
  refine card_bij (fun T _ => T.filter (· ∈ halfReps p)) ?_ ?_ ?_
  · intro T hT
    simp only [mem_filter, mem_powersetCard] at hT
    obtain ⟨⟨_, hcard⟩, hsym, hb⟩ := hT
    refine mem_powersetCard.mpr ⟨fun x hx => (mem_filter.mp hx).2, ?_⟩
    have := card_symm hodd hsym
    cases b <;> simp_all
  · intro T hT T' hT' h
    simp only [mem_filter, mem_powersetCard] at hT hT'
    exact symm_ext hodd hT.2.1 hT'.2.1 (by rw [hT.2.2, hT'.2.2]) h
  · intro S hS
    obtain ⟨hSH, hSk⟩ := mem_powersetCard.mp hS
    refine ⟨symmOf b S, ?_, symmOf_filter hodd b hSH⟩
    simp only [mem_filter, mem_powersetCard]
    refine ⟨⟨subset_univ _, ?_⟩, symmOf_symm b S, zero_mem_symmOf_iff b hSH⟩
    rw [card_symm hodd (symmOf_symm b S), symmOf_filter hodd b hSH, hSk]
    have := zero_mem_symmOf_iff b hSH
    cases b <;> simp_all

lemma odd_of_prime [Fact p.Prime] (hp3 : 3 < p) : p % 2 = 1 := by
  by_contra h
  have h2 : 2 ∣ p := by omega
  rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd 2 h2 with h' | h'
  all_goals omega

/-- For `#T = n ≤ 4`: `M₁ = M₃ = 0 ⇔ T = -T` (lem:newton + first claim of prop:n34). -/
lemma moments_iff_symm [Fact p.Prime] (hp3 : 3 < p) (T : Finset (ZMod p)) (hn : #T ≤ 4) :
    (moment 1 T = 0 ∧ moment 3 T = 0) ↔ SymmNeg T := by
  rw [moments_iff_esym (three_ne_zero_zmod hp3), n34_esym_iff_symm hp3 T hn]

lemma C_eq_card_symm [Fact p.Prime] (hp3 : 3 < p) (b : Bool) (k : ℕ)
    (hk : 2 * k + (if b then 1 else 0) ≤ 4) (hpar : ∀ T : Finset (ZMod p),
      #T = 2 * k + (if b then 1 else 0) → SymmNeg T → ((0 : ZMod p) ∈ T ↔ b = true)) :
    C13 (2 * k + (if b then 1 else 0)) p = (p / 2).choose k := by
  rw [← card_symm_sets (odd_of_prime hp3) b k, C13]
  congr 1
  refine filter_congr (fun T hT => ?_)
  have hcard := (mem_powersetCard.mp hT).2
  rw [moments_iff_symm hp3 T (hcard ▸ hk)]
  exact ⟨fun h => ⟨h, hpar T hcard h⟩, fun h => h.1⟩

/-- **prop:n34**, `n = 3`: `C(3,p) = (p-1)/2` (and `2·C(3,p) = p-1`). -/
theorem prop_n34_three [Fact p.Prime] (hp3 : 3 < p) :
    2 * C13 3 p = p - 1 ∧ C13 3 p = (p - 1) / 2 := by
  have hodd := odd_of_prime hp3
  have h := C_eq_card_symm hp3 true 1 (by simp) (fun T hT hs => by
    have := card_symm hodd hs
    split_ifs at this with h0
    · simpa using h0
    · simp at hT; omega)
  simp only [ite_true, Nat.choose_one_right] at h
  rw [show 2 * 1 + 1 = 3 by rfl] at h
  omega

/-- **prop:n34**, `n = 4`: `C(4,p) = (p-1)(p-3)/8` (and `8·C(4,p) = (p-1)(p-3)`). -/
theorem prop_n34_four [Fact p.Prime] (hp3 : 3 < p) :
    8 * C13 4 p = (p - 1) * (p - 3) ∧ C13 4 p = (p - 1) * (p - 3) / 8 := by
  have hodd := odd_of_prime hp3
  have h := C_eq_card_symm hp3 false 2 (by simp) (fun T hT hs => by
    have := card_symm hodd hs
    split_ifs at this with h0
    · simp at hT; omega
    · simpa using h0)
  simp only [Bool.false_eq_true, ite_false, add_zero] at h
  rw [show 2 * 2 = 4 by rfl, Nat.choose_two_right] at h
  obtain ⟨r, hr⟩ := Nat.even_mul_pred_self (p / 2)
  have hm1 : p - 1 = 2 * (p / 2) := by omega
  have hm3 : p - 3 = 2 * (p / 2 - 1) := by omega
  have h8 : 8 * C13 4 p = (p - 1) * (p - 3) := by
    rw [h, hr, hm1, hm3]
    have : (r + r) / 2 = r := by omega
    rw [this]
    have h4 : 2 * (p / 2) * (2 * (p / 2 - 1)) = 4 * ((p / 2) * (p / 2 - 1)) := by ring
    rw [h4, hr]; ring
  exact ⟨h8, by omega⟩

end N34

end P3c
