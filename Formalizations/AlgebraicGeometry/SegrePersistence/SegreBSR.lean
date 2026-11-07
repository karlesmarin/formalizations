/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

-- encaje: núcleo de la cota superior del Teorema 2 (qp(P^{m-1} × P^3) ≤ ⌈4m/3⌉) de la nota qp_bsr.
public import Mathlib.Algebra.Polynomial.RuleOfSigns
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# Descartes' rule and the linear algebra behind `qp(ℙ^{m-1} × ℙ³) ≤ ⌈4m/3⌉`

This file formalizes the linear-algebra core of the upper bound in Theorem 2 of
C. Marín, *Quadratic persistence of Segre varieties and a linear gap between biquadratic SOS rank
and Zarankiewicz bounds* (2026). With `b x = (1, x, x³)`: any three `b x` at distinct positive
nodes are independent, any six symmetric squares `b x ⊗ b x` are independent, and the
coefficients `c i j` attached to one group, or to two disjoint groups `U, V`, satisfying the
relations `∑_{j ∈ S} c i j • b j ∈ ℝ • b i` (equation (grupo) of the note) all vanish.

Everything is over `ℝ`, with arbitrary distinct positive real nodes (the note uses the integers
`1, …, m`, a special case).

## Main results

* `SegrePersistence.signVariations_lt_card_support`: a nonzero real polynomial has fewer sign
  variations than nonzero coefficients.
* `SegrePersistence.monomial_combination_eq_zero`: a combination of `k` distinct monomials
  vanishing at `≥ k` distinct positive nodes is zero (Descartes' rule of signs,
  `Polynomial.roots_countP_pos_le_signVariations`).
* `SegrePersistence.pow_linearIndependent`: the vectors `(t i ^ e j)_j`, for at most `k` distinct
  positive nodes `t i` and `k` distinct exponents `e j`, are linearly independent.
* `SegrePersistence.descartes_six`, `SegrePersistence.three_independent`: the instances with
  exponents `{0,1,2,3,4,6}` and `{0,1,3}`.
* `SegrePersistence.group_vanish`: inside one group (at most three nodes) the relations force
  `c i j = 0` for `j ≠ i`.
* `SegrePersistence.cross_vanish`: the key step for two disjoint groups `U, V`.

## What is not covered

The identification of `𝒟` with `⋀²A* ⊗ ⋀²B*`, the factorization
`D_{ij} = c_{ij} vol(b_i, b_j, ·, ·)` and the derivation of the relations (grupo) from the radical
conditions (hence the statement `qp ≤ ⌈4m/3⌉` itself), and the lower bound of Theorem 2, are not
formalized here.
-/

@[expose] public section

open Polynomial Finset

namespace SegrePersistence

/-- A nonzero real polynomial has strictly fewer sign variations than nonzero coefficients. -/
theorem signVariations_lt_card_support (P : ℝ[X]) (hP : P ≠ 0) :
    P.signVariations < P.support.card := by
  classical
  have hlen : ((P.coeffList.map SignType.sign).filter (· ≠ 0)).length = P.support.card := by
    have hq : P.support = ((List.range (P.natDegree + 1)).filter
        (fun i => decide (SignType.sign (P.coeff i) ≠ 0))).toFinset := by
      ext i
      simp only [mem_support_iff, List.mem_toFinset, List.mem_filter, List.mem_range,
        decide_eq_true_eq, ne_eq, sign_eq_zero_iff]
      exact ⟨fun h => ⟨Nat.lt_succ_of_le (le_natDegree_of_ne_zero h), h⟩, fun h => h.2⟩
    rw [hq, List.toFinset_card_of_nodup (List.nodup_range.filter _), coeffList_of_ne_zero hP,
      List.map_map, List.filter_map, List.length_map, List.filter_reverse, List.length_reverse]
    rfl
  have hpos : 0 < P.support.card := Finset.card_pos.mpr (Polynomial.support_nonempty.mpr hP)
  have h1 : P.signVariations ≤ ((P.coeffList.map SignType.sign).filter (· ≠ 0)).length - 1 := by
    unfold Polynomial.signVariations List.signVariations
    exact Nat.sub_le_sub_right (List.destutter_sublist _ _).length_le 1
  omega

/-- **Descartes, monomial form.** A combination of distinct monomials `X ^ e j` that vanishes at
at least as many distinct positive nodes as it has monomials is zero. -/
theorem monomial_combination_eq_zero {ι κ : Type*} [Fintype ι] [Fintype κ]
    (t : ι → ℝ) (ht : Function.Injective t) (hpos : ∀ i, 0 < t i)
    (e : κ → ℕ) (he : Function.Injective e) (hcard : Fintype.card κ ≤ Fintype.card ι)
    (c : κ → ℝ) (h : ∀ i, ∑ j, c j * t i ^ e j = 0) : c = 0 := by
  classical
  set P : ℝ[X] := ∑ j, C (c j) * X ^ e j with hPdef
  have hcoeff : ∀ j, P.coeff (e j) = c j := by
    intro j
    rw [hPdef, finsetSum_coeff, Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      have hne : ¬ e j = e b := fun hh => hb (he hh.symm)
      simp only [coeff_C_mul_X_pow, hne, ↓reduceIte]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  have heval : ∀ i, P.eval (t i) = 0 := by
    intro i
    simp [hPdef, eval_finsetSum, h i]
  by_contra hc
  have hP : P ≠ 0 := by
    intro h0; apply hc; funext j; rw [← hcoeff j, h0]; simp
  have hsupp : P.support ⊆ Finset.univ.image e := by
    intro n hn
    rw [mem_support_iff] at hn
    by_contra hn'
    apply hn
    rw [hPdef, finsetSum_coeff]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hne : ¬ n = e j := by
      rintro rfl
      exact hn' (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    simp only [coeff_C_mul_X_pow, hne, ↓reduceIte]
  have hsc : P.support.card ≤ Fintype.card κ :=
    (Finset.card_le_card hsupp).trans (Finset.card_image_le.trans (by simp))
  have hroots : Fintype.card ι ≤ P.roots.countP (0 < ·) := by
    rw [Multiset.countP_eq_card_filter]
    calc Fintype.card ι = (Finset.univ.image t).card := by
          rw [Finset.card_image_of_injective _ ht]; simp
      _ ≤ (P.roots.filter (0 < ·)).toFinset.card := by
          apply Finset.card_le_card
          intro x hx
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
          simp [Multiset.mem_toFinset, mem_roots hP, hpos i, heval i]
      _ ≤ _ := Multiset.toFinset_card_le _
  have h1 := roots_countP_pos_le_signVariations P
  have h2 := signVariations_lt_card_support P hP
  omega

/-- Dual form: at most `k` distinct positive nodes and `k` distinct exponents, a combination of
the nodes killed by every exponent is zero. -/
theorem pow_dual {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (t : ι → ℝ) (ht : Function.Injective t) (hpos : ∀ i, 0 < t i)
    (e : κ → ℕ) (he : Function.Injective e) (hcard : Fintype.card ι ≤ Fintype.card κ)
    (a : ι → ℝ) (h : ∀ j, ∑ i, a i * t i ^ e j = 0) : a = 0 := by
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard
  let M : Matrix ι ι ℝ := fun i i' => t i ^ e (f i')
  have hinj : Function.Injective M.mulVec := by
    intro x y hxy
    have hd : M.mulVec (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    have := monomial_combination_eq_zero t ht hpos (e ∘ f) (he.comp f.injective) le_rfl (x - y)
      (fun i => by
        have := congrFun hd i
        simp only [Matrix.mulVec, dotProduct, M, Pi.zero_apply] at this
        rw [← this]
        exact Finset.sum_congr rfl fun j _ => by simp [mul_comm])
    exact sub_eq_zero.mp this
  have hv := Matrix.vecMul_injective_iff_isUnit.mpr (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  apply hv
  show Matrix.vecMul a M = Matrix.vecMul 0 M
  rw [Matrix.zero_vecMul]
  funext i'
  exact h (f i')

/-- **Generalized Vandermonde independence.** For at most `k` distinct positive nodes `t i` and
`k` distinct exponents `e j`, the vectors `(t i ^ e j)_j` are linearly independent. -/
theorem pow_linearIndependent {ι κ : Type*} [Fintype ι] [Fintype κ]
    (t : ι → ℝ) (ht : Function.Injective t) (hpos : ∀ i, 0 < t i)
    (e : κ → ℕ) (he : Function.Injective e) (hcard : Fintype.card ι ≤ Fintype.card κ) :
    LinearIndependent ℝ (fun i : ι => fun j : κ => t i ^ e j) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have := pow_dual t ht hpos e he hcard g (fun j => by
    have := congrFun hg j
    simpa [Finset.sum_apply] using this)
  exact congrFun this i

/-- Finset form of `pow_dual`. -/
theorem pow_dual_finset {α κ : Type*} [Fintype κ] (W : Finset α) (t : α → ℝ)
    (ht : Set.InjOn t W) (hpos : ∀ x ∈ W, 0 < t x)
    (e : κ → ℕ) (he : Function.Injective e) (hcard : W.card ≤ Fintype.card κ)
    (a : α → ℝ) (h : ∀ j, ∑ x ∈ W, a x * t x ^ e j = 0) : ∀ x ∈ W, a x = 0 := by
  classical
  have := pow_dual (ι := W) (fun x => t x) (fun x y hxy => Subtype.ext (ht x.2 y.2 hxy))
    (fun x => hpos x x.2) e he (by simpa using hcard) (fun x => a x)
    (fun j => by rw [Finset.sum_coe_sort W (fun x => a x * t x ^ e j)]; exact h j)
  intro x hx
  exact congrFun this ⟨x, hx⟩

/-- **Six symmetric monomials.** For distinct positive nodes, the vectors
`(1, t, t², t³, t⁴, t⁶)` are linearly independent in `ℝ⁶`. -/
theorem descartes_six (t : Fin 6 → ℝ) (ht : Function.Injective t) (hpos : ∀ i, 0 < t i) :
    LinearIndependent ℝ (fun i => ![1, t i, t i ^ 2, t i ^ 3, t i ^ 4, t i ^ 6]) := by
  have := pow_linearIndependent t ht hpos (![0, 1, 2, 3, 4, 6] : Fin 6 → ℕ) (by decide) le_rfl
  convert this using 1
  funext i j
  fin_cases j <;> simp

/-- **Three monomials.** For distinct positive nodes, the vectors `(1, t, t³)` are linearly
independent in `ℝ³`. -/
theorem three_independent (t : Fin 3 → ℝ) (ht : Function.Injective t) (hpos : ∀ i, 0 < t i) :
    LinearIndependent ℝ (fun i => ![1, t i, t i ^ 3]) := by
  have := pow_linearIndependent t ht hpos (![0, 1, 3] : Fin 3 → ℕ) (by decide) le_rfl
  convert this using 1
  funext i j
  fin_cases j <;> simp

/-- The vector `b x = (1, x, x³)` of the note. -/
def b (x : ℝ) : Fin 3 → ℝ := ![1, x, x ^ 3]

/-- The symmetric square `b x ⊗ b x`, as a `3 × 3` array. -/
def sq (x : ℝ) : Fin 3 → Fin 3 → ℝ := fun p q => b x p * b x q

/-- At most three distinct positive nodes: the `b x` are independent (finset form). -/
theorem b_independent (S : Finset ℝ) (hpos : ∀ x ∈ S, 0 < x) (hS : S.card ≤ 3)
    (a : ℝ → ℝ) (h : ∑ x ∈ S, a x • b x = 0) : ∀ x ∈ S, a x = 0 := by
  refine pow_dual_finset S id (Set.injOn_id _) hpos (![0, 1, 3] : Fin 3 → ℕ) (by decide)
    (by simpa using hS) a fun j => ?_
  have := congrFun h j
  rw [Finset.sum_apply] at this
  refine (Finset.sum_congr rfl fun x _ => ?_).trans this
  fin_cases j <;> simp [b]

/-- At most six distinct positive nodes: the `b x ⊗ b x` are independent (finset form). -/
theorem sq_independent (S : Finset ℝ) (hpos : ∀ x ∈ S, 0 < x) (hS : S.card ≤ 6)
    (a : ℝ → ℝ) (h : ∑ x ∈ S, a x • sq x = 0) : ∀ x ∈ S, a x = 0 := by
  refine pow_dual_finset S id (Set.injOn_id _) hpos (![0, 1, 2, 3, 4, 6] : Fin 6 → ℕ) (by decide)
    (by simpa using hS) a fun j => ?_
  have key : ∀ p q : Fin 3, ∑ x ∈ S, a x * (b x p * b x q) = 0 := by
    intro p q
    have := congrFun (congrFun h p) q
    rw [Finset.sum_apply, Finset.sum_apply, Pi.zero_apply, Pi.zero_apply] at this
    rw [← this]
    simp [sq]
  fin_cases j
  · refine (Finset.sum_congr rfl fun x _ => ?_).trans (key 0 0); congr 1; simp [b]
  · refine (Finset.sum_congr rfl fun x _ => ?_).trans (key 0 1); congr 1
  · refine (Finset.sum_congr rfl fun x _ => ?_).trans (key 1 1); congr 1; simp [b]; ring
  · refine (Finset.sum_congr rfl fun x _ => ?_).trans (key 0 2); congr 1; simp [b]
  · refine (Finset.sum_congr rfl fun x _ => ?_).trans (key 1 2); congr 1; simp [b]; ring
  · refine (Finset.sum_congr rfl fun x _ => ?_).trans (key 2 2); congr 1; simp [b]; ring

/-- **Vanishing inside a group.** If `S` has at most three distinct positive nodes and, for every
`i ∈ S`, `∑_{j ∈ S} c i j • b j ∈ ℝ • b i`, then `c i j = 0` for `i ≠ j` in `S`. -/
theorem group_vanish (S : Finset ℝ) (hpos : ∀ x ∈ S, 0 < x) (hS : S.card ≤ 3)
    (c : ℝ → ℝ → ℝ) (h : ∀ i ∈ S, ∃ l : ℝ, ∑ j ∈ S, c i j • b j = l • b i) :
    ∀ i ∈ S, ∀ j ∈ S, j ≠ i → c i j = 0 := by
  classical
  intro i hi j hj hji
  obtain ⟨l, hl⟩ := h i hi
  have hsum : ∑ k ∈ S, (c i k - if k = i then l else 0) • b k = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq' S i,
      hi, ↓reduceIte, hl, sub_self]
  have := b_independent S hpos hS _ hsum j hj
  simpa [hji] using this

/-- **The key step of Theorem 2 (upper bound).** Let `U, V` be disjoint groups of at most three
distinct positive nodes and `c i j` (for `i ∈ U`, `j ∈ V`) real coefficients such that
`∑_{j ∈ V} c i j • b j ∈ ℝ • b i` for every `i ∈ U` and `∑_{i ∈ U} c i j • b i ∈ ℝ • b j` for every
`j ∈ V`. Then all `c i j` vanish. -/
theorem cross_vanish (U V : Finset ℝ) (hUV : Disjoint U V) (hpos : ∀ x ∈ U ∪ V, 0 < x)
    (hU : U.card ≤ 3) (hV : V.card ≤ 3) (c : ℝ → ℝ → ℝ)
    (hrow : ∀ i ∈ U, ∃ l : ℝ, ∑ j ∈ V, c i j • b j = l • b i)
    (hcol : ∀ j ∈ V, ∃ m : ℝ, ∑ i ∈ U, c i j • b i = m • b j) :
    ∀ i ∈ U, ∀ j ∈ V, c i j = 0 := by
  classical
  choose! l hl using hrow
  choose! m hm using hcol
  have hl' : ∀ i ∈ U, ∀ q, ∑ j ∈ V, c i j * b j q = l i * b i q := by
    intro i hi q
    have := congrFun (hl i hi) q
    simpa [Finset.sum_apply] using this
  have hm' : ∀ j ∈ V, ∀ p, ∑ i ∈ U, c i j * b i p = m j * b j p := by
    intro j hj p
    have := congrFun (hm j hj) p
    simpa [Finset.sum_apply] using this
  -- `T = ∑ c i j b i ⊗ b j` written in two ways
  have key : ∀ p q : Fin 3,
      ∑ i ∈ U, l i * (b i p * b i q) = ∑ j ∈ V, m j * (b j p * b j q) := by
    intro p q
    calc ∑ i ∈ U, l i * (b i p * b i q)
        = ∑ i ∈ U, b i p * ∑ j ∈ V, c i j * b j q :=
          Finset.sum_congr rfl fun i hi => by rw [hl' i hi q]; ring
      _ = ∑ i ∈ U, ∑ j ∈ V, c i j * b i p * b j q :=
          Finset.sum_congr rfl fun i _ => by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j ∈ V, ∑ i ∈ U, c i j * b i p * b j q := Finset.sum_comm
      _ = ∑ j ∈ V, b j q * ∑ i ∈ U, c i j * b i p :=
          Finset.sum_congr rfl fun j _ => by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ j ∈ V, m j * (b j p * b j q) :=
          Finset.sum_congr rfl fun j hj => by rw [hm' j hj p]; ring
  -- the at most six squares `b x ⊗ b x`, `x ∈ U ∪ V`, are independent
  set a : ℝ → ℝ := fun x => if x ∈ U then l x else -m x with ha
  have hsum : ∑ x ∈ U ∪ V, a x • sq x = 0 := by
    funext p q
    rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_union hUV]
    have hU' : ∑ x ∈ U, (a x • sq x) p q = ∑ x ∈ U, l x * (b x p * b x q) :=
      Finset.sum_congr rfl fun x hx => by simp [ha, hx, sq]
    have hV' : ∑ x ∈ V, (a x • sq x) p q = -∑ x ∈ V, m x * (b x p * b x q) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun x hx => by
        simp [ha, Finset.disjoint_right.mp hUV hx, sq]
    rw [hU', hV', key p q]
    simp
  have hcard : (U ∪ V).card ≤ 6 := (Finset.card_union_le U V).trans (by omega)
  have hzero := sq_independent (U ∪ V) hpos hcard a hsum
  intro i hi
  have hli : l i = 0 := by
    have := hzero i (Finset.mem_union_left V hi)
    simpa [ha, hi] using this
  have hrow0 : ∑ j ∈ V, c i j • b j = 0 := by rw [hl i hi, hli, zero_smul]
  exact b_independent V (fun x hx => hpos x (Finset.mem_union_right U hx)) hV (c i) hrow0

end SegrePersistence
