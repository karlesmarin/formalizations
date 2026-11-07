/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

-- encaje: cota inferior del Teorema 2 (qp(P^{m-1} × P^3) ≥ ⌈4m/3⌉) de la nota qp_bsr, en coordenadas.
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# The Plücker quadric behind `qp(ℙ^{m-1} × ℙ³) ≥ ⌈4m/3⌉`

This file formalizes the lower bound in Theorem 2 of
C. Marín, *Quadratic persistence of Segre varieties and a linear gap between biquadratic SOS rank
and Zarankiewicz bounds* (2026), for points in general position, in coordinates.

Let `A = ℝ^m` (`Fin m → ℝ`), `B = ℝ⁴` (`Fin 4 → ℝ`), and let `a i ∈ A`, `b i ∈ B`, `i : Fin k`.
Tensors in `A ⊗ B` are matrices `Matrix (Fin m) (Fin 4) ℝ`, the simple tensor `a ⊗ b` being
`Matrix.vecMulVec a b`. Linear maps `A → B` are matrices `Matrix (Fin 4) (Fin m) ℝ`.
Vectors of `⋀²B` are written by their `2 × 2` minors `U p q` (`wedge u v p q = u p v q - u q v p`),
and `pl` is the Plücker form on `⋀²ℝ⁴`.

## Main results

* `SegrePersistence.PluckerLower.exists_M`: if `3k < 4m` and all `b i ≠ 0`, there is `M ≠ 0` with
  `M a_i ∈ ⟨b_i⟩` for all `i` (dimension count, rank-nullity).
* `SegrePersistence.PluckerLower.M_rank_eq_four`: if any `≤ m` of the `a i` and any `≤ 4` of the
  `b i` are linearly independent and `m < k`, every such `M ≠ 0` has rank `4`.
  `M_rank_eq_four'` is the same with "any `m`" / "any `4`" (exactly) and `4 ≤ k`.
* `SegrePersistence.PluckerLower.Qform`: the bilinear form `Q(z, z') = pl(L z, L z')` with
  `L(a ⊗ b) = M a ∧ b`; `Q_symm`, `Q_simple` (it vanishes on simple tensors), `Q_radical`
  (each `a_i ⊗ b_i` is in its radical) and `Q_ne_zero` (it is nonzero when `rank M = 4`).
* `SegrePersistence.PluckerLower.lower_bound`: for `m < k`, `3k < 4m` and points in general
  position, there is a nonzero symmetric bilinear form on `A ⊗ B`, vanishing on all simple tensors,
  with every `a_i ⊗ b_i` in its radical.

## What is not covered

That general points compute `qp` (BSSV, Lemma 3.3), the passage from general points to all points
by closure, and the identification of the space of such forms with `𝒟 ≅ ⋀²A* ⊗ ⋀²B*`
(hence the statement `qp ≥ ⌈4m/3⌉` itself) are not formalized here. Nor is the existence of
points in general position, nor the cases `m = 2, 3`.
-/

@[expose] public section

open Module Finset Matrix

namespace SegrePersistence

namespace PluckerLower

variable {m k : ℕ}

/-! ### Step 1: existence of `M` by a dimension count -/

/-- The linear map `M ↦ (M a_i mod ⟨b_i⟩)_i`; its kernel is the space of admissible `M`. -/
noncomputable def condMap (a : Fin k → Fin m → ℝ) (b : Fin k → Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin m) ℝ →ₗ[ℝ] ((i : Fin k) → (Fin 4 → ℝ) ⧸ (ℝ ∙ b i)) :=
  LinearMap.pi fun i => (ℝ ∙ b i).mkQ ∘ₗ
    { toFun := fun M => M *ᵥ a i
      map_add' := fun M N => Matrix.add_mulVec M N (a i)
      map_smul' := fun c M => by simp [Matrix.smul_mulVec] }

lemma mem_ker_condMap {a : Fin k → Fin m → ℝ} {b : Fin k → Fin 4 → ℝ}
    {M : Matrix (Fin 4) (Fin m) ℝ} :
    M ∈ LinearMap.ker (condMap a b) ↔ ∀ i, M *ᵥ a i ∈ ℝ ∙ b i := by
  simp [condMap, funext_iff]

lemma finrank_condMap_target {b : Fin k → Fin 4 → ℝ} (hb : ∀ i, b i ≠ 0) :
    finrank ℝ ((i : Fin k) → (Fin 4 → ℝ) ⧸ (ℝ ∙ b i)) = 3 * k := by
  rw [Module.finrank_pi_fintype]
  have h : ∀ i, finrank ℝ ((Fin 4 → ℝ) ⧸ (ℝ ∙ b i)) = 3 := by
    intro i
    have := (ℝ ∙ b i).finrank_quotient_add_finrank
    rw [finrank_span_singleton (hb i), Module.finrank_fin_fun] at this
    omega
  simp [h, mul_comm]

/-- **Step 1.** If `3k < 4m` (and the `b i` are nonzero), there is a nonzero `M : A → B` with
`M a_i ∈ ⟨b_i⟩` for every `i`. -/
theorem exists_M (a : Fin k → Fin m → ℝ) (b : Fin k → Fin 4 → ℝ) (hb : ∀ i, b i ≠ 0)
    (hk : 3 * k < 4 * m) :
    ∃ M : Matrix (Fin 4) (Fin m) ℝ, M ≠ 0 ∧ ∀ i, M *ᵥ a i ∈ ℝ ∙ b i := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (condMap a b)
  have h2 : finrank ℝ (LinearMap.range (condMap a b)) ≤ 3 * k :=
    (Submodule.finrank_le _).trans (finrank_condMap_target hb).le
  rw [Module.finrank_matrix] at h1
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at h1
  have hne : LinearMap.ker (condMap a b) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at h1
    omega
  obtain ⟨M, hM, hM0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨M, hM0, mem_ker_condMap.1 hM⟩

/-! ### Step 2: `M` has rank four -/

/-- An independent family indexed by `t`, lying in `W`, has at most `finrank W` members. -/
lemma card_le_finrank_of_linearIndepOn {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (v : ι → V) (t : Finset ι) (ht : LinearIndepOn ℝ v (t : Set ι))
    (W : Submodule ℝ V) (hW : ∀ i ∈ t, v i ∈ W) : t.card ≤ finrank ℝ W := by
  have h := finrank_span_eq_card ht
  have hle : Submodule.span ℝ (Set.range fun x : (t : Set ι) => v x) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact hW x x.2
  have := Submodule.finrank_mono hle
  have hc : Fintype.card (t : Set ι) = t.card := by simp
  omega

/-- **Step 2.** If any `≤ m` of the `a i` and any `≤ 4` of the `b i` are linearly independent and
`m < k`, then every nonzero `M` with `M a_i ∈ ⟨b_i⟩` for all `i` has rank `4`. -/
theorem M_rank_eq_four (a : Fin k → Fin m → ℝ) (b : Fin k → Fin 4 → ℝ)
    (ha : ∀ s : Finset (Fin k), s.card ≤ m → LinearIndepOn ℝ a (s : Set (Fin k)))
    (hb : ∀ s : Finset (Fin k), s.card ≤ 4 → LinearIndepOn ℝ b (s : Set (Fin k)))
    (hmk : m < k) (M : Matrix (Fin 4) (Fin m) ℝ) (hM0 : M ≠ 0)
    (hM : ∀ i, M *ᵥ a i ∈ ℝ ∙ b i) : M.rank = 4 := by
  set f := M.mulVecLin with hf
  have hrk : M.rank = finrank ℝ (LinearMap.range f) := rfl
  have hnull := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun] at hnull
  have hr4 : M.rank ≤ 4 := by
    rw [hrk]
    exact (Submodule.finrank_le _).trans (by rw [Module.finrank_fin_fun])
  have hr1 : 1 ≤ M.rank := by
    rw [hrk, Nat.one_le_iff_ne_zero]
    intro h0
    rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
    apply hM0
    ext p j
    have := congrArg (fun g => g (Pi.single j 1) p) h0
    simpa [hf, Matrix.mulVec_single_one] using this
  by_contra hne
  have hr : M.rank < 4 := lt_of_le_of_ne hr4 hne
  set K := (univ : Finset (Fin k)).filter (fun i => M *ᵥ a i = 0) with hK
  set J := (univ : Finset (Fin k)).filter (fun i => ¬ M *ᵥ a i = 0) with hJ
  have hKJ : K.card + J.card = k := by
    rw [hK, hJ, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  -- at most `m - r` of the `a i` lie in `ker M`
  have hKc : K.card ≤ m - M.rank := by
    by_contra hc
    obtain ⟨t, htK, htc⟩ := Finset.exists_subset_card_eq (s := K) (n := m - M.rank + 1)
      (by omega)
    have := card_le_finrank_of_linearIndepOn a t (ha t (by omega)) (LinearMap.ker f)
      (fun i hi => by
        have := (Finset.mem_filter.1 (htK hi)).2
        simpa [hf] using this)
    omega
  -- the other `b i` lie in `im M`, which holds at most `r` of them
  have hJc : J.card ≤ M.rank := by
    by_contra hc
    obtain ⟨t, htJ, htc⟩ := Finset.exists_subset_card_eq (s := J) (n := M.rank + 1)
      (by omega)
    have := card_le_finrank_of_linearIndepOn b t (hb t (by omega)) (LinearMap.range f)
      (fun i hi => by
        have hi0 := (Finset.mem_filter.1 (htJ hi)).2
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hM i)
        have hc0 : c ≠ 0 := by
          rintro rfl
          simp at hc
          exact hi0 hc.symm
        refine ⟨c⁻¹ • a i, ?_⟩
        simp [hf, ← hc, smul_smul, inv_mul_cancel₀ hc0])
    omega
  omega

/-- **Step 2**, with "any `m`" and "any `4`" (exactly) as general-position hypotheses. -/
theorem M_rank_eq_four' (a : Fin k → Fin m → ℝ) (b : Fin k → Fin 4 → ℝ)
    (ha : ∀ s : Finset (Fin k), s.card = m → LinearIndepOn ℝ a (s : Set (Fin k)))
    (hb : ∀ s : Finset (Fin k), s.card = 4 → LinearIndepOn ℝ b (s : Set (Fin k)))
    (hmk : m < k) (h4k : 4 ≤ k) (M : Matrix (Fin 4) (Fin m) ℝ) (hM0 : M ≠ 0)
    (hM : ∀ i, M *ᵥ a i ∈ ℝ ∙ b i) : M.rank = 4 := by
  refine M_rank_eq_four a b (fun s hs => ?_) (fun s hs => ?_) hmk M hM0 hM
  · obtain ⟨t, hst, htu, htc⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ s) hs
      (by rw [Finset.card_univ, Fintype.card_fin]; omega)
    exact (ha t htc).mono (by exact_mod_cast hst)
  · obtain ⟨t, hst, htu, htc⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ s) hs
      (by rw [Finset.card_univ, Fintype.card_fin]; omega)
    exact (hb t htc).mono (by exact_mod_cast hst)

/-! ### Step 3: the pulled-back Plücker quadric -/

/-- The `2 × 2` minors of the columns `u, v`: coordinates of `u ∧ v ∈ ⋀²ℝ⁴`. -/
def wedge (u v : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ := fun p q => u p * v q - u q * v p

/-- The Plücker form on `⋀²ℝ⁴` in minor coordinates. -/
def pl (U V : Fin 4 → Fin 4 → ℝ) : ℝ :=
  U 0 1 * V 2 3 - U 0 2 * V 1 3 + U 0 3 * V 1 2 + U 1 2 * V 0 3 - U 1 3 * V 0 2 + U 2 3 * V 0 1

/-- The linear map `L : A ⊗ B → ⋀²B`, `L(a ⊗ b) = M a ∧ b`, in coordinates. -/
def L (M : Matrix (Fin 4) (Fin m) ℝ) (z : Matrix (Fin m) (Fin 4) ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun p q => ∑ i, (M p i * z i q - M q i * z i p)

/-- `Q(z, z') = pl(L z, L z')`. -/
def Q (M : Matrix (Fin 4) (Fin m) ℝ) (z z' : Matrix (Fin m) (Fin 4) ℝ) : ℝ :=
  pl (L M z) (L M z')

lemma pl_symm (U V : Fin 4 → Fin 4 → ℝ) : pl U V = pl V U := by
  unfold pl; ring

lemma L_add (M : Matrix (Fin 4) (Fin m) ℝ) (z z' : Matrix (Fin m) (Fin 4) ℝ) :
    L M (z + z') = L M z + L M z' := by
  funext p q
  simp only [L, Matrix.add_apply, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma L_smul (M : Matrix (Fin 4) (Fin m) ℝ) (c : ℝ) (z : Matrix (Fin m) (Fin 4) ℝ) :
    L M (c • z) = c • L M z := by
  funext p q
  simp only [L, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `Q` as a bilinear form on `A ⊗ B`. -/
noncomputable def Qform (M : Matrix (Fin 4) (Fin m) ℝ) :
    LinearMap.BilinForm ℝ (Matrix (Fin m) (Fin 4) ℝ) :=
  LinearMap.mk₂ ℝ (Q M)
    (fun z z' w => by simp only [Q, L_add, pl, Pi.add_apply]; ring)
    (fun c z w => by simp only [Q, L_smul, pl, Pi.smul_apply, smul_eq_mul]; ring)
    (fun z w w' => by simp only [Q, L_add, pl, Pi.add_apply]; ring)
    (fun c z w => by simp only [Q, L_smul, pl, Pi.smul_apply, smul_eq_mul]; ring)

@[simp] lemma Qform_apply (M : Matrix (Fin 4) (Fin m) ℝ) (z z' : Matrix (Fin m) (Fin 4) ℝ) :
    Qform M z z' = Q M z z' := rfl

/-- `Q` is symmetric. -/
theorem Q_symm (M : Matrix (Fin 4) (Fin m) ℝ) (z z' : Matrix (Fin m) (Fin 4) ℝ) :
    Q M z z' = Q M z' z :=
  pl_symm _ _

/-- `L(a ⊗ b) = M a ∧ b`. -/
lemma L_vecMulVec (M : Matrix (Fin 4) (Fin m) ℝ) (x : Fin m → ℝ) (y : Fin 4 → ℝ) :
    L M (vecMulVec x y) = wedge (M *ᵥ x) y := by
  funext p q
  simp only [L, wedge, vecMulVec_apply, mulVec, dotProduct, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `pl(w, w) = 0` for decomposable `w = u ∧ v`. -/
lemma pl_wedge_self (u v : Fin 4 → ℝ) : pl (wedge u v) (wedge u v) = 0 := by
  unfold pl wedge; ring

/-- `Q` vanishes on simple tensors. -/
theorem Q_simple (M : Matrix (Fin 4) (Fin m) ℝ) (x : Fin m → ℝ) (y : Fin 4 → ℝ) :
    Q M (vecMulVec x y) (vecMulVec x y) = 0 := by
  rw [Q, L_vecMulVec, pl_wedge_self]

/-- If `M a ∈ ⟨b⟩` then `L(a ⊗ b) = 0`. -/
lemma L_point_eq_zero (M : Matrix (Fin 4) (Fin m) ℝ) (x : Fin m → ℝ) (y : Fin 4 → ℝ)
    (h : M *ᵥ x ∈ ℝ ∙ y) : L M (vecMulVec x y) = 0 := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h
  rw [L_vecMulVec, ← hc]
  funext p q
  simp only [wedge, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  ring

/-- Each point `a ⊗ b` with `M a ∈ ⟨b⟩` lies in the radical of `Q`. -/
theorem Q_radical (M : Matrix (Fin 4) (Fin m) ℝ) (x : Fin m → ℝ) (y : Fin 4 → ℝ)
    (h : M *ᵥ x ∈ ℝ ∙ y) (z : Matrix (Fin m) (Fin 4) ℝ) :
    Q M (vecMulVec x y) z = 0 := by
  rw [Q, L_point_eq_zero M x y h]
  simp [pl]

/-- If `M` has rank `4` (is onto), `Q` is nonzero. -/
theorem Q_ne_zero (M : Matrix (Fin 4) (Fin m) ℝ) (hM : M.rank = 4) :
    ∃ z z' : Matrix (Fin m) (Fin 4) ℝ, Q M z z' ≠ 0 := by
  have htop : LinearMap.range M.mulVecLin = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact hM)
  have hx : ∀ p : Fin 4, ∃ x, M *ᵥ x = Pi.single p 1 := by
    intro p
    obtain ⟨x, hx⟩ := LinearMap.range_eq_top.1 htop (Pi.single p 1)
    exact ⟨x, by simpa using hx⟩
  obtain ⟨x0, h0⟩ := hx 0
  obtain ⟨x2, h2⟩ := hx 2
  refine ⟨vecMulVec x0 (Pi.single 1 1), vecMulVec x2 (Pi.single 3 1), ?_⟩
  rw [Q, L_vecMulVec, L_vecMulVec, h0, h2]
  simp [pl, wedge]

/-! ### The lower bound for points in general position -/

/-- **Lower bound of Theorem 2, for points in general position.** If `m < k`, `3k < 4m`, any `≤ m`
of the `a i` and any `≤ 4` of the `b i` are linearly independent, then there is a nonzero
symmetric bilinear form on `A ⊗ B`, vanishing on every simple tensor, with every `a_i ⊗ b_i` in
its radical. -/
theorem lower_bound (a : Fin k → Fin m → ℝ) (b : Fin k → Fin 4 → ℝ)
    (ha : ∀ s : Finset (Fin k), s.card ≤ m → LinearIndepOn ℝ a (s : Set (Fin k)))
    (hb : ∀ s : Finset (Fin k), s.card ≤ 4 → LinearIndepOn ℝ b (s : Set (Fin k)))
    (hmk : m < k) (hk : 3 * k < 4 * m) :
    ∃ D : LinearMap.BilinForm ℝ (Matrix (Fin m) (Fin 4) ℝ), D ≠ 0 ∧
      (∀ z z', D z z' = D z' z) ∧
      (∀ (x : Fin m → ℝ) (y : Fin 4 → ℝ), D (vecMulVec x y) (vecMulVec x y) = 0) ∧
      ∀ i z, D (vecMulVec (a i) (b i)) z = 0 := by
  have hb0 : ∀ i, b i ≠ 0 := fun i => by
    exact (hb {i} (by simp)).ne_zero (by simp)
  obtain ⟨M, hM0, hM⟩ := exists_M a b hb0 hk
  have hr := M_rank_eq_four a b ha hb hmk M hM0 hM
  refine ⟨Qform M, ?_, fun z z' => Q_symm M z z', fun x y => Q_simple M x y,
    fun i z => Q_radical M (a i) (b i) (hM i) z⟩
  intro h0
  obtain ⟨z, z', hz⟩ := Q_ne_zero M hr
  exact hz (by simpa using congrArg (fun D => D z z') h0)

end PluckerLower

end SegrePersistence
