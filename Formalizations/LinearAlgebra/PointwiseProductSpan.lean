/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.GroupTheory.CosetCover
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# Pointwise products of two stable subspaces span everything

Let `K` be an infinite field, `ι` a finite set and `Γ` a group acting transitively on `ι` and on
`ι → K` by signed permutations, `(γ • f) i = ε γ i * f (γ⁻¹ • i)`. If `V, W ≤ ι → K` are
`Γ`-stable (possibly with different signs `εV`, `εW`, as long as `εV γ i * εW γ i = 1`) and
`dim V + dim W > |ι|`, then the pointwise products `v * w` span `ι → K`. This is a statement of
Cauchy–Davenport type.

The proof: the orthogonal `U` of the span `S` for `∑ x_i y_i` is stable under the unsigned
translations; if `S ≠ ⊤` then `U ≠ 0`, and since a vector space over an infinite field is not a
finite union of proper subspaces (Mathlib's `Subspace.exists_eq_top_of_iUnion_eq_univ`), `U`
contains a vector `u` with full support; `v ↦ u * v` embeds `V` into the orthogonal of `W`.

## Main results

* `ConjeturaC.span_mul_eq_top`: the statement above.

## References

* C. Marín, *Where the character values of Sp(2m) at a torsion element fail to generate the ring
  of integers*, Zenodo (2026), doi:10.5281/zenodo.22813216 (Proposition `prop:mono`, complementary
  layers).
-/

@[expose] public section

namespace ConjeturaC

open Module Matrix

variable {K ι Γ : Type*} [Field K] [Fintype ι] [Group Γ] [MulAction Γ ι]

/-- The standard symmetric bilinear form `Σ x_i y_i`. -/
def dotB : LinearMap.BilinForm K (ι → K) := dotProductBilin K K

theorem dotB_apply (x y : ι → K) : dotB x y = ∑ i, x i * y i := rfl

theorem dotB_nondegenerate : (dotB : LinearMap.BilinForm K (ι → K)).Nondegenerate :=
  ⟨fun _ hx => dotProduct_eq_zero_iff.1 hx,
    fun _ hy => dotProduct_eq_zero_iff.1 fun w => (dotProduct_comm _ _).trans (hy w)⟩

/-- `dim W + dim Wᗮ = |ι|`. -/
theorem finrank_add_finrank_orth (W : Submodule K (ι → K)) :
    finrank K W + finrank K ((dotB : LinearMap.BilinForm K (ι → K)).orthogonal W) =
      Fintype.card ι := by
  have := Submodule.finrank_le W
  rw [LinearMap.BilinForm.finrank_orthogonal dotB_nondegenerate] at *
  rw [Module.finrank_fintype_fun_eq_card] at *
  omega

/-- Unsigned translation `f ↦ f ∘ (γ⁻¹ • ·)` as a linear map. -/
def transl (γ : Γ) : (ι → K) →ₗ[K] (ι → K) := LinearMap.funLeft K K (fun i => γ⁻¹ • i)

omit [Fintype ι] in
theorem transl_apply (γ : Γ) (f : ι → K) (i : ι) : transl γ f i = f (γ⁻¹ • i) := rfl

theorem dotB_transl (γ : Γ) (s u : ι → K) :
    dotB s (transl γ u) = dotB (transl γ⁻¹ s) u := by
  simp only [dotB_apply, transl_apply, inv_inv]
  exact (Fintype.sum_equiv (MulAction.toPerm γ⁻¹ : Equiv.Perm ι) _ _ (fun i => by
    simp [MulAction.toPerm_apply, smul_smul]))

/-- If `V`, `W` are stable under signed translations with `dim V + dim W > |ι|`, the pointwise
products `v * w` span `ι → K`. -/
theorem span_mul_eq_top [Infinite K] [MulAction.IsPretransitive Γ ι]
    (εV εW : Γ → ι → K) (hε : ∀ γ i, εV γ i * εW γ i = 1)
    (V W : Submodule K (ι → K))
    (hV : ∀ γ : Γ, ∀ v ∈ V, (fun i => εV γ i * v (γ⁻¹ • i)) ∈ V)
    (hW : ∀ γ : Γ, ∀ w ∈ W, (fun i => εW γ i * w (γ⁻¹ • i)) ∈ W)
    (hdim : Fintype.card ι < finrank K V + finrank K W) :
    Submodule.span K {f | ∃ v ∈ V, ∃ w ∈ W, f = v * w} = ⊤ := by
  set S := Submodule.span K {f : ι → K | ∃ v ∈ V, ∃ w ∈ W, f = v * w} with hSdef
  set U := (dotB : LinearMap.BilinForm K (ι → K)).orthogonal S with hUdef
  by_contra hS
  -- S is stable under unsigned translations
  have hSstab : ∀ γ : Γ, ∀ s ∈ S, transl γ s ∈ S := by
    intro γ s hs
    have hle : S ≤ S.comap (transl γ) := by
      rw [hSdef, Submodule.span_le]
      rintro f ⟨v, hv, w, hw, rfl⟩
      refine Submodule.subset_span ⟨_, hV γ v hv, _, hW γ w hw, ?_⟩
      funext i
      simp only [transl_apply, Pi.mul_apply]
      have := hε γ i
      linear_combination (-(v (γ⁻¹ • i) * w (γ⁻¹ • i))) * this
    exact hle hs
  -- U is stable under unsigned translations
  have hUstab : ∀ γ : Γ, ∀ u ∈ U, transl γ u ∈ U := by
    intro γ u hu s hs
    rw [dotB_transl]
    exact hu _ (hSstab γ⁻¹ s hs)
  -- U ≠ ⊥
  have hU : U ≠ ⊥ := by
    intro h0
    have h1 := finrank_add_finrank_orth (K := K) S
    rw [← hUdef, h0, finrank_bot, add_zero] at h1
    have h2 := Submodule.finrank_lt hS
    rw [Module.finrank_fintype_fun_eq_card] at h2
    omega
  obtain ⟨u0, hu0U, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  obtain ⟨j, hj⟩ : ∃ j, u0 j ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (funext h)
  -- an element of U with full support
  obtain ⟨u, huU, hu⟩ : ∃ u ∈ U, ∀ i, u i ≠ 0 := by
    by_contra hno
    push Not at hno
    let p : ι → Submodule K U := fun i => LinearMap.ker ((LinearMap.proj i).comp U.subtype)
    have hcov : ⋃ i, (p i : Set U) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨i, hi⟩ := hno x x.2
      exact Set.mem_iUnion.2 ⟨i, by simpa [p] using hi⟩
    obtain ⟨i, hi⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hcov
    obtain ⟨γ, hγ⟩ := MulAction.exists_smul_eq Γ i j
    have hmem : (⟨transl γ⁻¹ u0, hUstab _ _ hu0U⟩ : U) ∈ p i := by
      rw [hi]; exact Submodule.mem_top
    have : transl γ⁻¹ u0 i = 0 := by simpa [p] using hmem
    rw [transl_apply, inv_inv, hγ] at this
    exact hj this
  -- v ↦ u * v injects V into Wᗮ
  let L : (ι → K) →ₗ[K] (ι → K) := LinearMap.mulLeft K u
  have hL : Function.Injective L := by
    intro x y hxy
    funext i
    have := congrFun hxy i
    simp only [L, LinearMap.mulLeft_apply, Pi.mul_apply] at this
    exact mul_left_cancel₀ (hu i) this
  have hmap : V.map L ≤ (dotB : LinearMap.BilinForm K (ι → K)).orthogonal W := by
    rintro _ ⟨v, hv, rfl⟩ w hw
    have h0 : dotB (v * w) u = 0 := huU (v * w) (Submodule.subset_span ⟨v, hv, w, hw, rfl⟩)
    rw [dotB_apply] at h0 ⊢
    rw [← h0]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [L, LinearMap.mulLeft_apply, Pi.mul_apply]
    ring
  have hV1 : finrank K V = finrank K (V.map L) :=
    (Submodule.equivMapOfInjective L hL V).finrank_eq
  have hV2 := Submodule.finrank_mono hmap
  have hW1 := finrank_add_finrank_orth (K := K) W
  omega

end ConjeturaC
