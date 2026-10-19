/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.RingTheory.HopfAlgebra.ConnesKreimer.Coproduct
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# The Connes–Kreimer–Foissy Hopf algebra of planar rooted trees

The carrier is `H k = MonoidAlgebra k (FreeMonoid RTree)`: the free `k`-module on planar forests,
with forest concatenation as product. The combinatorial coproduct of
`Formalizations.RingTheory.HopfAlgebra.ConnesKreimer.Coproduct` is lifted to a linear map, and
`H k` becomes a Mathlib `Coalgebra`, `Bialgebra` and `HopfAlgebra`.

## Main results

* `ConnesKreimer.coassoc_map`: `(Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ` as linear maps.
* `ConnesKreimer.instCKCoalg`: `Coalgebra k (H k)`.
* `ConnesKreimer.Δ_mul`, `ConnesKreimer.Δ_one`, `ConnesKreimer.instCKBialg`: `Bialgebra k (H k)`.
* `ConnesKreimer.antipodeF`: the antipode by the connected-graded recursion
  `S(f) = −Σ_{(p,r), r ≠ ∅} S(p)·r`.
* `ConnesKreimer.leftAntipode_eq`, `ConnesKreimer.rightAntipode'_eq`,
  `ConnesKreimer.antipode_eq_antipode'`: both antipode axioms.
* `ConnesKreimer.instCKHopf`: `HopfAlgebra k (H k)`.

## Implementation notes

Ported from Lean v4.30.0-rc2. In current Mathlib `MonoidAlgebra` is a structure over its
coefficient `Finsupp`, no longer the `Finsupp` itself; linear maps out of `H k` are defined
through `MonoidAlgebra.coeffLinearEquiv` and tested on the basis by `ConnesKreimer.lhom_ext`. These
adaptations follow the port of the same development in
[LeanPool/lean-pool](https://github.com/LeanPool/lean-pool) (`LeanPool/ConnesKreimer/Core.lean`).

## References

* A. Connes, D. Kreimer, *Hopf algebras, renormalization and noncommutative geometry*,
  Comm. Math. Phys. 199 (1998) 203–242.
* L. Foissy, *Les algèbres de Hopf des arbres enracinés décorés, I*, Bull. Sci. Math. 126 (2002)
  193–239.
* C. Marín, *How a Tree Remembers Its Cuts: the Connes–Kreimer–Foissy Hopf Algebra of Rooted Trees,
  Machine-Checked in Lean 4* (2026), doi:10.5281/zenodo.20762280. Ported from `ConnesKreimer.lean`
  of [karlesmarin/connes-kreimer-lean](https://github.com/karlesmarin/connes-kreimer-lean)
  (Lean v4.30.0-rc2).
-/

@[expose] public section

open scoped TensorProduct

namespace ConnesKreimer

/-! ### Mathlib bridge: lift the combinatorial coassoc to a `Coalgebra` instance. -/

variable (k : Type*) [CommRing k]

/-- Carrier: forests with k-coefficients (product = forest concatenation). -/
abbrev H := MonoidAlgebra k (FreeMonoid RTree)

/-- Extensionality for linear maps out of `H k`, tested on the forest basis. A `Forest`-indexed
    repackaging of `MonoidAlgebra.lhom_ext'` (`Forest` and `FreeMonoid RTree` are definitionally
    but not reducibly equal, and `rw` needs the former). -/
theorem lhom_ext {N : Type*} [AddCommMonoid N] [Module k N] ⦃φ ψ : H k →ₗ[k] N⦄
    (h : ∀ (f : Forest) (b : k),
      φ (MonoidAlgebra.single f b) = ψ (MonoidAlgebra.single f b)) : φ = ψ :=
  MonoidAlgebra.lhom_ext' fun f => LinearMap.ext fun b => h (FreeMonoid.toList f) b

/-- Pure 2-tensor of a cut `(p, r)`. -/
noncomputable def e2 (pr : Forest × Forest) : H k ⊗[k] H k :=
  MonoidAlgebra.single pr.1 (1 : k) ⊗ₜ[k] MonoidAlgebra.single pr.2 (1 : k)

/-- Pure 3-tensor of an iterated cut `(a, b, c)`, associated to the right. -/
noncomputable def e3 (t : Forest × Forest × Forest) : H k ⊗[k] (H k ⊗[k] H k) :=
  MonoidAlgebra.single t.1 (1 : k) ⊗ₜ[k]
    (MonoidAlgebra.single t.2.1 (1 : k) ⊗ₜ[k] MonoidAlgebra.single t.2.2 (1 : k))

/-- Δ on a basis forest. -/
noncomputable def Δ₀ (f : Forest) : H k ⊗[k] H k := ((coprodForest f).map (e2 k)).sum

/-- E3 of a triple-tensor list. -/
noncomputable def E3 (l : Tens3) : H k ⊗[k] (H k ⊗[k] H k) := (l.map (e3 k)).sum

/-- Comultiplication. -/
noncomputable def Δ : H k →ₗ[k] H k ⊗[k] H k :=
  Finsupp.linearCombination k (Δ₀ k) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

theorem Δ_single (f : Forest) (b : k) :
    Δ k (MonoidAlgebra.single f b) = b • Δ₀ k f := by
  change Finsupp.linearCombination k (Δ₀ k) (Finsupp.single f b) = b • Δ₀ k f
  rw [Finsupp.linearCombination_single]

/-- E3 distributes over `flatMap`. -/
theorem E3_flatMap (L : Tens) (g : Forest × Forest → Tens3) :
    E3 k (L.flatMap g) = (L.map (fun x => E3 k (g x))).sum := by
  unfold E3
  induction L with
  | nil => simp
  | cons a as ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

/-- A linear map commutes with a `List.sum` of mapped terms. -/
theorem linmap_list_sum {α} {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module k M] [Module k N] (φ : M →ₗ[k] N) (l : List α) (h : α → M) :
    φ ((l.map h).sum) = (l.map (fun a => φ (h a))).sum := by
  rw [map_list_sum, List.map_map]; rfl

/-- The per-cut computation: `assoc ∘ rTensor Δ` on a pure 2-tensor `e2 (p,r)`
    equals `E3` of the left-leg refinement. This is the heart of the coassoc bridge. -/
theorem elem_lemma (pr : Forest × Forest) :
    (TensorProduct.assoc k (H k) (H k) (H k))
        (LinearMap.rTensor (H k) (Δ k) (e2 k pr))
      = E3 k ((coprodForest pr.1).map (fun ab => (ab.1, ab.2, pr.2))) := by
  obtain ⟨p, r⟩ := pr
  rw [e2, LinearMap.rTensor_tmul, Δ_single, one_smul, Δ₀]
  -- Ψ : y ↦ assoc (y ⊗ single r 1), linear; push through the list sum.
  let Ψ : H k ⊗[k] H k →ₗ[k] H k ⊗[k] (H k ⊗[k] H k) :=
    (TensorProduct.assoc k (H k) (H k) (H k)).toLinearMap ∘ₗ
      (TensorProduct.mk k (H k ⊗[k] H k) (H k)).flip (MonoidAlgebra.single r 1)
  have hΨ : (TensorProduct.assoc k (H k) (H k) (H k))
        ((((coprodForest p).map (e2 k)).sum) ⊗ₜ[k] MonoidAlgebra.single r (1 : k))
      = Ψ (((coprodForest p).map (e2 k)).sum) := rfl
  rw [hΨ, linmap_list_sum, E3, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab _
  obtain ⟨a, b⟩ := ab
  simp only [Function.comp_def, Ψ, e2, e3, LinearMap.coe_comp, LinearEquiv.coe_coe,
    TensorProduct.mk_apply, LinearMap.flip_apply, TensorProduct.assoc_tmul]

/-- Right-leg analogue: `lTensor Δ` on `e2 (p,r)` equals `E3` of the right-leg refinement.
    No `assoc` needed — the tensor is already right-associated. -/
theorem elem_lemma_R (pr : Forest × Forest) :
    LinearMap.lTensor (H k) (Δ k) (e2 k pr)
      = E3 k ((coprodForest pr.2).map (fun bc => (pr.1, bc.1, bc.2))) := by
  rw [e2, LinearMap.lTensor_tmul, Δ_single, one_smul, Δ₀]
  let Θ : H k ⊗[k] H k →ₗ[k] H k ⊗[k] (H k ⊗[k] H k) :=
    TensorProduct.mk k (H k) (H k ⊗[k] H k) (MonoidAlgebra.single pr.1 1)
  change Θ (((coprodForest pr.2).map (e2 k)).sum) = _
  rw [linmap_list_sum, E3, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro bc _
  simp only [Function.comp_def, Θ, e2, e3, TensorProduct.mk_apply]

/-- LHS structural map on `Δ₀ f`. -/
theorem lhs_core (f : Forest) :
    (TensorProduct.assoc k (H k) (H k) (H k))
        (LinearMap.rTensor (H k) (Δ k) (Δ₀ k f))
      = E3 k (coLeft (coprodForest f)) := by
  rw [Δ₀]
  let Φ : H k ⊗[k] H k →ₗ[k] H k ⊗[k] (H k ⊗[k] H k) :=
    (TensorProduct.assoc k (H k) (H k) (H k)).toLinearMap ∘ₗ LinearMap.rTensor (H k) (Δ k)
  have hΦ : (TensorProduct.assoc k (H k) (H k) (H k))
        (LinearMap.rTensor (H k) (Δ k) (((coprodForest f).map (e2 k)).sum))
      = Φ (((coprodForest f).map (e2 k)).sum) := rfl
  rw [hΦ, linmap_list_sum, coLeft, E3_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pr _
  exact elem_lemma k pr

/-- RHS structural map on `Δ₀ f`. -/
theorem rhs_core (f : Forest) :
    LinearMap.lTensor (H k) (Δ k) (Δ₀ k f) = E3 k (coRight (coprodForest f)) := by
  rw [Δ₀]
  rw [linmap_list_sum, coRight, E3_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pr _
  exact elem_lemma_R k pr

/-- The combinatorial coassoc, transported to `E3`. -/
theorem perm_E3 (f : Forest) :
    E3 k (coLeft (coprodForest f)) = E3 k (coRight (coprodForest f)) :=
  (List.Perm.map (e3 k) (coassocForest f)).sum_eq

/-- **Coassociativity** as an equality of linear maps. -/
theorem coassoc_map :
    (TensorProduct.assoc k (H k) (H k) (H k)).toLinearMap ∘ₗ
        LinearMap.rTensor (H k) (Δ k) ∘ₗ Δ k
      = LinearMap.lTensor (H k) (Δ k) ∘ₗ Δ k := by
  apply ConnesKreimer.lhom_ext
  intro f b
  change (TensorProduct.assoc k (H k) (H k) (H k))
        (LinearMap.rTensor (H k) (Δ k) (Δ k (MonoidAlgebra.single f b)))
      = LinearMap.lTensor (H k) (Δ k) (Δ k (MonoidAlgebra.single f b))
  rw [Δ_single]
  simp only [map_smul]
  rw [lhs_core, rhs_core, perm_E3]

/-! ### Counit. -/

/-- Counit monoid hom: every generator ↦ 0, so a word ↦ `0 ^ len` = indicator of empty. -/
def εmon : FreeMonoid RTree →* k := FreeMonoid.lift (fun _ => (0 : k))

@[simp] theorem εmon_nil : εmon k ([] : Forest) = 1 := map_one _

@[simp] theorem εmon_of (a : RTree) : εmon k (FreeMonoid.of a) = 0 := rfl

@[simp] theorem εmon_cons (a : RTree) (l : Forest) : εmon k (a :: l) = 0 := by
  change εmon k (FreeMonoid.of a * FreeMonoid.ofList l) = 0
  rw [map_mul, εmon_of, zero_mul]

theorem εmon_append (p p' : Forest) : εmon k (p ++ p') = εmon k p * εmon k p' := by
  induction p with
  | nil => simp
  | cons a as ih => simp

/-- Counit as an algebra hom, then linear. -/
noncomputable def εalg : H k →ₐ[k] k :=
  MonoidAlgebra.lift k k (FreeMonoid RTree) (εmon k)

/-- The Connes-Kreimer counit as a linear map. -/
noncomputable def ε : H k →ₗ[k] k := (εalg k).toLinearMap

theorem ε_single (f : Forest) (b : k) :
    ε k (MonoidAlgebra.single f b) = b * εmon k f := by
  have h : εalg k (MonoidAlgebra.single (FreeMonoid.ofList f) b)
      = b * εmon k (FreeMonoid.ofList f) := by
    rw [εalg, MonoidAlgebra.lift_single, smul_eq_mul]
  exact h

/-- Scalar smul commutes with a `List.sum`. -/
theorem smul_list_sum {M : Type*} [AddCommMonoid M] [Module k M] (c : k) (l : List M) :
    c • l.sum = (l.map (fun x => c • x)).sum := by
  induction l with
  | nil => simp
  | cons a as ih => simp [smul_add, ih]

/-- Smul through a mapped `List.sum`. -/
theorem smul_list_sum' {α M : Type*} [AddCommMonoid M] [Module k M]
    (c : k) (l : List α) (F : α → M) :
    c • (l.map F).sum = (l.map (fun x => c • F x)).sum := by
  rw [smul_list_sum, List.map_map]; rfl

/-- Pull a base-ring scalar out of the right tensor leg (avoids `CompatibleSMul`). -/
theorem tmul_scalar_right (m : H k) (c : k) :
    m ⊗ₜ[k] c = c • (m ⊗ₜ[k] (1 : k)) := by
  conv_lhs => rw [show c = c • (1 : k) from by rw [smul_eq_mul, mul_one]]
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']

/-- Pull a base-ring scalar out of the left tensor leg. -/
theorem tmul_scalar_left (c : k) (m : H k) :
    (c : k) ⊗ₜ[k] m = c • ((1 : k) ⊗ₜ[k] m) := by
  conv_lhs => rw [show c = c • (1 : k) from by rw [smul_eq_mul, mul_one]]
  rw [TensorProduct.smul_tmul']

/-- Generic map-over-`flatMap` `List.sum` distribution. -/
theorem map_flatMap_sum {α β : Type*} {M : Type*} [AddCommMonoid M]
    (L : List α) (G : α → List β) (h : β → M) :
    ((L.flatMap G).map h).sum = (L.map (fun a => ((G a).map h).sum)).sum := by
  induction L with
  | nil => simp
  | cons a as ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

/-! The left-counit collapse: `ε` on the left leg selects the unique `([], f)` cut. -/
mutual
  theorem collapseL_tree {M : Type*} [AddCommMonoid M] [Module k M]
      (t : RTree) (g : Forest → M) :
      ((coprodTree t).map (fun pr => εmon k pr.1 • g pr.2)).sum = g [t] := by
    cases t with
    | node F =>
      rw [coprodTree_node]
      simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def, εmon_cons,
        zero_smul, zero_add]
      exact collapseL_forest F (fun r => g [RTree.node r])
  theorem collapseL_forest {M : Type*} [AddCommMonoid M] [Module k M]
      (f : Forest) (g : Forest → M) :
      ((coprodForest f).map (fun pr => εmon k pr.1 • g pr.2)).sum = g f := by
    cases f with
    | nil =>
      rw [show coprodForest ([] : Forest) = [([], [])] from rfl]
      simp
    | cons t ts =>
      rw [show coprodForest (t :: ts) = tmul (coprodTree t) (coprodForest ts) from rfl, tmul,
          map_flatMap_sum]
      rw [show ((coprodTree t).map (fun pr =>
            (((coprodForest ts).map (fun pr' => (pr.1 ++ pr'.1, pr.2 ++ pr'.2))).map
              (fun q => εmon k q.1 • g q.2)).sum)).sum
          = ((coprodTree t).map (fun pr => εmon k pr.1 • g (pr.2 ++ ts))).sum from ?_]
      · exact collapseL_tree t (fun r => g (r ++ ts))
      · apply congrArg List.sum
        apply List.map_congr_left
        intro pr _
        simp only [List.map_map, Function.comp_def]
        trans (εmon k pr.1 •
            ((coprodForest ts).map (fun x => εmon k x.1 • g (pr.2 ++ x.2))).sum)
        · rw [smul_list_sum']
          apply congrArg List.sum
          apply List.map_congr_left
          intro x _
          rw [εmon_append k pr.1 x.1, mul_smul]
        · congr 1
          exact collapseL_forest ts (fun r => g (pr.2 ++ r))
end

/-! The right-counit collapse: `ε` on the right leg selects the unique `(f, [])` cut. -/
mutual
  theorem collapseR_tree {M : Type*} [AddCommMonoid M] [Module k M]
      (t : RTree) (g : Forest → M) :
      ((coprodTree t).map (fun pr => εmon k pr.2 • g pr.1)).sum = g [t] := by
    cases t with
    | node F =>
      simp only [coprodTree_node, List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
        εmon_nil, εmon_cons, zero_smul, one_smul]
      simp_all
  theorem collapseR_forest {M : Type*} [AddCommMonoid M] [Module k M]
      (f : Forest) (g : Forest → M) :
      ((coprodForest f).map (fun pr => εmon k pr.2 • g pr.1)).sum = g f := by
    cases f with
    | nil =>
      rw [show coprodForest ([] : Forest) = [([], [])] from rfl]
      simp
    | cons t ts =>
      rw [show coprodForest (t :: ts) = tmul (coprodTree t) (coprodForest ts) from rfl, tmul,
          map_flatMap_sum]
      rw [show ((coprodTree t).map (fun pr =>
            (((coprodForest ts).map (fun pr' => (pr.1 ++ pr'.1, pr.2 ++ pr'.2))).map
              (fun q => εmon k q.2 • g q.1)).sum)).sum
          = ((coprodTree t).map (fun pr => εmon k pr.2 • g (pr.1 ++ ts))).sum from ?_]
      · exact collapseR_tree t (fun r => g (r ++ ts))
      · apply congrArg List.sum
        apply List.map_congr_left
        intro pr _
        simp only [List.map_map, Function.comp_def]
        trans (εmon k pr.2 •
            ((coprodForest ts).map (fun x => εmon k x.2 • g (pr.1 ++ x.1))).sum)
        · rw [smul_list_sum']
          apply congrArg List.sum
          apply List.map_congr_left
          intro x _
          rw [εmon_append k pr.2 x.2, mul_smul]
        · congr 1
          exact collapseR_forest ts (fun r => g (pr.1 ++ r))
end

/-- `(ε ⊗ id) ∘ Δ` on a basis forest gives `1 ⊗ single f 1`. -/
theorem rTensor_ε_Δ₀ (f : Forest) :
    LinearMap.rTensor (H k) (ε k) (Δ₀ k f) = (1 : k) ⊗ₜ[k] MonoidAlgebra.single f 1 := by
  rw [Δ₀, linmap_list_sum]
  rw [show ((coprodForest f).map (fun pr => LinearMap.rTensor (H k) (ε k) (e2 k pr))).sum
        = ((coprodForest f).map (fun pr =>
            εmon k pr.1 • ((1 : k) ⊗ₜ[k] MonoidAlgebra.single pr.2 1))).sum from ?_]
  · exact collapseL_forest (k := k) f (fun r => (1 : k) ⊗ₜ[k] MonoidAlgebra.single r 1)
  · apply congrArg List.sum
    apply List.map_congr_left
    intro pr _
    rw [e2, LinearMap.rTensor_tmul, ε_single, one_mul]
    apply tmul_scalar_left

/-- `(id ⊗ ε) ∘ Δ` on a basis forest gives `single f 1 ⊗ 1`. -/
theorem lTensor_ε_Δ₀ (f : Forest) :
    LinearMap.lTensor (H k) (ε k) (Δ₀ k f) = MonoidAlgebra.single f 1 ⊗ₜ[k] (1 : k) := by
  rw [Δ₀, linmap_list_sum]
  rw [show ((coprodForest f).map (fun pr => LinearMap.lTensor (H k) (ε k) (e2 k pr))).sum
        = ((coprodForest f).map (fun pr =>
            εmon k pr.2 • (MonoidAlgebra.single pr.1 1 ⊗ₜ[k] (1 : k)))).sum from ?_]
  · exact collapseR_forest (k := k) f (fun r => MonoidAlgebra.single r 1 ⊗ₜ[k] (1 : k))
  · apply congrArg List.sum
    apply List.map_congr_left
    intro pr _
    rw [e2, LinearMap.lTensor_tmul, ε_single, one_mul]
    apply tmul_scalar_right

theorem single_smul_one (f : FreeMonoid RTree) (b : k) :
    MonoidAlgebra.single f b = b • MonoidAlgebra.single f 1 := by
  simp

noncomputable instance : CoalgebraStruct k (H k) where
  comul := Δ k
  counit := ε k

noncomputable instance instCKCoalg : Coalgebra k (H k) where
  coassoc := coassoc_map k
  rTensor_counit_comp_comul := by
    apply ConnesKreimer.lhom_ext
    intro f b
    change LinearMap.rTensor (H k) (ε k) (Δ k (MonoidAlgebra.single f b))
        = (TensorProduct.mk k k (H k)) 1 (MonoidAlgebra.single f b)
    rw [Δ_single, map_smul,
        rTensor_ε_Δ₀, TensorProduct.mk_apply, single_smul_one (k := k) (f := f) (b := b)]
    exact (TensorProduct.tmul_smul b (1 : k) (MonoidAlgebra.single f 1 : H k)).symm
  lTensor_counit_comp_comul := by
    apply ConnesKreimer.lhom_ext
    intro f b
    change LinearMap.lTensor (H k) (ε k) (Δ k (MonoidAlgebra.single f b))
        = (TensorProduct.mk k (H k) k).flip 1 (MonoidAlgebra.single f b)
    rw [Δ_single, map_smul,
        lTensor_ε_Δ₀, LinearMap.flip_apply, TensorProduct.mk_apply,
        single_smul_one (k := k) (f := f) (b := b)]
    exact TensorProduct.smul_tmul' b (MonoidAlgebra.single f 1 : H k) (1 : k)

/-! ### Bialgebra: `Δ` and `ε` are algebra homs. -/

/-- `single` of a concatenation is the product (algebra structure of `H`). -/
theorem single_append (p p' : Forest) :
    (MonoidAlgebra.single (p ++ p') (1 : k) : H k)
      = (MonoidAlgebra.single p 1 : H k) * (MonoidAlgebra.single p' 1 : H k) := by
  have h : (MonoidAlgebra.single (FreeMonoid.ofList p * FreeMonoid.ofList p') (1 : k) : H k)
      = (MonoidAlgebra.single (FreeMonoid.ofList p) (1 : k) : H k) *
        (MonoidAlgebra.single (FreeMonoid.ofList p') (1 : k) : H k) := by
    rw [MonoidAlgebra.single_mul_single, mul_one]
  exact h

/-- `e2` is multiplicative across leg-wise concatenation. -/
theorem e2_mul (pr pr' : Forest × Forest) :
    e2 k (pr.1 ++ pr'.1, pr.2 ++ pr'.2) = e2 k pr * e2 k pr' := by
  simp only [e2, Algebra.TensorProduct.tmul_mul_tmul, single_append]

/-- Left-distribute a product over a `List.sum`. -/
theorem mul_list_sum {M : Type*} [NonUnitalNonAssocSemiring M] (a : M) (L : List M) :
    a * L.sum = (L.map (fun b => a * b)).sum := by
  induction L with
  | nil => simp
  | cons b bs ih => simp [mul_add, ih]

/-- Product of two `List.sum`s is the double sum. -/
theorem list_sum_mul_sum {M : Type*} [NonUnitalNonAssocSemiring M] (L1 L2 : List M) :
    L1.sum * L2.sum = (L1.flatMap (fun a => L2.map (fun b => a * b))).sum := by
  induction L1 with
  | nil => simp
  | cons a as ih =>
    rw [List.sum_cons, add_mul, ih, mul_list_sum, List.flatMap_cons, List.sum_append]

/-- `Δ₀` is multiplicative. -/
theorem Δ₀_mul (F G : Forest) : Δ₀ k (F ++ G) = Δ₀ k F * Δ₀ k G := by
  rw [Δ₀, Δ₀, Δ₀, coprodForest_append, list_sum_mul_sum, tmul]
  simp only [List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def, e2_mul]

/-- `Δ` is multiplicative on all of `H` (reduce to the forest basis, bilinearly). -/
theorem Δ_mul (a b : H k) : Δ k (a * b) = Δ k a * Δ k b := by
  induction a using MonoidAlgebra.induction_on with
  | of F =>
    induction b using MonoidAlgebra.induction_on with
    | of G =>
      simp only [MonoidAlgebra.of_apply]
      change Δ k ((MonoidAlgebra.single (FreeMonoid.toList F) (1 : k) : H k) *
            (MonoidAlgebra.single (FreeMonoid.toList G) (1 : k) : H k))
          = Δ k (MonoidAlgebra.single (FreeMonoid.toList F) (1 : k) : H k) *
            Δ k (MonoidAlgebra.single (FreeMonoid.toList G) (1 : k) : H k)
      rw [← single_append, Δ_single, Δ_single, Δ_single, one_smul, one_smul, one_smul]
      exact Δ₀_mul k F G
    | add b1 b2 h1 h2 => rw [mul_add, map_add, map_add, h1, h2, mul_add]
    | smul r b hb => rw [mul_smul_comm, map_smul, map_smul, hb, mul_smul_comm]
  | add a1 a2 h1 h2 => rw [add_mul, map_add, map_add, h1, h2, add_mul]
  | smul r a ha => rw [smul_mul_assoc, map_smul, map_smul, ha, smul_mul_assoc]

/-- `Δ 1 = 1`. -/
theorem Δ_one : Δ k (1 : H k) = 1 := by
  rw [show (1 : H k) = MonoidAlgebra.single (M := FreeMonoid RTree) ([] : Forest) (1 : k) from rfl,
      Δ_single, one_smul]
  rw [Δ₀, show coprodForest ([] : Forest) = [([], [])] from rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, e2]
  rfl

noncomputable instance instCKBialg : Bialgebra k (H k) :=
  Bialgebra.mk' k (H k)
    (map_one (εalg k))
    (fun {a b} => map_mul (εalg k) a b)
    (Δ_one k)
    (fun {a b} => Δ_mul k a b)

/-! ### Toward HopfAlgebra: node count (grading) and its conservation under cuts.
    Conservation `|p| + |r| = |f|` makes the antipode recursion well-founded
    (`r ≠ [] ⟹ |p| < |f|`). -/

mutual
  /-- Number of nodes in a rooted tree. -/
  def sizeT : RTree → Nat
    | .node F => 1 + sizeF F
  /-- Number of nodes in a rooted forest. -/
  def sizeF : Forest → Nat
    | []      => 0
    | t :: ts => sizeT t + sizeF ts
end

theorem sizeF_append (F G : Forest) : sizeF (F ++ G) = sizeF F + sizeF G := by
  induction F with
  | nil => simp [sizeF]
  | cons t ts ih => simp only [List.cons_append, sizeF, ih]; ring

mutual
  theorem size_consTree (t : RTree) :
      ∀ pr ∈ coprodTree t, sizeF pr.1 + sizeF pr.2 = sizeT t := by
    cases t with
    | node F =>
      intro pr hpr
      rw [coprodTree_node] at hpr
      simp only [List.mem_cons, List.mem_map] at hpr
      rcases hpr with h | ⟨q, hq, rfl⟩
      · subst h; simp [sizeF, sizeT]
      · simp only [sizeF, sizeT]
        have := size_consForest F q hq
        omega
  theorem size_consForest (f : Forest) :
      ∀ pr ∈ coprodForest f, sizeF pr.1 + sizeF pr.2 = sizeF f := by
    cases f with
    | nil =>
      intro pr hpr
      simp only [show coprodForest ([] : Forest) = [([], [])] from rfl, List.mem_singleton] at hpr
      subst hpr; simp [sizeF]
    | cons t ts =>
      intro pr hpr
      rw [show coprodForest (t :: ts) = tmul (coprodTree t) (coprodForest ts) from rfl,
          tmul] at hpr
      simp only [List.mem_flatMap, List.mem_map] at hpr
      obtain ⟨a, ha, b, hb, rfl⟩ := hpr
      have h1 := size_consTree t a ha
      have h2 := size_consForest ts b hb
      simp only [sizeF, sizeF_append]
      omega
end

theorem sizeF_pos {f : Forest} (h : f ≠ []) : 0 < sizeF f := by
  cases f with
  | nil => exact absurd rfl h
  | cons t ts => cases t with | node F => simp [sizeF, sizeT]

/-- A forest as an `H`-basis element, with the index forced to `FreeMonoid RTree`
    via `ofList` (so it is always typed `H k`, even on the empty forest). -/
noncomputable def sf (r : Forest) : H k := MonoidAlgebra.single (FreeMonoid.ofList r) 1

@[simp] theorem sf_nil : sf k [] = 1 := by
  rw [sf, FreeMonoid.ofList_nil, ← MonoidAlgebra.one_def]

theorem sf_append (a b : Forest) : sf k (a ++ b) = sf k a * sf k b := by
  rw [sf, sf, sf, MonoidAlgebra.single_mul_single, mul_one, FreeMonoid.ofList_append]

/-- The antipode on the forest basis, by well-founded recursion on node count.
    `S(∅) = 1`; `S(f) = -Σ_{(p,r) cut, r ≠ ∅} S(p)·r`. Recursion decreases since
    `|p| < |f|`. -/
noncomputable def antipodeF : Forest → H k
  | [] => 1
  | (t :: ts) =>
    - (((coprodForest (t :: ts)).filter (fun pr => !pr.2.isEmpty)).attach.map
        (fun pr => antipodeF pr.val.1 * sf k pr.val.2)).sum
termination_by f => sizeF f
decreasing_by
  have hmem := pr.property
  rw [List.mem_filter] at hmem
  have hcons := size_consForest _ pr.val hmem.1
  have hr : pr.val.2 ≠ [] := by simpa [List.isEmpty_iff] using hmem.2
  have hpos := sizeF_pos hr
  have hlt : sizeF pr.val.1 < sizeF pr.val.1 + sizeF pr.val.2 := by omega
  simp_all

/-! ### Antipode as a linear map + the left convolution axiom (`S ⋆ id = η∘ε`). -/

/-- The antipode linear map obtained by extending `antipodeF` from the forest basis. -/
noncomputable def antipode : H k →ₗ[k] H k :=
  Finsupp.linearCombination k (antipodeF k) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

theorem antipode_single (f : Forest) (b : k) :
    antipode k (MonoidAlgebra.single f b) = b • antipodeF k f := by
  change Finsupp.linearCombination k (antipodeF k) (Finsupp.single f b) = b • antipodeF k f
  rw [Finsupp.linearCombination_single]

/-- `antipodeF` on a nonempty forest, as a plain (non-`attach`) sum. -/
theorem antipodeF_cons (t : RTree) (ts : Forest) :
    antipodeF k (t :: ts)
      = - (((coprodForest (t :: ts)).filter (fun pr => !pr.2.isEmpty)).map
          (fun pr => antipodeF k pr.1 * sf k pr.2)).sum := by
  conv_lhs => rw [antipodeF]
  simp only [List.map_attach_eq_pmap, List.pmap_eq_map]

/-- `r ++ b` is nonempty when `r` is. -/
theorem isEmpty_append_of_ne {r b : Forest} (h : r ≠ []) :
    (r ++ b).isEmpty = false := by
  simp_all

/-- Filtering cuts by "empty right leg" factorizes over `tmul`. -/
theorem filter_emptyR_tmul (A B : Tens) :
    (tmul A B).filter (fun pr => pr.2.isEmpty)
      = tmul (A.filter (fun pr => pr.2.isEmpty)) (B.filter (fun pr => pr.2.isEmpty)) := by
  induction A with
  | nil => rfl
  | cons a as ih =>
    obtain ⟨p, r⟩ := a
    rcases r with _ | ⟨c, cs⟩
    · simp only [tmul_cons, List.filter_append, ih, List.filter_cons, List.isEmpty_nil,
        ite_true, List.filter_map, Function.comp_def, List.nil_append]
    · simp only [tmul_cons, List.filter_append, ih, List.filter_cons, List.isEmpty_cons,
        Bool.false_eq_true, ite_false, List.filter_map, Function.comp_def]
      simp_all

mutual
  /-- The unique empty-right cut of a tree `t` is `([t], [])`. -/
  theorem coprodTree_filter_emptyR (t : RTree) :
      (coprodTree t).filter (fun pr => pr.2.isEmpty) = [([t], [])] := by
    cases t with
    | node F =>
      rw [coprodTree_node, List.filter_cons]
      simp only [List.isEmpty_nil, ite_true, List.filter_map, Function.comp_def]
      simp_all
  theorem coprodForest_filter_emptyR (f : Forest) :
      (coprodForest f).filter (fun pr => pr.2.isEmpty) = [(f, [])] := by
    cases f with
    | nil => rfl
    | cons t ts =>
      have ht := coprodTree_filter_emptyR t
      have hts := coprodForest_filter_emptyR ts
      rw [show coprodForest (t :: ts) = tmul (coprodTree t) (coprodForest ts) from rfl,
          filter_emptyR_tmul, ht, hts]
      simp [tmul]
end

/-- Filtering cuts by "empty left leg" factorizes over `tmul`. -/
theorem filter_emptyL_tmul (A B : Tens) :
    (tmul A B).filter (fun pr => pr.1.isEmpty)
      = tmul (A.filter (fun pr => pr.1.isEmpty)) (B.filter (fun pr => pr.1.isEmpty)) := by
  induction A with
  | nil => rfl
  | cons a as ih =>
    obtain ⟨p, r⟩ := a
    rcases p with _ | ⟨c, cs⟩
    · simp only [tmul_cons, List.filter_append, ih, List.filter_cons, List.isEmpty_nil,
        ite_true, List.filter_map, Function.comp_def, List.nil_append]
    · simp only [tmul_cons, List.filter_append, ih, List.filter_cons, List.isEmpty_cons,
        Bool.false_eq_true, ite_false, List.filter_map, Function.comp_def]
      simp_all

mutual
  /-- The unique empty-left cut of a tree `t` is `([], [t])`. -/
  theorem coprodTree_filter_emptyL (t : RTree) :
      (coprodTree t).filter (fun pr => pr.1.isEmpty) = [([], [t])] := by
    cases t with
    | node F =>
      rw [coprodTree_node, List.filter_cons]
      simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, List.filter_map,
        Function.comp_def]
      rw [coprodForest_filter_emptyL F]
      rfl
  theorem coprodForest_filter_emptyL (f : Forest) :
      (coprodForest f).filter (fun pr => pr.1.isEmpty) = [([], f)] := by
    cases f with
    | nil => rfl
    | cons t ts =>
      have ht := coprodTree_filter_emptyL t
      have hts := coprodForest_filter_emptyL ts
      rw [show coprodForest (t :: ts) = tmul (coprodTree t) (coprodForest ts) from rfl,
          filter_emptyL_tmul, ht, hts]
      simp [tmul]
end

/-- Split a mapped `List.sum` by a boolean predicate. -/
theorem map_sum_filter_split {α : Type*} (L : List α) (P : α → Bool)
    (g : α → H k) :
    (L.map g).sum
      = ((L.filter P).map g).sum + ((L.filter (fun x => !P x)).map g).sum := by
  rw [← List.sum_append, ← List.map_append]
  exact (List.Perm.map g (List.filter_append_perm P L).symm).sum_eq

/-- **Left convolution axiom** on a basis forest: `(S ⋆ id)(f) = ε(f)·1`. Near-definitional. -/
theorem leftConvF (f : Forest) :
    ((coprodForest f).map (fun pr => antipodeF k pr.1 * sf k pr.2)).sum =
      εmon k f • (1 : H k) := by
  cases f with
  | nil =>
    rw [show coprodForest ([] : Forest) = [([], [])] from rfl]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [antipodeF, one_mul, sf_nil, εmon_nil, one_smul]
  | cons t ts =>
    rw [map_sum_filter_split (k := k) (L := coprodForest (t :: ts))
          (P := fun pr => pr.2.isEmpty)
          (g := fun pr => antipodeF k pr.1 * sf k pr.2),
        coprodForest_filter_emptyR]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, sf_nil, mul_one]
    rw [εmon_cons, zero_smul, antipodeF_cons]
    abel

/-- `μ ∘ (S ⊗ id)` on a pure 2-tensor `e2 (p,r)` gives `S(p)·r`. -/
theorem mul_rTensor_antipode_e2 (pr : Forest × Forest) :
    LinearMap.mul' k (H k) (LinearMap.rTensor (H k) (antipode k) (e2 k pr))
      = antipodeF k pr.1 * sf k pr.2 := by
  rw [e2, LinearMap.rTensor_tmul, LinearMap.mul'_apply, antipode_single, one_smul]
  rfl

/-- `μ ∘ (S ⊗ id) ∘ Δ` on a basis forest equals `ε(f)·1` (left antipode identity). -/
theorem rTensor_antipode_Δ₀ (f : Forest) :
    (LinearMap.mul' k (H k) ∘ₗ LinearMap.rTensor (H k) (antipode k)) (Δ₀ k f)
      = εmon k f • (1 : H k) := by
  rw [Δ₀, linmap_list_sum]
  rw [show ((coprodForest f).map (fun pr =>
        (LinearMap.mul' k (H k) ∘ₗ LinearMap.rTensor (H k) (antipode k)) (e2 k pr))).sum
      = ((coprodForest f).map (fun pr => antipodeF k pr.1 * sf k pr.2)).sum from ?_]
  · exact leftConvF k f
  · apply congrArg List.sum
    apply List.map_congr_left
    intro pr _
    rw [LinearMap.comp_apply]
    exact mul_rTensor_antipode_e2 k pr

/-! ### Mirror (right) antipode `S'`, satisfying `id ⋆ S' = η∘ε`. -/

/-- The right antipode by well-founded recursion on node count.
    `S'(∅) = 1`; `S'(f) = -Σ_{(p,r) cut, p ≠ ∅} p·S'(r)`. Decreases since `|r| < |f|`. -/
noncomputable def antipodeF' : Forest → H k
  | [] => 1
  | (t :: ts) =>
    - (((coprodForest (t :: ts)).filter (fun pr => !pr.1.isEmpty)).attach.map
        (fun pr => sf k pr.val.1 * antipodeF' pr.val.2)).sum
termination_by f => sizeF f
decreasing_by
  have hmem := pr.property
  rw [List.mem_filter] at hmem
  have hcons := size_consForest _ pr.val hmem.1
  have hp : pr.val.1 ≠ [] := by simpa [List.isEmpty_iff] using hmem.2
  have hpos := sizeF_pos hp
  have hlt : sizeF pr.val.2 < sizeF pr.val.1 + sizeF pr.val.2 := by omega
  simp_all

theorem antipodeF'_cons (t : RTree) (ts : Forest) :
    antipodeF' k (t :: ts)
      = - (((coprodForest (t :: ts)).filter (fun pr => !pr.1.isEmpty)).map
          (fun pr => sf k pr.1 * antipodeF' k pr.2)).sum := by
  conv_lhs => rw [antipodeF']
  simp only [List.map_attach_eq_pmap, List.pmap_eq_map]

/-- Right convolution `id ⋆ S'` on a basis forest equals `ε(f)·1`. Near-definitional. -/
theorem rightConvF' (f : Forest) :
    ((coprodForest f).map (fun pr => sf k pr.1 * antipodeF' k pr.2)).sum =
      εmon k f • (1 : H k) := by
  cases f with
  | nil =>
    rw [show coprodForest ([] : Forest) = [([], [])] from rfl]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [antipodeF', mul_one, sf_nil, εmon_nil, one_smul]
  | cons t ts =>
    rw [map_sum_filter_split (k := k) (L := coprodForest (t :: ts))
          (P := fun pr => pr.1.isEmpty)
          (g := fun pr => sf k pr.1 * antipodeF' k pr.2),
        coprodForest_filter_emptyL]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, sf_nil, one_mul]
    rw [εmon_cons, zero_smul, antipodeF'_cons]
    abel

/-- The mirrored antipode candidate used to prove the right convolution identity. -/
noncomputable def antipode' : H k →ₗ[k] H k :=
  Finsupp.linearCombination k (antipodeF' k) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

theorem antipode'_single (f : Forest) (b : k) :
    antipode' k (MonoidAlgebra.single f b) = b • antipodeF' k f := by
  change Finsupp.linearCombination k (antipodeF' k) (Finsupp.single f b) = b • antipodeF' k f
  rw [Finsupp.linearCombination_single]

theorem mul_lTensor_antipode'_e2 (pr : Forest × Forest) :
    LinearMap.mul' k (H k) (LinearMap.lTensor (H k) (antipode' k) (e2 k pr))
      = sf k pr.1 * antipodeF' k pr.2 := by
  rw [e2, LinearMap.lTensor_tmul, LinearMap.mul'_apply, antipode'_single, one_smul]
  rfl

/-- `μ ∘ (id ⊗ S') ∘ Δ` on a basis forest equals `ε(f)·1` (right antipode identity). -/
theorem lTensor_antipode'_Δ₀ (f : Forest) :
    (LinearMap.mul' k (H k) ∘ₗ LinearMap.lTensor (H k) (antipode' k)) (Δ₀ k f)
      = εmon k f • (1 : H k) := by
  rw [Δ₀, linmap_list_sum]
  rw [show ((coprodForest f).map (fun pr =>
        (LinearMap.mul' k (H k) ∘ₗ LinearMap.lTensor (H k) (antipode' k)) (e2 k pr))).sum
      = ((coprodForest f).map (fun pr => sf k pr.1 * antipodeF' k pr.2)).sum from ?_]
  · exact rightConvF' k f
  · apply congrArg List.sum
    apply List.map_congr_left
    intro pr _
    rw [LinearMap.comp_apply]
    exact mul_lTensor_antipode'_e2 k pr

/-- Left antipode identity as a linear-map equality (the Hopf left axiom). -/
theorem leftAntipode_eq :
    LinearMap.mul' k (H k) ∘ₗ LinearMap.rTensor (H k) (antipode k) ∘ₗ Δ k
      = Algebra.linearMap k (H k) ∘ₗ ε k := by
  apply ConnesKreimer.lhom_ext
  intro f b
  change LinearMap.mul' k (H k)
        (LinearMap.rTensor (H k) (antipode k) (Δ k (MonoidAlgebra.single f b)))
      = Algebra.linearMap k (H k) (ε k (MonoidAlgebra.single f b))
  rw [Δ_single, map_smul,
      map_smul,
      show LinearMap.mul' k (H k) (LinearMap.rTensor (H k) (antipode k) (Δ₀ k f))
        = εmon k f • (1 : H k) from rTensor_antipode_Δ₀ k f,
      ε_single, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one, mul_smul]

/-- Right antipode identity for `S'` as a linear-map equality. -/
theorem rightAntipode'_eq :
    LinearMap.mul' k (H k) ∘ₗ LinearMap.lTensor (H k) (antipode' k) ∘ₗ Δ k
      = Algebra.linearMap k (H k) ∘ₗ ε k := by
  apply ConnesKreimer.lhom_ext
  intro f b
  change LinearMap.mul' k (H k)
        (LinearMap.lTensor (H k) (antipode' k) (Δ k (MonoidAlgebra.single f b)))
      = Algebra.linearMap k (H k) (ε k (MonoidAlgebra.single f b))
  rw [Δ_single, map_smul,
      map_smul,
      show LinearMap.mul' k (H k) (LinearMap.lTensor (H k) (antipode' k) (Δ₀ k f))
        = εmon k f • (1 : H k) from lTensor_antipode'_Δ₀ k f,
      ε_single, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one, mul_smul]

/-- The left and right antipodes coincide (a left convolution-inverse of `id` that has
    a right convolution-inverse must equal it — pure monoid algebra in `WithConv`). -/
theorem antipode_eq_antipode' : antipode k = antipode' k := by
  have hSI : WithConv.toConv (antipode k) * WithConv.toConv (LinearMap.id (R := k) (M := H k))
      = 1 := by
    apply WithConv.ext
    rw [LinearMap.convMul_def]
    exact leftAntipode_eq k
  have hIS' : WithConv.toConv (LinearMap.id (R := k) (M := H k)) * WithConv.toConv (antipode' k)
      = 1 := by
    apply WithConv.ext
    rw [LinearMap.convMul_def]
    exact rightAntipode'_eq k
  have key : WithConv.toConv (antipode k) = WithConv.toConv (antipode' k) := by
    calc WithConv.toConv (antipode k)
        = WithConv.toConv (antipode k) * 1 := (mul_one _).symm
      _ = WithConv.toConv (antipode k)
            * (WithConv.toConv (LinearMap.id (R := k) (M := H k)) *
                WithConv.toConv (antipode' k)) := by
            rw [hIS']
      _ = (WithConv.toConv (antipode k) * WithConv.toConv (LinearMap.id (R := k) (M := H k)))
            * WithConv.toConv (antipode' k) := (mul_assoc _ _ _).symm
      _ = 1 * WithConv.toConv (antipode' k) := by rw [hSI]
      _ = WithConv.toConv (antipode' k) := one_mul _
  simp_all

noncomputable instance : HopfAlgebraStruct k (H k) where
  antipode := antipode k

noncomputable instance instCKHopf : HopfAlgebra k (H k) where
  mul_antipode_rTensor_comul := leftAntipode_eq k
  mul_antipode_lTensor_comul := by
    change LinearMap.mul' k (H k) ∘ₗ LinearMap.lTensor (H k) (antipode k) ∘ₗ Δ k
        = Algebra.linearMap k (H k) ∘ₗ ε k
    rw [antipode_eq_antipode']
    exact rightAntipode'_eq k

end ConnesKreimer
