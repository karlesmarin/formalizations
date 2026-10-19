/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.RingTheory.HopfAlgebra.ConnesKreimer.Basic
public import Mathlib.Algebra.RingQuot

/-!
# The commutative Connes–Kreimer–Butcher Hopf algebra

The abelianization `Hab k = H k / ⟨ab − ba⟩` of the planar Hopf algebra, built with Mathlib's
`RingQuot`. Coproduct, counit and antipode descend through the projection `π`, so `Hab k` is the
classical (commutative) Connes–Kreimer / Butcher Hopf algebra of rooted trees. Coassociativity is
proved once on the planar algebra and transported.

## Main results

* `ConnesKreimer.Hab`, `ConnesKreimer.π`, `ConnesKreimer.π_mul_comm`: the quotient and its
  commutative ring structure.
* `ConnesKreimer.Δab`, `ConnesKreimer.εab`, `ConnesKreimer.Sab`: the descended structure maps.
* `ConnesKreimer.coassoc_Hab`, `ConnesKreimer.instHabCoalg`, `ConnesKreimer.instHabBialg`.
* `ConnesKreimer.instHabHopf`: `HopfAlgebra k (Hab k)`.

## References

* A. Connes, D. Kreimer, *Hopf algebras, renormalization and noncommutative geometry*,
  Comm. Math. Phys. 199 (1998) 203–242.
* J. C. Butcher, *An algebraic theory of integration methods*, Math. Comp. 26 (1972) 79–106.
* C. Marín, *How a Tree Forgets Its Order: the Eulerian idempotent and the Adams spectrum on the
  commutative Connes–Kreimer–Butcher Hopf algebra of rooted trees, machine-checked in Lean 4*
  (2026), doi:10.5281/zenodo.20774821. Ported from `ConnesKreimer.lean` of
  [karlesmarin/connes-kreimer-lean](https://github.com/karlesmarin/connes-kreimer-lean)
  (Lean v4.30.0-rc2).
-/

@[expose] public section

open scoped TensorProduct

namespace ConnesKreimer

variable (k : Type*) [CommRing k]

/-! ### The commutative quotient `H_ab = H / ⟨ab − ba⟩`
    (Foissy's planar → commutative map).

    Abelianizing the (forest) product turns the planar Hopf algebra into a commutative one. This is
    the algebra step: the quotient ring `RingQuot` by the commutator relation, shown
    commutative.
    The coproduct, counit and antipode descend in the following sections, giving the classical
    (commutative) Connes–Kreimer / Butcher Hopf algebra, where the Eulerian idempotents become
    genuine orthogonal idempotents. -/

/-- The commutator relation `x·y ∼ y·x` on `H`. -/
inductive commRel : H k → H k → Prop
  | mul (x y : H k) : commRel (x * y) (y * x)

/-- The commutative quotient `H_ab = H / ⟨ab − ba⟩`. -/
abbrev Hab : Type _ := RingQuot (commRel k)

/-- The quotient algebra map `π : H → H_ab`. -/
noncomputable def π : H k →ₐ[k] Hab k := RingQuot.mkAlgHom k (commRel k)

/-- `H_ab` is commutative: the relation forces `π(x)·π(y) = π(y)·x`. -/
noncomputable instance : CommRing (Hab k) where
  __ := (inferInstance : Ring (RingQuot (commRel k)))
  mul_comm a b := by
    obtain ⟨x, rfl⟩ := RingQuot.mkAlgHom_surjective k (commRel k) a
    obtain ⟨y, rfl⟩ := RingQuot.mkAlgHom_surjective k (commRel k) b
    rw [← map_mul, ← map_mul]
    exact RingQuot.mkAlgHom_rel k (commRel.mul x y)

theorem π_surjective : Function.Surjective (π k) :=
  RingQuot.mkAlgHom_surjective k (commRel k)

theorem π_mul_comm (x y : H k) : π k (x * y) = π k (y * x) :=
  RingQuot.mkAlgHom_rel k (commRel.mul x y)

/-! #### The coproduct descends to `Delta_ab : H_ab → H_ab ⊗ H_ab`. -/

/-- `Δ` as an algebra homomorphism (the bialgebra coproduct), from `Δ_one` and `Δ_mul`. -/
noncomputable def ΔAlg : H k →ₐ[k] H k ⊗[k] H k :=
  AlgHom.ofLinearMap (Δ k) (Δ_one k) (Δ_mul k)

/-- `(π⊗π)∘Δ` respects the commutator relation, since `H_ab ⊗ H_ab` is commutative. -/
theorem ΔAlg_resp_commRel ⦃a b : H k⦄ (h : commRel k a b) :
    (Algebra.TensorProduct.map (π k) (π k)).comp (ΔAlg k) a
      = (Algebra.TensorProduct.map (π k) (π k)).comp (ΔAlg k) b := by
  obtain ⟨x, y⟩ := h
  rw [map_mul, map_mul, mul_comm]

/-- The descended coproduct `Delta_ab : H_ab → H_ab ⊗ H_ab`. -/
noncomputable def Δab : Hab k →ₐ[k] Hab k ⊗[k] Hab k :=
  RingQuot.liftAlgHom k
    ⟨(Algebra.TensorProduct.map (π k) (π k)).comp (ΔAlg k), ΔAlg_resp_commRel k⟩

/-- The descent square commutes: `Delta_ab ∘ π = (π⊗π) ∘ Δ`. -/
theorem Δab_π (x : H k) :
    Δab k (π k x) = Algebra.TensorProduct.map (π k) (π k) (ΔAlg k x) :=
  RingQuot.liftAlgHom_mkAlgHom_apply k _ (ΔAlg_resp_commRel k) x

/-! #### The counit descends to `epsilon_ab : H_ab → k`. -/

/-- `ε` respects the commutator relation (`k` is commutative). -/
theorem εalg_resp_commRel ⦃a b : H k⦄ (h : commRel k a b) :
    εalg k a = εalg k b := by
  obtain ⟨x, y⟩ := h
  rw [map_mul, map_mul, mul_comm]

/-- The descended counit `epsilon_ab : H_ab → k`. -/
noncomputable def εab : Hab k →ₐ[k] k :=
  RingQuot.liftAlgHom k ⟨εalg k, εalg_resp_commRel k⟩

theorem εab_π (x : H k) : εab k (π k x) = εalg k x :=
  RingQuot.liftAlgHom_mkAlgHom_apply k _ (εalg_resp_commRel k) x

/-! #### `H_ab` is a coalgebra (coassoc + counit laws descend through `π`). -/

/-- Extensionality on `H_ab`: a linear map out of `H_ab` is determined by its values on `π`. -/
theorem Hab_lhom_ext {M : Type*} [AddCommMonoid M] [Module k M]
    {g₁ g₂ : Hab k →ₗ[k] M} (h : ∀ x : H k, g₁ (π k x) = g₂ (π k x)) :
    g₁ = g₂ := by
  ext u
  obtain ⟨x, rfl⟩ := π_surjective k u
  exact h x

/-- `ε` (right) counit naturality: `(epsilon_ab⊗id)∘(π⊗π) = ε⊗π`. -/
theorem εab_rTensor_natural :
    (LinearMap.rTensor (Hab k) (εab k).toLinearMap) ∘ₗ
        (Algebra.TensorProduct.map (π k) (π k)).toLinearMap
      = TensorProduct.map (ε k) (π k).toLinearMap := by
  apply TensorProduct.ext'
  intro a b
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Algebra.TensorProduct.map_tmul,
      LinearMap.rTensor_tmul,
      TensorProduct.map_tmul]
  change εab k (π k a) ⊗ₜ[k] π k b = ε k a ⊗ₜ[k] π k b
  rw [εab_π]; rfl

/-- `ε` (left) counit naturality: `(id⊗epsilon_ab)∘(π⊗π) = π⊗ε`. -/
theorem εab_lTensor_natural :
    (LinearMap.lTensor (Hab k) (εab k).toLinearMap) ∘ₗ
        (Algebra.TensorProduct.map (π k) (π k)).toLinearMap
      = TensorProduct.map (π k).toLinearMap (ε k) := by
  apply TensorProduct.ext'
  intro a b
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Algebra.TensorProduct.map_tmul,
      LinearMap.lTensor_tmul,
      TensorProduct.map_tmul]
  change π k a ⊗ₜ[k] εab k (π k b) = π k a ⊗ₜ[k] ε k b
  rw [εab_π]; rfl

/-- Left counitality on `H_ab`: `(epsilon_ab ⊗ id) ∘ Delta_ab = 1 ⊗ ·`. -/
theorem rTensor_εab_comp_Δab :
    (LinearMap.rTensor (Hab k) (εab k).toLinearMap) ∘ₗ (Δab k).toLinearMap
      = TensorProduct.mk k k (Hab k) 1 := by
  have hsplit : TensorProduct.map (ε k) (π k).toLinearMap
      = LinearMap.lTensor k (π k).toLinearMap ∘ₗ LinearMap.rTensor (H k) (ε k) := by
    simp_all
  apply Hab_lhom_ext
  intro x
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Δab_π, ← AlgHom.toLinearMap_apply,
      ← LinearMap.comp_apply,
      εab_rTensor_natural]
  change TensorProduct.map (ε k) (π k).toLinearMap (Δ k x) = (1 : k) ⊗ₜ[k] π k x
  rw [hsplit, LinearMap.comp_apply,
      show LinearMap.rTensor (H k) (ε k) (Δ k x) = (1 : k) ⊗ₜ[k] x from
        Coalgebra.rTensor_counit_comul (R := k) (A := H k) x,
      LinearMap.lTensor_tmul]
  rfl

/-- Right counitality on `H_ab`: `(id ⊗ epsilon_ab) ∘ Delta_ab = · ⊗ 1`. -/
theorem lTensor_εab_comp_Δab :
    (LinearMap.lTensor (Hab k) (εab k).toLinearMap) ∘ₗ (Δab k).toLinearMap
      = (TensorProduct.mk k (Hab k) k).flip 1 := by
  have hsplit : TensorProduct.map (π k).toLinearMap (ε k)
      = LinearMap.rTensor k (π k).toLinearMap ∘ₗ LinearMap.lTensor (H k) (ε k) := by
    simp_all
  apply Hab_lhom_ext
  intro x
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Δab_π, ← AlgHom.toLinearMap_apply,
      ← LinearMap.comp_apply,
      εab_lTensor_natural]
  change TensorProduct.map (π k).toLinearMap (ε k) (Δ k x) = π k x ⊗ₜ[k] (1 : k)
  rw [hsplit, LinearMap.comp_apply,
      show LinearMap.lTensor (H k) (ε k) (Δ k x) = x ⊗ₜ[k] (1 : k) from
        Coalgebra.lTensor_counit_comul (R := k) (A := H k) x,
      LinearMap.rTensor_tmul]
  rfl

/-- `Delta_ab ∘ π = (π⊗π) ∘ Δ` in purely linear (TensorProduct.map) form. -/
theorem Δab_π' (x : H k) :
    Δab k (π k x)
      = TensorProduct.map (π k).toLinearMap (π k).toLinearMap (Δ k x) := by
  have h : (Algebra.TensorProduct.map (π k) (π k)).toLinearMap
      = TensorProduct.map (π k).toLinearMap (π k).toLinearMap := by
    apply TensorProduct.ext'; simp_all
  rw [Δab_π, ← AlgHom.toLinearMap_apply, h]
  rfl

/-- `Delta_ab ∘ π` in `.toLinearMap` form (for use inside compositions). -/
theorem Δab_tl_π (x : H k) :
    (Δab k).toLinearMap (π k x)
      = TensorProduct.map (π k).toLinearMap (π k).toLinearMap (Δ k x) := by
  rw [AlgHom.toLinearMap_apply, Δab_π']

/-- Coproduct (right) naturality for the descent:
    `(Delta_ab⊗id)∘(π⊗π) = ((π⊗π)⊗π)∘(Δ⊗id)`. -/
theorem Δab_rTensor_natural :
    (LinearMap.rTensor (Hab k) (Δab k).toLinearMap)
        ∘ₗ TensorProduct.map (π k).toLinearMap (π k).toLinearMap
      = TensorProduct.map
          (TensorProduct.map (π k).toLinearMap (π k).toLinearMap) (π k).toLinearMap
          ∘ₗ LinearMap.rTensor (H k) (Δ k) := by
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.rTensor_tmul,
    AlgHom.toLinearMap_apply, Δab_π']

/-- Coproduct (left) naturality for the descent:
    `(id⊗Delta_ab)∘(π⊗π) = (π⊗(π⊗π))∘(id⊗Δ)`. -/
theorem Δab_lTensor_natural :
    (LinearMap.lTensor (Hab k) (Δab k).toLinearMap)
        ∘ₗ TensorProduct.map (π k).toLinearMap (π k).toLinearMap
      = TensorProduct.map (π k).toLinearMap
          (TensorProduct.map (π k).toLinearMap (π k).toLinearMap)
          ∘ₗ LinearMap.lTensor (H k) (Δ k) := by
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.lTensor_tmul,
    AlgHom.toLinearMap_apply, Δab_π']

/-- Coassociativity on `H_ab`, descended from the planar coassociativity via `π`. -/
theorem coassoc_Hab :
    (TensorProduct.assoc k (Hab k) (Hab k) (Hab k)).toLinearMap
        ∘ₗ (LinearMap.rTensor (Hab k) (Δab k).toLinearMap) ∘ₗ (Δab k).toLinearMap
      = (LinearMap.lTensor (Hab k) (Δab k).toLinearMap) ∘ₗ (Δab k).toLinearMap := by
  apply Hab_lhom_ext
  intro x
  have CP : (TensorProduct.assoc k (H k) (H k) (H k))
        (LinearMap.rTensor (H k) (Δ k) (Δ k x)) = LinearMap.lTensor (H k) (Δ k) (Δ k x) :=
    LinearMap.congr_fun (Coalgebra.coassoc (R := k) (A := H k)) x
  have hR := LinearMap.congr_fun (Δab_rTensor_natural k) (Δ k x)
  have hL := LinearMap.congr_fun (Δab_lTensor_natural k) (Δ k x)
  have hAssoc := LinearMap.congr_fun
    (TensorProduct.map_map_comp_assoc_eq (π k).toLinearMap (π k).toLinearMap (π k).toLinearMap)
    (LinearMap.rTensor (H k) (Δ k) (Δ k x))
  simp only [LinearMap.comp_apply] at hR hL hAssoc ⊢
  rw [Δab_tl_π, hR, hL, ← hAssoc]
  exact congrArg _ CP

/-- `H_ab` is a coalgebra (the commutative Connes–Kreimer coalgebra). -/
noncomputable instance : CoalgebraStruct k (Hab k) where
  comul := (Δab k).toLinearMap
  counit := (εab k).toLinearMap

noncomputable instance instHabCoalg : Coalgebra k (Hab k) where
  coassoc := coassoc_Hab k
  rTensor_counit_comp_comul := rTensor_εab_comp_Δab k
  lTensor_counit_comp_comul := lTensor_εab_comp_Δab k

/-! ### `H_ab` is a bialgebra.
    `Δab`, `εab` are algebra homs by construction, so the four `Bialgebra.mk'`
    compatibilities are just `map_one`/`map_mul` (cf. planar `instCKBialg`, which
    needed a separate `Δ_mul` because there `Δ` was not yet packaged as an AlgHom). -/
noncomputable instance instHabBialg : Bialgebra k (Hab k) :=
  Bialgebra.mk' k (Hab k)
    (map_one (εab k))
    (fun {a b} => map_mul (εab k) a b)
    (map_one (Δab k))
    (fun {a b} => map_mul (Δab k) a b)

/-! #### The antipode descends to `S_ab : H_ab → H_ab`, giving `HopfAlgebra k (H_ab)`.

`S = antipode k` is an algebra anti-homomorphism; composing with
`π` into the COMMUTATIVE quotient `H_ab` turns it into a genuine algebra hom, so it lifts
through `RingQuot`. The two antipode axioms then descend through `π` exactly like
coassociativity in S4. -/

/-- `π ∘ S : H → H_ab` as an algebra hom: on the commutative quotient the antipode
    anti-homomorphism becomes a homomorphism (`π(S(ab)) = π(Sb·Sa) = π(Sa)·π(Sb)`). -/
noncomputable def SalgHom : H k →ₐ[k] Hab k :=
  AlgHom.ofLinearMap ((π k).toLinearMap ∘ₗ antipode k)
    (by
      have h1 : antipode k (1 : H k) = 1 := HopfAlgebra.antipode_one (R := k) (A := H k)
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, h1, map_one])
    (by
      intro a b
      have hmul : antipode k (a * b) = antipode k b * antipode k a :=
        HopfAlgebra.antipode_mul_antidistrib (R := k) a b
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
      rw [hmul, map_mul]
      exact mul_comm _ _)

/-- `π ∘ S` respects the commutator relation (`H_ab` is commutative). -/
theorem SalgHom_resp_commRel ⦃a b : H k⦄ (h : commRel k a b) :
    SalgHom k a = SalgHom k b := by
  obtain ⟨x, y⟩ := h
  rw [map_mul, map_mul, mul_comm]

/-- The descended antipode `S_ab : H_ab → H_ab`. -/
noncomputable def Sab : Hab k →ₐ[k] Hab k :=
  RingQuot.liftAlgHom k ⟨SalgHom k, SalgHom_resp_commRel k⟩

/-- The descent square: `S_ab ∘ π = π ∘ S`. -/
theorem Sab_π (x : H k) : Sab k (π k x) = π k (antipode k x) :=
  RingQuot.liftAlgHom_mkAlgHom_apply k _ (SalgHom_resp_commRel k) x

/-- `mu_ab ∘ (π⊗π) = π ∘ μ` (multiplication naturality, `π` an algebra hom). -/
theorem mul'_π :
    LinearMap.mul' k (Hab k) ∘ₗ TensorProduct.map (π k).toLinearMap (π k).toLinearMap
      = (π k).toLinearMap ∘ₗ LinearMap.mul' k (H k) := by
  apply TensorProduct.ext'
  simp_all

/-- Antipode (left) naturality for the descent: `(S_ab⊗id)∘(π⊗π) = (π⊗π)∘(S⊗id)`. -/
theorem Sab_rTensor_natural :
    (LinearMap.rTensor (Hab k) (Sab k).toLinearMap)
        ∘ₗ TensorProduct.map (π k).toLinearMap (π k).toLinearMap
      = TensorProduct.map (π k).toLinearMap (π k).toLinearMap
          ∘ₗ LinearMap.rTensor (H k) (antipode k) := by
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.rTensor_tmul,
    AlgHom.toLinearMap_apply, Sab_π]

/-- Antipode (right) naturality for the descent: `(id⊗S_ab)∘(π⊗π) = (π⊗π)∘(id⊗S)`. -/
theorem Sab_lTensor_natural :
    (LinearMap.lTensor (Hab k) (Sab k).toLinearMap)
        ∘ₗ TensorProduct.map (π k).toLinearMap (π k).toLinearMap
      = TensorProduct.map (π k).toLinearMap (π k).toLinearMap
          ∘ₗ LinearMap.lTensor (H k) (antipode k) := by
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.lTensor_tmul,
    AlgHom.toLinearMap_apply, Sab_π]

/-- The (right-factor) left antipode identity, stated for `antipode k` rather than `antipode' k`
    (`id ⋆ S = u∘ε` re-expressed via `antipode = antipode'`). -/
theorem lTensor_antipode_eq :
    LinearMap.mul' k (H k) ∘ₗ LinearMap.lTensor (H k) (antipode k) ∘ₗ Δ k
      = Algebra.linearMap k (H k) ∘ₗ ε k := by
  rw [antipode_eq_antipode']
  exact rightAntipode'_eq k

/-- Left antipode identity on `H_ab`, descended through `π`. -/
theorem rTensor_Sab_Δab :
    LinearMap.mul' k (Hab k) ∘ₗ LinearMap.rTensor (Hab k) (Sab k).toLinearMap
        ∘ₗ (Δab k).toLinearMap
      = Algebra.linearMap k (Hab k) ∘ₗ (εab k).toLinearMap := by
  apply Hab_lhom_ext
  intro x
  have hLeft := LinearMap.congr_fun (leftAntipode_eq k) x
  have hNat := LinearMap.congr_fun (Sab_rTensor_natural k) (Δ k x)
  have hMul := LinearMap.congr_fun (mul'_π k) (LinearMap.rTensor (H k) (antipode k) (Δ k x))
  simp only [LinearMap.comp_apply] at hLeft hNat hMul ⊢
  rw [Δab_tl_π, hNat, hMul, hLeft]
  change π k (Algebra.linearMap k (H k) (ε k x)) = Algebra.linearMap k (Hab k) (εab k (π k x))
  rw [εab_π]
  exact (π k).commutes (ε k x)

/-- Right antipode identity on `H_ab`, descended through `π`. -/
theorem lTensor_Sab_Δab :
    LinearMap.mul' k (Hab k) ∘ₗ LinearMap.lTensor (Hab k) (Sab k).toLinearMap
        ∘ₗ (Δab k).toLinearMap
      = Algebra.linearMap k (Hab k) ∘ₗ (εab k).toLinearMap := by
  apply Hab_lhom_ext
  intro x
  have hRight := LinearMap.congr_fun (lTensor_antipode_eq k) x
  have hNat := LinearMap.congr_fun (Sab_lTensor_natural k) (Δ k x)
  have hMul := LinearMap.congr_fun (mul'_π k) (LinearMap.lTensor (H k) (antipode k) (Δ k x))
  simp only [LinearMap.comp_apply] at hRight hNat hMul ⊢
  rw [Δab_tl_π, hNat, hMul, hRight]
  change π k (Algebra.linearMap k (H k) (ε k x)) = Algebra.linearMap k (Hab k) (εab k (π k x))
  rw [εab_π]
  exact (π k).commutes (ε k x)

noncomputable instance : HopfAlgebraStruct k (Hab k) where
  antipode := (Sab k).toLinearMap

/-- `H_ab` is a Hopf algebra: the commutative Connes–Kreimer / Butcher Hopf algebra of
    rooted forests, obtained from the planar one by the abelianization quotient. -/
noncomputable instance instHabHopf : HopfAlgebra k (Hab k) where
  mul_antipode_rTensor_comul := rTensor_Sab_Δab k
  mul_antipode_lTensor_comul := lTensor_Sab_Δab k

end ConnesKreimer
