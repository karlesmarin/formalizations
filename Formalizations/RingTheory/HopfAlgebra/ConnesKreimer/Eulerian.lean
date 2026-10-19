/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.RingTheory.HopfAlgebra.ConnesKreimer.Abelianization
public import Formalizations.RingTheory.HopfAlgebra.ConnesKreimer.Adams
public import Formalizations.RingTheory.PowerSeries.LogMul

/-!
# The first Eulerian idempotent is idempotent on the commutative algebra

On the commutative Hopf algebra `Hab k` (over a `ℚ`-algebra `k`) the Adams operators are algebra
morphisms with `Ψᵖ ∘ Ψ^q = Ψ^{pq}`, the image of the first Eulerian idempotent is an eigenvector,
`Ψⁱ ∘ e⁽¹⁾ = i · e⁽¹⁾`, and a finite-difference identity collapses the convolution logarithm on
eigenvectors. Hence `e⁽¹⁾ ∘ e⁽¹⁾ = e⁽¹⁾` on `Hab k`; on the planar algebra this fails.

## Main results

* `ConnesKreimer.adamsAb_mul`, `ConnesKreimer.adamsAb_comp`: `Ψⁿ` is an algebra morphism on
  `Hab k`, and `Ψᵖ ∘ Ψ^q = Ψ^{pq}`.
* `ConnesKreimer.alternating_choose_weighted`: `Σᵢ (−1)^{j−i} C(j,i) · i = δ_{j,1}`.
* `ConnesKreimer.star_identity`, `ConnesKreimer.adamsAb_comp_JcAb_pow`: the eigen-transport
  `J_ab ↦ Yᵖ − 1` evaluated at the per-degree nilpotent `J_ab`.
* `ConnesKreimer.adamsAb_eigen`: `Ψⁱ ∘ e⁽¹⁾ = i · e⁽¹⁾`.
* `ConnesKreimer.brickC`: on an Adams eigenvector the truncated convolution logarithm is the
  identity.
* `ConnesKreimer.eulerian1_idem_ab`: `π (e⁽¹⁾ (e⁽¹⁾ x)) = π (e⁽¹⁾ x)`.

The power-series input is `PowerSeries.coeff_logTrunc_pow`
(`Formalizations.RingTheory.PowerSeries.LogMul`).

## References

* F. Patras, *L'algèbre des descentes d'une bigèbre graduée*, J. Algebra 170 (1994) 547–566.
* J.-L. Loday, *Opérations sur l'homologie cyclique des algèbres commutatives*, Invent. Math. 96
  (1989) 205–230.
* M. Aguiar, A. Lauve, *The characteristic polynomial of the Adams operators on graded connected
  Hopf algebras*, Algebra Number Theory 9 (2015) 547–583.
* C. Marín, *How a Tree Forgets Its Order: the Eulerian idempotent and the Adams spectrum on the
  commutative Connes–Kreimer–Butcher Hopf algebra of rooted trees, machine-checked in Lean 4*
  (2026), doi:10.5281/zenodo.20774821. Ported from `ConnesKreimer.lean` of
  [karlesmarin/connes-kreimer-lean](https://github.com/karlesmarin/connes-kreimer-lean)
  (Lean v4.30.0-rc2).
-/

@[expose] public section

open scoped TensorProduct

namespace ConnesKreimer

variable (k : Type*) [CommRing k] [Algebra ℚ k]

/-! ### Adams operators on `H_ab`

On the COMMUTATIVE `H_ab` the Eulerian idempotents `e⁽ⁱ⁾` become orthogonal idempotents
(Patras/Loday), so `e⁽¹⁾∘e⁽¹⁾ = e⁽¹⁾` holds (unlike on the planar algebra). The
principled route is via the Adams operators `Ψⁿ`: on a commutative Hopf algebra each `Ψⁿ` is an
algebra morphism, whence `Ψᵖ∘Ψq = Ψ^{pq}`, whence the `e⁽ⁱ⁾` are the orthogonal eigen-projectors.

First (no commutativity yet): the Adams operators on `H_ab`, and their naturality through `π`
(`Ψⁿ_ab ∘ π = π ∘ Ψⁿ`), which both defines `Ψⁿ_ab` and ties it to the planar `Ψⁿ`. -/

/-- The Adams operators `Ψⁿ = id^{⋆n}` on `H_ab` (convolution powers of the identity). -/
noncomputable def adamsAb (n : ℕ) : Hab k →ₗ[k] Hab k :=
  ((WithConv.toConv (LinearMap.id (R := k) (M := Hab k))) ^ n).ofConv

omit [Algebra ℚ k] in
/-- Element-level convolution on `H_ab`: `(F⋆G)(x) = mu_ab((F⊗G)(Delta_ab x))`. -/
theorem conv_apply_ab (F G : Hab k →ₗ[k] Hab k) (x : Hab k) :
    (WithConv.toConv F * WithConv.toConv G).ofConv x
      = LinearMap.mul' k (Hab k) (TensorProduct.map F G ((Δab k).toLinearMap x)) := by
  rw [LinearMap.convMul_def]; rfl

omit [Algebra ℚ k] in
/-- `Ψⁿ⁺¹_ab = id ⋆ Ψⁿ_ab` evaluated. -/
theorem adamsAb_succ_apply (n : ℕ) (x : Hab k) :
    adamsAb k (n + 1) x
      = LinearMap.mul' k (Hab k)
          (TensorProduct.map LinearMap.id (adamsAb k n) ((Δab k).toLinearMap x)) := by
  change (((WithConv.toConv (LinearMap.id (R := k) (M := Hab k))) ^ (n + 1)).ofConv) x = _
  rw [pow_succ', show (WithConv.toConv (LinearMap.id (R := k) (M := Hab k))) ^ n
        = WithConv.toConv (adamsAb k n) from rfl]
  exact conv_apply_ab k LinearMap.id (adamsAb k n) x

omit [Algebra ℚ k] in
/-- **Adams naturality**: `Ψⁿ_ab ∘ π = π ∘ Ψⁿ`. The planar Adams operators descend to `H_ab`
    through the bialgebra quotient map `π`. -/
theorem adamsAb_natural (n : ℕ) :
    (adamsAb k n) ∘ₗ (π k).toLinearMap = (π k).toLinearMap ∘ₗ (adams k n) := by
  induction n with
  | zero =>
    apply LinearMap.ext; intro x
    change (((WithConv.toConv (LinearMap.id (R := k) (M := Hab k))) ^ 0).ofConv)
        ((π k).toLinearMap x)
      = (π k).toLinearMap (((WithConv.toConv (LinearMap.id (R := k) (M := H k))) ^ 0).ofConv x)
    rw [pow_zero, pow_zero]
    change (1 : WithConv (Hab k →ₗ[k] Hab k)) ((π k).toLinearMap x)
       = (π k).toLinearMap ((1 : WithConv (H k →ₗ[k] H k)) x)
    rw [LinearMap.convOne_apply, LinearMap.convOne_apply, AlgHom.toLinearMap_apply]
    change algebraMap k (Hab k) (εab k (π k x)) = π k (algebraMap k (H k) (ε k x))
    rw [εab_π]
    exact ((π k).commutes (ε k x)).symm
  | succ m ih =>
    apply LinearMap.ext; intro x
    have hT : TensorProduct.map LinearMap.id (adamsAb k m)
          ∘ₗ TensorProduct.map (π k).toLinearMap (π k).toLinearMap
        = TensorProduct.map (π k).toLinearMap (π k).toLinearMap
          ∘ₗ TensorProduct.map LinearMap.id (adams k m) := by
      rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp,
          LinearMap.comp_id, ih]
    have hTx := LinearMap.congr_fun hT (Δ k x)
    have hMul := LinearMap.congr_fun (mul'_π k)
      (TensorProduct.map LinearMap.id (adams k m) (Δ k x))
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at hTx hMul ⊢
    rw [adamsAb_succ_apply, Δab_tl_π, hTx, hMul, adams_succ_apply]

/-! ### Adams operators are algebra morphisms

    Commutativity enters: each Adams operator `Ψⁿ` is an algebra morphism on the
    commutative `H_ab`. We package `Ψⁿ` as an `AlgHom` built by composition:
    `Ψⁿ⁺¹ = mu_ab∘(id⊗Ψⁿ)∘Delta_ab`. This is a composite of the algebra homs
    `Delta_ab`, `id⊗Ψⁿ`, and `mu_ab`, and the multiplication is an algebra hom precisely
    because `H_ab` is commutative. -/

/-- `Ψⁿ` packaged as an algebra hom on the commutative `H_ab` (`Ψ₀ = u∘ε`,
    `Ψⁿ⁺¹ = mu_ab ∘ (id ⊗ Ψⁿ) ∘ Delta_ab`). -/
noncomputable def adamsAbHom : ℕ → (Hab k →ₐ[k] Hab k)
  | 0 => (Algebra.ofId k (Hab k)).comp (εab k)
  | (n + 1) => (Algebra.TensorProduct.lmul' k).comp
      ((Algebra.TensorProduct.map (AlgHom.id k (Hab k)) (adamsAbHom n)).comp (Δab k))

omit [Algebra ℚ k] in
/-- The algebra-hom `Ψⁿ` and the convolution-power `Ψⁿ` agree as linear maps. -/
theorem adamsAbHom_toLinearMap (n : ℕ) :
    (adamsAbHom k n).toLinearMap = adamsAb k n := by
  induction n with
  | zero =>
    apply LinearMap.ext; intro x
    change (Algebra.ofId k (Hab k)).comp (εab k) x = adamsAb k 0 x
    rw [AlgHom.comp_apply]
    change algebraMap k (Hab k) (εab k x) = adamsAb k 0 x
    rw [show adamsAb k 0
          = ((WithConv.toConv (LinearMap.id (R := k) (M := Hab k))) ^ 0).ofConv from rfl, pow_zero]
    change algebraMap k (Hab k) (εab k x) = (1 : WithConv (Hab k →ₗ[k] Hab k)) x
    rw [LinearMap.convOne_apply]
    rfl
  | succ m ih =>
    apply LinearMap.ext; intro x
    rw [adamsAb_succ_apply]
    have e1 : (Algebra.TensorProduct.map (AlgHom.id k (Hab k)) (adamsAbHom k m)).toLinearMap
        = TensorProduct.map LinearMap.id (adamsAb k m) := by
      apply TensorProduct.ext'
      simp_all
    change Algebra.TensorProduct.lmul' k
        ((Algebra.TensorProduct.map (AlgHom.id k (Hab k)) (adamsAbHom k m)) ((Δab k) x))
      = LinearMap.mul' k (Hab k)
          (TensorProduct.map LinearMap.id (adamsAb k m) ((Δab k).toLinearMap x))
    rw [show (Algebra.TensorProduct.lmul' k)
            ((Algebra.TensorProduct.map (AlgHom.id k (Hab k)) (adamsAbHom k m)) ((Δab k) x))
          = LinearMap.mul' k (Hab k)
              ((Algebra.TensorProduct.map (AlgHom.id k (Hab k)) (adamsAbHom k m)).toLinearMap
                ((Δab k).toLinearMap x)) from rfl,
        e1]

omit [Algebra ℚ k] in
/-- **`Ψⁿ` is an algebra morphism on `H_ab`**: `Ψⁿ(ab) = Ψⁿ(a)·Ψⁿ(b)`. The key
    commutative-Hopf fact behind the orthogonality of the Eulerian idempotents. -/
theorem adamsAb_mul (n : ℕ) (a b : Hab k) :
    adamsAb k n (a * b) = adamsAb k n a * adamsAb k n b := by
  rw [← adamsAbHom_toLinearMap]
  simp_all

/-! ### The Adams composition law

    `Ψᵖ ∘ Ψq = Ψ^{pq}`. Post-composition by an algebra hom
    distributes over convolution (`LinearMap.algHom_comp_convMul_distrib`), so an algebra-hom
    `φ` post-composed with `Ψᵖ = id^{⋆p}` gives `(φ ∘ id)^{⋆p} = (toConv φ)^p`.
    Taking `φ = Ψq` gives `Ψq ∘ Ψᵖ = (Ψq)^{⋆p} = id^{⋆qp} = Ψ^{qp}`. -/

omit [Algebra ℚ k] in
/-- An algebra hom `φ` post-composed with the Adams operator `Ψᵖ` is the `p`-th convolution power
    of `φ` itself: `φ ∘ Ψᵖ = (toConv φ)^p` in `WithConv`. -/
theorem algHom_comp_adamsAb (φ : Hab k →ₐ[k] Hab k) (p : ℕ) :
    φ.toLinearMap ∘ₗ adamsAb k p = ((WithConv.toConv φ.toLinearMap) ^ p).ofConv := by
  induction p with
  | zero =>
    change φ.toLinearMap ∘ₗ ((WithConv.toConv (LinearMap.id (R := k) (M := Hab k))) ^ 0).ofConv
       = ((WithConv.toConv φ.toLinearMap) ^ 0).ofConv
    rw [pow_zero, pow_zero]
    apply LinearMap.ext; simp_all
  | succ n ih =>
    change φ.toLinearMap ∘ₗ
        ((WithConv.toConv (LinearMap.id (R := k) (M := Hab k))) ^ (n + 1)).ofConv
         = ((WithConv.toConv φ.toLinearMap) ^ (n + 1)).ofConv
    rw [pow_succ' (WithConv.toConv (LinearMap.id (R := k) (M := Hab k))) n,
        LinearMap.algHom_comp_convMul_distrib, WithConv.ofConv_toConv, LinearMap.comp_id,
        show φ.toLinearMap ∘ₗ
            ((WithConv.toConv (LinearMap.id (R := k) (M := Hab k))) ^ n).ofConv
          = ((WithConv.toConv φ.toLinearMap) ^ n).ofConv from ih,
        WithConv.toConv_ofConv, pow_succ' (WithConv.toConv φ.toLinearMap) n]

omit [Algebra ℚ k] in
/-- **The Adams composition law `Ψᵖ ∘ Ψq = Ψ^{pq}`** on the commutative `H_ab`. The
    Adams (Hopf-power) operators form a commuting family of algebra endomorphisms realising the
    multiplicative monoid `(ℕ, ·)`; this is the structural reason the Eulerian idempotents are
    orthogonal. -/
theorem adamsAb_comp (p q : ℕ) :
    adamsAb k p ∘ₗ adamsAb k q = adamsAb k (p * q) := by
  have h := algHom_comp_adamsAb k (adamsAbHom k p) q
  rw [adamsAbHom_toLinearMap] at h
  rw [h, show (WithConv.toConv (adamsAb k p))
        = (WithConv.toConv (LinearMap.id (R := k) (M := Hab k))) ^ p from
        WithConv.toConv_ofConv _, ← pow_mul]
  rfl

/-! ### Toward `e⁽¹⁾∘e⁽¹⁾ = e⁽¹⁾` on the commutative `H_ab`: the finite-difference engine

    The route avoids the full Eulerian decomposition / Vandermonde inversion. The point:
    if `v` is an Adams eigenvector with `Ψⁱ(v) = i·v` for all `i`, then expanding
    `J^{⋆j} = (id − u∘ε)^{⋆j}` into Adams operators and applying to `v` collapses
    each `J^{⋆j}(v)` to a scalar multiple of `v` by the finite-difference identity below.
    Hence `e⁽¹⁾` is the identity on its own image. -/

/-- **Finite-difference engine**: the `j`-th finite difference of the identity sequence `i ↦ i`,
    `∑ᵢ (-1)^{j-i} C(j,i)·i = δ_{j,1}`. This collapses the convolution-log of an
    Adams eigenvector to its weight-1 component, which is the combinatorial heart of the
    Eulerian idempotency on `H_ab`. -/
theorem alternating_choose_weighted (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1), ((-1 : ℤ) ^ (j - i) * (j.choose i) * i)
      = if j = 1 then 1 else 0 := by
  rcases j with _ | n
  · simp
  · rw [Finset.sum_range_succ']
    have hinner : ∀ i ∈ Finset.range (n + 1),
        ((-1 : ℤ) ^ (n + 1 - (i + 1)) * ((n + 1).choose (i + 1)) * ((i + 1 : ℕ) : ℤ))
          = (n + 1 : ℤ) * ((-1 : ℤ) ^ (n - i) * (n.choose i)) := by
      intro i _
      have hc : (((n + 1).choose (i + 1) : ℤ)) * ((i + 1 : ℕ) : ℤ)
          = (n + 1 : ℤ) * (n.choose i) := by
        exact_mod_cast (Nat.add_one_mul_choose_eq n i).symm
      rw [show n + 1 - (i + 1) = n - i from by omega, mul_assoc, hc]
      ring
    rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
    have hsum : ∑ i ∈ Finset.range (n + 1), ((-1 : ℤ) ^ (n - i) * (n.choose i))
        = (0 : ℤ) ^ n := by
      have hap := add_pow (1 : ℤ) (-1) n
      simp_all
    simp only [Nat.cast_zero, mul_zero, add_zero, Nat.sub_zero, hsum]
    rcases n with _ | m
    · simp
    · simp [pow_succ]

/-! ### Binomial expansion of `J_ab^{⋆j}` into Adams operators on the commutative `H_ab`
    Toward `e⁽¹⁾∘e⁽¹⁾ = e⁽¹⁾`: expand the convolution-log's `J^{⋆j}` into the Adams
    basis so that, on an Adams eigenvector, `alternating_choose_weighted` collapses it. -/

-- On the commutative `H_ab`, the convolution power
-- `J_ab^{⋆j} = (id − u∘ε)^{⋆j}` expands into Adams operators:
-- `(J_ab^j)(x) = Σ_{i=0}^{j} (-1)^{j-i} C(j,i) · Ψⁱ(x)`. Pure ring
-- algebra in the commutative convolution ring (`convCommRing`); no nilpotency needed
-- (`Commute.add_pow` on `id + (-1)`, then `ofConv` linearity per term via the `key` scalar bridge).
omit [Algebra ℚ k] in
theorem JcAb_pow_ofConv_eq_adams_sum (j : ℕ) (x : Hab k) :
    ((WithConv.toConv (LinearMap.id (R := k) (M := Hab k)) - 1) ^ j).ofConv x
      = ∑ i ∈ Finset.range (j + 1),
          ((-1 : k) ^ (j - i) * (j.choose i : k)) • adamsAb k i x := by
  have hcomm : Commute (WithConv.toConv (LinearMap.id (R := k) (M := Hab k)))
      (-1 : WithConv (Hab k →ₗ[k] Hab k)) :=
    Commute.neg_one_right (WithConv.toConv (LinearMap.id (R := k) (M := Hab k)))
  have key : ∀ (e c : ℕ),
      (-1 : WithConv (Hab k →ₗ[k] Hab k)) ^ e * (c : WithConv (Hab k →ₗ[k] Hab k))
        = ((-1 : k) ^ e * (c : k)) • (1 : WithConv (Hab k →ₗ[k] Hab k)) := by
    intro e c
    have hc : ((c : k) • (1 : WithConv (Hab k →ₗ[k] Hab k)))
        = (c : WithConv (Hab k →ₗ[k] Hab k)) := by
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one]
    have hpow : (-1 : WithConv (Hab k →ₗ[k] Hab k)) ^ e
        = (-1 : k) ^ e • (1 : WithConv (Hab k →ₗ[k] Hab k)) := by
      rw [← neg_one_smul k (1 : WithConv (Hab k →ₗ[k] Hab k)), smul_pow, one_pow]
    rw [hpow, smul_mul_assoc, one_mul, mul_smul, hc]
  rw [sub_eq_add_neg, hcomm.add_pow, WithConv.ofConv_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, key (j - i) (j.choose i), mul_smul_comm, mul_one,
      WithConv.ofConv_smul, LinearMap.smul_apply]
  rfl

/-! ### `J^{⋆j}` naturality through `π` and per-degree nilpotency on `H_ab` -/

-- The same binomial expansion on the planar `H` (the convolution ring is
-- non-commutative, but `id` and `1` commute, so `Commute.add_pow` still applies).
-- Used to transport `J^{⋆j}` through `π`.
omit [Algebra ℚ k] in
theorem Jc_pow_ofConv_eq_adams_sum (j : ℕ) (z : H k) :
    ((Jc k) ^ j).ofConv z
      = ∑ i ∈ Finset.range (j + 1),
          ((-1 : k) ^ (j - i) * (j.choose i : k)) • adams k i z := by
  have hcomm : Commute (WithConv.toConv (LinearMap.id (R := k) (M := H k)))
      (-1 : WithConv (H k →ₗ[k] H k)) :=
    Commute.neg_one_right (WithConv.toConv (LinearMap.id (R := k) (M := H k)))
  have key : ∀ (e c : ℕ),
      (-1 : WithConv (H k →ₗ[k] H k)) ^ e * (c : WithConv (H k →ₗ[k] H k))
        = ((-1 : k) ^ e * (c : k)) • (1 : WithConv (H k →ₗ[k] H k)) := by
    intro e c
    have hc : ((c : k) • (1 : WithConv (H k →ₗ[k] H k)))
        = (c : WithConv (H k →ₗ[k] H k)) := by
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one]
    have hpow : (-1 : WithConv (H k →ₗ[k] H k)) ^ e
        = (-1 : k) ^ e • (1 : WithConv (H k →ₗ[k] H k)) := by
      rw [← neg_one_smul k (1 : WithConv (H k →ₗ[k] H k)), smul_pow, one_pow]
    rw [hpow, smul_mul_assoc, one_mul, mul_smul, hc]
  rw [Jc, sub_eq_add_neg, hcomm.add_pow, WithConv.ofConv_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, key (j - i) (j.choose i), mul_smul_comm, mul_one,
      WithConv.ofConv_smul, LinearMap.smul_apply]
  rfl

-- **`J^{⋆j}` naturality through `π`.** Both binomial expansions plus Adams naturality.
omit [Algebra ℚ k] in
theorem Jc_pow_ofConv_natural (j : ℕ) (z : H k) :
    π k (((Jc k) ^ j).ofConv z)
      = ((WithConv.toConv (LinearMap.id (R := k) (M := Hab k)) - 1) ^ j).ofConv (π k z) := by
  rw [Jc_pow_ofConv_eq_adams_sum, map_sum, JcAb_pow_ofConv_eq_adams_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hnat : π k (adams k i z) = adamsAb k i (π k z) := by
    have h := LinearMap.congr_fun (adamsAb_natural k i) z
    simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] using h.symm
  rw [map_smul, hnat]

-- **Per-degree nilpotency on `H_ab`.** `J_ab^{⋆n}` kills `π`-images of forests with `< n` nodes
-- (transport of the planar `Jc_pow_ofConv_sf_eq_zero` through `π`). Makes the log series
-- finite per degree.
omit [Algebra ℚ k] in
theorem JcAb_pow_ofConv_sf_eq_zero (n : ℕ) (f : Forest) (h : sizeF f < n) :
    ((WithConv.toConv (LinearMap.id (R := k) (M := Hab k)) - 1) ^ n).ofConv
      (π k (sf k f)) = 0 := by
  rw [← Jc_pow_ofConv_natural, Jc_pow_ofConv_sf_eq_zero k n f h, map_zero]

/-! ### The ring-hom step: post-composition by `Ψᵖ` (`adamsAb p`, an
algebra hom) is a ⋆-ring hom, sending `J_ab ↦ Yᵖ − 1` (`Y = toConv id_ab`). This is
`Ψᵖ ∘ e = log(Yᵖ)`. -/

-- General: an algebra hom `φ` post-composed with a convolution power `g^{⋆j}` is the `j`-th
-- convolution power of `φ ∘ g`:
-- `φ ∘ (g^j).ofConv = ((toConv(φ ∘ g.ofConv))^j).ofConv`. Mirrors
-- `algHom_comp_adamsAb` (the case `g = toConv id`); pure `algHom_comp_convMul_distrib` induction.
omit [Algebra ℚ k] in
theorem algHom_comp_convPow (φ : Hab k →ₐ[k] Hab k)
    (g : WithConv (Hab k →ₗ[k] Hab k)) (j : ℕ) :
    φ.toLinearMap ∘ₗ (g ^ j).ofConv
      = ((WithConv.toConv (φ.toLinearMap ∘ₗ g.ofConv)) ^ j).ofConv := by
  induction j with
  | zero =>
    rw [pow_zero, pow_zero]
    apply LinearMap.ext; simp_all
  | succ n ih =>
    rw [pow_succ' g n, LinearMap.algHom_comp_convMul_distrib,
        show WithConv.toConv (φ.toLinearMap ∘ₗ (g ^ n).ofConv)
            = (WithConv.toConv (φ.toLinearMap ∘ₗ g.ofConv)) ^ n from by
          rw [ih, WithConv.toConv_ofConv],
        ← pow_succ']

-- **Φ_p on `J_ab`**: `Ψᵖ ∘ (J_ab^{⋆j}) = (Yᵖ − 1)^{⋆j}`. Post-composition
-- sends `J_ab ↦ Yᵖ − 1`.
omit [Algebra ℚ k] in
theorem adamsAb_comp_JcAb_pow (p j : ℕ) (y : Hab k) :
    adamsAb k p (((WithConv.toConv (LinearMap.id (R := k) (M := Hab k)) - 1) ^ j).ofConv y)
      = (((WithConv.toConv (LinearMap.id (R := k) (M := Hab k))) ^ p - 1) ^ j).ofConv y := by
  have hPhi : WithConv.toConv ((adamsAbHom k p).toLinearMap
        ∘ₗ (WithConv.toConv (LinearMap.id (R := k) (M := Hab k)) - 1).ofConv)
      = (WithConv.toConv (LinearMap.id (R := k) (M := Hab k))) ^ p - 1 := by
    rw [WithConv.ofConv_sub, WithConv.ofConv_toConv, LinearMap.comp_sub, WithConv.toConv_sub]
    congr 1
    · rw [LinearMap.comp_id, adamsAbHom_toLinearMap, adamsAb, WithConv.toConv_ofConv]
    · have hu : (adamsAbHom k p).toLinearMap ∘ₗ (1 : WithConv (Hab k →ₗ[k] Hab k)).ofConv
          = (1 : WithConv (Hab k →ₗ[k] Hab k)).ofConv := by
        apply LinearMap.ext; simp_all
      rw [hu, WithConv.toConv_ofConv]
  have hgen := LinearMap.congr_fun
    (algHom_comp_convPow k (adamsAbHom k p)
      (WithConv.toConv (LinearMap.id (R := k) (M := Hab k)) - 1) j) y
  rw [LinearMap.comp_apply, hPhi, adamsAbHom_toLinearMap] at hgen
  exact hgen

/-! ### Evaluation: bridge the power-series coefficient identity (`coeff_logTrunc_pow`)
    to the convolution sums via `eval₂ (X ↦ J_ab)`, then kill high powers with nilpotency. -/

/-- `J_ab = id − u∘ε` on `H_ab`, as a convolution-ring element. -/
noncomputable def JcAb : WithConv (Hab k →ₗ[k] Hab k) :=
  WithConv.toConv (LinearMap.id (R := k) (M := Hab k)) - 1

/-- `r ↦ r • 1` as a ring hom `k →+* WithConv(H_ab)` (image central; `convCommRing`). -/
noncomputable def smulOne : k →+* WithConv (Hab k →ₗ[k] Hab k) where
  toFun r := r • (1 : WithConv (Hab k →ₗ[k] Hab k))
  map_one' := one_smul _ _
  map_mul' r s := by rw [smul_mul_assoc, one_mul, smul_smul]
  map_zero' := zero_smul _ _
  map_add' r s := add_smul _ _ _

/-- The Eulerian coefficient `(-1)^{j+1}/j` equals the `j`-th coefficient of the formal `log`. -/
theorem eulerCoef_eq_coeff_log (j : ℕ) :
    eulerCoef k j = PowerSeries.coeff j (PowerSeries.log k) := by
  rw [eulerCoef, PowerSeries.coeff_log]
  simp_all

omit [Algebra ℚ k] in
/-- `eval₂ smulOne J_ab P`, applied through `.ofConv` to `w`, is the explicit sum
    `Σₘ (P.coeff m) • (J_ab^m).ofConv w`. -/
theorem eval₂_ofConv (P : Polynomial k) (w : Hab k) :
    (Polynomial.eval₂ (smulOne k) (JcAb k) P).ofConv w
      = ∑ m ∈ Finset.range (P.natDegree + 1), (P.coeff m) • ((JcAb k ^ m).ofConv w) := by
  rw [Polynomial.eval₂_eq_sum_range, WithConv.ofConv_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro m _
  change (((P.coeff m) • (1 : WithConv (Hab k →ₗ[k] Hab k))) * (JcAb k) ^ m).ofConv w = _
  rw [smul_mul_assoc, one_mul, WithConv.ofConv_smul, LinearMap.smul_apply]

/-- The truncated `∑ⱼ cⱼ X^j` polynomial has `coeff m = cₘ` for `m ≤ N`. -/
theorem PR_coeff (N m : ℕ) (hm : m ≤ N) :
    (∑ j ∈ Finset.range (N + 1),
        Polynomial.C (PowerSeries.coeff j (PowerSeries.log k)) * Polynomial.X ^ j).coeff m
      = PowerSeries.coeff m (PowerSeries.log k) := by
  simp_all

/-- **(★) — the eigen-transport identity** on a per-degree-nilpotent `w`: applying `Ψᵖ`
    to the truncated convolution-log scales it by `p`. Proven by evaluating the polynomial
    `coeff_logTrunc_pow` identity at `J_ab` (`eval₂`), killing the surplus `J_ab^{>N}` by
    nilpotency. -/
theorem star_identity (p N : ℕ) (w : Hab k)
    (hnil : ∀ m, N < m → ((JcAb k) ^ m).ofConv w = 0) :
    (∑ j ∈ Finset.range (N + 1), PowerSeries.coeff j (PowerSeries.log k) •
        ((WithConv.toConv (LinearMap.id (R := k) (M := Hab k)) ^ p - 1) ^ j).ofConv w)
      = (p : k) • ∑ j ∈ Finset.range (N + 1),
          PowerSeries.coeff j (PowerSeries.log k) • ((JcAb k ^ j).ofConv w) := by
  set Y := WithConv.toConv (LinearMap.id (R := k) (M := Hab k)) with hY
  set PL : Polynomial k :=
    ∑ j ∈ Finset.range (N + 1),
      (Polynomial.C (PowerSeries.coeff j (PowerSeries.log k)) *
        ((1 + Polynomial.X) ^ p - 1) ^ j) with hPL
  set PR : Polynomial k :=
    ∑ j ∈ Finset.range (N + 1),
      Polynomial.C (PowerSeries.coeff j (PowerSeries.log k)) * Polynomial.X ^ j with hPR
  set D : Polynomial k := PL - Polynomial.C (p : k) * PR with hD
  have hcomm : ∀ a : k, Commute ((smulOne k) a) (JcAb k) := by
    intro a
    change Commute (a • (1 : WithConv (Hab k →ₗ[k] Hab k))) (JcAb k)
    exact (Commute.one_left (JcAb k)).smul_left a
  have hYeq : (1 : WithConv (Hab k →ₗ[k] Hab k)) + JcAb k = Y := by
    rw [JcAb, hY]
    simp
  have hevPL : (Polynomial.eval₂ (smulOne k) (JcAb k) PL).ofConv w
      = ∑ j ∈ Finset.range (N + 1),
          PowerSeries.coeff j (PowerSeries.log k) • ((Y ^ p - 1) ^ j).ofConv w := by
    have hpoly : Polynomial.eval₂ (smulOne k) (JcAb k) PL
        = ∑ j ∈ Finset.range (N + 1),
            PowerSeries.coeff j (PowerSeries.log k) • (Y ^ p - 1) ^ j := by
      rw [← Polynomial.eval₂RingHom'_apply (smulOne k) (JcAb k) hcomm PL]
      rw [hPL, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_pow, map_sub, map_pow, map_add, map_one,
          Polynomial.eval₂RingHom'_apply (smulOne k) (JcAb k) hcomm
            (Polynomial.C (PowerSeries.coeff j (PowerSeries.log k))),
          Polynomial.eval₂_C,
          Polynomial.eval₂RingHom'_apply (smulOne k) (JcAb k) hcomm Polynomial.X,
          Polynomial.eval₂_X, hYeq]
      change ((PowerSeries.coeff j (PowerSeries.log k)) • (1 : WithConv (Hab k →ₗ[k] Hab k)))
            * (Y ^ p - 1) ^ j = _
      rw [smul_mul_assoc, one_mul]
    rw [hpoly, WithConv.ofConv_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [WithConv.ofConv_smul, LinearMap.smul_apply]
  have hevPR : (Polynomial.eval₂ (smulOne k) (JcAb k) PR).ofConv w
      = ∑ j ∈ Finset.range (N + 1),
          PowerSeries.coeff j (PowerSeries.log k) • ((JcAb k ^ j).ofConv w) := by
    have hpoly : Polynomial.eval₂ (smulOne k) (JcAb k) PR
        = ∑ j ∈ Finset.range (N + 1),
            PowerSeries.coeff j (PowerSeries.log k) • (JcAb k) ^ j := by
      rw [← Polynomial.eval₂RingHom'_apply (smulOne k) (JcAb k) hcomm PR]
      rw [hPR, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_pow,
          Polynomial.eval₂RingHom'_apply (smulOne k) (JcAb k) hcomm
            (Polynomial.C (PowerSeries.coeff j (PowerSeries.log k))),
          Polynomial.eval₂_C,
          Polynomial.eval₂RingHom'_apply (smulOne k) (JcAb k) hcomm Polynomial.X,
          Polynomial.eval₂_X]
      change ((PowerSeries.coeff j (PowerSeries.log k)) • (1 : WithConv (Hab k →ₗ[k] Hab k)))
            * (JcAb k) ^ j = _
      rw [smul_mul_assoc, one_mul]
    rw [hpoly, WithConv.ofConv_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [WithConv.ofConv_smul, LinearMap.smul_apply]
  have hDcoeff : ∀ m, m ≤ N → D.coeff m = 0 := by
    intro m hm
    have : HasUniqueDiv k := .of_module_rat k
    rw [hD, Polynomial.coeff_sub, Polynomial.coeff_C_mul, hPL,
        PowerSeries.polyPL_coeff (A := k) p N m hm, hPR, PR_coeff (k := k) N m hm,
        nsmul_eq_mul]
    ring
  have hD0 : (Polynomial.eval₂ (smulOne k) (JcAb k) D).ofConv w = 0 := by
    rw [eval₂_ofConv]
    apply Finset.sum_eq_zero
    intro m _
    rcases le_or_gt m N with h | h
    · rw [hDcoeff m h, zero_smul]
    · rw [hnil m h, smul_zero]
  have hevD : (Polynomial.eval₂ (smulOne k) (JcAb k) D).ofConv w
      = (Polynomial.eval₂ (smulOne k) (JcAb k) PL).ofConv w
        - (p : k) • (Polynomial.eval₂ (smulOne k) (JcAb k) PR).ofConv w := by
    rw [hD, Polynomial.eval₂_sub,
        Polynomial.eval₂_mul_noncomm (smulOne k) (JcAb k) (fun n => hcomm (PR.coeff n)),
        Polynomial.eval₂_C, WithConv.ofConv_sub, LinearMap.sub_apply]
    congr 1
    change (((p : k) • (1 : WithConv (Hab k →ₗ[k] Hab k))) *
            Polynomial.eval₂ (smulOne k) (JcAb k) PR).ofConv w = _
    rw [smul_mul_assoc, one_mul, WithConv.ofConv_smul, LinearMap.smul_apply]
  rw [hevD, hevPL, hevPR, sub_eq_zero] at hD0
  exact hD0

/-- `π(e⁽¹⁾ y)` as a truncated convolution-log sum on `H_ab`, for any degree bound
    `M ≥ deg(y)`. -/
theorem pi_eulerian1_eq (y : H k) (M : ℕ) (hMy : ∀ a ∈ y.coeff.support, sizeF a ≤ M) :
    π k (eulerian1 k y)
      = ∑ j ∈ Finset.range (M + 1),
          PowerSeries.coeff j (PowerSeries.log k) • ((JcAb k ^ j).ofConv (π k y)) := by
  rw [eulerian1_eq_logTrunc k y M hMy, logTrunc_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, eulerCoef_eq_coeff_log, Jc_pow_ofConv_natural, JcAb]

/-- **Adams eigen-relation on a basis forest**:
    `Ψᵖ(π(e⁽¹⁾(sf f))) = p · π(e⁽¹⁾(sf f))`. -/
theorem adamsAb_eigen_basis (p : ℕ) (f : Forest) :
    adamsAb k p (π k (eulerian1 k (sf k f))) = (p : k) • π k (eulerian1 k (sf k f)) := by
  have hMy : ∀ a ∈ (sf k f).coeff.support, sizeF a ≤ sizeF f := by
    intro a ha
    have ha' : a = FreeMonoid.ofList f :=
      Finset.mem_singleton.mp (Finsupp.support_single_subset ha)
    rw [ha']
    rfl
  rw [pi_eulerian1_eq k (sf k f) (sizeF f) hMy, map_sum]
  rw [Finset.sum_congr rfl (fun j _ => by rw [map_smul, JcAb, adamsAb_comp_JcAb_pow] :
    ∀ j ∈ Finset.range (sizeF f + 1),
      adamsAb k p
        (PowerSeries.coeff j (PowerSeries.log k) • ((JcAb k ^ j).ofConv (π k (sf k f))))
        = PowerSeries.coeff j (PowerSeries.log k) •
            ((WithConv.toConv (LinearMap.id (R := k) (M := Hab k)) ^ p - 1) ^ j).ofConv
              (π k (sf k f)))]
  exact star_identity k p (sizeF f) (π k (sf k f))
    (fun m hm => JcAb_pow_ofConv_sf_eq_zero k m f hm)

/-- **Adams eigen-relation** (general): `Ψᵖ(π(e⁽¹⁾ x)) = p · π(e⁽¹⁾ x)` for all
    `x`. -/
theorem adamsAb_eigen (p : ℕ) (x : H k) :
    adamsAb k p (π k (eulerian1 k x)) = (p : k) • π k (eulerian1 k x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero =>
    change adamsAb k p (π k (eulerian1 k (0 : H k)))
      = (p : k) • π k (eulerian1 k (0 : H k))
    simp
  | add f g hf hg =>
    have he : eulerian1 k ((f : H k) + (g : H k))
        = eulerian1 k (f : H k) + eulerian1 k (g : H k) :=
      map_add (eulerian1 k) (f : H k) (g : H k)
    simp_all
  | single a b =>
    have hsa : (MonoidAlgebra.single a b : H k) = b • sf k (FreeMonoid.toList a) := by
      rw [sf, FreeMonoid.ofList_toList]
      exact single_smul_one (k := k) (f := a) (b := b)
    rw [hsa]
    simp only [map_smul]
    rw [adamsAb_eigen_basis k p (FreeMonoid.toList a), smul_comm]

/-! ### The finite-difference collapse: on an Adams eigenvector the convolution-log
truncation collapses to the eigenvector itself (only the weight-1 term survives). -/

/-- **Collapse.** On an Adams eigenvector `v` (`Ψⁱ(v) = i·v`), the truncated
    convolution-log is the identity: `Σⱼ≤M cⱼ · J_ab^{⋆j}(v) = v` (`M ≥ 1`). The
    `J_ab^{⋆j}` expands into Adams ops, the eigen-relation turns each into a scalar, and
    `alternating_choose_weighted` kills all but `j = 1`. -/
theorem brickC (v : Hab k) (M : ℕ) (hM : 1 ≤ M)
    (heig : ∀ i, adamsAb k i v = (i : k) • v) :
    (∑ j ∈ Finset.range (M + 1), PowerSeries.coeff j (PowerSeries.log k) •
      ((JcAb k ^ j).ofConv v))
      = v := by
  have hcollapse : ∀ j, (JcAb k ^ j).ofConv v = (if j = 1 then (1 : k) else 0) • v := by
    intro j
    rw [JcAb, JcAb_pow_ofConv_eq_adams_sum,
        Finset.sum_congr rfl (fun i _ => by rw [heig i, smul_smul] :
          ∀ i ∈ Finset.range (j + 1),
            ((-1 : k) ^ (j - i) * (j.choose i : k)) • adamsAb k i v
              = ((-1 : k) ^ (j - i) * (j.choose i : k) * (i : k)) • v),
        ← Finset.sum_smul]
    congr 1
    rw [show (∑ i ∈ Finset.range (j + 1),
        (-1 : k) ^ (j - i) * (j.choose i : k) * (i : k))
        = ((if j = 1 then (1 : ℤ) else 0) : k) from by
          have h := congrArg (fun z : ℤ => (z : k)) (alternating_choose_weighted j)
          simpa using h]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun j _ => by rw [hcollapse j] :
      ∀ j ∈ Finset.range (M + 1),
        PowerSeries.coeff j (PowerSeries.log k) • ((JcAb k ^ j).ofConv v)
          = PowerSeries.coeff j (PowerSeries.log k) • ((if j = 1 then (1 : k) else 0) • v)),
      Finset.sum_eq_single 1]
  · rw [ite_eq_left rfl, one_smul, PowerSeries.coeff_one_log, one_smul]
  · intro b _ hb; rw [ite_eq_right hb, zero_smul, smul_zero]
  · intro h1; exact absurd (Finset.mem_range.2 (by omega : 1 < M + 1)) h1

/-- **`e⁽¹⁾ ∘ e⁽¹⁾ = e⁽¹⁾` on the commutative `H_ab`** (the Eulerian idempotency, via
    `π`). The first Eulerian idempotent is genuinely idempotent on the abelianized
    Connes–Kreimer / Butcher Hopf algebra. Combines `pi_eulerian1_eq`, the Adams
    eigen-relation `adamsAb_eigen`, and the collapse `brickC`. -/
theorem eulerian1_idem_ab (x : H k) :
    π k (eulerian1 k (eulerian1 k x)) = π k (eulerian1 k x) := by
  set M := (eulerian1 k x).coeff.support.sup sizeF + 1 with hMdef
  have hMy : ∀ a ∈ (eulerian1 k x).coeff.support, sizeF a ≤ M := fun a ha =>
    le_trans (Finset.le_sup ha) (by rw [hMdef]; omega)
  rw [pi_eulerian1_eq k (eulerian1 k x) M hMy]
  exact brickC k (π k (eulerian1 k x)) M (by rw [hMdef]; omega) (fun i => adamsAb_eigen k i x)

end ConnesKreimer
