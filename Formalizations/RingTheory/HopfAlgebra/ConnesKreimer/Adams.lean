/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.RingTheory.HopfAlgebra.ConnesKreimer.Basic
public import Mathlib.Algebra.Algebra.Rat

/-!
# Adams operators and the first Eulerian idempotent on the planar algebra

In the convolution ring `WithConv (H k →ₗ[k] H k)` the identity is a unit with inverse the
antipode; its convolution powers are the Adams operators `Ψₙ = id^{⋆n}`. The augmentation
`J = id − u∘ε` is locally nilpotent, so over a `ℚ`-algebra the convolution logarithm
`e⁽¹⁾ = log_⋆ id` is a finite sum on each forest.

## Main results

* `ConnesKreimer.adams`, `ConnesKreimer.toConv_adams_add`, `ConnesKreimer.adamsUnit`,
  `ConnesKreimer.adamsUnit_inv_val`: Adams operators, `Ψₘ ⋆ Ψₙ = Ψₘ₊ₙ`, and `Ψ₋₁ = S`.
* `ConnesKreimer.Jc_pow_ofConv_sf_eq_zero`: `J^{⋆n}` vanishes on forests with fewer than `n` nodes.
* `ConnesKreimer.adams_primitive`: `Ψₙ x = n • x` for a primitive `x`.
* `ConnesKreimer.eulerian1`, `ConnesKreimer.eulerian1_eq_logTrunc`: the first Eulerian idempotent
  and its truncation formula.
* `ConnesKreimer.eulerian1_primitive`: `e⁽¹⁾` fixes every primitive element.
* `ConnesKreimer.eulerian1_idem_dot`: `e⁽¹⁾ (e⁽¹⁾ •) = e⁽¹⁾ •` on the one-node tree.

## References

* M. Aguiar, A. Lauve, *The characteristic polynomial of the Adams operators on graded connected
  Hopf algebras*, Algebra Number Theory 9 (2015) 547–583.
* J.-L. Loday, *Opérations sur l'homologie cyclique des algèbres commutatives*, Invent. Math. 96
  (1989) 205–230.
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

/-! ### Adams operators `Ψₙ = id^{⋆n}` and the antipode as `Ψ₋₁`.

    The convolution ring `WithConv (H k →ₗ[k] H k)` (Mathlib `LinearMap.convRing`) turns the
    identity into a ring element whose convolution powers are the Adams (Hopf-power) operators.
    `Ψ₀ = u∘ε` (the convolution unit), `Ψ₁ = id`, the semigroup law `Ψₘ ⋆ Ψₙ = Ψₘ₊ₙ`, and the
    identity is a convolution unit whose inverse is the antipode — i.e. `Ψ₋₁ = S`
    (Aguiar–Lauve theory; the Eulerian idempotent `e⁽¹⁾ = log_⋆ id` is the next step, needing
    connected-graded nilpotence). -/

/-- The `n`-th Adams operator `Ψₙ = id^{⋆n}`: the `n`-th convolution power of the identity in the
    convolution ring `WithConv (H k →ₗ[k] H k)`. -/
noncomputable def adams (n : ℕ) : H k →ₗ[k] H k :=
  ((WithConv.toConv (LinearMap.id (R := k) (M := H k))) ^ n).ofConv

theorem toConv_adams (n : ℕ) :
    WithConv.toConv (adams k n)
      = (WithConv.toConv (LinearMap.id (R := k) (M := H k))) ^ n :=
  WithConv.toConv_ofConv _

/-- `Ψ₀ = u∘ε` is the convolution unit. -/
@[simp] theorem toConv_adams_zero : WithConv.toConv (adams k 0) = 1 := by
  rw [toConv_adams, pow_zero]

/-- `Ψ₁ = id`. -/
@[simp] theorem adams_one : adams k 1 = LinearMap.id (R := k) (M := H k) := by
  rw [adams, pow_one, WithConv.ofConv_toConv]

/-- The convolution-power semigroup law `Ψₘ ⋆ Ψₙ = Ψₘ₊ₙ`. -/
theorem toConv_adams_add (m n : ℕ) :
    WithConv.toConv (adams k (m + n))
      = WithConv.toConv (adams k m) * WithConv.toConv (adams k n) := by
  rw [toConv_adams, toConv_adams, toConv_adams, pow_add]

/-- `S ⋆ id = u∘ε`: the antipode is a left convolution inverse of `Ψ₁ = id`. -/
theorem antipode_convMul_id :
    WithConv.toConv (antipode k) * WithConv.toConv (LinearMap.id (R := k) (M := H k)) = 1 := by
  apply WithConv.ext
  rw [LinearMap.convMul_def]
  exact leftAntipode_eq k

/-- `id ⋆ S = u∘ε`: the antipode is also a right convolution inverse of `Ψ₁ = id`. -/
theorem id_convMul_antipode :
    WithConv.toConv (LinearMap.id (R := k) (M := H k)) * WithConv.toConv (antipode k) = 1 := by
  rw [antipode_eq_antipode']
  apply WithConv.ext
  rw [LinearMap.convMul_def]
  exact rightAntipode'_eq k

/-- `Ψ₁ = id` is a convolution UNIT, with the antipode as its (two-sided) inverse. This is the
    precise sense in which `Ψ₋₁ = S`. -/
noncomputable def adamsUnit : (WithConv (H k →ₗ[k] H k))ˣ where
  val := WithConv.toConv (LinearMap.id (R := k) (M := H k))
  inv := WithConv.toConv (antipode k)
  val_inv := id_convMul_antipode k
  inv_val := antipode_convMul_id k

/-- `Ψ₋₁ = S`: the inverse of the Adams unit `Ψ₁` is the antipode. -/
theorem adamsUnit_inv_val : (adamsUnit k)⁻¹.val = WithConv.toConv (antipode k) := rfl

/-! ### Local nilpotency of `J = id − u∘ε` (the connected-graded engine for `log_⋆`).

    `J` kills the empty forest and is the identity on nonempty ones. Its convolution powers
    `J^{⋆k}` vanish on every basis forest of fewer than `k` nodes (`Jc_pow_ofConv_sf_eq_zero`):
    each of the `k` convolution factors must absorb at least one node, so `k` nodes are needed.
    Hence the series `log_⋆(id) = Σ_{k≥1} ((-1)^{k+1}/k)·J^{⋆k}` is finite in each degree — the
    connected-graded local nilpotency on which the Aguiar–Lauve Eulerian spectrum rests. -/

/-- `Δ` on a basis forest, packaged for `sf`. -/
theorem Δ_sf (f : Forest) : Δ k (sf k f) = Δ₀ k f := by
  change Finsupp.linearCombination k (Δ₀ k) (Finsupp.single f (1 : k)) = Δ₀ k f
  rw [Finsupp.linearCombination_single, one_smul]

/-- `ε` on a basis forest: the counit of `sf f` is `εmon f`. -/
theorem ε_sf (p : Forest) : ε k (sf k p) = εmon k p := by
  have h := ε_single k p 1
  rw [one_mul] at h
  exact h

/-- `μ ∘ (F ⊗ G)` on a pure cut-tensor `e2 (p,r)` is `F(p)·G(r)`. -/
theorem mul_map_e2 (F G : H k →ₗ[k] H k) (pr : Forest × Forest) :
    LinearMap.mul' k (H k) (TensorProduct.map F G (e2 k pr))
      = F (sf k pr.1) * G (sf k pr.2) := by
  obtain ⟨p, r⟩ := pr
  rw [e2, TensorProduct.map_tmul, LinearMap.mul'_apply]
  rfl

/-- `comul` on a basis forest equals the combinatorial `Δ₀`. -/
theorem comul_sf (f : Forest) :
    (Coalgebra.comul (R := k) (A := H k)) (sf k f) = Δ₀ k f := Δ_sf k f

/-- **Convolution-on-basis engine.** `(F ⋆ G)` on a basis forest is the sum over cuts:
    `(F ⋆ G)(f) = Σ_{(p,r) ∈ coprodForest f} F(p)·G(r)`. -/
theorem conv_ofConv_sf (F G : H k →ₗ[k] H k) (f : Forest) :
    (WithConv.toConv F * WithConv.toConv G).ofConv (sf k f)
      = ((coprodForest f).map (fun pr => F (sf k pr.1) * G (sf k pr.2))).sum := by
  rw [LinearMap.convMul_def]
  change LinearMap.mul' k (H k) (TensorProduct.map F G (Coalgebra.comul (R := k) (sf k f))) = _
  rw [comul_sf, Δ₀,
      show LinearMap.mul' k (H k) (TensorProduct.map F G (((coprodForest f).map (e2 k)).sum))
        = (LinearMap.mul' k (H k) ∘ₗ TensorProduct.map F G) (((coprodForest f).map (e2 k)).sum)
        from rfl,
      linmap_list_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pr _
  rw [LinearMap.comp_apply]
  exact mul_map_e2 k F G pr

/-- The augmentation projector `J = id − u∘ε`, as an element of the convolution ring. -/
noncomputable def Jc : WithConv (H k →ₗ[k] H k) := WithConv.toConv LinearMap.id - 1

/-- The convolution unit `1 = u∘ε` on a basis forest: `ε(f)·1`. -/
theorem convOne_ofConv_sf (p : Forest) :
    (1 : WithConv (H k →ₗ[k] H k)).ofConv (sf k p) = εmon k p • (1 : H k) := by
  rw [LinearMap.convOne_def]
  change
    (Algebra.linearMap k (H k) ∘ₗ Coalgebra.counit (R := k)) (sf k p)
      = εmon k p • (1 : H k)
  rw [LinearMap.comp_apply]
  change Algebra.linearMap k (H k) (ε k (sf k p)) = εmon k p • (1 : H k)
  rw [ε_sf, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]

/-- `J = id − u∘ε` on a basis forest: kills the empty forest, identity otherwise. -/
theorem Jc_ofConv_sf (p : Forest) :
    (Jc k).ofConv (sf k p) = sf k p - εmon k p • (1 : H k) := by
  rw [Jc, WithConv.ofConv_sub, LinearMap.sub_apply, WithConv.ofConv_toConv,
      LinearMap.id_apply, convOne_ofConv_sf]

/-- **Local nilpotency.** `J^{⋆n} = (id − u∘ε)^{⋆n}` vanishes on every basis forest with fewer
    than `n` nodes. Proof: induction on `n` via the convolution engine and degree conservation;
    in a nonzero cut the left leg carries ≥1 node, so the right leg has `< n−1` nodes and the
    induction hypothesis kills it, while an empty left leg is killed by `J` directly. -/
theorem Jc_pow_ofConv_sf_eq_zero :
    ∀ (n : ℕ) (f : Forest), sizeF f < n → ((Jc k) ^ n).ofConv (sf k f) = 0 := by
  intro n
  induction n with
  | zero => intro f hf; exact absurd hf (Nat.not_lt_zero _)
  | succ m ih =>
    intro f hf
    have hrec : ((Jc k) ^ (m + 1)).ofConv (sf k f)
        = ((coprodForest f).map (fun pr =>
            (Jc k).ofConv (sf k pr.1) * ((Jc k) ^ m).ofConv (sf k pr.2))).sum := by
      have hsplit : (Jc k) ^ (m + 1)
          = WithConv.toConv ((Jc k).ofConv) * WithConv.toConv (((Jc k) ^ m).ofConv) := by
        rw [WithConv.toConv_ofConv, WithConv.toConv_ofConv]
        exact pow_succ' _ _
      rw [hsplit, conv_ofConv_sf]
    rw [hrec]
    apply List.sum_eq_zero
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨pr, hpr, rfl⟩ := hx
    obtain ⟨p, r⟩ := pr
    have hcons := size_consForest f (p, r) hpr
    by_cases hp : p = []
    · subst hp
      rw [Jc_ofConv_sf, sf_nil, εmon_nil, one_smul, sub_self, zero_mul]
    · have hpos : 0 < sizeF p := sizeF_pos hp
      have hr : sizeF r < m := by simp only at hcons ⊢; omega
      rw [ih r hr, mul_zero]

/-! ### The Adams eigenvalue on primitives: `Ψₙ(x) = n·x` for primitive `x`.

    The first piece of the Aguiar–Lauve spectrum, valid on ANY connected graded bialgebra (no
    commutativity needed): the primitives are the eigenspace of every Adams operator `Ψₙ` with
    eigenvalue `n`. Proof is at the element level (not the basis): on a primitive `x`, the recursion
    `Ψₙ₊₁ = id ⋆ Ψₙ` and `Δx = x⊗1 + 1⊗x` give `Ψₙ₊₁(x) = x + Ψₙ(x)`, and `Ψₙ` fixes the unit. -/

/-- A primitive element: `Δx = x⊗1 + 1⊗x`. -/
def IsPrimitive (x : H k) : Prop := Δ k x = x ⊗ₜ[k] (1 : H k) + (1 : H k) ⊗ₜ[k] x

/-- Convolution at the element level: `(F ⋆ G)(x) = μ((F⊗G)(Δx))`. -/
theorem conv_apply (F G : H k →ₗ[k] H k) (x : H k) :
    (WithConv.toConv F * WithConv.toConv G).ofConv x
      = LinearMap.mul' k (H k) (TensorProduct.map F G (Δ k x)) := by
  rw [LinearMap.convMul_def]; rfl

/-- `Δ(1) = 1⊗1` (the unit is grouplike), in pure-tensor form. -/
theorem Δ_one_tmul : Δ k (1 : H k) = (1 : H k) ⊗ₜ[k] (1 : H k) := by
  rw [Δ_one, Algebra.TensorProduct.one_def]

/-- `Ψₙ₊₁ = id ⋆ Ψₙ` evaluated: `Ψₙ₊₁(x) = μ((id⊗Ψₙ)(Δx))`. -/
theorem adams_succ_apply (n : ℕ) (x : H k) :
    adams k (n + 1) x
      = LinearMap.mul' k (H k) (TensorProduct.map LinearMap.id (adams k n) (Δ k x)) := by
  change (((WithConv.toConv (LinearMap.id (R := k) (M := H k))) ^ (n + 1)).ofConv) x = _
  rw [pow_succ',
      show (WithConv.toConv (LinearMap.id (R := k) (M := H k))) ^ n
        = WithConv.toConv (adams k n) from rfl]
  exact conv_apply k LinearMap.id (adams k n) x

/-- Every Adams operator fixes the unit: `Ψₙ(1) = 1`. -/
theorem adams_unit (n : ℕ) : adams k n (1 : H k) = 1 := by
  induction n with
  | zero =>
    change ((WithConv.toConv (LinearMap.id (R := k) (M := H k))) ^ 0).ofConv (1 : H k) = 1
    rw [pow_zero]
    have h := convOne_ofConv_sf k []
    simp_all
  | succ m ih =>
    rw [adams_succ_apply, Δ_one_tmul, TensorProduct.map_tmul, LinearMap.id_apply, ih,
        LinearMap.mul'_apply, one_mul]

/-- **Adams eigenvalue on primitives**: for primitive `x`, `Ψₙ₊₁(x) = (n+1)·x`. The
    primitives are the eigenspace of `Ψₙ` with eigenvalue `n`, and `S = Ψ₋₁` acts as `−1`,
    recovering `S(x) = −x`. -/
theorem adams_primitive (n : ℕ) {x : H k} (hx : IsPrimitive k x) :
    adams k (n + 1) x = (n + 1) • x := by
  induction n with
  | zero => simp [adams_one]
  | succ m ih =>
    rw [adams_succ_apply, hx, map_add, TensorProduct.map_tmul, TensorProduct.map_tmul,
        LinearMap.id_apply, LinearMap.id_apply, adams_unit, map_add, LinearMap.mul'_apply,
        LinearMap.mul'_apply, mul_one, one_mul, ih]
    conv_rhs => rw [succ_nsmul]
    exact add_comm _ _

/-! ### The first Eulerian idempotent `e⁽¹⁾ = log_⋆(id)` as a linear map.

    Over a `ℚ`-algebra the series `log_⋆(id) = Σ_{k≥1} ((-1)^{k+1}/k)·J^{⋆k}` is, by the local
    nilpotency above, finite on each basis forest (only `k ≤ |f|` contribute). We define `e⁽¹⁾`
    by that finite per-degree sum, mirroring how `Δ` and the antipode are defined on the basis.
    `e⁽¹⁾` kills the unit and fixes primitives (eigenvalue `1`) — the connected-graded projector
    onto primitives that begins the Aguiar–Lauve spectral decomposition. -/

variable [Algebra ℚ k]

/-- Coefficient `(-1)^{j+1}/j` of the convolution-log series, pushed into `k`. `j = 0 ↦ 0`. -/
noncomputable def eulerCoef (j : ℕ) : k := algebraMap ℚ k ((-1) ^ (j + 1) / (j : ℚ))

@[simp] theorem eulerCoef_zero : eulerCoef k 0 = 0 := by
  simp [eulerCoef]

@[simp] theorem eulerCoef_one : eulerCoef k 1 = 1 := by
  simp [eulerCoef]

/-- `e⁽¹⁾` on a basis forest: the finite log series `Σ_{j=0}^{|f|} ((-1)^{j+1}/j)·J^{⋆j}(f)`
    (the `j=0` term is `0`; terms with `j > |f|` are absent — and would vanish anyway). -/
noncomputable def eulerian1F (f : Forest) : H k :=
  ((List.range (sizeF f + 1)).map
    (fun j => eulerCoef k j • ((Jc k ^ j).ofConv (sf k f)))).sum

/-- The first Eulerian idempotent `e⁽¹⁾ : H → H`, linear extension of `eulerian1F`. -/
noncomputable def eulerian1 : H k →ₗ[k] H k :=
  Finsupp.linearCombination k (eulerian1F k) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

theorem eulerian1_sf (f : Forest) : eulerian1 k (sf k f) = eulerian1F k f := by
  change Finsupp.linearCombination k (eulerian1F k) (Finsupp.single f (1 : k)) = eulerian1F k f
  rw [Finsupp.linearCombination_single, one_smul]

/-- `e⁽¹⁾` kills the unit: there are no positive-degree terms on the empty forest. -/
@[simp] theorem eulerian1_one : eulerian1 k (1 : H k) = 0 := by
  rw [show (1 : H k) = sf k [] from (sf_nil k).symm, eulerian1_sf, eulerian1F,
      show sizeF ([] : Forest) = 0 from rfl]
  simp [List.range_succ, List.range_zero, eulerCoef_zero]

/-- `e⁽¹⁾` fixes the generating primitive `•` (eigenvalue `1`): only the `j=1` term survives,
    with coefficient `1`, and `J(•) = •`. -/
theorem eulerian1_dot : eulerian1 k (sf k [RTree.node []]) = sf k [RTree.node []] := by
  rw [eulerian1_sf, eulerian1F, show sizeF [RTree.node []] = 1 from rfl]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.map_append, List.sum_append, List.sum_cons, List.sum_nil, add_zero, zero_add,
    eulerCoef_zero, eulerCoef_one, zero_smul, one_smul]
  rw [pow_one, Jc_ofConv_sf, εmon_cons, zero_smul, sub_zero]

/-- **Idempotency on the primitive `•`**: `e⁽¹⁾(e⁽¹⁾ •) = e⁽¹⁾ •`. Immediate from `eulerian1_dot`
    (since `e⁽¹⁾` fixes `•`); likewise `e⁽¹⁾` is idempotent on anything it fixes or kills.

    NOTE (honest scope): the GENERAL projector identity `e⁽¹⁾∘e⁽¹⁾ = e⁽¹⁾` is **false** on this
    *planar* (Foissy) Hopf algebra — it is neither commutative nor cocommutative, and the Eulerian
    idempotents are orthogonal idempotents only in the (co)commutative case (Patras, Loday).
    On the cherry, `e⁽¹⁾∘e⁽¹⁾` and `e⁽¹⁾` differ in the `•·ℓ₂` vs `ℓ₂·•` terms (computed by
    evaluation, not proved here) — exactly the planar non-commutativity. Genuine idempotency (the
    Hodge/Eulerian decomposition) lives on the commutative quotient
    (`Formalizations.RingTheory.HopfAlgebra.ConnesKreimer.Eulerian`), not here. -/
theorem eulerian1_idem_dot :
    eulerian1 k (eulerian1 k (sf k [RTree.node []])) = eulerian1 k (sf k [RTree.node []]) := by
  simp only [eulerian1_dot]

/-! ### `e⁽¹⁾` fixes every primitive (element-level primitive facts).
    For primitive `x`: `ε(x)=0`, `J(x)=x`, and `J^{⋆k}(x)=0` for `k ≥ 2` (each higher factor must
    absorb the unit, which `J` kills). These feed the operator identity below. -/

omit [Algebra ℚ k] in
/-- A primitive element has zero counit (forced by the counit axiom `(ε⊗id)∘Δ = 1⊗·`). -/
theorem IsPrimitive.counit_zero {x : H k} (hx : IsPrimitive k x) : ε k x = 0 := by
  have hc : LinearMap.rTensor (H k) (ε k) (Δ k x) = (1 : k) ⊗ₜ[k] x :=
    Coalgebra.rTensor_counit_comul (R := k) (A := H k) x
  rw [hx, map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
      show ε k (1 : H k) = 1 by rw [← sf_nil, ε_sf, εmon_nil]] at hc
  have ha : (ε k x) ⊗ₜ[k] (1 : H k) = 0 := by
    simp_all
  have h1 : ε k x • (1 : H k) = 0 := by
    have := congrArg (TensorProduct.lid k (H k)) ha; simpa using this
  have h2 := congrArg (ε k) h1
  rwa [map_smul, map_zero, show ε k (1 : H k) = 1 by rw [← sf_nil, ε_sf, εmon_nil],
       smul_eq_mul, mul_one] at h2

omit [Algebra ℚ k] in
/-- `J = id − u∘ε` at the element level: `J(x) = x − ε(x)·1`. -/
theorem Jc_ofConv_apply (x : H k) : (Jc k).ofConv x = x - ε k x • (1 : H k) := by
  rw [Jc, WithConv.ofConv_sub, LinearMap.sub_apply, WithConv.ofConv_toConv, LinearMap.id_apply]
  congr 1
  rw [LinearMap.convOne_def]
  change Algebra.linearMap k (H k) (ε k x) = ε k x • (1 : H k)
  rw [Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]

omit [Algebra ℚ k] in
/-- `J` kills the unit. -/
theorem Jc_ofConv_one : (Jc k).ofConv (1 : H k) = 0 := by
  rw [Jc_ofConv_apply,
    show ε k (1 : H k) = 1 by rw [← sf_nil, ε_sf, εmon_nil],
    one_smul, sub_self]

omit [Algebra ℚ k] in
/-- `J^{⋆(j+1)}` kills the unit (the first factor `J(1)=0`). -/
theorem Jc_pow_succ_ofConv_one (j : ℕ) : ((Jc k) ^ (j + 1)).ofConv (1 : H k) = 0 := by
  have hsplit : (Jc k) ^ (j + 1)
      = WithConv.toConv ((Jc k).ofConv) * WithConv.toConv (((Jc k) ^ j).ofConv) := by
    rw [WithConv.toConv_ofConv, WithConv.toConv_ofConv]; exact pow_succ' _ _
  rw [hsplit, conv_apply, Δ_one_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply,
      Jc_ofConv_one, zero_mul]

omit [Algebra ℚ k] in
/-- `J` fixes a primitive: `J(x) = x`. -/
theorem Jc_ofConv_primitive {x : H k} (hx : IsPrimitive k x) : (Jc k).ofConv x = x := by
  rw [Jc_ofConv_apply, hx.counit_zero, zero_smul, sub_zero]

omit [Algebra ℚ k] in
/-- `J^{⋆(k+2)}` kills a primitive: each of the two top factors absorbs the unit (`J(1)=0`). -/
theorem Jc_pow_ofConv_primitive {x : H k} (hx : IsPrimitive k x) (j : ℕ) :
    ((Jc k) ^ (j + 2)).ofConv x = 0 := by
  have hsplit : (Jc k) ^ (j + 2)
      = WithConv.toConv ((Jc k).ofConv) * WithConv.toConv (((Jc k) ^ (j + 1)).ofConv) := by
    rw [WithConv.toConv_ofConv, WithConv.toConv_ofConv]; exact pow_succ' _ _
  rw [hsplit, conv_apply, hx, map_add, TensorProduct.map_tmul, TensorProduct.map_tmul, map_add,
      LinearMap.mul'_apply, LinearMap.mul'_apply, Jc_pow_succ_ofConv_one, Jc_ofConv_one,
      mul_zero, zero_mul, add_zero]

/-! ### `e⁽¹⁾` fixes every primitive (the operator identity).
    `e⁽¹⁾` agrees on degree-`≤N` elements with the finite truncation `Σ_{j≤N} c_j J^{⋆j}` (extra
    terms vanish by nilpotency); on a primitive only the `j=1` term survives, giving `e⁽¹⁾(x)=x`. -/

/-- Bridge: a `List.range` map-sum equals the corresponding `Finset.range` sum. -/
theorem list_range_sum_eq {M : Type*} [AddCommMonoid M] (m : ℕ) (g : ℕ → M) :
    ((List.range m).map g).sum = ∑ j ∈ Finset.range m, g j := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- The degree-`N` truncation of `log_⋆(id)`, as a linear map. -/
noncomputable def logTrunc (N : ℕ) : H k →ₗ[k] H k :=
  ∑ j ∈ Finset.range (N + 1), eulerCoef k j • ((Jc k ^ j).ofConv)

theorem logTrunc_apply (N : ℕ) (y : H k) :
    logTrunc k N y = ∑ j ∈ Finset.range (N + 1), eulerCoef k j • ((Jc k ^ j).ofConv y) := by
  simp [logTrunc, LinearMap.sum_apply, LinearMap.smul_apply]

/-- On a basis forest of degree `≤ N`, `e⁽¹⁾` equals the degree-`N` truncation (nilpotency kills
    the surplus terms). -/
theorem eulerian1F_eq_logTrunc (f : Forest) (N : ℕ) (h : sizeF f ≤ N) :
    eulerian1F k f = logTrunc k N (sf k f) := by
  rw [eulerian1F, list_range_sum_eq, logTrunc_apply]
  refine Finset.sum_subset (fun j hj => ?_) (fun j _ hjnot => ?_)
  · rw [Finset.mem_range] at hj ⊢; omega
  · rw [Finset.mem_range, not_lt] at hjnot
    rw [Jc_pow_ofConv_sf_eq_zero k j f (by omega), smul_zero]

omit [Algebra ℚ k] in
/-- A linear endomorphism of `H` is the basis-sum of its values on the singletons (proved by
    `exact`, sidestepping the `MonoidAlgebra`/`Finsupp` syntactic wall in `rw`). -/
theorem lmap_eq_sum (g : H k →ₗ[k] H k) (y : H k) :
    g y = y.coeff.sum (fun a b => g (MonoidAlgebra.single a b)) := by
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single y]
  exact map_finsuppSum g y.coeff MonoidAlgebra.single

/-- `e⁽¹⁾` agrees with the truncation `logTrunc N` on any element supported in degrees `≤ N`. -/
theorem eulerian1_eq_logTrunc (x : H k) (N : ℕ)
    (hN : ∀ f ∈ x.coeff.support, sizeF f ≤ N) :
    eulerian1 k x = logTrunc k N x := by
  rw [lmap_eq_sum k (eulerian1 k) x, lmap_eq_sum k (logTrunc k N) x]
  refine Finsupp.sum_congr (fun a ha => ?_)
  have hsf : (MonoidAlgebra.single a (x.coeff a) : H k)
      = (x.coeff a) • sf k (FreeMonoid.toList a) := by
    rw [sf, FreeMonoid.ofList_toList]
    exact single_smul_one (k := k) (f := a) (b := x.coeff a)
  rw [hsf, map_smul, map_smul, eulerian1_sf,
      eulerian1F_eq_logTrunc k (FreeMonoid.toList a) N (hN a ha)]

/-- **`e⁽¹⁾` fixes every primitive**: `e⁽¹⁾(x) = x` for primitive `x`. Only the `j=1` term of the
    log series survives (`J(x)=x`; `j=0` has coefficient `0`; `j≥2` vanish), so `e⁽¹⁾(x)=x`. The
    primitives are exactly the eigenvalue-`1` eigenspace of `e⁽¹⁾`. -/
theorem eulerian1_primitive {x : H k} (hx : IsPrimitive k x) : eulerian1 k x = x := by
  set N := x.coeff.support.sup sizeF + 1 with hNdef
  have hbound : ∀ f ∈ x.coeff.support, sizeF f ≤ N := by
    intro f hf
    exact le_trans (Finset.le_sup (f := sizeF) hf) (by rw [hNdef]; exact Nat.le_succ _)
  rw [eulerian1_eq_logTrunc k x N hbound, logTrunc_apply]
  have key : ∑ j ∈ Finset.range (N + 1), eulerCoef k j • ((Jc k ^ j).ofConv x)
      = eulerCoef k 1 • ((Jc k ^ 1).ofConv x) := by
    refine Finset.sum_eq_single 1 (fun j _ hj1 => ?_) (fun h1 => ?_)
    · rcases j with _ | _ | j
      · rw [eulerCoef_zero, zero_smul]
      · exact absurd rfl hj1
      · rw [Jc_pow_ofConv_primitive k hx j, smul_zero]
    · rw [Finset.mem_range, not_lt] at h1; omega
  rw [key, eulerCoef_one, one_smul, pow_one, Jc_ofConv_primitive k hx]

end ConnesKreimer
