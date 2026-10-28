/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.LinearAlgebra.Matrix.StdBasis
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Module
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.Order.WellFounded
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.Tactic.Zify
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
# Schur's bound for commuting matrices

Over any field, a subspace of `n × n` matrices whose elements commute pairwise has dimension at most
`⌊n²/4⌋ + 1`, and for `n ≥ 1` the bound is attained by the identity together with the matrices
`[[0, X], [0, 0]]` with `X` of size `⌈n/2⌉ × ⌊n/2⌋` (Theorem of the Day; Schur 1905, Jacobson 1944,
short proof by Mirzakhani 1998).

## Main results

* `SchurCommuting.finrank_le`: commuting subspaces of n × n matrices have dimension ≤ ⌊n²/4⌋ + 1
* `SchurCommuting.exists_finrank_eq`: the bound is attained for n ≥ 1
* `SchurCommuting.finrank_le_and_attained`: both together (Theorem of the Day)

## References

* R. Whitty, Theorem of the Day, «Schur's Commuting Matrices Bound» (Algebra/SchurMatrix).
* I. Schur (1905); N. Jacobson, Schur's theorems on commutative matrices, Bull. AMS 50 (1944); M. Mirzakhani, A simple proof of a theorem of Schur, Amer. Math. Monthly 105 (1998) 260–262.
-/

@[expose] public section

universe u

namespace SchurCommuting

section Parts

variable {K : Type*} [Field K] {V : Type u} [AddCommGroup V] [Module K V]

/-- `W` is stable under every element of `S`. -/
def Inv (S : Submodule K (Module.End K V)) (W : Submodule K V) : Prop :=
  ∀ s ∈ S, ∀ w ∈ W, s w ∈ W

lemma inv_range {S : Submodule K (Module.End K V)} (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    {a : Module.End K V} (ha : a ∈ S) : Inv S (LinearMap.range a) := by
  rintro s hs _ ⟨v, rfl⟩
  refine ⟨s v, ?_⟩
  have := congrArg (fun f => f v) (hS a ha s hs)
  simpa using this

lemma inv_ker {S : Submodule K (Module.End K V)} (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    {a : Module.End K V} (ha : a ∈ S) : Inv S (LinearMap.ker a) := by
  intro s hs w hw
  have hw' : a w = 0 := hw
  have := congrArg (fun f => f w) (hS a ha s hs)
  simp only [Module.End.mul_apply] at this
  show a (s w) = 0
  rw [this, hw', map_zero]

lemma dual_lemma [FiniteDimensional K V] (P : Submodule K (Module.Dual K V)) (Q : Submodule K V)
    (h : ∀ f ∈ P, ∀ q ∈ Q, f q = 0) :
    Module.finrank K P + Module.finrank K Q ≤ Module.finrank K V := by
  have h1 : P ≤ Q.dualAnnihilator := fun f hf => by
    rw [Submodule.mem_dualAnnihilator]; exact fun q hq => h f hf q hq
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq Q
  have h3 := Submodule.finrank_mono h1
  omega

lemma key [FiniteDimensional K V] (S : Submodule K (Module.End K V))
    (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (H U : Submodule K V)
    (hUH : U ≤ H) (hUne : U ≠ ⊥) (hHtop : H ≠ ⊤)
    (hHmax : ∀ W : Submodule K V, Inv S W → W ≠ ⊥ → W ≠ ⊤ → H ≤ W → W = H)
    (hUmin : ∀ W : Submodule K V, Inv S W → W ≠ ⊥ → W ≤ U → W = U)
    (X Y : Submodule K S) (hX : ∀ x ∈ X, ∀ v, (x : Module.End K V) v ∈ U)
    (hY : ∀ y ∈ Y, ∀ h ∈ H, (y : Module.End K V) h = 0) :
    Module.finrank K X + Module.finrank K Y ≤ Module.finrank K V := by
  obtain ⟨u₀, hu₀, hu₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
  obtain ⟨lam, hlam⟩ := Module.Projective.exists_dual_eq_one K hu₀ne
  obtain ⟨v₀, hv₀⟩ : ∃ v, v ∉ H := by
    by_contra hcon
    push Not at hcon
    exact hHtop (eq_top_iff.2 fun v _ => hcon v)
  let α : X →ₗ[K] Module.Dual K V :=
    { toFun := fun x => lam ∘ₗ ((x : S) : Module.End K V)
      map_add' := fun x y => by ext v; simp
      map_smul' := fun c x => by ext v; simp }
  let β : Y →ₗ[K] V :=
    { toFun := fun y => ((y : S) : Module.End K V) v₀
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }
  have hα : Function.Injective α := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    have hne : (x.1.1 : Module.End K V) ≠ 0 := by
      intro h; apply hx0; apply Subtype.ext; apply Subtype.ext; exact h
    have hinv := inv_range hS x.1.2
    have hr : LinearMap.range x.1.1 = U :=
      hUmin _ hinv (by simpa [LinearMap.range_eq_bot] using hne)
        (by rintro _ ⟨w, rfl⟩; exact hX x.1 x.2 w)
    have hmem : u₀ ∈ LinearMap.range x.1.1 := hr ▸ hu₀
    obtain ⟨w, hw⟩ := hmem
    have h2 : α x w = 0 := by rw [hx]; rfl
    have h3 : α x w = 1 := by
      show lam (x.1.1 w) = 1
      rw [hw]; exact hlam
    rw [h2] at h3
    exact zero_ne_one h3
  have hβ : Function.Injective β := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    have hy' : y.1.1 v₀ = 0 := hy
    have hinv := inv_ker hS y.1.2
    have hHle : H ≤ LinearMap.ker y.1.1 := fun h hh => hY y.1 y.2 h hh
    by_cases htop : LinearMap.ker y.1.1 = ⊤
    · apply Subtype.ext; apply Subtype.ext; exact LinearMap.ker_eq_top.1 htop
    · exfalso
      have hne : LinearMap.ker y.1.1 ≠ ⊥ := by
        intro h0
        apply hUne
        rw [eq_bot_iff]
        intro u hu
        have := hHle (hUH hu)
        rwa [h0] at this
      have heq := hHmax _ hinv hne htop hHle
      apply hv₀
      rw [← heq]
      exact LinearMap.mem_ker.2 hy'
  have hP := dual_lemma (LinearMap.range α) (LinearMap.range β) (by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    show lam (x.1.1 (y.1.1 v₀)) = 0
    have hc := congrArg (fun f => f v₀) (hS x.1.1 x.1.2 y.1.1 y.1.2)
    simp only [Module.End.mul_apply] at hc
    rw [hc]
    have := hY y.1 y.2 _ (hUH (hX x.1 x.2 v₀))
    rw [this, map_zero])
  rw [LinearMap.finrank_range_of_inj hα, LinearMap.finrank_range_of_inj hβ] at hP
  exact hP

/-- Action on the quotient `V ⧸ U`. -/
noncomputable def quotHom (S : Submodule K (Module.End K V)) (U : Submodule K V) (hU : Inv S U) :
    S →ₗ[K] Module.End K (V ⧸ U) where
  toFun s := U.mapQ U s.1 (fun u hu => hU s.1 s.2 u hu)
  map_add' a b := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective U x
    simp [Submodule.mapQ_apply]
  map_smul' c a := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective U x
    simp [Submodule.mapQ_apply]

lemma quotHom_apply (S : Submodule K (Module.End K V)) (U : Submodule K V) (hU : Inv S U)
    (s : S) (v : V) : quotHom S U hU s (Submodule.Quotient.mk v) = Submodule.Quotient.mk (s.1 v) :=
  rfl

/-- Restriction to an invariant subspace. -/
noncomputable def resHom (S : Submodule K (Module.End K V)) (H : Submodule K V) (hH : Inv S H) :
    S →ₗ[K] Module.End K H where
  toFun s := LinearMap.restrict s.1 (fun h hh => hH s.1 s.2 h hh)
  map_add' a b := by
    refine LinearMap.ext fun x => ?_
    apply Subtype.ext
    simp
  map_smul' c a := by
    refine LinearMap.ext fun x => ?_
    apply Subtype.ext
    simp

lemma resHom_apply (S : Submodule K (Module.End K V)) (H : Submodule K V) (hH : Inv S H)
    (s : S) (h : H) : ((resHom S H hH s h : H) : V) = s.1 h := rfl

lemma bmono {a b : ℕ} (h : a ≤ b) : a * a / 4 + 1 ≤ b * b / 4 + 1 := by
  have := Nat.div_le_div_right (c := 4) (Nat.mul_le_mul h h)
  omega

lemma self_le (n : ℕ) : n ≤ n * n / 4 + 1 := by
  rcases n with _ | k
  · omega
  · have : k * 4 ≤ (k + 1) * (k + 1) := by
      zify
      nlinarith [sq_nonneg ((k : ℤ) - 1)]
    omega

lemma arith (n d : ℕ) (hn : 1 ≤ n) (h : 2 * d ≤ n + 2 * (((n - 1) * (n - 1)) / 4 + 1)) :
    d ≤ n * n / 4 + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · have e1 : 2 * j * (2 * j) / 4 = j * j := by
      have : 2 * j * (2 * j) = 4 * (j * j) := by ring
      omega
    have e2 : (2 * j + 1) * (2 * j + 1) / 4 = j * j + j := by
      have : (2 * j + 1) * (2 * j + 1) = 4 * (j * j + j) + 1 := by ring
      omega
    rw [e1] at h
    rw [e2]
    omega
  · have e1 : (2 * j + 1) * (2 * j + 1) / 4 = j * j + j := by
      have : (2 * j + 1) * (2 * j + 1) = 4 * (j * j + j) + 1 := by ring
      omega
    have e2 : (2 * j + 1 + 1) * (2 * j + 1 + 1) / 4 = j * j + 2 * j + 1 := by
      have : (2 * j + 1 + 1) * (2 * j + 1 + 1) = 4 * (j * j + 2 * j + 1) := by ring
      omega
    rw [e1] at h
    rw [e2]
    omega

end Parts

theorem finrank_le_aux (K : Type*) [Field K] (n : ℕ) :
    ∀ (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
      Module.finrank K V = n → ∀ S : Submodule K (Module.End K V),
      (∀ a ∈ S, ∀ b ∈ S, a * b = b * a) → Module.finrank K S ≤ n * n / 4 + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hn S hS
  have : IsArtinian K V := inferInstance
  by_cases hB : ∃ W : Submodule K V, Inv S W ∧ W ≠ ⊥ ∧ W ≠ ⊤
  · obtain ⟨W, hW, hW0, hWt⟩ := hB
    obtain ⟨H, ⟨hHinv, hH0, hHt⟩, hHmax⟩ := (wellFounded_gt (α := Submodule K V)).has_min
      {W : Submodule K V | Inv S W ∧ W ≠ ⊥ ∧ W ≠ ⊤} ⟨W, hW, hW0, hWt⟩
    have hHmax' : ∀ W : Submodule K V, Inv S W → W ≠ ⊥ → W ≠ ⊤ → H ≤ W → W = H := by
      intro W' h1 h2 h3 h4
      by_contra hne
      exact hHmax W' ⟨h1, h2, h3⟩ (lt_of_le_of_ne h4 (Ne.symm hne))
    obtain ⟨U, ⟨hUinv, hU0, hUH⟩, hUmin⟩ := (wellFounded_lt (α := Submodule K V)).has_min
      {W : Submodule K V | Inv S W ∧ W ≠ ⊥ ∧ W ≤ H} ⟨H, hHinv, hH0, le_rfl⟩
    have hUmin' : ∀ W : Submodule K V, Inv S W → W ≠ ⊥ → W ≤ U → W = U := by
      intro W' h1 h2 h3
      exact eq_of_le_of_not_lt h3 (hUmin W' ⟨h1, h2, h3.trans hUH⟩)
    have hu : 1 ≤ Module.finrank K U := Submodule.one_le_finrank_iff.2 hU0
    have hh : Module.finrank K H < n := hn ▸ Submodule.finrank_lt hHt
    have hq := Submodule.finrank_quotient_add_finrank U
    have hcomm_q : ∀ a ∈ LinearMap.range (quotHom S U hUinv), ∀ b ∈ LinearMap.range (quotHom S U hUinv),
        a * b = b * a := by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      refine LinearMap.ext fun x => ?_
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective U x
      have := congrArg (fun f => f x) (hS a.1 a.2 b.1 b.2)
      simp only [Module.End.mul_apply] at this
      simp only [Module.End.mul_apply, quotHom_apply, this]
    have hcomm_r : ∀ a ∈ LinearMap.range (resHom S H hHinv), ∀ b ∈ LinearMap.range (resHom S H hHinv),
        a * b = b * a := by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      refine LinearMap.ext fun x => ?_
      apply Subtype.ext
      have := congrArg (fun f => f (x : V)) (hS a.1 a.2 b.1 b.2)
      simp only [Module.End.mul_apply] at this
      simp only [Module.End.mul_apply, resHom_apply, this]
    have iq := ih (Module.finrank K (V ⧸ U)) (by omega) (V ⧸ U) rfl _ hcomm_q
    have ir := ih (Module.finrank K H) hh H rfl _ hcomm_r
    have rq := LinearMap.finrank_range_add_finrank_ker (quotHom S U hUinv)
    have rr := LinearMap.finrank_range_add_finrank_ker (resHom S H hHinv)
    have hk := key S hS H U hUH hU0 hHt hHmax' hUmin'
      (LinearMap.ker (quotHom S U hUinv)) (LinearMap.ker (resHom S H hHinv))
      (by
        intro x hx v
        have h0 : quotHom S U hUinv x = 0 := hx
        have := LinearMap.congr_fun h0 (Submodule.Quotient.mk v)
        rw [quotHom_apply] at this
        exact (Submodule.Quotient.mk_eq_zero U).1 this)
      (by
        intro y hy h hh
        have h0 : resHom S H hHinv y = 0 := hy
        have := congrArg Subtype.val (LinearMap.congr_fun h0 ⟨h, hh⟩)
        simpa [resHom_apply] using this)
    have b1 := bmono (a := Module.finrank K (V ⧸ U)) (b := n - 1) (by omega)
    have b2 := bmono (a := Module.finrank K H) (b := n - 1) (by omega)
    apply arith n _ (by omega)
    omega
  · push Not at hB
    rcases subsingleton_or_nontrivial V with hV | hV
    · have : Subsingleton S :=
        ⟨fun a b => Subtype.ext (LinearMap.ext fun v => Subsingleton.elim _ _)⟩
      rw [Module.finrank_zero_of_subsingleton]
      omega
    · obtain ⟨v, hv⟩ := exists_ne (0 : V)
      let ev : S →ₗ[K] V :=
        { toFun := fun s => s.1 v
          map_add' := by simp
          map_smul' := by simp }
      have hinj : Function.Injective ev := by
        rw [injective_iff_map_eq_zero]
        intro s hs
        have hs' : s.1 v = 0 := hs
        have hinv := inv_ker hS s.2
        have hne : LinearMap.ker s.1 ≠ ⊥ := by
          intro h0
          have : v ∈ LinearMap.ker s.1 := hs'
          rw [h0] at this
          exact hv (by simpa using this)
        have htop : LinearMap.ker s.1 = ⊤ := hB _ hinv hne
        apply Subtype.ext
        exact LinearMap.ker_eq_top.1 htop
      have h1 := LinearMap.finrank_le_finrank_of_injective hinj
      have h2 := self_le n
      omega

end SchurCommuting

namespace SchurCommuting

variable (K : Type*) [Field K] (n : ℕ)

/-- Index set of the upper-right block: rows `< a`, columns `≥ a`. -/
abbrev Idx (a : ℕ) : Type := {x : Fin n × Fin n // x.1.val < a ∧ a ≤ x.2.val}

/-- Matrices supported on the upper-right block. -/
noncomputable def blk (a : ℕ) : Submodule K (Matrix (Fin n) (Fin n) K) :=
  Submodule.span K (Set.range fun x : Idx n a => Matrix.single x.1.1 x.1.2 (1 : K))

variable {K n}

lemma blk_mul_blk {a : ℕ} {b₁ b₂ : Matrix (Fin n) (Fin n) K} (h₁ : b₁ ∈ blk K n a)
    (h₂ : b₂ ∈ blk K n a) : b₁ * b₂ = 0 := by
  induction h₁ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    induction h₂ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨q, rfl⟩ := hy
      apply Matrix.single_mul_single_of_ne
      intro h
      have h1 := p.2.2
      have h2 := q.2.1
      have h3 : p.1.2.val = q.1.1.val := by rw [h]
      omega
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add, hy, hz, add_zero]
    | smul c y _ hy => rw [mul_smul_comm, hy, smul_zero]
  | zero => simp
  | add y z _ _ hy hz => rw [add_mul, hy, hz, add_zero]
  | smul c y _ hy => rw [smul_mul_assoc, hy, smul_zero]

lemma finrank_blk (a : ℕ) : Module.finrank K (blk K n a) = min n a * (n - a) := by
  have hli : LinearIndependent K (fun x : Idx n a => Matrix.single x.1.1 x.1.2 (1 : K)) := by
    have := (Matrix.stdBasis K (Fin n) (Fin n)).linearIndependent.comp
      (fun x : Idx n a => x.1) Subtype.val_injective
    convert this using 1
    ext x : 1
    exact (Matrix.stdBasis_eq_single K x.1.1 x.1.2).symm
  rw [blk, finrank_span_eq_card hli, Fintype.card_subtype, ← Finset.univ_product_univ,
    Finset.filter_product (fun i : Fin n => i.val < a) (fun j : Fin n => a ≤ j.val),
    Finset.card_product]
  congr 1
  · exact Fin.card_filter_val_lt
  · have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun j : Fin n => j.val < a)
    have h2 : (Finset.univ.filter (fun j : Fin n => j.val < a)).card = min n a :=
      Fin.card_filter_val_lt
    simp only [not_lt, Finset.card_univ, Fintype.card_fin] at h1
    omega

lemma entry_zero_of_mem_blk {a : ℕ} (ha : 0 < a) (hn : 0 < n) {b : Matrix (Fin n) (Fin n) K}
    (hb : b ∈ blk K n a) : b ⟨0, hn⟩ ⟨0, hn⟩ = 0 := by
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    have h2 := p.2.2
    have : p.1.2 ≠ ⟨0, hn⟩ := by
      intro h
      rw [h] at h2
      simp at h2
      omega
    simp only [Matrix.single_apply]
    split_ifs with h
    · exact absurd h.2 this
    · rfl
  | zero => simp
  | add y z _ _ hy hz => simp [hy, hz]
  | smul c y _ hy => simp [hy]

/-- The extremal commutative subspace: scalars plus the upper-right block. -/
noncomputable def extremal (K : Type*) [Field K] (n a : ℕ) : Submodule K (Matrix (Fin n) (Fin n) K) :=
  Submodule.span K {(1 : Matrix (Fin n) (Fin n) K)} ⊔ blk K n a

lemma extremal_comm (a : ℕ) {A B : Matrix (Fin n) (Fin n) K} (hA : A ∈ extremal K n a)
    (hB : B ∈ extremal K n a) : A * B = B * A := by
  obtain ⟨s, hs, b₁, hb₁, rfl⟩ := Submodule.mem_sup.mp hA
  obtain ⟨t, ht, b₂, hb₂, rfl⟩ := Submodule.mem_sup.mp hB
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp ht
  have h12 := blk_mul_blk hb₁ hb₂
  have h21 := blk_mul_blk hb₂ hb₁
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, h12, h21,
    add_zero]
  module

lemma finrank_extremal (hn : 0 < n) {a : ℕ} (ha : 0 < a) :
    Module.finrank K (extremal K n a) = min n a * (n - a) + 1 := by
  have hdis : Disjoint (Submodule.span K {(1 : Matrix (Fin n) (Fin n) K)}) (blk K n a) := by
    rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have := entry_zero_of_mem_blk ha hn hx'
    simp at this
    simp [this]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span K {(1 : Matrix (Fin n) (Fin n) K)})
    (blk K n a)
  rw [hdis.eq_bot, finrank_bot, add_zero] at h
  have h1 : (1 : Matrix (Fin n) (Fin n) K) ≠ 0 := by
    intro h0
    have := congrFun (congrFun h0 ⟨0, hn⟩) ⟨0, hn⟩
    simp at this
  rw [extremal, h, finrank_blk, finrank_span_singleton h1]
  ring

/-- The bound `n ^ 2 / 4 + 1` is attained for `n ≥ 1`. -/
theorem exists_finrank_eq (hn : 1 ≤ n) :
    ∃ S : Submodule K (Matrix (Fin n) (Fin n) K), (∀ A ∈ S, ∀ B ∈ S, A * B = B * A) ∧
      Module.finrank K S = n ^ 2 / 4 + 1 := by
  refine ⟨extremal K n ((n + 1) / 2), fun A hA B hB => extremal_comm _ hA hB, ?_⟩
  rw [finrank_extremal (by omega) (by omega)]
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
  · subst hm
    have e1 : (2 * m + 1) / 2 = m := by omega
    have e2 : (2 * m) ^ 2 / 4 = m * m := by
      rw [show (2 * m) ^ 2 = 4 * (m * m) by ring]; exact Nat.mul_div_cancel_left _ (by norm_num)
    rw [e1, e2, min_eq_right (by omega)]
    congr 2
    omega
  · subst hm
    have e1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    have e2 : (2 * m + 1) ^ 2 / 4 = (m + 1) * m := by
      rw [show (2 * m + 1) ^ 2 = 4 * ((m + 1) * m) + 1 by ring]; omega
    rw [e1, e2, min_eq_right (by omega)]
    congr 2
    omega

/-- Schur's bound: a commutative subspace of `M_n(K)` has dimension `≤ n ^ 2 / 4 + 1`. -/
theorem finrank_le (S : Submodule K (Matrix (Fin n) (Fin n) K))
    (hS : ∀ A ∈ S, ∀ B ∈ S, A * B = B * A) : Module.finrank K S ≤ n ^ 2 / 4 + 1 := by
  let e := Matrix.toLinAlgEquiv' (R := K) (n := Fin n)
  let S' : Submodule K (Module.End K (Fin n → K)) := S.map e.toLinearMap
  have h1 : Module.finrank K S' = Module.finrank K S := LinearEquiv.finrank_map_eq e.toLinearEquiv S
  have hc : ∀ a ∈ S', ∀ b ∈ S', a * b = b * a := by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
    show e A * e B = e B * e A
    rw [← map_mul, ← map_mul, hS A hA B hB]
  have := finrank_le_aux K n (Fin n → K) (Module.finrank_fin_fun K) S' hc
  rw [h1] at this
  simpa [sq] using this

theorem finrank_le_and_attained (K : Type*) [Field K] (n : ℕ) :
    (∀ S : Submodule K (Matrix (Fin n) (Fin n) K), (∀ A ∈ S, ∀ B ∈ S, A * B = B * A) →
      Module.finrank K S ≤ n ^ 2 / 4 + 1) ∧
    (1 ≤ n → ∃ S : Submodule K (Matrix (Fin n) (Fin n) K), (∀ A ∈ S, ∀ B ∈ S, A * B = B * A) ∧
      Module.finrank K S = n ^ 2 / 4 + 1) :=
  ⟨fun S hS => finrank_le S hS, fun hn => exists_finrank_eq hn⟩

end SchurCommuting
