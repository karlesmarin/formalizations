/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.RingTheory.Polynomial.CoefficientRing.Operations
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Algebra.Ring.NonZeroDivisors

/-!
# `A_SU(n) = A_Sp(q−n−1)`, and the free quadratic extension `R ⊕ θR`

For `q` odd and `n < q` even, the coefficient rings of the segment polynomials satisfy
`A_SU(n) = A_Sp(q−n−1)`. The second part treats `B = R ⊕ θR` with `θ² = c`
(`QuadraticAlgebra R c 0`): its trace, its trace dual and its Kähler differentials.

## Main results

* `NotaPuente.A_F_eq_A_Gsp_of_odd`: `A_SU(n) = A_Sp(q−n−1)` for `q` odd, `n < q` even.
* `NotaPuente.trace_quadraticAlgebra`, `NotaPuente.trace_B`: `Tr(x + yω) = 2x + b y`.
* `NotaPuente.dual_of_mem`, `NotaPuente.dual_eq`: with `2` a unit and `c` a non-zero-divisor,
  `x ↦ Tr(x ·)` identifies `(2θ)⁻¹B` with `Hom_R(B, R)`, stated without localization
  (`2c · f z = Tr(θ y z)` for exactly one `y ∈ B`).
* `NotaPuente.kaehlerEquiv`: `Ω_{B/R} ≃ B ⧸ (2θ)`, for every `c`.

## References

* C. Marín, *Non-real orders of character values of `GL(n)`*, preprint (2026).
* C. Marín, *The ring of character values depends only on the segment: SU(n), Sp(2m) and GL(n) at
  a torsion element*, Zenodo (2026), doi:10.5281/zenodo.22847476.
-/

@[expose] public section

namespace NotaPuente

open Polynomial

section Segments

variable {K : Type*} [Field K] {t : K} {q : ℕ}

/-! ### Corollary 2.3 -/

/-- **Corollary 2.3**: for `q` odd and `n < q` even, `A_SU(n) = A_Sp(q-n-1)`.
`q - n` is odd, `q - n = 2m + 1` with `m = (q - n - 1)/2`; apply Prop. 2.2(b), then (a). -/
theorem A_F_eq_A_Gsp_of_odd (hq : 0 < q) (ht : IsPrimitiveRoot t (2 * q)) (hqo : Odd q)
    {n : ℕ} (hne : Even n) (hn : n < q) :
    A (F t n) = A (Gsp t ((q - n - 1) / 2)) := by
  have hm : q - n = 2 * ((q - n - 1) / 2) + 1 := by
    obtain ⟨k, rfl⟩ := hqo; obtain ⟨j, rfl⟩ := hne; omega
  rw [A_F_eq_A_F_sub hq ht hn.le,
    show F t (q - n) = F t (2 * ((q - n - 1) / 2) + 1) by rw [← hm], A_F_odd_eq_A_Gsp]

end Segments

/-! ### Lemma 5.7: the free quadratic extension `B = R ⊕ θR`, `θ² = c`

`B := QuadraticAlgebra R c 0` (Mathlib: `ω * ω = c • 1 + 0 • ω`), `θ := ω`.

Formulation without localization. In `B[1/c]` (2 a unit) one has `1/(2θ) = θ/(2c)`, so an element
of `(2θ)⁻¹B` is `x = y/(2θ) = θy/(2c)` with `y ∈ B` unique, and `Tr(x z) = Tr(θ y z)/(2c)`.
Hence "`x ↦ Tr(x·)` identifies `(2θ)⁻¹B` with `Hom_R(B,R)`" is equivalent to:
* `dual_of_mem`: for each `y ∈ B`, `Tr(θ y z)` is divisible by `2c`, uniformly and linearly in `z`
  (so `z ↦ Tr(xz)` is an `R`-valued functional: `(2θ)⁻¹B ⊆ dual`);
* `dual_eq`: each `f : B →ₗ[R] R` satisfies `2c · f z = Tr(θ y z)` for exactly one `y ∈ B`
  (`dual ⊆ (2θ)⁻¹B`, and the map is injective). Since `2c` is a non-zero-divisor, `2c·f z = Tr(θyz)`
  is equivalent to `f z = Tr(xz)` in `R[1/c]`.
The Kähler part (c) holds for every `c` (no hypothesis on 2 or `c`). -/

section Quadratic

open QuadraticAlgebra

variable {R : Type*} [CommRing R]

/-- Trace of a general quadratic algebra `R[ω]/(ω² - bω - a)`: `Tr(x + yω) = 2x + b y`. -/
theorem trace_quadraticAlgebra (a b : R) (z : QuadraticAlgebra R a b) :
    Algebra.trace R (QuadraticAlgebra R a b) z = 2 * z.re + b * z.im := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis a b), Matrix.trace_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul]
  simp [QuadraticAlgebra.basis]
  ring

variable (c : R)

local notation "B" => QuadraticAlgebra R c 0

/-- (a) `Tr(x + yθ) = 2x`. -/
theorem trace_B (z : B) : Algebra.trace R B z = 2 * z.re := by
  rw [trace_quadraticAlgebra]; ring

/-- (a) The trace form on the basis `1, θ`: `Tr 1 = 2`, `Tr θ = 0`, `Tr θ² = 2c`. -/
theorem trace_B_basis :
    Algebra.trace R B 1 = 2 ∧ Algebra.trace R B ω = 0 ∧ Algebra.trace R B (ω * ω) = 2 * c := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [trace_B] <;> simp

/-- The pairing `Tr(θ y z)` is divisible by `2c`: `Tr(θ y z) = 2c (y.im z.re + y.re z.im)`. -/
theorem trace_omega_mul (y z : B) :
    Algebra.trace R B (ω * y * z) = 2 * c * (y.im * z.re + y.re * z.im) := by
  rw [trace_B]; simp; ring

/-- (b), inclusion `(2θ)⁻¹B ⊆ dual`: for every `y ∈ B` the functional `z ↦ Tr(y z / (2θ))`
is `R`-valued, i.e. there is `f : B →ₗ[R] R` with `2c · f z = Tr(θ y z)`. -/
theorem dual_of_mem (y : B) :
    ∃ f : B →ₗ[R] R, ∀ z, 2 * c * f z = Algebra.trace R B (ω * y * z) :=
  ⟨y.im • reₗ c 0 + y.re • imₗ c 0, fun z => by
    rw [trace_omega_mul]; simp⟩

/-- (b), every functional comes from a unique `y ∈ B`, i.e. dual `⊆ (2θ)⁻¹B` and the
identification is bijective (needs `2` a unit and `c` a non-zero-divisor only for uniqueness). -/
theorem dual_eq (h2 : IsUnit (2 : R)) (hc : c ∈ nonZeroDivisors R) (f : B →ₗ[R] R) :
    ∃! y : B, ∀ z, 2 * c * f z = Algebra.trace R B (ω * y * z) := by
  have hf : ∀ z : B, f z = z.re * f 1 + z.im * f ω := by
    intro z
    have : z = z.re • (1 : B) + z.im • ω := by ext <;> simp
    conv_lhs => rw [this]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have h2c : 2 * c ∈ nonZeroDivisors R :=
    mul_mem_nonZeroDivisors.mpr ⟨h2.mem_nonZeroDivisors, hc⟩
  refine ⟨⟨f ω, f 1⟩, fun z => ?_, fun y hy => ?_⟩
  · rw [trace_omega_mul, hf z]; ring
  · have h1 := hy 1
    have hω := hy ω
    rw [trace_omega_mul] at h1 hω
    simp only [re_one, im_one, re_omega, im_omega, mul_one, mul_zero, add_zero, zero_add] at h1 hω
    rw [mul_cancel_left_mem_nonZeroDivisors h2c] at h1 hω
    ext
    · exact hω.symm
    · exact h1.symm

/-! (c) Kähler differentials: `Ω_{B/R} ≅ B ⧸ (2θ)`. -/

/-- The ideal `2θ·B`. -/
abbrev I2θ : Ideal B := Ideal.span {2 * ω}

/-- `θ² = c` in `B`. -/
theorem omega_mul_omega_B : (ω : B) * ω = algebraMap R B c := by
  ext <;> simp

/-- The universal derivation, explicitly: `d(x + yθ) = y mod 2θ` (i.e. `y · dθ`). -/
def dQ : Derivation R B (B ⧸ I2θ c) :=
  Derivation.mk'
    { toFun := fun z => Ideal.Quotient.mk (I2θ c) (algebraMap R B z.im)
      map_add' := fun x y => by simp
      map_smul' := fun r x => by
        rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def,
          ← Ideal.Quotient.mk_algebraMap, ← map_mul, ← map_mul]
        congr 1
        ext <;> simp }
    (fun x y => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_add]
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
      refine ⟨algebraMap R B (-(x.im * y.im)), ?_⟩
      ext <;> simp <;> ring)

theorem dQ_apply (z : B) : dQ c z = Ideal.Quotient.mk (I2θ c) (algebraMap R B z.im) := rfl

/-- `2θ · dθ = d(θ²) = d c = 0` in `Ω_{B/R}`. -/
theorem two_omega_smul_D : (2 * ω : B) • KaehlerDifferential.D R B ω = 0 := by
  have h := (KaehlerDifferential.D R B).leibniz ω ω
  rw [omega_mul_omega_B, Derivation.map_algebraMap] at h
  rw [two_mul, add_smul, ← h]

/-- `Ω_{B/R} → B ⧸ 2θB`, induced by the derivation `dQ`. -/
noncomputable def kPhi : Ω[B⁄R] →ₗ[B] B ⧸ I2θ c := (dQ c).liftKaehlerDifferential

/-- `B ⧸ 2θB → Ω_{B/R}`, `b ↦ b · dθ` (well defined by `two_omega_smul_D`). -/
noncomputable def kPsi : B ⧸ I2θ c →ₗ[B] Ω[B⁄R] :=
  Submodule.liftQ (I2θ c) (LinearMap.toSpanSingleton B _ (KaehlerDifferential.D R B ω))
    (Ideal.span_le.mpr (by
      rw [Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker,
        LinearMap.toSpanSingleton_apply]
      exact two_omega_smul_D c))

theorem kPsi_mk (b : B) :
    kPsi c (Ideal.Quotient.mk (I2θ c) b) = b • KaehlerDifferential.D R B ω := rfl

/-- **(c)** `Ω_{B/R} ≅ B ⧸ 2θB` as `B`-modules, `dθ ↦ 1`. -/
noncomputable def kaehlerEquiv : Ω[B⁄R] ≃ₗ[B] B ⧸ I2θ c :=
  LinearEquiv.ofLinearMap (kPhi c) (kPsi c)
    (by
      ext
      show kPhi c (kPsi c (Ideal.Quotient.mk (I2θ c) 1)) = Ideal.Quotient.mk (I2θ c) 1
      rw [kPsi_mk, one_smul, kPhi, Derivation.liftKaehlerDifferential_comp_D, dQ_apply,
        im_omega, map_one])
    (by
      apply Derivation.liftKaehlerDifferential_unique
      ext z
      show kPsi c (kPhi c (KaehlerDifferential.D R B z)) = KaehlerDifferential.D R B z
      have hz : z = algebraMap R B z.re + z.im • ω := by ext <;> simp
      rw [kPhi, Derivation.liftKaehlerDifferential_comp_D, dQ_apply, kPsi_mk, algebraMap_smul]
      conv_rhs => rw [hz]
      rw [map_add, Derivation.map_algebraMap, zero_add, Derivation.map_smul])

theorem kaehlerEquiv_D_omega :
    kaehlerEquiv c (KaehlerDifferential.D R B ω) = 1 := by
  show kPhi c _ = _
  rw [kPhi, Derivation.liftKaehlerDifferential_comp_D, dQ_apply, im_omega, map_one, map_one]

end Quadratic

end NotaPuente
