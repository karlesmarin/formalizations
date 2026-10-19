/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Tactic.Ring

/-!
# Completeness of the Tonnetz spectrum

`ℂ^(ZMod 12 × Bool)` is `ℂ^(ZMod 12) ⊗ ℂ²`. For each frequency `k` the Tonnetz adjacency matrix
preserves `dftChar k ⊗ ℂ²` and acts there as a `2 × 2` block with eigenvalues `±λ k`,
`λ k ^ 2 = pp k * pm k`. The 24 eigenvectors so obtained are linearly independent (a tensor
product of the character basis with an independent pair for each character), hence a basis.
So `A` is diagonalizable with exactly these eigenvalues, without the classification of the
irreducible representations of the dihedral group.

## Main results

* `tensor_linearIndependent`: characters tensored with independent pairs are independent.
* `eigFam_is_eigenvector`, `eigFam_linearIndependent`, `eigenBasis`.
* `tonnetz_spectrum_complete`, `tonnetz_spectrum_complete_unconditional`: a basis of
  eigenvectors with eigenvalues `±λ k`.

## References

* L. Babai, *Spectra of Cayley graphs*, J. Combin. Theory Ser. B 27 (1979).
* C. Marín, *The Tonnetz spectrum is the generating triad's Fourier balance profile*,
  Zenodo (2026), doi:10.5281/zenodo.20862821.
-/

@[expose] public section

namespace MusicTheory

open scoped Matrix BigOperators
open Complex

namespace TonnetzCompleteness

/-! ### The triad type, neo-Riemannian ops, and the adjacency operator (re-stated, as in
TonnetzSpectrum.lean). -/

abbrev Triad := ZMod 12 × Bool

def Pf : Triad → Triad | (x, b) => (x, !b)
def Lf : Triad → Triad
  | (x, true)  => (x + 4, false)
  | (x, false) => (x - 4, true)
def Rf : Triad → Triad
  | (x, true)  => (x - 3, false)
  | (x, false) => (x + 3, true)

def adj (t t' : Triad) : ℂ := if t' = Pf t ∨ t' = Lf t ∨ t' = Rf t then 1 else 0
def A : Matrix Triad Triad ℂ := Matrix.of adj
@[simp] lemma A_apply (t t' : Triad) : A t t' = adj t t' := rfl

theorem neighbours_distinct : ∀ t : Triad,
    Pf t ≠ Lf t ∧ Pf t ≠ Rf t ∧ Lf t ≠ Rf t := by decide

def nbhd (t : Triad) : Finset Triad := {Pf t, Lf t, Rf t}

lemma adj_eq_indicator (t t' : Triad) : adj t t' = if t' ∈ nbhd t then 1 else 0 := by
  unfold adj nbhd; congr 1; simp only [Finset.mem_insert, Finset.mem_singleton]

/-- The generic row sum: `Σ_{t'} adj t t' · f t' = f (P t) + f (L t) + f (R t)`. -/
lemma row_sum (f : Triad → ℂ) (t : Triad) :
    ∑ t' : Triad, adj t t' * f t' = f (Pf t) + f (Lf t) + f (Rf t) := by
  rw [Finset.sum_congr rfl (fun t' _ => by rw [adj_eq_indicator t t', boole_mul])]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  obtain ⟨hPL, hPR, hLR⟩ := neighbours_distinct t
  unfold nbhd
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; push Not; exact ⟨hPL, hPR⟩),
      Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hLR),
      Finset.sum_singleton, add_assoc]

/-! ### The DFT character on the root, and its shift law. -/

open ZMod AddChar

/-- The k-th DFT character on the root: `dftChar k x = stdAddChar (x * k)`. -/
noncomputable def dftChar (k : ZMod 12) : ZMod 12 → ℂ := fun x => stdAddChar (x * k)

@[simp] lemma dftChar_apply (k x : ZMod 12) : dftChar k x = stdAddChar (x * k) := rfl

/-- Character shift law: `dftChar k (x + c) = dftChar k x · stdAddChar (c * k)`. -/
lemma dftChar_shift (k x c : ZMod 12) :
    dftChar k (x + c) = dftChar k x * stdAddChar (c * k) := by
  simp only [dftChar_apply, add_mul, map_add_eq_mul]

/-! ### The generic eigenvector `eig k q (x,b) = dftChar k x · q b`.

For the quality 2-vector `q : Bool → ℂ`, the vector `eig k q` is an `A`-eigenvector with eigenvalue
`lam` provided the two structural relations hold:
  `q false · (1 + stdAddChar (4·k) + stdAddChar ((-3)·k)) = lam · q true`   (major side),
  `q true  · (1 + stdAddChar ((-4)·k) + stdAddChar (3·k)) = lam · q false`  (minor side). -/

/-- The eigenvector skeleton: DFT character on the root times a quality 2-vector. -/
noncomputable def eig (k : ZMod 12) (q : Bool → ℂ) : Triad → ℂ :=
  fun t => dftChar k t.1 * q t.2

@[simp] lemma eig_maj (k : ZMod 12) (q : Bool → ℂ) (x : ZMod 12) :
    eig k q (x, true) = dftChar k x * q true := rfl
@[simp] lemma eig_min (k : ZMod 12) (q : Bool → ℂ) (x : ZMod 12) :
    eig k q (x, false) = dftChar k x * q false := rfl

/-- **Generic eigenvector lemma (dftChar form).** Given the two structural relations, `eig k q` is an
    `A`-eigenvector with eigenvalue `lam`. -/
theorem A_mulVec_eig (k : ZMod 12) (q : Bool → ℂ) (lam : ℂ)
    (hmaj : q false * (1 + stdAddChar (4 * k) + stdAddChar ((-3) * k)) = lam * q true)
    (hmin : q true * (1 + stdAddChar ((-4) * k) + stdAddChar (3 * k)) = lam * q false) :
    A *ᵥ (eig k q) = lam • (eig k q) := by
  funext t
  obtain ⟨x, b⟩ := t
  simp only [Matrix.mulVec, dotProduct, A_apply, Pi.smul_apply, smul_eq_mul]
  rw [row_sum (eig k q) (x, b)]
  cases b
  · -- minor (x,false): neighbours (x,true), (x−4,true), (x+3,true) — all majors
    show eig k q (x, true) + eig k q (x - 4, true) + eig k q (x + 3, true) = _
    rw [eig_maj, eig_maj, eig_maj, eig_min,
        show (x - 4) = x + (-4) from by ring, show (x + 3) = x + 3 from rfl,
        dftChar_shift k x (-4), dftChar_shift k x 3]
    have e : dftChar k x * q true + dftChar k x * stdAddChar ((-4) * k) * q true
              + dftChar k x * stdAddChar (3 * k) * q true
            = dftChar k x * (q true * (1 + stdAddChar ((-4) * k) + stdAddChar (3 * k))) := by ring
    rw [e, hmin]; ring
  · -- major (x,true): neighbours (x,false), (x+4,false), (x−3,false) — all minors
    show eig k q (x, false) + eig k q (x + 4, false) + eig k q (x - 3, false) = _
    rw [eig_min, eig_min, eig_min, eig_maj,
        show (x - 3) = x + (-3) from by ring,
        dftChar_shift k x 4, dftChar_shift k x (-3)]
    have e : dftChar k x * q false + dftChar k x * stdAddChar (4 * k) * q false
              + dftChar k x * stdAddChar ((-3) * k) * q false
            = dftChar k x * (q false * (1 + stdAddChar (4 * k) + stdAddChar ((-3) * k))) := by ring
    rw [e, hmaj]; ring

/-! ### DFT-character linear independence (as in `CycleGraphSpectrum`). -/

/-- The k-th DFT character is `N` times the inverse-DFT of the standard delta `Pi.single k 1`. -/
lemma dftChar_eq_smul_invDFT (k : ZMod 12) :
    dftChar k = (12 : ℂ) • (ZMod.dft (N := 12)).symm (Pi.single k (1 : ℂ)) := by
  funext x
  rw [Pi.smul_apply, ZMod.invDFT_apply]
  rw [Finset.sum_eq_single k
        (fun j _ hj => by rw [Pi.single_eq_of_ne hj, smul_zero])
        (fun h => absurd (Finset.mem_univ k) h),
      Pi.single_eq_same, dftChar_apply, mul_comm x k]
  simp only [smul_eq_mul, mul_one]
  rw [show ((12 : ℕ) : ℂ) = (12 : ℂ) by norm_num, ← mul_assoc,
      mul_inv_cancel₀ (by norm_num : (12 : ℂ) ≠ 0), one_mul]

/-- Sealed helper (as in CycleGraphSpectrum): the standard basis pushed through an injective map. -/
theorem linearIndependent_single_one_map (M' : Type*) [AddCommGroup M'] [Module ℂ M']
    (f : (ZMod 12 → ℂ) →ₗ[ℂ] M') (hf : Function.Injective f) :
    LinearIndependent ℂ (fun k : ZMod 12 => f (Pi.single k (1 : ℂ))) :=
  (Pi.linearIndependent_single_one (ZMod 12) ℂ).map' f (LinearMap.ker_eq_bot.2 hf)

/-- **The DFT characters are linearly independent.** -/
theorem dftChar_linearIndependent :
    LinearIndependent ℂ (fun k : ZMod 12 => dftChar k) := by
  have hmap : LinearIndependent ℂ
      (fun k : ZMod 12 => (ZMod.dft (N := 12) (E := ℂ)).symm (Pi.single k (1 : ℂ))) :=
    linearIndependent_single_one_map (ZMod 12 → ℂ)
      (ZMod.dft (N := 12) (E := ℂ)).symm.toLinearMap
      (ZMod.dft (N := 12) (E := ℂ)).symm.injective
  have hN : (12 : ℂ) ≠ 0 := by norm_num
  have hscale := hmap.units_smul (fun _ : ZMod 12 => (Units.mk0 (12 : ℂ) hN))
  have hfam : (fun _ : ZMod 12 => (Units.mk0 (12 : ℂ) hN)) •
      (fun k : ZMod 12 => (ZMod.dft (N := 12) (E := ℂ)).symm (Pi.single k (1 : ℂ)))
      = fun k : ZMod 12 => dftChar k := by
    funext k
    rw [Pi.smul_apply', dftChar_eq_smul_invDFT, Units.smul_mk0]
  rwa [hfam] at hscale

/-! ### Abstract "(character basis) ⊗ (independent quality pair)" independence. -/

/-- **Abstract product-independence.** If `(f i)_i` is a linearly independent family in `ι → ℂ` and
    for each `i`, `(q i b)_{b}` is a linearly independent family in `κ → ℂ`, then the tensor family
    `(x, b') ↦ f i x * q i b b'`  indexed by `(i, b)`  is linearly independent in `(ι × κ) → ℂ`. -/
theorem tensor_linearIndependent {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → (ι → ℂ)) (hf : LinearIndependent ℂ f)
    (q : ι → κ → (κ → ℂ)) (hq : ∀ i, LinearIndependent ℂ (q i)) :
    LinearIndependent ℂ
      (fun ib : ι × κ => fun xb : ι × κ => f ib.1 xb.1 * q ib.1 ib.2 xb.2) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i₀
  obtain ⟨i, b₀⟩ := i₀
  rw [Fintype.linearIndependent_iff] at hf
  have key : ∀ b' : κ, ∀ i : ι, ∑ b : κ, c (i, b) * q i b b' = 0 := by
    intro b'
    refine hf (fun i => ∑ b : κ, c (i, b) * q i b b') ?_
    funext x
    have hcx := congrFun hc (x, b')
    simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hcx
    rw [Fintype.sum_prod_type] at hcx
    simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hcx]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hqi := hq i
  rw [Fintype.linearIndependent_iff] at hqi
  exact hqi (fun b => c (i, b)) (by
    funext b'
    simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact key b' i) b₀

/-! ### The unconditional 24-vector BASIS of `ℂ^Triad`.

The 24 vectors `eig j (Pi.single b 1)` — DFT character on the root tensored with a STANDARD quality
basis vector — are linearly independent (character basis ⊗ standard basis, both manifestly
independent), hence (card = 24 = dim) a BASIS of `Triad → ℂ`. This is the structural backbone of
completeness: `A` preserves each frequency's 2-dim quality block (the eigenvector lemma `A_mulVec_eig`
says so), so in this basis `A` is block-diagonal with twelve explicit 2×2 blocks. -/

/-- The standard product family: `stdFam (j,b) (x,b') = dftChar j x · (Pi.single b 1) b'`,
    i.e. `dftChar j` on the root, the `b`-th standard quality vector on the quality bit. -/
noncomputable def stdFam : (ZMod 12 × Bool) → (Triad → ℂ) :=
  fun jb => fun xb => dftChar jb.1 xb.1 * (Pi.single (M := fun _ : Bool => ℂ) jb.2 (1 : ℂ)) xb.2

/-- **The 24 standard product vectors are linearly independent.** -/
theorem stdFam_linearIndependent : LinearIndependent ℂ stdFam := by
  have h := tensor_linearIndependent dftChar dftChar_linearIndependent
    (fun _ : ZMod 12 => fun b : Bool => (Pi.single (M := fun _ : Bool => ℂ) b (1 : ℂ)))
    (fun _ => Pi.linearIndependent_single_one Bool ℂ)
  exact h

/-- `Triad → ℂ` has dimension 24 = `card (ZMod 12 × Bool)`. -/
lemma finrank_triad_fun : Module.finrank ℂ (Triad → ℂ) = Fintype.card (ZMod 12 × Bool) :=
  Module.finrank_fintype_fun_eq_card ℂ

/-- **THE COMPLETENESS BASIS.** The 24 vectors `stdFam (j,b)` form a basis of `Triad → ℂ`.
    (Linear independence + card = dim.) In this basis `A` is block-diagonal across the 12 frequencies;
    combined with `A_mulVec_eig` this exhibits the full spectrum as the twelve 2×2 quality blocks. -/
noncomputable def tonnetzBasis : Module.Basis (ZMod 12 × Bool) ℂ (Triad → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank
    stdFam_linearIndependent finrank_triad_fun.symm

@[simp] lemma tonnetzBasis_apply (jb : ZMod 12 × Bool) : tonnetzBasis jb = stdFam jb := by
  simp only [tonnetzBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

/-! ### The completeness ENGINE: a basis of `A`-eigenvectors ⇒ spectrum complete.

The general, reusable statement. The per-frequency major/minor structure constants are
  `pp k = 1 + stdAddChar (4·k) + stdAddChar ((-3)·k)`,
  `pm k = 1 + stdAddChar ((-4)·k) + stdAddChar (3·k)`,
and the two quality eigenvectors for frequency `k` are `q⁺ = (pp k, lam)`, `q⁻ = (pp k, -lam)` with
`lam² = pp k · pm k`. These are `A`-eigenvectors with eigenvalues `± lam` (lemma `A_mulVec_eig`),
and across the 12 frequencies they form a basis IFF, per frequency, the pair `q⁺, q⁻` is independent
— equivalently `pp k ≠ 0` (then `lam ≠ 0` too, since `lam² = ‖pp k‖² ≠ 0`). -/

/-- Major-side structure constant `pp k = 1 + ω^{4k} + ω^{-3k}`. -/
noncomputable def pp (k : ZMod 12) : ℂ := 1 + stdAddChar (4 * k) + stdAddChar ((-3) * k)
/-- Minor-side structure constant `pm k = 1 + ω^{-4k} + ω^{3k}`. -/
noncomputable def pm (k : ZMod 12) : ℂ := 1 + stdAddChar ((-4) * k) + stdAddChar (3 * k)

/-- The `+` quality eigenvector for frequency `k`: `(pp k, lam)`. -/
noncomputable def qPlus (k : ZMod 12) (lam : ℂ) : Bool → ℂ := fun b => if b then pp k else lam
/-- The `−` quality eigenvector for frequency `k`: `(pp k, −lam)`. -/
noncomputable def qMinus (k : ZMod 12) (lam : ℂ) : Bool → ℂ := fun b => if b then pp k else -lam

@[simp] lemma qPlus_true  (k : ZMod 12) (lam : ℂ) : qPlus k lam true  = pp k := rfl
@[simp] lemma qPlus_false (k : ZMod 12) (lam : ℂ) : qPlus k lam false = lam  := rfl
@[simp] lemma qMinus_true  (k : ZMod 12) (lam : ℂ) : qMinus k lam true  = pp k := rfl
@[simp] lemma qMinus_false (k : ZMod 12) (lam : ℂ) : qMinus k lam false = -lam := rfl

/-- `eig k (qPlus k lam)` is an `A`-eigenvector with eigenvalue `lam`, when `lam² = pp k · pm k`. -/
theorem A_mulVec_eig_plus (k : ZMod 12) (lam : ℂ) (hlam : lam ^ 2 = pp k * pm k) :
    A *ᵥ (eig k (qPlus k lam)) = lam • (eig k (qPlus k lam)) := by
  apply A_mulVec_eig k (qPlus k lam) lam
  · -- q false · pp = lam · q true : lam · pp = lam · pp
    rw [qPlus_false, qPlus_true,
        show (1 : ℂ) + stdAddChar (4 * k) + stdAddChar ((-3) * k) = pp k from rfl]
  · -- q true · pm = lam · q false : pp · pm = lam · lam
    rw [qPlus_true, qPlus_false,
        show (1 : ℂ) + stdAddChar ((-4) * k) + stdAddChar (3 * k) = pm k from rfl,
        mul_comm lam lam, ← pow_two, hlam]

/-- `eig k (qMinus k lam)` is an `A`-eigenvector with eigenvalue `−lam`, when `lam² = pp k · pm k`. -/
theorem A_mulVec_eig_minus (k : ZMod 12) (lam : ℂ) (hlam : lam ^ 2 = pp k * pm k) :
    A *ᵥ (eig k (qMinus k lam)) = (-lam) • (eig k (qMinus k lam)) := by
  apply A_mulVec_eig k (qMinus k lam) (-lam)
  · rw [qMinus_false, qMinus_true,
        show (1 : ℂ) + stdAddChar (4 * k) + stdAddChar ((-3) * k) = pp k from rfl]
  · rw [qMinus_true, qMinus_false,
        show (1 : ℂ) + stdAddChar ((-4) * k) + stdAddChar (3 * k) = pm k from rfl,
        show (-lam) * -lam = lam ^ 2 by ring, hlam]

/-- For each frequency, the two quality eigenvectors are linearly independent ⟺ `pp k ≠ 0 ∧ lam ≠ 0`.
    Here we prove the `⇐` direction (the one we need): nonvanishing ⇒ independence. -/
theorem qPair_linearIndependent (k : ZMod 12) (lam : ℂ)
    (hpp : pp k ≠ 0) (hlam : lam ≠ 0) :
    LinearIndependent ℂ (fun s : Bool => bif s then qPlus k lam else qMinus k lam) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  -- c true • qPlus + c false • qMinus = 0 as a function of b' : Bool
  have htrue := congrFun hc true
  have hfalse := congrFun hc false
  simp only [Fintype.sum_bool, Pi.add_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul,
    Bool.cond_true, Bool.cond_false, qPlus_true, qPlus_false, qMinus_true, qMinus_false] at htrue hfalse
  -- htrue : c true * pp k + c false * pp k = 0  →  (c true + c false) * pp k = 0
  -- hfalse: c true * lam + c false * (-lam) = 0  →  (c true - c false) * lam = 0
  have hsum : c true + c false = 0 := by
    have h0 : (c true + c false) * pp k = 0 := by linear_combination htrue
    exact (mul_eq_zero.mp h0).resolve_right hpp
  have hdiff : c true - c false = 0 := by
    have h0 : (c true - c false) * lam = 0 := by linear_combination hfalse
    exact (mul_eq_zero.mp h0).resolve_right hlam
  intro s
  cases s
  · -- s = false : c false = 0
    linear_combination (hsum - hdiff) / 2
  · -- s = true : c true = 0
    linear_combination (hsum + hdiff) / 2

/-! ### The capstone: a BASIS of `A`-eigenvectors ⇒ the spectrum is complete.

Assemble the 24 vectors. `lam : ZMod 12 → ℂ` picks, per frequency, a complex square root of
`pp k · pm k` (it exists — ℂ is algebraically closed). The eigenvector family is
  `eigFam (k, s) = eig k (qPlus k (lam k))`  for `s = true`  (eigenvalue `lam k`),
  `eigFam (k, s) = eig k (qMinus k (lam k))` for `s = false` (eigenvalue `−lam k`).
Given the per-frequency nonvanishing `pp k ≠ 0 ∧ lam k ≠ 0`, the 24 are linearly independent
(`tensor_linearIndependent` ∘ `qPair_linearIndependent`), hence a BASIS — a diagonalization of `A`. -/

/-- The 24-vector eigen-family (parametrized by a choice of square roots `lam`). -/
noncomputable def eigFam (lam : ZMod 12 → ℂ) : (ZMod 12 × Bool) → (Triad → ℂ) :=
  fun ks => eig ks.1 (bif ks.2 then qPlus ks.1 (lam ks.1) else qMinus ks.1 (lam ks.1))

/-- Each member of `eigFam` is an `A`-eigenvector (eigenvalue `± lam k`), given `lam k² = pp k·pm k`. -/
theorem eigFam_is_eigenvector (lam : ZMod 12 → ℂ)
    (hlam : ∀ k, lam k ^ 2 = pp k * pm k) (k : ZMod 12) (s : Bool) :
    A *ᵥ (eigFam lam (k, s)) = (bif s then lam k else -lam k) • (eigFam lam (k, s)) := by
  cases s
  · exact A_mulVec_eig_minus k (lam k) (hlam k)
  · exact A_mulVec_eig_plus k (lam k) (hlam k)

/-- **The eigen-family is linearly independent** (given per-frequency nonvanishing). The crux: the
    "(DFT character basis) ⊗ (per-frequency independent quality pair)" lemma. -/
theorem eigFam_linearIndependent (lam : ZMod 12 → ℂ)
    (hpp : ∀ k, pp k ≠ 0) (hlamne : ∀ k, lam k ≠ 0) :
    LinearIndependent ℂ (eigFam lam) := by
  have h := tensor_linearIndependent dftChar dftChar_linearIndependent
    (fun k : ZMod 12 => fun s : Bool => bif s then qPlus k (lam k) else qMinus k (lam k))
    (fun k => qPair_linearIndependent k (lam k) (hpp k) (hlamne k))
  -- the tensor family IS eigFam, up to the `eig`/`bif` unfolding
  exact h

/-- **THE COMPLETENESS BASIS OF EIGENVECTORS (engine).** Given square roots `lam k` of `pp k·pm k`
    with `pp k ≠ 0` and `lam k ≠ 0` for every frequency, the 24 vectors `eigFam lam` form a BASIS of
    `Triad → ℂ` consisting of `A`-eigenvectors. This is a full diagonalization of the Tonnetz adjacency
    operator: the certified eigenvalues `± lam k` (k = 0..11) are ALL of the spectrum, with their
    multiplicities — completeness, without the dihedral-irrep classification. -/
noncomputable def eigenBasis (lam : ZMod 12 → ℂ)
    (hpp : ∀ k, pp k ≠ 0) (hlamne : ∀ k, lam k ≠ 0) :
    Module.Basis (ZMod 12 × Bool) ℂ (Triad → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank
    (eigFam_linearIndependent lam hpp hlamne) finrank_triad_fun.symm

@[simp] lemma eigenBasis_apply (lam : ZMod 12 → ℂ)
    (hpp : ∀ k, pp k ≠ 0) (hlamne : ∀ k, lam k ≠ 0) (ks : ZMod 12 × Bool) :
    eigenBasis lam hpp hlamne ks = eigFam lam ks := by
  simp only [eigenBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

/-! ### Reducing the residual hypothesis to the single fact `pp k ≠ 0`.

`pm k = conj (pp k)` (the minor-side constant is the complex conjugate of the major-side one, since
`stdAddChar` is unimodular), hence `pp k · pm k = ‖pp k‖²`. So the square root `lam k` exists (ℂ is
algebraically closed) and is nonzero exactly when `pp k ≠ 0`; the whole eigen-basis is then a basis of
`A`-eigenvectors. The completeness of the Tonnetz spectrum thus rests on the SINGLE concrete algebraic
input `∀ k, pp k ≠ 0`. -/

/-- `conj (stdAddChar a) = stdAddChar (-a)` — `stdAddChar` is unimodular (factors through `Circle`). -/
lemma conj_stdAddChar (a : ZMod 12) :
    (starRingEnd ℂ) (stdAddChar a) = stdAddChar (-a) := by
  rw [AddChar.map_neg_eq_inv]
  rw [show (stdAddChar a : ℂ) = ((ZMod.toCircle a : Circle) : ℂ) from rfl,
      ← Circle.coe_inv_eq_conj, ← Circle.coe_inv]

/-- `pm k = conj (pp k)`: the minor-side structure constant is the conjugate of the major-side one. -/
lemma pm_eq_conj_pp (k : ZMod 12) : pm k = (starRingEnd ℂ) (pp k) := by
  unfold pp pm
  rw [map_add, map_add, map_one, conj_stdAddChar, conj_stdAddChar]
  congr 2 <;> ring_nf

/-- `pp k · pm k = ‖pp k‖²` (a nonneg real); in particular it is `0` iff `pp k = 0`. -/
lemma pp_mul_pm (k : ZMod 12) : pp k * pm k = (Complex.normSq (pp k) : ℂ) := by
  rw [pm_eq_conj_pp, Complex.normSq_eq_conj_mul_self]; ring

/-- `pp k · pm k ≠ 0` precisely when `pp k ≠ 0`. -/
lemma pp_mul_pm_ne_zero (k : ZMod 12) (hpp : pp k ≠ 0) : pp k * pm k ≠ 0 := by
  rw [pp_mul_pm]
  simp only [ne_eq, Complex.ofReal_eq_zero, Complex.normSq_eq_zero]
  exact hpp

/-- **THE COMPLETENESS THEOREM (packaged).** Assuming only the concrete algebraic nonvanishing
    `∀ k, pp k ≠ 0`, the Tonnetz adjacency operator `A` has a BASIS of eigenvectors — i.e. it is
    diagonalizable and the certified eigenvalues `± √(pp k · pm k)` (k = 0..11) are its COMPLETE
    spectrum with multiplicities. The square roots are produced from ℂ being algebraically closed;
    no dihedral-irrep classification. -/
theorem tonnetz_spectrum_complete (hpp : ∀ k, pp k ≠ 0) :
    ∃ (lam : ZMod 12 → ℂ),
      (∀ k, lam k ^ 2 = pp k * pm k) ∧
      (∃ B : Module.Basis (ZMod 12 × Bool) ℂ (Triad → ℂ),
        ∀ ks : ZMod 12 × Bool,
          A *ᵥ (B ks) = (bif ks.2 then lam ks.1 else -lam ks.1) • (B ks)) := by
  -- choose a square root of pp k · pm k for each k (ℂ algebraically closed)
  have hroot : ∀ k, ∃ z : ℂ, z ^ 2 = pp k * pm k :=
    fun k => IsAlgClosed.exists_pow_nat_eq (pp k * pm k) (by norm_num)
  choose lam hlam using hroot
  have hlamne : ∀ k, lam k ≠ 0 := by
    intro k hz
    apply pp_mul_pm_ne_zero k (hpp k)
    rw [← hlam k, hz]; ring
  refine ⟨lam, hlam, eigenBasis lam hpp hlamne, ?_⟩
  intro ks
  rw [eigenBasis_apply]
  obtain ⟨k, s⟩ := ks
  exact eigFam_is_eigenvector lam hlam k s

/-! ### Discharging the residual `∀ k, pp k ≠ 0`: explicit root-of-unity arithmetic.

`pp k = 1 + ω^{4k} + ω^{-3k}` only ever involves `ω^m` for `m ∈ {0,3,4,6,8,9}`. We evaluate these six
`stdAddChar` values to their closed forms (`exp(2πi m/12)`), giving `pp k = (rational) + (rational)·I`
whose REAL part is one of `{3, 1, 2, 3/2, 1/2, -1/2}` for every `k` — never zero. Hence `pp k ≠ 0` for
all 12 frequencies, by a `decide` exponent reduction + `Complex.re` extraction. Elementary algebraic
arithmetic on twelfth roots of unity. -/

open Real in
private lemma sac_int (j : ℤ) :
    (stdAddChar ((j : ZMod 12)) : ℂ) = Complex.exp (2 * Real.pi * I * j / 12) := by
  rw [stdAddChar_coe]; norm_num

/-- `stdAddChar 0 = 1`. -/
private lemma sac0 : (stdAddChar (0 : ZMod 12) : ℂ) = 1 := by
  rw [show (0 : ZMod 12) = ((0:ℤ):ZMod 12) by rfl, sac_int]; norm_num
/-- `stdAddChar 3 = I`. -/
private lemma sac3 : (stdAddChar (3 : ZMod 12) : ℂ) = I := by
  rw [show (3 : ZMod 12) = ((3:ℤ):ZMod 12) by push_cast; rfl, sac_int]
  push_cast
  rw [show (2 * (Real.pi:ℂ) * I * 3 / 12) = (Real.pi/2) * I by ring, Complex.exp_mul_I,
      show ((Real.pi:ℂ)/2) = (((Real.pi/2 : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp
/-- `stdAddChar 6 = -1`. -/
private lemma sac6 : (stdAddChar (6 : ZMod 12) : ℂ) = -1 := by
  rw [show (6 : ZMod 12) = ((6:ℤ):ZMod 12) by push_cast; rfl, sac_int]
  push_cast
  rw [show (2 * (Real.pi:ℂ) * I * 6 / 12) = Real.pi * I by ring, Complex.exp_pi_mul_I]
/-- `stdAddChar 9 = -I`. -/
private lemma sac9 : (stdAddChar (9 : ZMod 12) : ℂ) = -I := by
  rw [show (9 : ZMod 12) = ((9:ℤ):ZMod 12) by push_cast; rfl, sac_int]
  push_cast
  rw [show (2 * (Real.pi:ℂ) * I * 9 / 12) = (3*Real.pi/2) * I by ring, Complex.exp_mul_I,
      show ((3*(Real.pi:ℂ)/2)) = (((3*Real.pi/2 : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      show (3*Real.pi/2) = Real.pi + Real.pi/2 by ring, Real.cos_add, Real.sin_add,
      Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast; ring
/-- `stdAddChar 4 = (-1 + √3·I)/2`. -/
private lemma sac4 : (stdAddChar (4 : ZMod 12) : ℂ) = (-1 + (Real.sqrt 3 : ℝ) * I)/2 := by
  rw [show (4 : ZMod 12) = ((4:ℤ):ZMod 12) by push_cast; rfl, sac_int]
  push_cast
  rw [show (2 * (Real.pi:ℂ) * I * 4 / 12) = (2*Real.pi/3) * I by ring, Complex.exp_mul_I,
      show ((2*(Real.pi:ℂ)/3)) = (((2*Real.pi/3 : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      show (2*Real.pi/3) = Real.pi - Real.pi/3 by ring, Real.cos_pi_sub, Real.sin_pi_sub,
      Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast; ring
/-- `stdAddChar 8 = (-1 - √3·I)/2`. -/
private lemma sac8 : (stdAddChar (8 : ZMod 12) : ℂ) = (-1 - (Real.sqrt 3 : ℝ) * I)/2 := by
  rw [show (8 : ZMod 12) = ((8:ℤ):ZMod 12) by push_cast; rfl, sac_int]
  push_cast
  rw [show (2 * (Real.pi:ℂ) * I * 8 / 12) = (4*Real.pi/3) * I by ring, Complex.exp_mul_I,
      show ((4*(Real.pi:ℂ)/3)) = (((4*Real.pi/3 : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      show (4*Real.pi/3) = Real.pi + Real.pi/3 by ring, Real.cos_add, Real.sin_add,
      Real.cos_pi, Real.sin_pi, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast; ring

/-- `pp` written via the reduced exponents (`rfl` unfolding). -/
private lemma pp_eq (k : ZMod 12) :
    pp k = 1 + stdAddChar (4 * k) + stdAddChar ((-3) * k) := rfl

/-- Helper: a nonzero real part forces a nonzero complex number. -/
private lemma finRe : ∀ (z : ℂ), z.re ≠ 0 → z ≠ 0 := fun z hz h => hz (by rw [h]; rfl)

private lemma pp0_ne : pp (0 : ZMod 12) ≠ 0 := by
  rw [pp_eq, show (4:ZMod 12)*0 = 0 by decide, show ((-3):ZMod 12)*0 = 0 by decide, sac0]
  norm_num
private lemma pp1_ne : pp (1 : ZMod 12) ≠ 0 := by
  rw [pp_eq, show (4:ZMod 12)*1 = 4 by decide, show ((-3):ZMod 12)*1 = 9 by decide, sac4, sac9]
  apply finRe
  simp only [Complex.add_re, Complex.one_re, Complex.div_ofNat_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num
private lemma pp2_ne : pp (2 : ZMod 12) ≠ 0 := by
  rw [pp_eq, show (4:ZMod 12)*2 = 8 by decide, show ((-3):ZMod 12)*2 = 6 by decide, sac8, sac6]
  apply finRe
  simp only [Complex.add_re, Complex.one_re, Complex.div_ofNat_re, Complex.neg_re]
  norm_num
private lemma pp3_ne : pp (3 : ZMod 12) ≠ 0 := by
  rw [pp_eq, show (4:ZMod 12)*3 = 0 by decide, show ((-3):ZMod 12)*3 = 3 by decide, sac0, sac3]
  apply finRe
  simp only [Complex.add_re, Complex.one_re, Complex.I_re]
  norm_num
private lemma pp4_ne : pp (4 : ZMod 12) ≠ 0 := by
  rw [pp_eq, show (4:ZMod 12)*4 = 4 by decide, show ((-3):ZMod 12)*4 = 0 by decide, sac4, sac0]
  apply finRe
  simp only [Complex.add_re, Complex.one_re, Complex.div_ofNat_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num
private lemma pp5_ne : pp (5 : ZMod 12) ≠ 0 := by
  rw [pp_eq, show (4:ZMod 12)*5 = 8 by decide, show ((-3):ZMod 12)*5 = 9 by decide, sac8, sac9]
  apply finRe
  simp only [Complex.add_re, Complex.one_re, Complex.div_ofNat_re, Complex.neg_re, Complex.I_re]
  norm_num
private lemma pp6_ne : pp (6 : ZMod 12) ≠ 0 := by
  rw [pp_eq, show (4:ZMod 12)*6 = 0 by decide, show ((-3):ZMod 12)*6 = 6 by decide, sac0, sac6]
  apply finRe
  simp only [Complex.add_re, Complex.one_re, Complex.neg_re]
  norm_num
private lemma pp7_ne : pp (7 : ZMod 12) ≠ 0 := by
  rw [pp_eq, show (4:ZMod 12)*7 = 4 by decide, show ((-3):ZMod 12)*7 = 3 by decide, sac4, sac3]
  apply finRe
  simp only [Complex.add_re, Complex.one_re, Complex.div_ofNat_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num
private lemma pp8_ne : pp (8 : ZMod 12) ≠ 0 := by
  rw [pp_eq, show (4:ZMod 12)*8 = 8 by decide, show ((-3):ZMod 12)*8 = 0 by decide, sac8, sac0]
  apply finRe
  simp only [Complex.add_re, Complex.one_re, Complex.div_ofNat_re]
  norm_num
private lemma pp9_ne : pp (9 : ZMod 12) ≠ 0 := by
  rw [pp_eq, show (4:ZMod 12)*9 = 0 by decide, show ((-3):ZMod 12)*9 = 9 by decide, sac0, sac9]
  apply finRe
  simp only [Complex.add_re, Complex.one_re, Complex.neg_re, Complex.I_re]
  norm_num
private lemma pp10_ne : pp (10 : ZMod 12) ≠ 0 := by
  rw [pp_eq, show (4:ZMod 12)*10 = 4 by decide, show ((-3):ZMod 12)*10 = 6 by decide, sac4, sac6]
  apply finRe
  simp only [Complex.add_re, Complex.one_re, Complex.div_ofNat_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num
private lemma pp11_ne : pp (11 : ZMod 12) ≠ 0 := by
  rw [pp_eq, show (4:ZMod 12)*11 = 8 by decide, show ((-3):ZMod 12)*11 = 3 by decide, sac8, sac3]
  apply finRe
  simp only [Complex.add_re, Complex.one_re, Complex.div_ofNat_re, Complex.I_re]
  norm_num

/-- **THE RESIDUAL NONVANISHING — DISCHARGED.** `pp k ≠ 0` for every frequency `k`. The 12 cases use
    the six explicit twelfth-root values; each `pp k` has nonzero real part. -/
theorem pp_ne_zero : ∀ k : ZMod 12, pp k ≠ 0 := by
  intro k
  fin_cases k <;>
    first
      | exact pp0_ne | exact pp1_ne | exact pp2_ne | exact pp3_ne | exact pp4_ne | exact pp5_ne
      | exact pp6_ne | exact pp7_ne | exact pp8_ne | exact pp9_ne | exact pp10_ne | exact pp11_ne

/-! ### The unconditional completeness theorem. -/

/-- **THE TONNETZ SPECTRUM IS COMPLETE (unconditional).** The adjacency operator `A` of the
    PLR/Tonnetz Cayley graph has a BASIS of 24 explicit eigenvectors — it is diagonalizable, and the
    eigenvalues `± √(pp k · pm k)` (k = 0..11), which are exactly `± {3, √5, 2cos(π/12), √3, 1,
    2cos(5π/12)}` with their multiplicities, are its COMPLETE spectrum, without the
    dihedral-irrep classification. -/
theorem tonnetz_spectrum_complete_unconditional :
    ∃ (lam : ZMod 12 → ℂ),
      (∀ k, lam k ^ 2 = pp k * pm k) ∧
      (∃ B : Module.Basis (ZMod 12 × Bool) ℂ (Triad → ℂ),
        ∀ ks : ZMod 12 × Bool,
          A *ᵥ (B ks) = (bif ks.2 then lam ks.1 else -lam ks.1) • (B ks)) :=
  tonnetz_spectrum_complete pp_ne_zero

end TonnetzCompleteness

end MusicTheory
