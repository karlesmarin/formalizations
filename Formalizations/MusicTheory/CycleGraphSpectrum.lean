/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.LinearAlgebra.Matrix.Circulant
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Ring

/-!
# Circulant matrices are diagonalized by the discrete Fourier transform

For `v : ZMod N → ℂ`, Mathlib's `Matrix.circulant v` satisfies
`circulant v *ᵥ dftChar k = ZMod.dft v k • dftChar k`, where `dftChar k j = stdAddChar (j * k)`.
The characters form a basis (`N` times the inverse transform of the standard basis), so every
circulant is diagonal in it. For the cycle graph `C₁₂` this gives the spectrum
`2 cos (2πk / 12)`; for a Cayley graph of `ℤ/N` the eigenvalue is a character sum.

## Main results

* `circulant_mulVec_dftChar`: every circulant has the characters as eigenvectors, with eigenvalue
  the transform of its first column.
* `dftChar_linearIndependent`, `dftChar_basis`: the characters form a basis of `ZMod N → ℂ`.
* `C12_eq_adjMatrix`, `C12_eigenvalue_cos`: the adjacency matrix of `SimpleGraph.cycleGraph 12`
  and its eigenvalues `2 cos (2πk / 12)`.
* `cayleyAdj_eigenvalue`, `cayleyAdj_eq_adjMatrix`: the spectrum of a Cayley graph of `ℤ/N`.

## References

* C. Godsil, G. Royle, *Algebraic Graph Theory*, Springer (2001).
* L. Babai, *Spectra of Cayley graphs*, J. Combin. Theory Ser. B 27 (1979).
* C. Marín, *The Tonnetz spectrum is the generating triad's Fourier balance profile*,
  Zenodo (2026), doi:10.5281/zenodo.20862821.
-/

@[expose] public section

namespace MusicTheory

open scoped Matrix
open Complex Real

namespace CycleGraphSpectrum

open ZMod AddChar

variable {N : ℕ} [NeZero N]

/-! ### T1 — circulants are diagonalized by the DFT characters. -/

/-- The k-th DFT character as a vector on `ZMod N`: `dftChar k j = stdAddChar (j * k) = exp(2πi·jk/N)`.
    These are the simultaneous eigenvectors of every circulant operator. -/
noncomputable def dftChar (k : ZMod N) : ZMod N → ℂ := fun j => stdAddChar (j * k)

@[simp] lemma dftChar_apply (k j : ZMod N) : dftChar k j = stdAddChar (j * k) := rfl

/-- The DFT character is nowhere the zero vector: its value at `0` is `stdAddChar 0 = 1 ≠ 0`. -/
lemma dftChar_ne_zero (k : ZMod N) : dftChar k ≠ 0 := by
  intro h
  have : dftChar k 0 = 0 := by rw [h]; rfl
  rw [dftChar_apply, zero_mul, map_zero_eq_one] at this
  exact one_ne_zero this

/-- **THE DIAGONALIZATION (T1).** Every circulant matrix is diagonalized by the DFT characters:
    `circulant v` sends the k-th character `dftChar k` to `(dft v k) • dftChar k`. The eigenvalue
    is exactly the k-th discrete Fourier coefficient of the generating vector `v`. -/
theorem circulant_mulVec_dftChar (v : ZMod N → ℂ) (k : ZMod N) :
    (Matrix.circulant v) *ᵥ (dftChar k) = (ZMod.dft v k) • dftChar k := by
  funext i
  -- LHS i = Σ_j v(i-j) * stdAddChar(j*k)
  simp only [Matrix.mulVec, dotProduct, Matrix.circulant_apply]
  -- reindex m = i - j via Equiv.subLeft i  (j ↦ i - j),  so v(i - (i-m)) = v m
  rw [← Equiv.sum_comp (Equiv.subLeft i)]
  simp only [Equiv.subLeft_apply, sub_sub_cancel, dftChar_apply]
  -- now: Σ_m v m * stdAddChar ((i - m) * k)
  -- (i - m)*k = i*k - m*k = i*k + (-(m*k)); split the character
  have hsplit : ∀ m : ZMod N,
      v m * stdAddChar ((i - m) * k)
        = stdAddChar (i * k) * (stdAddChar (-(m * k)) * v m) := by
    intro m
    rw [sub_mul, sub_eq_add_neg, map_add_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun m _ => hsplit m), ← Finset.mul_sum]
  -- RHS = (dft v k) • dftChar k at i = (dft v k) * stdAddChar (i*k)
  rw [Pi.smul_apply, smul_eq_mul, dftChar_apply, ZMod.dft_apply]
  simp only [smul_eq_mul]
  rw [mul_comm]

/-! ### T2 — the DFT characters are a BASIS: the simultaneous eigenbasis of all circulants.

The 12 characters `dftChar k` are linearly independent, hence (card = dim = N) a basis of `ZMod N → ℂ`.
This is the classical "characters of a finite abelian group are independent", here in the concrete
`stdAddChar` form. Combined with T1 (`circulant_mulVec_dftChar`), it makes the DFT the literal
diagonalizing eigenbasis of every circulant — in particular of `C12`.

The load-bearing observation: each `dftChar k` is `N` times the inverse-DFT image of the standard
basis vector `Pi.single k 1`. Since `Pi.single · 1` is independent (`Pi.linearIndependent_single_one`),
the injective linear equiv `𝓕⁻ = dft.symm` preserves independence (`LinearIndependent.map'`), and
scaling by the nonzero constant `(N : ℂ)` preserves it again (`LinearIndependent.units_smul`). -/

/-- **The bridge to the standard basis.** The k-th DFT character is `N` times the inverse-DFT of the
    standard basis vector `Pi.single k 1`: `dftChar k = (N : ℂ) • 𝓕⁻ (Pi.single k 1)`. The inverse-DFT
    of a delta is (up to the `N⁻¹` normalization) exactly a character. -/
lemma dftChar_eq_smul_invDFT (k : ZMod N) :
    dftChar k = (N : ℂ) • (ZMod.dft (N := N)).symm (Pi.single k (1 : ℂ)) := by
  funext x
  rw [Pi.smul_apply, ZMod.invDFT_apply]
  -- the inner sum collapses to the j = k term: stdAddChar (k * x) • 1
  rw [Finset.sum_eq_single k
        (fun j _ hj => by rw [Pi.single_eq_of_ne hj, smul_zero])
        (fun h => absurd (Finset.mem_univ k) h),
      Pi.single_eq_same, dftChar_apply, mul_comm x k]
  -- now: stdAddChar (k*x) = (N:ℂ) • (N:ℂ)⁻¹ • (stdAddChar (k*x) • 1)
  simp only [smul_eq_mul, mul_one]
  rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast (NeZero.ne N)), one_mul]

/-- **Sealed helper.** An injective linear map out of `ZMod N → ℂ` carries the standard basis
    `(Pi.single k 1)_k` to a linearly independent family. Stated generically (`f` opaque) so the
    elaborator/kernel never unfolds the heavy `dft` structure — the direct inline `map'` over
    `ZMod.dft.symm` provokes a `whnf`/`isDefEq` blow-up; this generic version sidesteps it. -/
theorem linearIndependent_single_one_map (M' : Type*) [AddCommGroup M'] [Module ℂ M']
    (n : ℕ) (f : (ZMod n → ℂ) →ₗ[ℂ] M') (hf : Function.Injective f) :
    LinearIndependent ℂ (fun k : ZMod n => f (Pi.single k (1 : ℂ))) :=
  (Pi.linearIndependent_single_one (ZMod n) ℂ).map' f (LinearMap.ker_eq_bot.2 hf)

/-- **THE EIGENBASIS — LINEAR INDEPENDENCE (T2, load-bearing).** The DFT characters
    `(dftChar k)_{k ∈ ZMod N}` are linearly independent over ℂ. (Characters of the finite abelian
    group `ZMod N`, in `stdAddChar` form.) Pushed through `𝓕⁻` from the standard basis and scaled. -/
theorem dftChar_linearIndependent :
    LinearIndependent ℂ (fun k : ZMod N => dftChar k) := by
  -- (Pi.single k 1)_k pushed through the injective inverse-DFT (sealed helper)
  have hmap : LinearIndependent ℂ
      (fun k : ZMod N => (ZMod.dft (N := N) (E := ℂ)).symm (Pi.single k (1 : ℂ))) :=
    linearIndependent_single_one_map (ZMod N → ℂ) N
      (ZMod.dft (N := N) (E := ℂ)).symm.toLinearMap
      (ZMod.dft (N := N) (E := ℂ)).symm.injective
  -- scale each by the nonzero constant (N : ℂ) (as a unit) — preserves independence
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hscale := hmap.units_smul (fun _ : ZMod N => (Units.mk0 (N : ℂ) hN))
  -- the scaled family IS (dftChar k)_k, via dftChar_eq_smul_invDFT
  have hfam : (fun _ : ZMod N => (Units.mk0 (N : ℂ) hN)) •
      (fun k : ZMod N => (ZMod.dft (N := N) (E := ℂ)).symm (Pi.single k (1 : ℂ)))
      = fun k : ZMod N => dftChar k := by
    funext k
    rw [Pi.smul_apply', dftChar_eq_smul_invDFT, Units.smul_mk0]
  rwa [hfam] at hscale

/-- **THE EIGENBASIS — AS A BASIS (T2).** The DFT characters form a basis of `ZMod N → ℂ`
    (linear independence + card = dim). This is the simultaneous eigenbasis diagonalizing every
    circulant operator on `ZMod N`. -/
noncomputable def dftChar_basis : Module.Basis (ZMod N) ℂ (ZMod N → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank (b := fun k : ZMod N => dftChar k)
    dftChar_linearIndependent (Module.finrank_fintype_fun_eq_card ℂ).symm

@[simp] lemma dftChar_basis_apply (k : ZMod N) : dftChar_basis k = dftChar k := by
  simp only [dftChar_basis, coe_basisOfLinearIndependentOfCardEqFinrank]

/-! ### T3 — the pitch-class cycle graph C₁₂ and its spectrum.

The chromatic circle: vertex `m ∈ ℤ/12` joined to `m ± 1` (its semitone neighbours). The adjacency
operator is `C12 = circulant cycAdj` where `cycAdj` is the ±1 semitone indicator. By T1 its
eigenvalues are `dft cycAdj k`, which we compute to the textbook `2·cos(2πk/12)`. -/

/-- The ±1 semitone-neighbour indicator on ℤ/12: `cycAdj m = 1` iff `m = 1 ∨ m = -1`, else `0`.
    This is the first column of the C₁₂ adjacency matrix. -/
noncomputable def cycAdj : ZMod 12 → ℂ := fun m => if m = 1 ∨ m = -1 then 1 else 0

/-- The adjacency operator of the pitch-class cycle graph C₁₂, as a circulant matrix over ℂ. -/
noncomputable def C12 : Matrix (ZMod 12) (ZMod 12) ℂ := Matrix.circulant cycAdj

/-- C₁₂ is diagonalized by the DFT characters: eigenvector `dftChar k`, eigenvalue `dft cycAdj k`.
    (Direct specialization of the general T1 diagonalization.) -/
theorem C12_mulVec_dftChar (k : ZMod 12) :
    C12 *ᵥ (dftChar k) = (ZMod.dft cycAdj k) • dftChar k :=
  circulant_mulVec_dftChar cycAdj k

/-- **The C₁₂ eigenvalue, as a character sum.** Only the two semitone steps `m = 1, -1` contribute,
    giving `dft cycAdj k = stdAddChar k + stdAddChar (-k) = ω^k + ω^(-k)`, `ω = exp(2πi/12)`. -/
theorem C12_eigenvalue (k : ZMod 12) :
    ZMod.dft cycAdj k = stdAddChar k + stdAddChar (-k) := by
  rw [ZMod.dft_apply]
  have h1 : (1 : ZMod 12) ≠ -1 := by decide
  -- split univ into the pair {1, -1} and its complement
  rw [← Finset.sum_add_sum_compl ({1, -1} : Finset (ZMod 12)), Finset.sum_pair h1]
  -- the two surviving terms evaluate the character; the complement sum vanishes
  have hc1 : cycAdj (1 : ZMod 12) = 1 := ite_eq_left (Or.inl rfl)
  have hc2 : cycAdj (-1 : ZMod 12) = 1 := ite_eq_left (Or.inr rfl)
  have e1 : stdAddChar (-((1 : ZMod 12) * k)) • cycAdj 1 = stdAddChar (-k) := by
    rw [hc1, one_mul, smul_eq_mul, mul_one]
  have e2 : stdAddChar (-(((-1) : ZMod 12) * k)) • cycAdj (-1) = stdAddChar k := by
    rw [hc2, neg_one_mul, neg_neg, smul_eq_mul, mul_one]
  rw [e1, e2]
  have hzero : ∑ m ∈ ({1, -1} : Finset (ZMod 12))ᶜ,
      stdAddChar (-(m * k)) • cycAdj m = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton] at hm
    push Not at hm
    have : cycAdj m = 0 := by
      simp only [cycAdj, ite_eq_right (by tauto : ¬(m = 1 ∨ m = -1))]
    rw [this, smul_zero]
  rw [hzero, add_zero, add_comm]

/-- `stdAddChar` of a class equals the explicit root of unity `exp(2πi·k.val/12)`. -/
lemma stdAddChar_eq_exp (k : ZMod 12) :
    stdAddChar k = exp (2 * π * I * (k.val : ℂ) / 12) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val k]
  rw [show ((k.val : ZMod 12)) = ((k.val : ℤ) : ZMod 12) by push_cast; rfl,
      stdAddChar_coe]
  push_cast
  ring_nf

/-- **The C₁₂ eigenvalue in closed form (T3 payload).** The k-th eigenvalue of the chromatic
    cycle graph is the textbook `2·cos(2πk/12)` — the cosine spectrum of C₁₂. -/
theorem C12_eigenvalue_cos (k : ZMod 12) :
    ZMod.dft cycAdj k = 2 * Complex.cos (2 * π * (k.val : ℂ) / 12) := by
  rw [C12_eigenvalue]
  set θ : ℂ := 2 * π * (k.val : ℂ) / 12 with hθ
  -- stdAddChar k = exp(θ·I),  stdAddChar(-k) = exp(-θ·I)
  have hk : stdAddChar k = exp (θ * I) := by
    rw [stdAddChar_eq_exp]; congr 1; rw [hθ]; ring
  have hnk : stdAddChar (-k) = exp (-θ * I) := by
    rw [show (-k : ZMod 12) = ((-(k.val) : ℤ) : ZMod 12) by push_cast; rw [ZMod.natCast_val,
        ZMod.cast_id], stdAddChar_coe]
    rw [hθ]; push_cast; congr 1; ring
  rw [hk, hnk, Complex.cos]
  ring

/-! ### T4 — the graph bridge: `C12` IS Mathlib's cycle-graph adjacency matrix.

So the eigenvalues `C12_eigenvalue_cos` are LITERALLY the spectrum of `SimpleGraph.cycleGraph 12`.
The Fin/ZMod subtraction-instance mismatch that defeats a direct `rw [cycleGraph_adj]` (cycleGraph
lives over `Fin n`, our work over `ZMod 12`) is sidestepped by proving the adjacency characterization
with `decide` over the 144 vertex pairs — the kernel evaluates both sides to a boolean, no pattern
unification needed. -/

/-- The adjacency relation of `cycleGraph 12` on ℤ/12 is "differ by a semitone" (`i - j = ±1`).
    Checked by `decide` over the 144 pairs of `Fin 12`. -/
theorem cycleGraph12_adj_iff : ∀ i j : ZMod 12,
    (SimpleGraph.cycleGraph 12).Adj i j ↔ (i - j = 1 ∨ i - j = -1) :=
  (by decide : ∀ i j : Fin 12,
    (SimpleGraph.cycleGraph 12).Adj i j ↔ (i - j = 1 ∨ i - j = -1))

/-- **THE GRAPH BRIDGE (T4).** The circulant `C12` IS the adjacency matrix of the chromatic cycle
    graph `cycleGraph 12` over ℂ. Combined with `C12_eigenvalue_cos`, this says the eigenvalues
    `2·cos(2πk/12)` are the spectrum of Mathlib's `SimpleGraph.cycleGraph 12`. -/
theorem C12_eq_adjMatrix : C12 = (SimpleGraph.cycleGraph 12).adjMatrix ℂ := by
  ext i j
  rw [C12, Matrix.circulant_apply]
  by_cases h : (i - j = 1 ∨ i - j = -1)
  · rw [show cycAdj (i - j) = 1 from ite_eq_left h]
    exact (ite_eq_left ((cycleGraph12_adj_iff i j).mpr h)).symm
  · rw [show cycAdj (i - j) = 0 from ite_eq_right h]
    exact (ite_eq_right (fun hadj => h ((cycleGraph12_adj_iff i j).mp hadj))).symm

/-- **THE PAYOFF (T2 ⋈ T1).** `C12` is diagonalized by the DFT basis: every basis vector
    `dftChar_basis k` is an eigenvector of `C12` with eigenvalue `dft cycAdj k`. The eigenvectors
    range over a genuine basis (`dftChar_basis`), so the DFT is a full diagonalizing eigenbasis of the
    chromatic cycle graph's adjacency operator. -/
theorem C12_diagonalized_by_dftChar_basis (k : ZMod 12) :
    C12 *ᵥ (dftChar_basis k) = (ZMod.dft cycAdj k) • (dftChar_basis k) := by
  rw [dftChar_basis_apply]; exact C12_mulVec_dftChar k

/-! ### The spectrum of every abelian Cayley graph.

C₁₂ is one instance of a general fact: an abelian Cayley graph `Cay(ℤ_N, S)` — equivalently Mathlib's
`circulantGraph S` over `ZMod N` — has adjacency operator the circulant of the connection-set indicator
`1_S`, so by T1 it is diagonalized by the DFT characters with eigenvalue the character sum
`∑_{s∈S} stdAddChar(-(s·k))` (Babai's formula for abelian Cayley spectra). The bridge `cayleyAdj S =
circulantGraph S` mirrors T4's `C12_eq_adjMatrix`, now for an arbitrary SYMMETRIC, `0∉S` connection set.
Folklore (Babai 1979, Lovász). -/

/-- The connection-set indicator `1_S` on `ZMod N` (first column of the Cayley adjacency matrix). -/
noncomputable def cayleyAdjVec (S : Finset (ZMod N)) : ZMod N → ℂ := fun m => if m ∈ S then 1 else 0

/-- The adjacency operator of the abelian Cayley graph `Cay(ℤ_N, S)`, as a circulant over ℂ. -/
noncomputable def cayleyAdj (S : Finset (ZMod N)) : Matrix (ZMod N) (ZMod N) ℂ :=
  Matrix.circulant (cayleyAdjVec S)

/-- **Abelian Cayley diagonalization (C-2).** Every abelian Cayley graph is diagonalized by the DFT
    characters: `cayleyAdj S *ᵥ dftChar k = (dft 1_S k) • dftChar k`. Direct specialization of T1. -/
theorem cayleyAdj_mulVec_dftChar (S : Finset (ZMod N)) (k : ZMod N) :
    cayleyAdj S *ᵥ (dftChar k) = (ZMod.dft (cayleyAdjVec S) k) • dftChar k :=
  circulant_mulVec_dftChar (cayleyAdjVec S) k

/-- **The abelian Cayley eigenvalue = the character sum (C-2, Babai's formula).** The k-th eigenvalue is
    `dft 1_S k = ∑_{s∈S} stdAddChar(-(s·k))` — sum of the k-th character over the connection set. -/
theorem cayleyAdj_eigenvalue (S : Finset (ZMod N)) (k : ZMod N) :
    ZMod.dft (cayleyAdjVec S) k = ∑ s ∈ S, stdAddChar (-(s * k)) := by
  have hzero : ∀ x ∈ (Finset.univ : Finset (ZMod N)), x ∉ S →
      stdAddChar (-(x * k)) • cayleyAdjVec S x = 0 := by
    intro x _ hx; unfold cayleyAdjVec; rw [ite_eq_right hx, smul_zero]
  rw [ZMod.dft_apply, ← Finset.sum_subset (Finset.subset_univ S) hzero]
  apply Finset.sum_congr rfl
  intro s hs; unfold cayleyAdjVec; rw [ite_eq_left hs, smul_eq_mul, mul_one]

omit [NeZero N] in
/-- **The abelian Cayley graph bridge (C-2, mirrors T4).** For a SYMMETRIC connection set `S` not
    containing `0`, the circulant `cayleyAdj S` IS the adjacency matrix of Mathlib's `circulantGraph S`.
    Combined with `cayleyAdj_eigenvalue` this gives the spectrum of every such abelian Cayley graph. -/
theorem cayleyAdj_eq_adjMatrix (S : Finset (ZMod N))
    (hsymm : ∀ x : ZMod N, x ∈ S → -x ∈ S) (h0 : (0 : ZMod N) ∉ S) :
    cayleyAdj S = (SimpleGraph.circulantGraph (S : Set (ZMod N))).adjMatrix ℂ := by
  have hadj : ∀ i j : ZMod N,
      (SimpleGraph.circulantGraph (S : Set (ZMod N))).Adj i j ↔ (i - j ∈ S) := by
    intro i j
    rw [SimpleGraph.circulantGraph_adj]
    simp only [Finset.mem_coe]
    constructor
    · rintro ⟨_, h | h⟩
      · exact h
      · have : -(j - i) ∈ S := hsymm _ h
        rwa [neg_sub] at this
    · intro h
      refine ⟨fun hij => h0 ?_, Or.inl h⟩
      rwa [sub_eq_zero.mpr hij] at h
  ext i j
  rw [cayleyAdj, Matrix.circulant_apply, SimpleGraph.adjMatrix_apply]
  unfold cayleyAdjVec
  by_cases h : i - j ∈ S
  · rw [ite_eq_left h, ite_eq_left ((hadj i j).mpr h)]
  · rw [ite_eq_right h, ite_eq_right (fun ha => h ((hadj i j).mp ha))]

/-- **Instantiation: C₁₂ is the abelian Cayley graph `Cay(ℤ₁₂, {±1})`.** The semitone indicator
    `cycAdj` is `1_{{1,-1}}`, so `C12 = cayleyAdj {1, -1}` — C₁₂ is the C-2 lemma at `S = {1, -1}`. -/
example : C12 = cayleyAdj ({1, -1} : Finset (ZMod 12)) := by
  rw [C12, cayleyAdj]
  congr 1
  funext m
  unfold cycAdj cayleyAdjVec
  simp only [Finset.mem_insert, Finset.mem_singleton]

end CycleGraphSpectrum

end MusicTheory
