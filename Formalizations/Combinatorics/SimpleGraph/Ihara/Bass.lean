/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Dart
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Bass's determinant formula for the Ihara zeta function

For a finite simple graph with adjacency matrix `A`, degree matrix `D` and non-backtracking
(Hashimoto) operator `B` on darts, and `u` in a field,

`(1 - u²)^|V| · det(1 - u B) = (1 - u²)^|E| · det(1 - u A + u² (D - 1))`.

The left determinant is the reciprocal of the Ihara zeta function. The proof writes
`B = Tᵀ S - J` with the start and terminus incidence matrices `S`, `T` and the dart reversal `J`,
computes `det(1 + u J) = (1 - u²)^|E|` through the splitting of darts into positively and negatively
oriented ones, and applies Sylvester's determinant identity.

## Main definitions

* `SimpleGraph.reversal`, `SimpleGraph.hashimoto`, `SimpleGraph.startInc`, `SimpleGraph.termInc`:
  the dart reversal, the non-backtracking operator and the start and terminus incidence matrices.
  The degree matrix is Mathlib's `SimpleGraph.degMatrix`.
* `SimpleGraph.dartEquiv`: `G.Dart ≃ Bool × {positive darts}` for a linear order on `V`.

## Main results

* `SimpleGraph.bass_determinant`: Bass's determinant formula.

## References

* H. Bass, *The Ihara–Selberg zeta function of a tree lattice*, Internat. J. Math. 3 (1992)
  717–797.
* A. Terras, *Zeta Functions of Graphs: A Stroll through the Garden*, Cambridge University Press,
  2011.
-/

@[expose] public section

open scoped Classical
open Matrix Finset

-- These lemmas share one `variable` block; some don't touch every instance, and a
-- couple of `<;>` chains act on a single goal. Both are cosmetic in this self-contained file.
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The dart-reversal permutation matrix `J`: `J d e = 1` iff `e = d.symm`. -/
def reversal (R : Type*) [CommRing R] : Matrix G.Dart G.Dart R :=
  Matrix.of fun d e => if e = d.symm then (1 : R) else 0

/-- The Hashimoto / non-backtracking edge operator `B`:
`B d e = 1` iff the head of `d` is the tail of `e` and `e` is not the reverse of
`d` (i.e. `d` may be followed by `e` without backtracking). -/
def hashimoto (R : Type*) [CommRing R] : Matrix G.Dart G.Dart R :=
  Matrix.of fun d e => if d.snd = e.fst ∧ e ≠ d.symm then (1 : R) else 0

/-- Start incidence matrix `S`: `S v d = 1` iff `d` originates at `v`. -/
def startInc (R : Type*) [CommRing R] : Matrix V G.Dart R :=
  Matrix.of fun v d => if d.fst = v then (1 : R) else 0

/-- Terminus incidence matrix `T`: `T v d = 1` iff `d` terminates at `v`. -/
def termInc (R : Type*) [CommRing R] : Matrix V G.Dart R :=
  Matrix.of fun v d => if d.snd = v then (1 : R) else 0

/-! ### Incidence layer — step 1 of the proof (all numerically pre-verified) -/

section Incidence
variable (R : Type*) [CommRing R]

@[simp] lemma startInc_apply (v : V) (d : G.Dart) :
    G.startInc R v d = if d.fst = v then 1 else 0 := rfl
@[simp] lemma termInc_apply (v : V) (d : G.Dart) :
    G.termInc R v d = if d.snd = v then 1 else 0 := rfl
@[simp] lemma reversal_apply (d e : G.Dart) :
    G.reversal R d e = if e = d.symm then 1 else 0 := rfl
@[simp] lemma hashimoto_apply (d e : G.Dart) :
    G.hashimoto R d e = if d.snd = e.fst ∧ e ≠ d.symm then 1 else 0 := rfl

/-- Number of darts with prescribed endpoints `(v, w)` is `1` iff `v ~ w`. -/
lemma adj_dart_card (v w : V) :
    #{d : G.Dart | d.fst = v ∧ d.snd = w} = if G.Adj v w then 1 else 0 := by
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨⟨(v, w), h⟩, Finset.eq_singleton_iff_unique_mem.mpr ⟨by simp, fun d hd => ?_⟩⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    exact Dart.ext _ _ (Prod.ext_iff.mpr ⟨hd.1, hd.2⟩)
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro d - ⟨h1, h2⟩
    exact h (h1 ▸ h2 ▸ d.adj)

/-- `S Tᵀ = A`: darts from `v` to `w` realise the adjacency matrix. -/
lemma startInc_mul_termInc_transpose :
    G.startInc R * (G.termInc R)ᵀ = G.adjMatrix R := by
  ext v w
  rw [Matrix.mul_apply, adjMatrix_apply]
  simp only [Matrix.transpose_apply, startInc_apply, termInc_apply]
  have step : ∀ d : G.Dart, (if d.fst = v then (1 : R) else 0) * (if d.snd = w then 1 else 0)
      = if (d.fst = v ∧ d.snd = w) then 1 else 0 := by
    intro d; split_ifs <;> simp_all
  rw [Finset.sum_congr rfl (fun d _ => step d), Finset.sum_boole, adj_dart_card]
  split_ifs <;> simp

/-- `S Sᵀ = D`: the start-incidence Gram matrix is the degree matrix. -/
lemma startInc_mul_startInc_transpose :
    G.startInc R * (G.startInc R)ᵀ = G.degMatrix R := by
  ext v w
  rw [Matrix.mul_apply, degMatrix, Matrix.diagonal_apply]
  simp only [Matrix.transpose_apply, startInc_apply]
  split_ifs with hvw
  · subst hvw
    have step : ∀ d : G.Dart, (if d.fst = v then (1 : R) else 0) * (if d.fst = v then 1 else 0)
        = if d.fst = v then 1 else 0 := by intro d; split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun d _ => step d), Finset.sum_boole,
      dart_fst_fiber_card_eq_degree]
  · apply Finset.sum_eq_zero
    intro d _
    split_ifs with h1 h2 <;> simp_all

/-- `B = Tᵀ S − J`: the Hashimoto operator removes backtracking from `Tᵀ S`. -/
lemma hashimoto_eq :
    G.hashimoto R = (G.termInc R)ᵀ * G.startInc R - G.reversal R := by
  ext d e
  rw [Matrix.sub_apply, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, termInc_apply, startInc_apply, reversal_apply,
    hashimoto_apply]
  have hsum : (∑ x : V, (if d.snd = x then (1 : R) else 0) * (if e.fst = x then 1 else 0))
      = if d.snd = e.fst then 1 else 0 := by
    rw [Finset.sum_eq_single d.snd]
    · rw [ite_eq_left rfl, one_mul]
      by_cases hc : d.snd = e.fst
      · rw [ite_eq_left hc, ite_eq_left hc.symm]
      · rw [ite_eq_right hc, ite_eq_right fun h => hc h.symm]
    · intro x _ hx; rw [ite_eq_right (Ne.symm hx), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsum]
  by_cases hsy : e = d.symm
  · subst hsy; simp
  · simp [hsy]

/-- `S J = T`: pre-composing start-incidence with reversal gives terminus-incidence. -/
lemma startInc_mul_reversal :
    G.startInc R * G.reversal R = G.termInc R := by
  ext v e
  rw [Matrix.mul_apply]
  simp only [startInc_apply, reversal_apply, termInc_apply]
  rw [Finset.sum_eq_single e.symm]
  · have hfst : e.symm.fst = e.snd := rfl
    simp only [Dart.symm_symm, hfst, ite_true, mul_one]
  · intro d _ hd
    have : e ≠ d.symm := fun he => hd (by rw [he, Dart.symm_symm])
    rw [ite_eq_right this, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `J` is symmetric: reversal is its own transpose (since `symm` is an involution). -/
lemma reversal_transpose : (G.reversal R)ᵀ = G.reversal R := by
  ext d e
  simp only [Matrix.transpose_apply, reversal_apply]
  by_cases h : e = d.symm
  · rw [ite_eq_left h, ite_eq_left (show d = e.symm by rw [h, Dart.symm_symm])]
  · rw [ite_eq_right h, ite_eq_right (show ¬ d = e.symm from fun hd => h (by rw [hd, Dart.symm_symm]))]

/-- `J² = I`: reversal is an involution. -/
lemma reversal_mul_self : G.reversal R * G.reversal R = 1 := by
  ext d e
  rw [Matrix.mul_apply]
  simp only [reversal_apply]
  rw [Finset.sum_eq_single d.symm]
  · rw [ite_eq_left rfl, one_mul, Dart.symm_symm, Matrix.one_apply]
    by_cases h : d = e
    · rw [ite_eq_left h.symm, ite_eq_left h]
    · rw [ite_eq_right fun he => h he.symm, ite_eq_right h]
  · intro f _ hf; rw [ite_eq_right hf, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `T Tᵀ = D`: via `T = S J`, `Jᵀ = J`, `J² = I`, and `S Sᵀ = D`. -/
lemma termInc_mul_termInc_transpose :
    G.termInc R * (G.termInc R)ᵀ = G.degMatrix R := by
  have hT : G.termInc R = G.startInc R * G.reversal R := (G.startInc_mul_reversal R).symm
  rw [hT, Matrix.transpose_mul, reversal_transpose, Matrix.mul_assoc,
    ← Matrix.mul_assoc (G.reversal R), reversal_mul_self, Matrix.one_mul,
    startInc_mul_startInc_transpose]

/-- The algebraic heart of `det(I + uJ) = (1 - u²)^m`:
`(I + uJ)(I − uJ) = (1 − u²) I`, since `J² = I`. -/
lemma one_add_smul_reversal_mul (u : R) :
    (1 + u • G.reversal R) * (1 - u • G.reversal R)
      = (1 - u ^ 2) • (1 : Matrix G.Dart G.Dart R) := by
  have key : (u • G.reversal R) * (u • G.reversal R)
      = u ^ 2 • (1 : Matrix G.Dart G.Dart R) := by
    rw [smul_mul_smul_comm, G.reversal_mul_self R, pow_two]
  rw [mul_sub, mul_one, add_mul, one_mul, key, sub_smul, one_smul]
  abel

/-- Determinant consequence: `det(I + uJ) · det(I − uJ) = (1 − u²)^{2m}`
(here `2m = |Dart|`). The individual factor `det(I + uJ) = (1 − u²)^m` needs the
orientation reindex `Dart ≃ edges × Fin 2` — the next lemma. -/
lemma det_one_add_smul_reversal_mul (u : R) :
    (1 + u • G.reversal R).det * (1 - u • G.reversal R).det
      = (1 - u ^ 2) ^ Fintype.card G.Dart := by
  rw [← Matrix.det_mul, one_add_smul_reversal_mul, Matrix.det_smul, Matrix.det_one, mul_one]

end Incidence

/-! ### Orientation reindex — toward `det(I + uJ) = (1 - u²)^m`

With a linear order on the vertices, each edge has a unique "positive" dart
(tail < head); a general dart is that positive dart together with a sign bit.
This realises `Dart ≃ Bool × PosDart`, under which `J = reversal` becomes a
block-diagonal of `2×2` swaps — the route to `det(I + uJ) = (1 - u²)^m`. -/

section Orientation
variable [LinearOrder V]

/-- A dart is positive when its tail precedes its head. -/
def IsPos (d : G.Dart) : Prop := d.fst < d.snd

instance : DecidablePred G.IsPos := fun d => (inferInstance : Decidable (d.fst < d.snd))

/-- If a dart is not positive, its reverse is. -/
lemma isPos_symm_of_not {d : G.Dart} (h : ¬ G.IsPos d) : G.IsPos d.symm :=
  lt_of_le_of_ne (not_lt.mp h) d.snd_ne_fst

/-- Orientation reindex: a dart is a chosen positive dart plus a sign bit. -/
def dartEquiv : G.Dart ≃ Bool × {d : G.Dart // G.IsPos d} where
  toFun d := if h : G.IsPos d then (true, ⟨d, h⟩) else (false, ⟨d.symm, G.isPos_symm_of_not h⟩)
  invFun p := if p.1 then p.2.1 else p.2.1.symm
  left_inv d := by
    by_cases h : G.IsPos d
    · simp [h]
    · simp [h, Dart.symm_symm]
  right_inv := by
    rintro ⟨b, q, hq⟩
    cases b
    · have hneg : ¬ G.IsPos q.symm := by
        show ¬ (q.snd < q.fst); exact not_lt.mpr (le_of_lt hq)
      simp [hneg, Dart.symm_symm]
    · simp [hq]

/-- The positive darts are in bijection with the edges: `|PosDart| = |E|`.
Proof: `dartEquiv` gives `|Dart| = 2·|PosDart|`, and the handshake lemma gives
`|Dart| = 2·|E|`; cancel the `2`. -/
lemma card_posDart : Fintype.card {d : G.Dart // G.IsPos d} = G.edgeFinset.card := by
  have h1 : Fintype.card G.Dart = 2 * Fintype.card {d : G.Dart // G.IsPos d} := by
    rw [Fintype.card_congr G.dartEquiv, Fintype.card_prod, Fintype.card_bool]
  have h2 : Fintype.card G.Dart = 2 * G.edgeFinset.card := by
    rw [dart_card_eq_sum_degrees, sum_degrees_eq_twice_card_edges]
  omega

/-- A dart never equals its own reverse. -/
lemma dart_ne_symm (d : G.Dart) : d ≠ d.symm :=
  fun h => d.fst_ne_snd (congrArg (fun e : G.Dart => e.fst) h)

@[simp] lemma dartEquiv_symm_apply (b : Bool) (p : {d : G.Dart // G.IsPos d}) :
    G.dartEquiv.symm (b, p) = if b then (p : G.Dart) else (p : G.Dart).symm := rfl

/-- Reversing a dart flips the orientation bit. -/
lemma dartEquiv_symm_symm (b : Bool) (p : {d : G.Dart // G.IsPos d}) :
    (G.dartEquiv.symm (b, p)).symm = G.dartEquiv.symm (!b, p) := by
  cases b <;> simp [Dart.symm_symm]

end Orientation

/-- The `2×2` sign block `[[1,u],[u,1]]` (indexed by `Bool`). -/
def signBlock (R : Type*) [CommRing R] (u : R) : Matrix Bool Bool R :=
  Matrix.of fun b1 b2 => if b1 = b2 then 1 else u

@[simp] lemma signBlock_apply (R : Type*) [CommRing R] (u : R) (b1 b2 : Bool) :
    signBlock R u b1 b2 = if b1 = b2 then 1 else u := rfl

lemma det_signBlock (R : Type*) [CommRing R] (u : R) : (signBlock R u).det = 1 - u ^ 2 := by
  rw [← Matrix.det_reindex_self finTwoEquiv.symm, Matrix.det_fin_two]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, signBlock_apply,
    EmbeddingLike.apply_eq_iff_eq]
  norm_num
  ring

/-- **`det(I + uJ) = (1 - u²)^m`.** Reindex by `dartEquiv` turns `I + uJ` into a
block-diagonal of `2×2` sign blocks (one per edge); `det_blockDiagonal` then gives
`(det signBlock)^|E| = (1 - u²)^|E|`. -/
lemma det_one_add_smul_reversal (R : Type*) [CommRing R] [LinearOrder V] (u : R) :
    (1 + u • G.reversal R).det = (1 - u ^ 2) ^ G.edgeFinset.card := by
  rw [← Matrix.det_reindex_self G.dartEquiv]
  have hblock : Matrix.reindex G.dartEquiv G.dartEquiv (1 + u • G.reversal R)
      = Matrix.blockDiagonal (fun _ : {d : G.Dart // G.IsPos d} => signBlock R u) := by
    ext ⟨i1, p1⟩ ⟨i2, p2⟩
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply, Matrix.one_apply,
      Matrix.smul_apply, reversal_apply, smul_eq_mul, Matrix.blockDiagonal_apply, signBlock_apply]
    rw [dartEquiv_symm_symm]
    simp only [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, eq_comm (a := p2) (b := p1)]
    cases i1 <;> cases i2 <;> by_cases hp : p1 = p2 <;> simp_all
  rw [hblock, Matrix.det_blockDiagonal]
  simp only [Finset.prod_const, Finset.card_univ, card_posDart, det_signBlock]

/-- `det(I − uJ) = (1 − u²)^|E|` (same blockDiagonal argument, via `u ↦ -u`). -/
lemma det_one_sub_smul_reversal (R : Type*) [CommRing R] [LinearOrder V] (u : R) :
    (1 - u • G.reversal R).det = (1 - u ^ 2) ^ G.edgeFinset.card := by
  have h := G.det_one_add_smul_reversal R (-u)
  rw [neg_smul, ← sub_eq_add_neg, neg_sq] at h
  exact h

/-- `I − uB = (I + uJ) − u·TᵀS`, from `B = TᵀS − J`. -/
lemma one_sub_smul_hashimoto (R : Type*) [CommRing R] (u : R) :
    1 - u • G.hashimoto R
      = (1 + u • G.reversal R) - u • ((G.termInc R)ᵀ * G.startInc R) := by
  rw [hashimoto_eq, smul_sub]
  abel

/-- `S(I − uJ)Tᵀ = A − uD`. -/
lemma startInc_mul_one_sub_smul_reversal_mul_termInc (R : Type*) [CommRing R] (u : R) :
    G.startInc R * (1 - u • G.reversal R) * (G.termInc R)ᵀ
      = G.adjMatrix R - u • G.degMatrix R := by
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, startInc_mul_reversal,
    Matrix.sub_mul, startInc_mul_termInc_transpose, Matrix.smul_mul,
    termInc_mul_termInc_transpose]


/-- **Bass's determinant formula** (division-free form, over a field).

`(1 - u²)^|V| · det(I - u·B) = (1 - u²)^|E| · det(I - u·A + u²·(D - I))`,

with `B` the Hashimoto operator on darts, `A` the adjacency matrix, `D` the
degree matrix. Equivalent to `det(I - uB) = (1-u²)^{|E|-|V|} det(I - uA + (D-I)u²)`.
Proved over a field (the standard setting); the Sylvester step inverts `I + uJ`,
which is a unit exactly when `1 - u² ≠ 0`. -/
theorem bass_determinant (R : Type*) [Field R] [LinearOrder V] (u : R) :
    (1 - u ^ 2) ^ (Fintype.card V) * (1 - u • G.hashimoto R).det
      = (1 - u ^ 2) ^ G.edgeFinset.card
        * (1 - u • G.adjMatrix R + u ^ 2 • (G.degMatrix R - 1)).det := by
  by_cases hc : (1 - u ^ 2 : R) = 0
  · -- degenerate value u² = 1: only no-edge / empty graphs carry content
    by_cases hm : G.edgeFinset.card = 0
    · have hnoadj : ∀ v w, ¬ G.Adj v w := fun v w hvw => by
        have h0 : 0 < G.edgeFinset.card :=
          Finset.card_pos.mpr ⟨s(v, w), SimpleGraph.mem_edgeFinset.mpr hvw⟩
        omega
      have hA : G.adjMatrix R = 0 := by
        ext v w; simp [SimpleGraph.adjMatrix_apply, hnoadj v w]
      have hD : G.degMatrix R = 0 := by
        ext v w
        have hemp : G.neighborFinset v = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
          (fun x hx => hnoadj v x (by simpa using hx))
        have hdeg : G.degree v = 0 := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree, hemp, Finset.card_empty]
        simp [degMatrix, Matrix.diagonal_apply, hdeg]
      have hMeq : (1 - u • G.adjMatrix R + u ^ 2 • (G.degMatrix R - 1))
          = (1 - u ^ 2) • (1 : Matrix V V R) := by
        rw [hA, hD]; module
      rw [hMeq, hc, zero_smul, hm, pow_zero, one_mul]
      rcases Nat.eq_zero_or_pos (Fintype.card V) with hn | hn
      · have : IsEmpty V := Fintype.card_eq_zero_iff.mp hn
        have : IsEmpty G.Dart := Function.isEmpty Dart.toProd
        rw [hn, pow_zero, one_mul, Matrix.det_isEmpty, Matrix.det_isEmpty]
      · have : Nonempty V := Fintype.card_pos_iff.mp hn
        rw [zero_pow hn.ne', zero_mul, Matrix.det_zero]
    · have hn : Fintype.card V ≠ 0 := fun h => hm (by
        have : IsEmpty V := Fintype.card_eq_zero_iff.mp h
        simp [Finset.eq_empty_of_isEmpty])
      rw [hc, zero_pow hn, zero_pow hm, zero_mul, zero_mul]
  · have hUnit : IsUnit (1 + u • G.reversal R).det := by
      rw [G.det_one_add_smul_reversal R u]; exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ hc)
    have hinv : (1 + u • G.reversal R)⁻¹ = (1 - u ^ 2)⁻¹ • (1 - u • G.reversal R) := by
      refine Matrix.inv_eq_right_inv ?_
      rw [Matrix.mul_smul, G.one_add_smul_reversal_mul R u, smul_smul, inv_mul_cancel₀ hc, one_smul]
    have hstep2 : G.startInc R * (1 + u • G.reversal R)⁻¹ * (G.termInc R)ᵀ
        = (1 - u ^ 2)⁻¹ • (G.adjMatrix R - u • G.degMatrix R) := by
      rw [hinv]
      simp only [Matrix.mul_smul, Matrix.smul_mul]
      rw [G.startInc_mul_one_sub_smul_reversal_mul_termInc R u]
    have hfact : (1 + u • G.reversal R)
        * (1 - (1 + u • G.reversal R)⁻¹ * (u • ((G.termInc R)ᵀ * G.startInc R)))
        = 1 - u • G.hashimoto R := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hUnit,
        Matrix.one_mul, ← one_sub_smul_hashimoto]
    have hdetB : (1 - u • G.hashimoto R).det
        = (1 - u ^ 2) ^ G.edgeFinset.card
          * (1 - u • (G.startInc R * (1 + u • G.reversal R)⁻¹ * (G.termInc R)ᵀ)).det := by
      rw [← hfact, Matrix.det_mul, G.det_one_add_smul_reversal R u]
      congr 1
      rw [show (1 + u • G.reversal R)⁻¹ * (u • ((G.termInc R)ᵀ * G.startInc R))
            = ((1 + u • G.reversal R)⁻¹ * (u • (G.termInc R)ᵀ)) * G.startInc R by
          rw [Matrix.mul_assoc, Matrix.smul_mul],
        Matrix.det_one_sub_mul_comm]
      congr 2
      rw [← Matrix.mul_assoc, Matrix.mul_smul]
    rw [hdetB, hstep2,
      show (1 : Matrix V V R) - u • ((1 - u ^ 2)⁻¹ • (G.adjMatrix R - u • G.degMatrix R))
          = (1 - u ^ 2)⁻¹ • (1 - u • G.adjMatrix R + u ^ 2 • (G.degMatrix R - 1)) by
        rw [smul_smul]; match_scalars <;> field_simp; ring,
      Matrix.det_smul, inv_pow]
    field_simp

end SimpleGraph
