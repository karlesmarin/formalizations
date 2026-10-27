/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Combinatorics.Configuration
public import Mathlib.NumberTheory.SumFourSquares
public import Mathlib.NumberTheory.SumTwoSquares
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Data.Matrix.Block
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The Bruck–Ryser–Chowla theorem for projective planes

If a finite projective plane of order `n` exists (Mathlib's `Configuration.ProjectivePlane`) and
`n ≡ 1` or `2 (mod 4)`, then `n` is a sum of two squares; in particular there are no planes of order
6 or 14. With points and lines matched by a bijection, the incidence matrix scales the dot product
of zero-sum vectors by `n` (two points lie on `n + 1` common lines if equal and on one otherwise).
Padding to dimension `n² + n + 2 ≡ 0 (mod 4)`, Lagrange's four squares (`Nat.sum_four_squares`) and
Euler's 4×4 blocks give a rational `M` with `M Mᵀ = n I`. An isometry-extension lemma for the
standard form on `ℚⁿ` (a case of Witt's theorem, by reflections) then yields a vector of squared
length `n` constant on lines, i.e. `n = d² + (n² + n + 1) c²` with rational `c, d`; a descent modulo
primes `q ≡ 3 (mod 4)` and `Nat.eq_sq_add_sq_iff` turn this into two integer squares.

## Main results

* `BruckRyserChowla.exists_sq_add_sq`: projective plane of order n = 1, 2 mod 4: n is a sum of two squares
* `BruckRyserChowla.exists_isometry`: extension of isometries for the standard form on Q^n (a case of Witt)
* `BruckRyserChowla.exists_orthogonal_vector`: a rational vector of squared length n constant on the lines
* `BruckRyserChowla.exists_sq_add_sq_of_rat`: n z^2 = x^2 + y^2 over Q with z != 0 gives n a sum of two integer squares

## References

* R. H. Bruck and H. J. Ryser, *The nonexistence of certain finite projective planes*, Canad. J. Math. 1 (1949), 88–93.
* S. Chowla and H. J. Ryser, *Combinatorial problems*, Canad. J. Math. 2 (1950), 93–99.
* Witt's extension theorem in general (not used here) is in facebookresearch/atlas-lean, `v1/Atlas/Buildings/code/GeometricAlgebra/ExtendingIsometries.lean`.
-/

@[expose] public section

open Configuration

namespace BruckRyserChowla

open Matrix

/-! ### Part B: extension of finite families of isometries on `ι → ℚ` (Witt-style) -/

section Extension

variable {ι κ : Type*} [Fintype ι]

/-- Reflection of `ι → ℚ` in the hyperplane orthogonal to `d` (identity when `d = 0`). -/
private noncomputable def refl (d x : ι → ℚ) : ι → ℚ :=
  if d = 0 then x else x - (2 * (x ⬝ᵥ d) / (d ⬝ᵥ d)) • d

private lemma refl_dot (d x y : ι → ℚ) : refl d x ⬝ᵥ refl d y = x ⬝ᵥ y := by
  unfold refl
  split_ifs with h
  · rfl
  · have hd : d ⬝ᵥ d ≠ 0 := fun h0 => h (dotProduct_self_eq_zero.mp h0)
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm d y]
    field_simp
    ring

private lemma refl_fix (d x : ι → ℚ) (h : x ⬝ᵥ d = 0) : refl d x = x := by
  unfold refl
  split_ifs <;> simp [h]

/-- Finite families with equal Gram matrices are related by an isometry of `ι → ℚ`. -/
theorem exists_isometry (s : List κ) (u v : κ → ι → ℚ)
    (h : ∀ a ∈ s, ∀ b ∈ s, u a ⬝ᵥ u b = v a ⬝ᵥ v b) :
    ∃ O : (ι → ℚ) → (ι → ℚ), (∀ x y, O x ⬝ᵥ O y = x ⬝ᵥ y) ∧ ∀ a ∈ s, O (u a) = v a := by
  induction s with
  | nil => exact ⟨id, fun _ _ => rfl, by simp⟩
  | cons a s ih =>
    obtain ⟨O', hO'1, hO'2⟩ := ih (fun b hb c hc => h b (List.mem_cons_of_mem _ hb) c
      (List.mem_cons_of_mem _ hc))
    set x := O' (u a) with hx
    set d := x - v a with hd
    have hxx : x ⬝ᵥ x = v a ⬝ᵥ v a := by
      rw [hx, hO'1]; exact h a (List.mem_cons_self) a (List.mem_cons_self)
    have horth : ∀ b ∈ s, v b ⬝ᵥ d = 0 := by
      intro b hb
      have h1 : O' (u b) = v b := hO'2 b hb
      have h2 := h a (List.mem_cons_self) b (List.mem_cons_of_mem _ hb)
      have e1 : O' (u b) ⬝ᵥ x = u b ⬝ᵥ u a := by rw [hx, hO'1]
      rw [h1, dotProduct_comm (u b), h2, dotProduct_comm] at e1
      rw [hd, dotProduct_sub, dotProduct_comm (v b) x, e1, dotProduct_comm (v a) (v b), sub_self]
    refine ⟨fun z => refl d (O' z), fun z w => by rw [refl_dot, hO'1], ?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · show refl d x = v b
      unfold refl
      split_ifs with h0
      · rw [hd] at h0; exact sub_eq_zero.mp h0
      · have hdd : d ⬝ᵥ d = 2 * (x ⬝ᵥ d) := by
          have : d ⬝ᵥ d = x ⬝ᵥ x - 2 * (x ⬝ᵥ v b) + v b ⬝ᵥ v b := by
            rw [hd]
            simp only [sub_dotProduct, dotProduct_sub, dotProduct_comm (v b) x]
            ring
          have h3 : x ⬝ᵥ d = x ⬝ᵥ x - x ⬝ᵥ v b := by rw [hd, dotProduct_sub]
          rw [this, h3, hxx]; ring
        have hd0 : d ⬝ᵥ d ≠ 0 := fun h0' => h0 (dotProduct_self_eq_zero.mp h0')
        have : 2 * (x ⬝ᵥ d) / (d ⬝ᵥ d) = 1 := by
          rw [hdd] at hd0 ⊢; exact div_self hd0
        rw [this, one_smul, hd]; abel
    · show refl d (O' (u b)) = v b
      rw [hO'2 b hb]
      exact refl_fix d _ (horth b hb)

end Extension

/-! ### Part C: Euler's four-square similarity on `ι → ℚ` when `4 ∣ card ι` -/

section Euler

/-- Left multiplication by the quaternion `a + bi + cj + dk` as a rational `4 × 4` matrix. -/
private def eulerMat (a b c d : ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  !![a, -b, -c, -d; b, a, -d, c; c, d, a, -b; d, -c, b, a]

private lemma eulerMat_mul_transpose (a b c d : ℚ) :
    eulerMat a b c d * (eulerMat a b c d)ᵀ = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerMat, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

private lemma eulerMat_transpose_mul (a b c d : ℚ) :
    (eulerMat a b c d)ᵀ * eulerMat a b c d = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerMat, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/-- A rational similarity of ratio `n` on `ι → ℚ`, as soon as `n` is a sum of four squares
and `4 ∣ card ι`. -/
private lemma exists_similarity {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ)
    (h4 : 4 ∣ Fintype.card ι) :
    ∃ M : Matrix ι ι ℚ, M * Mᵀ = (n : ℚ) • 1 ∧ Mᵀ * M = (n : ℚ) • 1 := by
  obtain ⟨a, b, c, d, habcd⟩ := Nat.sum_four_squares n
  obtain ⟨k, hk⟩ := h4
  let e : ι ≃ Fin 4 × Fin k := Fintype.equivOfCardEq (by simp [hk])
  have hn : ((a : ℚ) ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) = n := by exact_mod_cast habcd
  have key : ∀ B C : Matrix (Fin 4) (Fin 4) ℚ, B * C = (n : ℚ) • 1 →
      ((Matrix.blockDiagonal fun _ : Fin k => B).submatrix e e) *
        ((Matrix.blockDiagonal fun _ : Fin k => C).submatrix e e) = (n : ℚ) • 1 := by
    intro B C hBC
    rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal_mul]
    simp only [hBC]
    show (Matrix.blockDiagonal ((n : ℚ) • (1 : Fin k → Matrix (Fin 4) (Fin 4) ℚ))).submatrix e e
      = _
    rw [Matrix.blockDiagonal_smul, Matrix.blockDiagonal_one]
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply, e.injective.eq_iff]
  refine ⟨(Matrix.blockDiagonal fun _ : Fin k => eulerMat a b c d).submatrix e e, ?_, ?_⟩
  · rw [Matrix.transpose_submatrix, Matrix.blockDiagonal_transpose]
    exact key _ _ (by rw [eulerMat_mul_transpose, hn])
  · rw [Matrix.transpose_submatrix, Matrix.blockDiagonal_transpose]
    exact key _ _ (by rw [eulerMat_transpose_mul, hn])

private lemma sim_dot {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℚ} {n : ℚ}
    (h : Mᵀ * M = n • 1) (x y : ι → ℚ) : (M *ᵥ x) ⬝ᵥ (M *ᵥ y) = n * (x ⬝ᵥ y) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h,
    Matrix.smul_mulVec, Matrix.one_mulVec, smul_dotProduct, smul_eq_mul]

private lemma adj_dot {ι : Type*} [Fintype ι] (M : Matrix ι ι ℚ) (p g : ι → ℚ) :
    (Mᵀ *ᵥ p) ⬝ᵥ g = p ⬝ᵥ (M *ᵥ g) := by
  rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]

/-- **Algebraic core.** Let `u a` and `g a` be families in `ι → ℚ`, with `4 ∣ card ι`, such that
the Gram matrix of `u` is `n` times that of `g`, and let `ε` be a unit vector orthogonal to all
`u a`. Then some vector of squared norm `n` is orthogonal to all `g a`. -/
theorem exists_orthogonal_vector {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (n : ℕ) (h4 : 4 ∣ Fintype.card ι) (u g : κ → ι → ℚ) (ε : ι → ℚ)
    (hG : ∀ a b, u a ⬝ᵥ u b = n * (g a ⬝ᵥ g b)) (hε : ∀ a, ε ⬝ᵥ u a = 0)
    (hε1 : ε ⬝ᵥ ε = 1) :
    ∃ r : ι → ℚ, (∀ a, r ⬝ᵥ g a = 0) ∧ r ⬝ᵥ r = n := by
  obtain ⟨M, hM1, hM2⟩ := exists_similarity (ι := ι) n h4
  obtain ⟨O, hO1, hO2⟩ := exists_isometry (Finset.univ : Finset κ).toList u (fun a => M *ᵥ g a)
    (fun a _ b _ => by rw [hG, sim_dot hM2])
  have hO2' : ∀ a, O (u a) = M *ᵥ g a := fun a => hO2 a (by simp)
  refine ⟨Mᵀ *ᵥ O ε, fun a => ?_, ?_⟩
  · rw [adj_dot, ← hO2' a, hO1, hε]
  · rw [sim_dot (M := Mᵀ) (n := (n : ℚ)) (by rw [transpose_transpose, hM1]), hO1, hε1, mul_one]

end Euler

/-! ### Part A: `n = d² + v c²` over `ℚ` with `v ≡ 1 (mod q)` forces even valuations -/

section Arithmetic

private lemma even_padicValNat_of_sq_add {q v : ℕ} [Fact q.Prime] (hq3 : q % 4 = 3)
    (hv : (v : ZMod q) = 1) :
    ∀ N : ℕ, ∀ A B : ℤ, (N : ℤ) = A ^ 2 + v * B ^ 2 → N ≠ 0 → Even (padicValNat q N) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro A B h hN
  by_cases hqN : q ∣ N
  · have h0 : (A : ZMod q) ^ 2 + (B : ZMod q) ^ 2 = 0 := by
      have h1 := congrArg (Int.cast : ℤ → ZMod q) h
      push_cast at h1
      rw [hv, (ZMod.natCast_eq_zero_iff N q).mpr hqN] at h1
      linear_combination -h1
    have hB : (B : ZMod q) = 0 := by
      by_contra hB
      have hsq : IsSquare (-1 : ZMod q) := ⟨(A : ZMod q) / B, by
        field_simp
        linear_combination -h0⟩
      exact (ZMod.exists_sq_eq_neg_one_iff.mp hsq) hq3
    have hA : (A : ZMod q) = 0 := by
      rw [hB] at h0
      simpa using h0
    obtain ⟨A', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd A q).mp hA
    obtain ⟨B', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd B q).mp hB
    have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
    have hdvd : q ^ 2 ∣ N := by
      have : ((q ^ 2 : ℕ) : ℤ) ∣ (N : ℤ) := ⟨A' ^ 2 + v * B' ^ 2, by rw [h]; push_cast; ring⟩
      exact_mod_cast this
    obtain ⟨N', rfl⟩ := hdvd
    have hN' : N' ≠ 0 := fun h0 => hN (by simp [h0])
    have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
    have hlt : N' < q ^ 2 * N' := by
      have : 1 < q ^ 2 := by nlinarith
      have : 0 < N' := Nat.pos_of_ne_zero hN'
      nlinarith
    have hN'eq : (N' : ℤ) = A' ^ 2 + v * B' ^ 2 := by
      have : ((q : ℤ) ^ 2) * N' = (q : ℤ) ^ 2 * (A' ^ 2 + v * B' ^ 2) := by
        push_cast at h; rw [h]; ring
      exact mul_left_cancel₀ (pow_ne_zero 2 hq0) this
    have := ih N' hlt A' B' hN'eq hN'
    rw [padicValNat.mul (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero) hN',
      padicValNat.prime_pow]
    exact (even_two).add this
  · rw [padicValNat.eq_zero_of_not_dvd hqN]
    exact Even.zero

/-- If `n = d² + (n² + n + 1) c²` with `c d` rational, then `n` is a sum of two squares. -/
theorem exists_sq_add_sq_of_rat (n : ℕ) (c d : ℚ)
    (h : (n : ℚ) = d ^ 2 + ((n : ℚ) ^ 2 + n + 1) * c ^ 2) :
    ∃ a b : ℕ, n = a ^ 2 + b ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, 0, rfl⟩
  rw [Nat.eq_sq_add_sq_iff]
  intro q hq hq3
  have : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hq⟩
  have hqn : q ∣ n := Nat.dvd_of_mem_primeFactors hq
  have hv : (((n ^ 2 + n + 1 : ℕ)) : ZMod q) = 1 := by
    have : (n : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff n q).mpr hqn
    push_cast
    rw [this]; ring
  set s : ℕ := c.den * d.den with hsdef
  have hs : 0 < s := Nat.mul_pos c.den_pos d.den_pos
  have hdq : d = d.num / d.den := (Rat.num_div_den d).symm
  have hcq : c = c.num / c.den := (Rat.num_div_den c).symm
  have hdd : (d.den : ℚ) ≠ 0 := by exact_mod_cast d.den_nz
  have hcd : (c.den : ℚ) ≠ 0 := by exact_mod_cast c.den_nz
  have hA : ((d.num * c.den : ℤ) : ℚ) = d * s := by
    rw [hsdef]; push_cast
    nth_rewrite 2 [hdq]
    field_simp
  have hB : ((c.num * d.den : ℤ) : ℚ) = c * s := by
    rw [hsdef]; push_cast
    nth_rewrite 2 [hcq]
    field_simp
  have key : ((n * s ^ 2 : ℕ) : ℤ) = (d.num * c.den) ^ 2 + ((n ^ 2 + n + 1 : ℕ) : ℤ) *
      (c.num * d.den) ^ 2 := by
    have : ((n * s ^ 2 : ℕ) : ℚ) = ((d.num * c.den : ℤ) : ℚ) ^ 2 +
        (((n ^ 2 + n + 1 : ℕ) : ℤ) : ℚ) * ((c.num * d.den : ℤ) : ℚ) ^ 2 := by
      rw [hA, hB]
      push_cast
      linear_combination (s : ℚ) ^ 2 * h
    exact_mod_cast this
  have hne : n * s ^ 2 ≠ 0 := by positivity
  have hev := even_padicValNat_of_sq_add hq3 hv (n * s ^ 2) _ _ key hne
  rw [padicValNat.mul hn.ne' (pow_ne_zero 2 hs.ne'), padicValNat.pow s 2] at hev
  exact (Nat.even_add.mp hev).mpr (even_two_mul _)

end Arithmetic

/-! ### Part D: the incidence structure of a finite projective plane -/

section Geometry

open scoped Classical in
/-- Number of lines through two (possibly equal) points, as a rational number. -/
private lemma count_lines {P L : Type*} [Membership P L] [ProjectivePlane P L] [Fintype P]
    [Fintype L] (x y : P) :
    ∑ l : L, ((if x ∈ l then (1 : ℚ) else 0) * (if y ∈ l then 1 else 0)) =
      if x = y then (ProjectivePlane.order P L : ℚ) + 1 else 1 := by
  simp_rw [ite_zero_mul_ite_zero, mul_one]
  rw [Finset.sum_boole]
  by_cases hxy : x = y
  · subst hxy
    have h1 : (Finset.univ.filter fun l : L => x ∈ l ∧ x ∈ l).card = Configuration.lineCount L x := by
      rw [Configuration.lineCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
      simp
    rw [h1, ProjectivePlane.lineCount_eq]
    simp
  · obtain ⟨l0, hl0, huniq⟩ := HasLines.existsUnique_line P L x y hxy
    have : (Finset.univ.filter fun l : L => x ∈ l ∧ y ∈ l) = {l0} := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun hl => huniq l hl, fun hl => hl ▸ hl0⟩
    rw [this]
    simp [hxy]

/-- **Bruck–Ryser–Chowla (1949, 1950).** If a finite projective plane of order `n` exists and
`n ≡ 1` or `2 (mod 4)`, then `n` is a sum of two squares (so there is no plane of order 6 or 14). -/
theorem exists_sq_add_sq (P L : Type*) [Membership P L] [ProjectivePlane P L] [Finite P]
    [Finite L] (h : ProjectivePlane.order P L % 4 = 1 ∨ ProjectivePlane.order P L % 4 = 2) :
    ∃ a b : ℕ, ProjectivePlane.order P L = a ^ 2 + b ^ 2 := by
  classical
  have := Fintype.ofFinite P
  have := Fintype.ofFinite L
  set n := ProjectivePlane.order P L with hn
  have hP : Fintype.card P = n ^ 2 + n + 1 := ProjectivePlane.card_points P L
  have hL : Fintype.card L = n ^ 2 + n + 1 := ProjectivePlane.card_lines P L
  let σ : P ≃ L := Fintype.equivOfCardEq (by rw [hP, hL])
  have h4 : 4 ∣ Fintype.card (L ⊕ Unit) := by
    rw [Fintype.card_sum, hL]
    apply Nat.dvd_of_mod_eq_zero
    rcases h with h | h <;> simp [Nat.add_mod, Nat.pow_mod, h]
  let g : P × P → L ⊕ Unit → ℚ := fun q =>
    Pi.single (Sum.inl (σ q.1)) 1 - Pi.single (Sum.inl (σ q.2)) 1
  let u : P × P → L ⊕ Unit → ℚ := fun q => Sum.elim
    (fun l => (if q.1 ∈ l then (1 : ℚ) else 0) - (if q.2 ∈ l then 1 else 0)) (fun _ => 0)
  let ε : L ⊕ Unit → ℚ := Sum.elim (fun _ => 0) (fun _ => 1)
  have hε : ∀ a, ε ⬝ᵥ u a = 0 := by
    intro a
    simp [dotProduct, Fintype.sum_sum_type, ε, u]
  have hε1 : ε ⬝ᵥ ε = 1 := by
    simp [dotProduct, Fintype.sum_sum_type, ε]
  have hG : ∀ a b, u a ⬝ᵥ u b = n * (g a ⬝ᵥ g b) := by
    intro a b
    have e1 : u a ⬝ᵥ u b = ∑ l : L, ((if a.1 ∈ l then (1 : ℚ) else 0) - (if a.2 ∈ l then 1 else 0))
        * ((if b.1 ∈ l then (1 : ℚ) else 0) - (if b.2 ∈ l then 1 else 0)) := by
      simp [dotProduct, Fintype.sum_sum_type, u]
    have e2 : g a ⬝ᵥ g b = (if a.1 = b.1 then (1 : ℚ) else 0) - (if a.1 = b.2 then 1 else 0)
        - (if a.2 = b.1 then 1 else 0) + (if a.2 = b.2 then 1 else 0) := by
      simp [g, dotProduct_sub, Pi.single_apply, σ.injective.eq_iff]
      simp only [@eq_comm _ b.1 a.1, @eq_comm _ b.1 a.2, @eq_comm _ b.2 a.1, @eq_comm _ b.2 a.2]
      ring
    have e3 : ∑ l : L, ((if a.1 ∈ l then (1 : ℚ) else 0) - (if a.2 ∈ l then 1 else 0))
        * ((if b.1 ∈ l then (1 : ℚ) else 0) - (if b.2 ∈ l then 1 else 0)) =
        (∑ l : L, (if a.1 ∈ l then (1 : ℚ) else 0) * (if b.1 ∈ l then 1 else 0))
        - (∑ l : L, (if a.1 ∈ l then (1 : ℚ) else 0) * (if b.2 ∈ l then 1 else 0))
        - (∑ l : L, (if a.2 ∈ l then (1 : ℚ) else 0) * (if b.1 ∈ l then 1 else 0))
        + (∑ l : L, (if a.2 ∈ l then (1 : ℚ) else 0) * (if b.2 ∈ l then 1 else 0)) := by
      simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => by ring
    rw [e1, e3, e2, count_lines, count_lines, count_lines, count_lines]
    split_ifs <;> linarith
  obtain ⟨r, hr1, hr2⟩ := exists_orthogonal_vector (ι := L ⊕ Unit) n h4 u g ε hG hε hε1
  obtain ⟨p0, -⟩ := @ProjectivePlane.exists_config P L _ _
  have hconst : ∀ l : L, r (Sum.inl l) = r (Sum.inl (σ p0)) := by
    intro l
    have := hr1 (σ.symm l, p0)
    simp [g, dotProduct_sub, dotProduct_single] at this
    linarith
  refine exists_sq_add_sq_of_rat n (r (Sum.inl (σ p0))) (r (Sum.inr ())) ?_
  have hsum : r ⬝ᵥ r = (n ^ 2 + n + 1 : ℚ) * r (Sum.inl (σ p0)) ^ 2 + r (Sum.inr ()) ^ 2 := by
    simp only [dotProduct, Fintype.sum_sum_type, hconst]
    simp [← sq, hL]
  rw [hr2] at hsum
  linear_combination hsum

end Geometry

end BruckRyserChowla
