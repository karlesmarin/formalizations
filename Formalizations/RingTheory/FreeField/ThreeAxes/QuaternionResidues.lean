/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.Field.ZMod

/-!
# Residues modulo `5` of the quaternions `1 ± 2q`

Finite part of the lemma that no binomial degenerates on the quaternion curve of the three-axes
problem (Part 2, Lemma 3.1). The Lipschitz quaternions map to `M₂(𝔽₅)` by `𝐢 ↦ diag(2,3)`,
`𝐣 ↦ !![0,1;-1,0]`. The six generators `1 ± 2𝐢, 1 ± 2𝐣, 1 ± 2𝐤` reduce to matrices of rank one,
and the product of two residues vanishes exactly when the letters are mutually inverse. Hence the
residue of the product of a reduced word is never zero.

## Main results

* `qi_mul_qi`, `qj_mul_qj`, `qk_mul_qk`, `qi_mul_qj`, `qj_mul_qi`: the quaternion relations mod `5`.
* `res_eq_vecMulVec`: each residue is `vecMulVec (col a) (row a)`; `rank_res`: it has rank `1`.
* `res_mul_res_eq_zero_iff`: `res a * res b = 0 ↔ b = a⁻¹` (all `36` cases).
* `prod_res_ne_zero`: the product of the residues along a nonempty reduced word is nonzero.
-/

@[expose] public section

namespace ThreeAxes.QuaternionResidues

open Matrix

local instance fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The image of `𝐢` in `M₂(𝔽₅)`. -/
def qi : Matrix (Fin 2) (Fin 2) (ZMod 5) := !![2, 0; 0, 3]

/-- The image of `𝐣` in `M₂(𝔽₅)`. -/
def qj : Matrix (Fin 2) (Fin 2) (ZMod 5) := !![0, 1; -1, 0]

/-- The image of `𝐤 = 𝐢𝐣` in `M₂(𝔽₅)`. -/
def qk : Matrix (Fin 2) (Fin 2) (ZMod 5) := qi * qj

theorem qi_mul_qi : qi * qi = -1 := by decide
theorem qj_mul_qj : qj * qj = -1 := by decide
theorem qk_mul_qk : qk * qk = -1 := by decide
theorem qi_mul_qj : qi * qj = qk := rfl
theorem qj_mul_qi : qj * qi = -qk := by decide

/-- The six generators `x = 1 + 2𝐢`, `X = 1 − 2𝐢`, `y = 1 + 2𝐣`, `Y = 1 − 2𝐣`, `z = 1 + 2𝐤`,
`Z = 1 − 2𝐤` (up to the scalar `5`, `X = x⁻¹` etc.). -/
inductive Gen
  | x | X | y | Y | z | Z
  deriving DecidableEq

/-- The inverse letter. -/
def Gen.inv : Gen → Gen
  | .x => .X | .X => .x | .y => .Y | .Y => .y | .z => .Z | .Z => .z

/-- The residue mod `5` of a generator. -/
def res : Gen → Matrix (Fin 2) (Fin 2) (ZMod 5)
  | .x => 1 + 2 • qi
  | .X => 1 - 2 • qi
  | .y => 1 + 2 • qj
  | .Y => 1 - 2 • qj
  | .z => 1 + 2 • qk
  | .Z => 1 - 2 • qk

/-- Column factor of the rank-one residue. -/
def col : Gen → Fin 2 → ZMod 5
  | .x => ![0, 1] | .X => ![1, 0] | .y => ![1, 3] | .Y => ![1, 2] | .z => ![1, 4] | .Z => ![1, 1]

/-- Row factor of the rank-one residue. -/
def row : Gen → Fin 2 → ZMod 5
  | .x => ![0, 2] | .X => ![2, 0] | .y => ![1, 2] | .Y => ![1, 3] | .z => ![1, 4] | .Z => ![1, 1]

theorem res_eq_vecMulVec (a : Gen) : res a = vecMulVec (col a) (row a) := by
  cases a <;> decide

theorem det_res (a : Gen) : (res a).det = 0 := by
  rw [res_eq_vecMulVec, det_fin_two]
  simp only [vecMulVec_apply]
  ring

theorem res_ne_zero (a : Gen) : res a ≠ 0 := by
  cases a <;> decide

theorem rank_pos_of_ne_zero {m n K : Type*} [Fintype m] [Fintype n] [DecidableEq n] [Field K]
    {A : Matrix m n K} (h : A ≠ 0) : 0 < A.rank := by
  rw [Nat.pos_iff_ne_zero]
  intro h0
  apply h
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
  ext i j
  simpa [mulVecLin_apply, mulVec_single] using congrFun (congrArg (· (Pi.single j 1)) h0) i

theorem rank_res (a : Gen) : (res a).rank = 1 := by
  apply le_antisymm
  · rw [res_eq_vecMulVec]
    exact rank_vecMulVec_le _ _
  · exact rank_pos_of_ne_zero (res_ne_zero a)

/-- The `36` products: `res a * res b = 0` exactly when `b = a⁻¹`. -/
theorem res_mul_res_eq_zero_iff (a b : Gen) : res a * res b = 0 ↔ b = a.inv := by
  cases a <;> cases b <;> decide

theorem row_dotProduct_col_ne_zero {a b : Gen} (h : b ≠ a.inv) : row a ⬝ᵥ col b ≠ 0 := by
  cases a <;> cases b <;> simp_all [Gen.inv] <;> decide

theorem vecMulVec_col_row_ne_zero (a b : Gen) : vecMulVec (col a) (row b) ≠ 0 := by
  cases a <;> cases b <;> decide

/-- Along a reduced word `a :: w` (no letter followed by its inverse) the product of the residues
is a nonzero multiple of `vecMulVec (col a) (row b)` for the last letter `b`. -/
theorem prod_res_eq_smul (a : Gen) (w : List Gen) (hw : (a :: w).IsChain fun p q => q ≠ p.inv) :
    ∃ c : ZMod 5, c ≠ 0 ∧ ((a :: w).map res).prod =
      c • vecMulVec (col a) (row ((a :: w).getLast (List.cons_ne_nil a w))) := by
  induction w generalizing a with
  | nil => exact ⟨1, one_ne_zero, by simp [res_eq_vecMulVec]⟩
  | cons b w ih =>
    rw [List.isChain_cons_cons] at hw
    obtain ⟨c, hc, hprod⟩ := ih b hw.2
    refine ⟨(row a ⬝ᵥ col b) * c, mul_ne_zero (row_dotProduct_col_ne_zero hw.1) hc, ?_⟩
    rw [List.map_cons, List.prod_cons, hprod, res_eq_vecMulVec, mul_smul_comm,
      vecMulVec_mul_vecMulVec, List.getLast_cons (List.cons_ne_nil b w)]
    ext i j
    simp [vecMulVec_apply, mul_assoc, mul_left_comm]

/-- The residue mod `5` of the product along a nonempty reduced word is nonzero. -/
theorem prod_res_ne_zero (w : List Gen) (hne : w ≠ []) (hw : w.IsChain fun p q => q ≠ p.inv) :
    (w.map res).prod ≠ 0 := by
  obtain ⟨a, w, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨c, hc, h⟩ := prod_res_eq_smul a w hw
  rw [h]
  exact smul_ne_zero hc (vecMulVec_col_row_ne_zero _ _)

end ThreeAxes.QuaternionResidues
