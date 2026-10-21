/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# The `2 × 2` representation `Θ` of the quaternion curve

Over a commutative ring `R` with an element `ι`, `ι² = −1` (in the paper `R = ℂ[t]`, `ι = √−1`),
let `𝐢 = diag(ι, −ι)`, `𝐣 = !![0,1;−1,0]`, `𝐤 = 𝐢𝐣`. The map `Θ` of §4.2 sends the generators
to `I + t𝐢`, `I + t𝐣`, `I + t𝐤`, so `ξ = x − 1`, `η = y − 1`, `ζ = z − 1` go to `t𝐢`, `t𝐣`, `t𝐤`.

## Main results

* `mi_mul_mi`, `mj_mul_mj`, `mk_mul_mk`, `mi_mul_mj`, `mj_mul_mi`: the quaternion relations.
* `smul_mul_smul_self`: if `q² = −1`, then `(t q)² = −t² I` (so `ξ² = η² = ζ² = −t² I` under `Θ`).
* `theta_c_eq_zero`: `c = ξη + ηξ ↦ t²(𝐢𝐣 + 𝐣𝐢) = 0`.
* `det_one_add_smul`: `det(I + t q) = 1 + t²` for `q ∈ {𝐢, 𝐣, 𝐤}`.
* `one_add_smul_mul_one_sub_smul`, `one_sub_smul_mul_one_add_smul`: `(I + t q)(I − t q) = (1 + t²) I`
  in both orders, so `Θ(x)⁻¹ = (I − t𝐢)/(1 + t²)` wherever `1 + t²` is invertible.
-/

@[expose] public section

namespace ThreeAxes.QuaternionTheta

open Matrix

variable {R : Type*} [CommRing R] (ι : R)

/-- `𝐢 = diag(ι, −ι)`. -/
def mi : Matrix (Fin 2) (Fin 2) R := !![ι, 0; 0, -ι]

/-- `𝐣 = !![0, 1; −1, 0]`. -/
def mj : Matrix (Fin 2) (Fin 2) R := !![0, 1; -1, 0]

/-- `𝐤 = 𝐢𝐣`. -/
def mk : Matrix (Fin 2) (Fin 2) R := mi ι * mj

variable {ι}

theorem mi_mul_mi (hι : ι * ι = -1) : mi ι * mi ι = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [mi, hι]

theorem mj_mul_mj : mj * mj = (-1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [mj]

theorem mi_mul_mj : mi ι * mj = mk ι := rfl

theorem mj_mul_mi : mj * mi ι = -mk ι := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [mi, mj, mk]

theorem mk_mul_mk (hι : ι * ι = -1) : mk ι * mk ι = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [mi, mj, mk, hι]

theorem mi_mul_mj_add : mi ι * mj + mj * mi ι = 0 := by
  rw [mj_mul_mi, mi_mul_mj, add_neg_cancel]

/-- If `q² = −1`, then `(t q)² = −t² I`. -/
theorem smul_mul_smul_self {q : Matrix (Fin 2) (Fin 2) R} (hq : q * q = -1) (t : R) :
    (t • q) * (t • q) = (-t ^ 2) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  rw [smul_mul_smul_comm, hq, smul_neg, neg_smul, sq]

/-- `c = ξη + ηξ` maps to `0`. -/
theorem theta_c_eq_zero (t : R) : (t • mi ι) * (t • mj) + (t • mj) * (t • mi ι) = 0 := by
  rw [smul_mul_smul_comm, smul_mul_smul_comm, ← smul_add, mi_mul_mj_add, smul_zero]

theorem det_one_add_smul_mi (hι : ι * ι = -1) (t : R) : (1 + t • mi ι).det = 1 + t ^ 2 := by
  simp [mi, det_fin_two]; linear_combination (-t ^ 2) * hι

theorem det_one_add_smul_mj (t : R) : (1 + t • mj : Matrix (Fin 2) (Fin 2) R).det = 1 + t ^ 2 := by
  simp [mj, det_fin_two]; ring

theorem det_one_add_smul_mk (hι : ι * ι = -1) (t : R) : (1 + t • mk ι).det = 1 + t ^ 2 := by
  simp [mi, mj, mk, det_fin_two]; linear_combination (-t ^ 2) * hι

/-- `(I + t q)(I − t q) = (1 + t²) I` when `q² = −1`. -/
theorem one_add_smul_mul_one_sub_smul {q : Matrix (Fin 2) (Fin 2) R} (hq : q * q = -1) (t : R) :
    (1 + t • q) * (1 - t • q) = (1 + t ^ 2) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  rw [add_mul, one_mul, mul_sub, mul_one, smul_mul_smul_self hq, add_smul, one_smul, neg_smul]
  abel

theorem one_sub_smul_mul_one_add_smul {q : Matrix (Fin 2) (Fin 2) R} (hq : q * q = -1) (t : R) :
    (1 - t • q) * (1 + t • q) = (1 + t ^ 2) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  rw [sub_mul, one_mul, mul_add, mul_one, smul_mul_smul_self hq, add_smul, one_smul, neg_smul]
  abel

end ThreeAxes.QuaternionTheta
