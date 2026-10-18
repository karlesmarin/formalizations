/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The atom certificate for the `9 × 9` pencil of the three-axes problem

Integer data behind the proof that the `3 × 3` target matrix `F` of the three-axes problem is an
atom (Lemma 7.8(a)). The linear pencil `Q = Q₀ + u Q_u + v Q_v + w Q_w` is a `9 × 9`
linearisation of `F`; at the point `u = v = w = 2` it is invertible with `det Q(2,2,2) = 256`, and
the normalised coefficients `K_i = 16 Q(2,2,2)⁻¹ Q_i` are integer matrices. The algebra they
generate is all of `M₉`, witnessed by a rank-one element `r ℓ` (a polynomial without constant term
in `K_v`) together with two bases of words acting on `r` and on `ℓ`.

Determinants of the explicit `9 × 9` matrices are not computed by Laplace expansion: each one is
certified by an integer factorisation `L * M.submatrix σ σ = U` with `L` lower triangular, `U` upper
triangular and `σ` a permutation (`det_eq_of_certificate`), checked by `decide`.

## Main results

* `det_eq_of_certificate`: if `L * M.submatrix σ σ = U` with `L` lower and `U` upper triangular over
  an integral domain, and `∏ U i i = (∏ L i i) * d` with `∏ L i i ≠ 0`, then `det M = d`.
* `Q2_mul_K`: `Q(2,2,2) * K i = 16 • Q i` for `i = u, v, w`; `det_Q2`: `det Q(2,2,2) = 256`.
* `Kv_identity`: `K_v² (K_v² − 12 K_v + 48) = 2048 • vecMulVec r ℓ`.
* `det_wordsR`: `det [K_ω r]_{ω ∈ R} = 5 * 2 ^ 56`; `det_wordsO`: `det [ℓ K_ω]_{ω ∈ O} = 2 ^ 49`,
  with `K_ω = K_{ω₁} K_{ω₂} ⋯` (left to right).
-/

@[expose] public section

namespace ThreeAxes.AtomCertificate

open Matrix

/-! ### Determinants from triangular certificates -/

section Certificate

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n] {R : Type*} [CommRing R]

theorem prod_diag_mul_det_of_mul_eq {L M U : Matrix n n R} (h : L * M = U)
    (hL : L.IsLowerTriangular) (hU : U.IsUpperTriangular) :
    (∏ i, L i i) * M.det = ∏ i, U i i := by
  rw [← det_of_isLowerTriangular L hL, ← det_of_isUpperTriangular hU, ← h, det_mul]

theorem det_eq_of_certificate [IsDomain R] {L M U : Matrix n n R} (σ : Equiv.Perm n) (d : R)
    (h : L * M.submatrix σ σ = U) (hL : L.IsLowerTriangular) (hU : U.IsUpperTriangular)
    (hd : ∏ i, U i i = (∏ i, L i i) * d) (h0 : ∏ i, L i i ≠ 0) : M.det = d := by
  have := prod_diag_mul_det_of_mul_eq h hL hU
  rw [det_submatrix_equiv_self, hd] at this
  exact mul_left_cancel₀ h0 this

end Certificate

/-! ### The pencil -/

/-- The constant coefficient `Q₀` of the pencil. -/
def Q0 : Matrix (Fin 9) (Fin 9) ℤ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- The coefficient `Q_u` of `u`. -/
def Qu : Matrix (Fin 9) (Fin 9) ℤ :=
  !![0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, -1, 0, 0;
    -1, -1, 1, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, -1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The coefficient `Q_v` of `v`. -/
def Qv : Matrix (Fin 9) (Fin 9) ℤ :=
  !![0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, -1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    -1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0]

/-- The coefficient `Q_w` of `w`. -/
def Qw : Matrix (Fin 9) (Fin 9) ℤ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, -1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The three variables of the pencil. -/
inductive Letter
  | u
  | v
  | w
  deriving DecidableEq

/-- The coefficient of a variable. -/
def Q : Letter → Matrix (Fin 9) (Fin 9) ℤ
  | .u => Qu
  | .v => Qv
  | .w => Qw

/-- The pencil at `u = v = w = 2`. -/
def Q2 : Matrix (Fin 9) (Fin 9) ℤ := Q0 + 2 • (Qu + Qv + Qw)

/-! ### The normalised coefficients `K_i = 16 Q(2,2,2)⁻¹ Q_i` -/

/-- `K_u = 16 Q(2,2,2)⁻¹ Q_u`. -/
def Ku : Matrix (Fin 9) (Fin 9) ℤ :=
  !![2, 2, -4, 1, 0, 0, -1, 0, -2;
    2, 2, -4, 1, 0, 0, -1, 0, -2;
    2, 2, 4, 1, 0, 0, 3, 0, -2;
    -4, -4, 8, 6, 0, 0, 2, 0, 4;
    4, 4, -8, 2, 0, 0, -2, 0, -4;
    4, 4, -8, 2, 0, 0, -2, 0, -4;
    4, 4, -8, 2, 0, 0, 6, 0, -4;
    -8, -8, 16, -4, 0, 0, 4, 0, 8;
    -4, -4, -8, -2, 0, 0, -6, 0, 4]

/-- `K_v = 16 Q(2,2,2)⁻¹ Q_v`. -/
def Kv : Matrix (Fin 9) (Fin 9) ℤ :=
  !![6, 0, 4, 0, 3, 0, 0, 1, 0;
    -2, 0, 4, 0, -1, 0, 0, 1, 0;
    -2, 0, 4, 0, -1, 0, 0, -3, 0;
    4, 0, -8, 0, 2, 0, 0, -2, 0;
    -4, 0, 8, 0, 6, 0, 0, 2, 0;
    -4, 0, 8, 0, -2, 0, 0, 2, 0;
    -4, 0, 8, 0, -2, 0, 0, -6, 0;
    8, 0, -16, 0, 4, 0, 0, 12, 0;
    4, 0, 8, 0, 2, 0, 0, 6, 0]

/-- `K_w = 16 Q(2,2,2)⁻¹ Q_w`. -/
def Kw : Matrix (Fin 9) (Fin 9) ℤ :=
  !![0, -2, 0, 0, 0, -1, 0, 0, 0;
    0, 6, 0, 0, 0, 3, 0, 0, 0;
    0, -2, 0, 0, 0, -1, 0, 0, 0;
    0, 4, 0, 0, 0, 2, 0, 0, 0;
    0, -4, 0, 0, 0, -2, 0, 0, 0;
    0, -4, 0, 0, 0, 6, 0, 0, 0;
    0, -4, 0, 0, 0, -2, 0, 0, 0;
    0, 8, 0, 0, 0, 4, 0, 0, 0;
    0, 4, 0, 0, 0, 2, 0, 0, 0]

/-- The normalised coefficient of a variable. -/
def K : Letter → Matrix (Fin 9) (Fin 9) ℤ
  | .u => Ku
  | .v => Kv
  | .w => Kw

/-- `K_i = 16 Q(2,2,2)⁻¹ Q_i`, stated without inverses. -/
theorem Q2_mul_K (i : Letter) : Q2 * K i = 16 • Q i := by
  cases i <;> decide

/-! ### `det Q(2,2,2) = 256` -/

/-- The permutation of the certificate for `Q(2,2,2)`. -/
def σQ2 : Equiv.Perm (Fin 9) where
  toFun := ![3, 0, 4, 1, 5, 2, 6, 7, 8]
  invFun := ![1, 3, 5, 0, 2, 4, 6, 7, 8]
  left_inv := by decide
  right_inv := by decide

/-- Lower triangular factor of the certificate for `Q(2,2,2)`. -/
def LQ2 : Matrix (Fin 9) (Fin 9) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    -2, 1, 0, 0, 0, 0, 0, 0, 0;
    -2, 1, 2, 0, 0, 0, 0, 0, 0;
    -2, -1, 2, 2, 0, 0, 0, 0, 0;
    -2, -1, 2, 2, 2, 0, 0, 0, 0;
    -2, -1, 2, -1, 2, 3, 0, 0, 0;
    2, 1, -2, 1, -2, -3, 2, 0, 0;
    -2, -1, 2, -1, 2, 3, -2, 4, 0;
    2, 1, -2, 1, -2, -3, 6, -6, 4]

/-- Upper triangular factor of the certificate for `Q(2,2,2)`. -/
def UQ2 : Matrix (Fin 9) (Fin 9) ℤ :=
  !![1, -2, 0, -2, 0, 2, 0, 0, 2;
    0, 4, 2, 4, 0, -4, 0, 0, -4;
    0, 0, 4, 4, 0, -4, 0, 0, -4;
    0, 0, 0, 4, 4, -4, 0, 0, -4;
    0, 0, 0, 0, 6, -4, 0, 0, -4;
    0, 0, 0, 0, 0, -4, -6, -6, -4;
    0, 0, 0, 0, 0, 0, 8, 6, 4;
    0, 0, 0, 0, 0, 0, 0, -2, -4;
    0, 0, 0, 0, 0, 0, 0, 0, 8]

theorem det_Q2 : Q2.det = 256 :=
  det_eq_of_certificate (L := LQ2) (U := UQ2) σQ2 256 (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-! ### The rank-one element: identity (7.1) -/

/-- The column vector `r`. -/
def r : Fin 9 → ℤ := ![0, 0, -1, 0, 0, 0, -2, 4, 1]

/-- The row vector `ℓ`. -/
def ℓ : Fin 9 → ℤ := ![2, 0, -2, 0, 2, 0, 0, 3, 0]

/-- `K_v² (K_v² − 12 K_v + 48) = 2048 r ℓ`: the rank-one matrix `r ℓ` is a polynomial without
constant term in `K_v`. -/
theorem Kv_identity :
    Kv * Kv * (Kv * Kv - 12 • Kv + 48 • (1 : Matrix (Fin 9) (Fin 9) ℤ)) =
      2048 • vecMulVec r ℓ := by
  decide

/-! ### The two bases of words: identities (7.2) -/

/-- `K_ω = K_{ω₁} K_{ω₂} ⋯` (left to right). -/
def word (ω : List Letter) : Matrix (Fin 9) (Fin 9) ℤ := (ω.map K).prod

open Letter in
/-- The words `R = (∅, u, uu, vu, wu, uuu, vuu, uvu, vvu)`. -/
def wordsR : Fin 9 → List Letter :=
  ![[], [u], [u, u], [v, u], [w, u], [u, u, u], [v, u, u], [u, v, u], [v, v, u]]

open Letter in
/-- The words `O = (∅, u, w, uu, uv, wu, ww, uuu, uuv)`. -/
def wordsO : Fin 9 → List Letter :=
  ![[], [u], [w], [u, u], [u, v], [w, u], [w, w], [u, u, u], [u, u, v]]

/-- The matrix with columns `K_ω r`, `ω ∈ R`. -/
def matR : Matrix (Fin 9) (Fin 9) ℤ := Matrix.of fun i j => (word (wordsR j) *ᵥ r) i

/-- The matrix with rows `ℓ K_ω`, `ω ∈ O`. -/
def matO : Matrix (Fin 9) (Fin 9) ℤ := Matrix.of fun i j => (ℓ ᵥ* word (wordsO i)) j

/-- The permutation of the certificate for `matR`. -/
def σR : Equiv.Perm (Fin 9) where
  toFun := ![1, 2, 3, 0, 4, 6, 7, 8, 5]
  invFun := ![3, 0, 1, 2, 4, 8, 5, 6, 7]
  left_inv := by decide
  right_inv := by decide

/-- Lower triangular factor of the certificate for `matR`. -/
def LR : Matrix (Fin 9) (Fin 9) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    3, 1, 0, 0, 0, 0, 0, 0, 0;
    -1, -1, 1, 0, 0, 0, 0, 0, 0;
    -3, 1, -1, 4, 0, 0, 0, 0, 0;
    -1, 0, 0, -1, 1, 0, 0, 0, 0;
    -1, -2, 2, -11, 6, 1, 0, 0, 0;
    0, -4, 4, -8, 8, 4, 1, 0, 0;
    -1, 1, 1, -2, 1, 0, 0, 1, 0;
    -2, 1, 1, -1, 0, 0, 0, 1, 1]

/-- Upper triangular factor of the certificate for `matR`. -/
def UR : Matrix (Fin 9) (Fin 9) ℤ :=
  !![4, 16, -80, 0, 48, -576, 384, 128, 0;
    0, -64, -256, -1, 128, -2048, 1280, 256, -1024;
    0, 0, 256, 1, 0, 2048, 0, -256, 256;
    0, 0, 0, -1, -256, -1024, 0, -1792, -256;
    0, 0, 0, 0, -64, 0, 0, -256, 0;
    0, 0, 0, 0, 0, 1024, 1280, 512, 256;
    0, 0, 0, 0, 0, 0, 5120, -2048, 0;
    0, 0, 0, 0, 0, 0, 0, -256, 256;
    0, 0, 0, 0, 0, 0, 0, 0, 256]

/-- The permutation of the certificate for `matO`. -/
def σO : Equiv.Perm (Fin 9) where
  toFun := ![0, 1, 3, 2, 4, 5, 6, 7, 8]
  invFun := ![0, 1, 3, 2, 4, 5, 6, 7, 8]
  left_inv := by decide
  right_inv := by decide

/-- Lower triangular factor of the certificate for `matO`. -/
def LO : Matrix (Fin 9) (Fin 9) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    8, 1, 0, 0, 0, 0, 0, 0, 0;
    0, -4, 1, 0, 0, 0, 0, 0, 0;
    64, 12, -1, 8, 0, 0, 0, 0, 0;
    -32, -12, 1, -8, 1, 0, 0, 0, 0;
    64, 0, 1, -8, 4, 3, 0, 0, 0;
    64, 0, 1, -12, 4, 3, 1, 0, 0;
    -128, 32, -14, 24, -8, -6, -2, 1, 0;
    -512, 128, -56, 96, -52, -24, -8, 4, 5]

/-- Upper triangular factor of the certificate for `matO`. -/
def UO : Matrix (Fin 9) (Fin 9) ℤ :=
  !![2, 0, 0, -2, 2, 0, 0, 3, 0;
    0, -16, -8, 0, 16, 0, 0, 24, 16;
    0, 0, -64, -64, 0, 0, -32, 0, 0;
    0, 0, 0, 64, 128, 64, 32, 192, 128;
    0, 0, 0, 0, -96, -64, -32, -64, -128;
    0, 0, 0, 0, 0, -64, -128, 320, -128;
    0, 0, 0, 0, 0, 0, -128, 320, -128;
    0, 0, 0, 0, 0, 0, 0, -640, 256;
    0, 0, 0, 0, 0, 0, 0, 0, 1024]

/-- `det [K_ω r]_{ω ∈ R} = 5 · 2⁵⁶`. -/
theorem det_matR : matR.det = 5 * 2 ^ 56 :=
  det_eq_of_certificate (L := LR) (U := UR) σR _ (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-- `det [ℓ K_ω]_{ω ∈ O} = 2⁴⁹`. -/
theorem det_matO : matO.det = 2 ^ 49 :=
  det_eq_of_certificate (L := LO) (U := UO) σO _ (by decide) (by decide) (by decide)
    (by decide) (by decide)

end ThreeAxes.AtomCertificate
