/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.NumberTheory.MahlerBasis.FiniteMahlerBasis
public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# The change of variable `z ↦ ((1+p)^z − 1)/p` is unitriangular in the Mahler basis

Let `p` be an odd prime, `F(z) = ((1+p)^z − 1)/p` and `L = F⁻¹`, as maps of `ℤ/p^t`. On functions
`ℤ/p^t → k` with `char k = p`, the maps `q ↦ q ∘ F` and `q ↦ q ∘ L` are unitriangular in the
Mahler basis `C(z, i)`: `C(F(z), i)` and `C(L(z), i)` have Mahler degree `i` and leading
coefficient `1`. The proof uses `(1+X)^{λ y + 1} = (1+X)((1+X)^λ)^y` with `λ = 1 + p`,
`(1+X)^λ − 1 ≡ X + X^p + X^{p+1} (mod p)`, and `F(z+1) = λ F(z) + 1`; the statement for `L` comes
from inverting the unitriangular relation.

## Main results

* `LemaLog.choose_F_nat`, `LemaLog.choose_Ft`, `LemaLog.choose_Lt`: the Mahler expansions.
* `LemaLog.Ft_bijective`: `F` is a bijection of `ℤ/p^t`.
* `LemaLog.lem_log_F`, `LemaLog.lem_log_L`: the matrices of `q ↦ q ∘ F` and `q ↦ q ∘ L` in the
  basis `ConjeturaC.chooseBasis` are upper unitriangular.

## References

* C. Marín, *Reading Iwasawa λ-invariants from Mahler matrices modulo p: programs, data and Lean
  files*, Zenodo (2026), doi:10.5281/zenodo.23085315.
-/

@[expose] public section

namespace LemaLog

open Finset Polynomial

/-! ## Mahler-type combinations on any domain -/

section Low

variable {α R : Type*} [CommRing R]

/-- `g` is a combination of `C(e x, j)`, `j < m` (Mahler degree `< m` through `e`). -/
def Low (e : α → ℕ) (m : ℕ) (g : α → R) : Prop :=
  ∃ a : ℕ → R, ∀ x, g x = ∑ j ∈ range m, a j * ((e x).choose j : R)

variable {e : α → ℕ}

lemma Low.zero (m : ℕ) : Low e m (fun _ => (0 : R)) := ⟨fun _ => 0, fun _ => by simp⟩

lemma Low.add {m : ℕ} {f g : α → R} (hf : Low e m f) (hg : Low e m g) :
    Low e m (fun x => f x + g x) := by
  obtain ⟨a, ha⟩ := hf; obtain ⟨b, hb⟩ := hg
  exact ⟨fun j => a j + b j, fun x => by beta_reduce; rw [ha, hb, ← sum_add_distrib]; congr 1; ext j; ring⟩

lemma Low.smul {m : ℕ} (c : R) {f : α → R} (hf : Low e m f) : Low e m (fun x => c * f x) := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨fun j => c * a j, fun x => by beta_reduce; rw [ha, mul_sum]; congr 1; ext j; ring⟩

lemma Low.neg {m : ℕ} {f : α → R} (hf : Low e m f) : Low e m (fun x => - f x) := by
  simpa using hf.smul (-1)

lemma Low.mono {m m' : ℕ} (h : m ≤ m') {f : α → R} (hf : Low e m f) : Low e m' f := by
  obtain ⟨a, ha⟩ := hf
  refine ⟨fun j => if j < m then a j else 0, fun x => ?_⟩
  rw [ha, ← sum_subset (range_subset_range.2 h)]
  · exact sum_congr rfl fun j hj => by beta_reduce; rw [ite_eq_left (mem_range.1 hj)]
  · intro j _ hj; beta_reduce; rw [ite_eq_right (by simpa using hj), zero_mul]

lemma Low.choose {m j : ℕ} (h : j < m) : Low e m (fun x => ((e x).choose j : R)) :=
  ⟨fun l => if l = j then 1 else 0, fun x => by
    simp [ite_mul, sum_ite_eq', mem_range.2 h]⟩

lemma Low.sum {m n : ℕ} (c : ℕ → R) {g : ℕ → α → R} (hg : ∀ j < n, Low e m (g j)) :
    Low e m (fun x => ∑ j ∈ range n, c j * g j x) := by
  induction n with
  | zero => simpa using Low.zero (e := e) m
  | succ n ih =>
    simp only [sum_range_succ]
    exact (ih fun j hj => hg j (by omega)).add ((hg n (by omega)).smul (c n))

end Low

/-! ## The forward difference: an antidifference raises the degree by one -/

lemma low_of_diff {R : Type*} [CommRing R] {m : ℕ} (g : ℕ → R) (h0 : g 0 = 0)
    (hd : Low id m (fun z => g (z + 1) - g z)) : Low id (m + 1) g := by
  obtain ⟨a, ha⟩ := hd
  have key : ∀ z, g z = ∑ j ∈ range m, a j * ((z.choose (j + 1) : ℕ) : R) := by
    intro z
    induction z with
    | zero => simp [h0]
    | succ z ih =>
      have h := ha z
      simp only [id] at h
      rw [show g (z + 1) = g z + (g (z + 1) - g z) by ring, h, ih, ← sum_add_distrib]
      refine sum_congr rfl fun j _ => ?_
      rw [Nat.choose_succ_succ', Nat.cast_add]; ring
  refine ⟨fun j => match j with | 0 => 0 | j + 1 => a j, fun z => ?_⟩
  rw [key z, sum_range_succ']
  simp

/-! ## `F` on `ℕ` -/

/-- `F` on `ℕ` through its recursion `F(0) = 0`, `F(z+1) = (1+p)F(z) + 1`
(the identity `F(z+1) = λF(z) + 1` of the proof). -/
def Fn (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | z + 1 => (1 + p) * Fn p z + 1

/-- `F(z) = ((1+p)^z − 1)/p`: `p F(z) + 1 = (1+p)^z`. -/
theorem p_mul_Fn (p z : ℕ) : p * Fn p z + 1 = (1 + p) ^ z := by
  induction z with
  | zero => simp [Fn]
  | succ z ih => rw [Fn, pow_succ, ← ih]; ring

/-! ## The generating-function step, modulo `p` -/

section StepA

variable (p : ℕ) [hp : Fact p.Prime]

/-- `V = X^{p−3} + X^{p−2}`. -/
noncomputable def V : (ZMod p)[X] := X ^ (p - 3) + X ^ (p - 2)

/-- `W = 1 + X^{p−1} + X^p = 1 + X²V` (for `p ≥ 3`). -/
noncomputable def W : (ZMod p)[X] := 1 + X ^ 2 * V p

/-- `(1+X)^λ − 1 ≡ X + X^p + X^{p+1} = X·W (mod p)`, `λ = 1 + p`. -/
lemma X_add_one_pow_lam (hp3 : 3 ≤ p) : (X + 1 : (ZMod p)[X]) ^ (1 + p) = X * W p + 1 := by
  have hfrob : (X + 1 : (ZMod p)[X]) ^ p = X ^ p + 1 := by rw [add_pow_char, one_pow]
  have h1 : (X : (ZMod p)[X]) ^ 2 * (X ^ (p - 3) + X ^ (p - 2)) = X ^ (p - 1) + X ^ p := by
    rw [mul_add, ← pow_add, ← pow_add, show 2 + (p - 3) = p - 1 by omega,
      show 2 + (p - 2) = p by omega]
  have h2 : (X : (ZMod p)[X]) * X ^ (p - 1) = X ^ p := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega)]
  rw [add_comm 1 p, pow_succ, hfrob, W, V, h1]
  linear_combination -h2

omit hp in
/-- `(1+X)W^k = 1 + X + X²Q`: the coefficients of `X⁰` and `X¹` are `1` (uses `p − 1 ≥ 2`). -/
lemma W_pow (k : ℕ) : ∃ Q : (ZMod p)[X], (X + 1) * W p ^ k = X + 1 + X ^ 2 * Q := by
  obtain ⟨Q, hQ⟩ := sub_dvd_pow_sub_pow (W p) 1 k
  refine ⟨(X + 1) * V p * Q, ?_⟩
  rw [one_pow, show W p - 1 = X ^ 2 * V p by simp [W]] at hQ
  linear_combination (X + 1) * hQ

omit hp in
lemma coeff_W_pow_zero (k : ℕ) : ((X + 1) * W p ^ k).coeff 0 = 1 := by
  obtain ⟨Q, hQ⟩ := W_pow p k
  rw [hQ]; simp [coeff_X, coeff_one]

omit hp in
lemma coeff_W_pow_one (k : ℕ) : ((X + 1) * W p ^ k).coeff 1 = 1 := by
  obtain ⟨Q, hQ⟩ := W_pow p k
  rw [hQ]; simp [coeff_X_pow_mul', coeff_X, coeff_one]

/-- Step of the proof: `C(λy+1, i) − C(y, i) ≡ C(y, i−1) + (lower degree) (mod p)`, with
`i = n + 1`; the coefficients are `c_j = [X^i](1+X)((1+X)^λ − 1)^j`. -/
theorem stepA (hp3 : 3 ≤ p) (n : ℕ) :
    Low id n (fun y : ℕ => (((1 + p) * y + 1).choose (n + 1) : ZMod p) -
      (y.choose (n + 1) : ZMod p) - (y.choose n : ZMod p)) := by
  set c : ℕ → ZMod p := fun m => ((X + 1) * (X * W p) ^ m).coeff (n + 1) with hc
  have hc' : ∀ m, c m = if m ≤ n + 1 then ((X + 1) * W p ^ m).coeff (n + 1 - m) else 0 := by
    intro m
    simp only [hc]
    rw [mul_pow, show (X + 1) * (X ^ m * W p ^ m) = X ^ m * ((X + 1) * W p ^ m) by ring,
      coeff_X_pow_mul']
  have hgen : ∀ y : ℕ, (((1 + p) * y + 1).choose (n + 1) : ZMod p) =
      ∑ m ∈ range (y + 1), c m * (y.choose m : ZMod p) := by
    intro y
    rw [← coeff_X_add_one_pow (ZMod p), pow_succ, pow_mul, X_add_one_pow_lam p hp3, add_pow,
      sum_mul, finsetSum_coeff]
    refine sum_congr rfl fun m _ => ?_
    rw [one_pow, mul_one, show (X * W p) ^ m * ((y.choose m : ℕ) : (ZMod p)[X]) * (X + 1) =
      (X + 1) * (X * W p) ^ m * ((y.choose m : ℕ) : (ZMod p)[X]) by ring, coeff_mul_natCast]
  have hcut : ∀ y : ℕ, ∑ m ∈ range (y + 1), c m * (y.choose m : ZMod p) =
      ∑ m ∈ range (n + 2), c m * (y.choose m : ZMod p) := by
    intro y
    have hbig : ∀ A, y + 1 ≤ A ∨ n + 2 ≤ A → ∑ m ∈ range A, c m * (y.choose m : ZMod p) =
        ∑ m ∈ range (y + n + 2), c m * (y.choose m : ZMod p) := by
      intro A hA
      rcases le_total A (y + n + 2) with h | h
      · refine sum_subset (range_subset_range.2 h) fun m hm hmA => ?_
        simp only [mem_range, not_lt] at hm hmA
        rcases hA with hA | hA
        · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
        · rw [hc' m, ite_eq_right (by omega), zero_mul]
      · refine (sum_subset (range_subset_range.2 h) fun m hm hmA => ?_).symm
        simp only [mem_range, not_lt] at hm hmA
        rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
    rw [hbig _ (Or.inl le_rfl), hbig _ (Or.inr le_rfl)]
  have hcn : c n = 1 := by
    rw [hc' n, ite_eq_left (by omega), show n + 1 - n = 1 by omega, coeff_W_pow_one]
  have hcn1 : c (n + 1) = 1 := by
    rw [hc' (n + 1), ite_eq_left le_rfl, Nat.sub_self, coeff_W_pow_zero]
  refine ⟨c, fun y => ?_⟩
  simp only [id]
  rw [hgen, hcut, sum_range_succ, sum_range_succ, hcn, hcn1]
  ring

end StepA

lemma Low.congr {α R : Type*} [CommRing R] {e : α → ℕ} {m : ℕ} {f g : α → R}
    (h : ∀ x, f x = g x) (hf : Low e m f) : Low e m g := by
  obtain ⟨a, ha⟩ := hf; exact ⟨a, fun x => by rw [← h, ha]⟩

/-! ## `C(F(z), i)` has Mahler degree `i` and leading coefficient `1` (on `ℕ`, mod `p`) -/

/-- The induction of the proof: `C(F(z), i) − C(z, i)` is a combination of `C(z, j)`, `j < i`,
modulo `p`. -/
theorem choose_F_nat (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) (i : ℕ) :
    Low id i (fun z : ℕ => ((Fn p z).choose i : ZMod p) - (z.choose i : ZMod p)) := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  rcases i with _ | n
  · exact ⟨fun _ => 0, fun z => by simp⟩
  · obtain ⟨c, hc⟩ := stepA p hp3 n
    have hFj : ∀ j < n, Low id n (fun z : ℕ => ((Fn p z).choose j : ZMod p)) := fun j hj =>
      Low.congr (fun z => by simp) (((ih j (by omega)).mono hj.le).add
        (Low.choose (e := (id : ℕ → ℕ)) (R := ZMod p) hj))
    have hd : Low id n (fun z : ℕ =>
        (((Fn p (z + 1)).choose (n + 1) : ZMod p) - ((z + 1).choose (n + 1) : ZMod p)) -
        (((Fn p z).choose (n + 1) : ZMod p) - (z.choose (n + 1) : ZMod p))) := by
      refine Low.congr (fun z => ?_) ((Low.sum c hFj).add (ih n (by omega)))
      have h := hc (Fn p z)
      simp only [id] at h
      rw [show Fn p (z + 1) = (1 + p) * Fn p z + 1 from rfl, Nat.choose_succ_succ' z n,
        Nat.cast_add]
      linear_combination -h
    exact low_of_diff _ (by simp [Fn]) hd

/-! ## Transfer to `ℤ/p^t`: Lucas -/

/-- `C(n mod p^t, k) ≡ C(n, k) (mod p)` for `k < p^t` (Lucas). -/
lemma choose_mod_pow (p : ℕ) [Fact p.Prime] {t k : ℕ} (hk : k < p ^ t) (n : ℕ) :
    (((n % p ^ t).choose k : ℕ) : ZMod p) = ((n.choose k : ℕ) : ZMod p) := by
  have h1 := Choose.choose_modEq_choose_mul_prod_range_choose (p := p) (n := n) (k := k) t
  have h2 := Choose.choose_modEq_choose_mul_prod_range_choose (p := p) (n := n % p ^ t) (k := k) t
  have hp0 : 0 < p ^ t := pow_pos (Fact.out : p.Prime).pos t
  have hdig : ∀ i ∈ range t, (n % p ^ t) / p ^ i % p = n / p ^ i % p := by
    intro i hi
    have hi' := mem_range.1 hi
    rw [show p ^ t = p ^ i * p ^ (t - i) by rw [← pow_add]; congr 1; omega,
      Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self p (by omega))]
  rw [Nat.div_eq_of_lt hk, Nat.div_eq_of_lt (Nat.mod_lt _ hp0), Nat.choose_zero_right,
    prod_congr rfl fun i hi => by rw [hdig i hi]] at h2
  rw [Nat.div_eq_of_lt hk, Nat.choose_zero_right] at h1
  have h3 := h2.trans h1.symm
  have h4 := (ZMod.intCast_eq_intCast_iff _ _ p).2 h3
  simpa using h4

/-- `NeZero (p^t)`. -/
instance neZero_pow (p t : ℕ) [Fact p.Prime] : NeZero (p ^ t) :=
  ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩

/-- `F` on `ℤ/p^t`: `z ↦ F(z̃) mod p^t` with `z̃ ∈ [0, p^t)` the representative of `z`. -/
def Ft (p t : ℕ) (z : ZMod (p ^ t)) : ZMod (p ^ t) := (Fn p z.val : ZMod (p ^ t))

section Zt

variable (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) (t : ℕ)
include hp3

/-- `C(F(z), i) − C(z, i)`, `z ∈ ℤ/p^t`, `i < p^t`, is a combination of `C(z, j)`, `j < i`. -/
theorem choose_Ft {i : ℕ} (hi : i < p ^ t) :
    Low ZMod.val i (fun z : ZMod (p ^ t) =>
      (((Ft p t z).val.choose i : ℕ) : ZMod p) - ((z.val.choose i : ℕ) : ZMod p)) := by
  obtain ⟨a, ha⟩ := choose_F_nat p hp3 i
  exact ⟨a, fun z => by
    beta_reduce; unfold Ft; rw [ZMod.val_natCast, choose_mod_pow p hi]; exact ha z.val⟩

/-- `F` is a bijection of `ℤ/p^t` (here deduced from the unitriangularity). -/
theorem Ft_bijective : Function.Bijective (Ft p t) := by
  refine Finite.injective_iff_bijective.mp fun z₁ z₂ h => ?_
  have hall : ∀ i < p ^ t, ((z₁.val.choose i : ℕ) : ZMod p) = ((z₂.val.choose i : ℕ) : ZMod p) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
    intro hi
    obtain ⟨a, ha⟩ := choose_Ft p hp3 t hi
    have e1 := ha z₁
    have e2 := ha z₂
    beta_reduce at e1 e2
    rw [h] at e1
    have hs : ∑ j ∈ range i, a j * ((z₁.val.choose j : ℕ) : ZMod p) =
        ∑ j ∈ range i, a j * ((z₂.val.choose j : ℕ) : ZMod p) :=
      sum_congr rfl fun j hj => by rw [ih j (mem_range.1 hj) (by have := mem_range.1 hj; omega)]
    linear_combination e2 - e1 - hs
  by_contra hne
  have hv : z₁.val ≠ z₂.val := fun hv => hne (ZMod.val_injective _ hv)
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · have := hall z₂.val (ZMod.val_lt z₂)
    rw [Nat.choose_eq_zero_of_lt hlt, Nat.choose_self] at this
    simp at this
  · have := hall z₁.val (ZMod.val_lt z₁)
    rw [Nat.choose_self, Nat.choose_eq_zero_of_lt hgt] at this
    simp at this

/-- `L = F⁻¹` on `ℤ/p^t`. -/
noncomputable def Lt : ZMod (p ^ t) → ZMod (p ^ t) :=
  (Equiv.ofBijective _ (Ft_bijective p hp3 t)).symm

theorem Ft_Lt (z : ZMod (p ^ t)) : Ft p t (Lt p hp3 t z) = z :=
  Equiv.ofBijective_apply_symm_apply _ (Ft_bijective p hp3 t) z

theorem Lt_Ft (z : ZMod (p ^ t)) : Lt p hp3 t (Ft p t z) = z :=
  Equiv.ofBijective_symm_apply_apply _ (Ft_bijective p hp3 t) z

/-- `C(L(z), i) − C(z, i)`, `i < p^t`, is a combination of `C(z, j)`, `j < i`
("by inverting the unitriangular matrix"). -/
theorem choose_Lt {i : ℕ} (hi : i < p ^ t) :
    Low ZMod.val i (fun z : ZMod (p ^ t) =>
      (((Lt p hp3 t z).val.choose i : ℕ) : ZMod p) - ((z.val.choose i : ℕ) : ZMod p)) := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  obtain ⟨a, ha⟩ := choose_Ft p hp3 t hi
  have hLj : ∀ j < i, Low ZMod.val i (fun z : ZMod (p ^ t) =>
      (((Lt p hp3 t z).val.choose j : ℕ) : ZMod p)) := fun j hj =>
    Low.congr (fun z => by simp) (((ih j hj (by omega)).mono hj.le).add
      (Low.choose (e := (ZMod.val : ZMod (p ^ t) → ℕ)) (R := ZMod p) hj))
  refine Low.congr (fun z => ?_) (Low.sum (fun j => - a j) hLj)
  have h := ha (Lt p hp3 t z)
  beta_reduce at h
  rw [Ft_Lt] at h
  simp only [neg_mul, sum_neg_distrib]
  linear_combination h

end Zt

/-! ## The Mahler basis of `ℤ/N → k` (`ConjeturaC.chooseBasis`) and the matrices of `q ↦ q∘F`,
`q ↦ q∘L` -/

open ConjeturaC (chooseFun linearIndependent_choose chooseBasis coe_chooseBasis)

/-- If `C(G(z), i) − C(z, i)` is a combination of `C(z, j)`, `j < i` (mod `p`), the column `i` of
the matrix of `q ↦ q∘G` in the Mahler basis has `1` on the diagonal and `0` below it. -/
theorem column_unitri {p N : ℕ} [NeZero N] (k : Type*) [Field k] [CharP k p]
    (G : ZMod N → ZMod N) (i : Fin N)
    (h : Low ZMod.val i (fun z : ZMod N =>
      (((G z).val.choose i : ℕ) : ZMod p) - ((z.val.choose i : ℕ) : ZMod p))) :
    (chooseBasis N k).repr (chooseFun N k i ∘ G) i = 1 ∧
      ∀ j, i < j → (chooseBasis N k).repr (chooseFun N k i ∘ G) j = 0 := by
  obtain ⟨a, ha⟩ := h
  set φ := ZMod.castHom (dvd_refl p) k
  set c' : ℕ → k := fun m => (if m = (i : ℕ) then 1 else 0) + (if m < i then φ (a m) else 0)
  have hfun : chooseFun N k i ∘ G = ∑ j : Fin N, c' j.val • chooseBasis N k j := by
    funext z
    have hz := congrArg φ (ha z)
    simp only [map_sub, map_sum, map_mul, map_natCast] at hz
    simp only [Function.comp, chooseFun, coe_chooseBasis, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [Fin.sum_univ_eq_sum_range (fun m => c' m * ((z.val.choose m : ℕ) : k)) N]
    simp only [c', add_mul, sum_add_distrib, ite_mul, one_mul, zero_mul,
      sum_ite_eq', mem_range.2 i.isLt, ite_true]
    rw [← sum_filter, show (range N).filter (· < (i : ℕ)) = range i by
      ext m; simp only [mem_filter, mem_range]; have := i.isLt; omega]
    linear_combination hz
  rw [hfun, Module.Basis.repr_sum_self]
  refine ⟨by simp [c'], fun j hj => ?_⟩
  have h1 : (j : ℕ) ≠ i := by have : (i : ℕ) < j := hj; omega
  have h2 : ¬ (j : ℕ) < i := by have : (i : ℕ) < j := hj; omega
  simp [c', h1, h2]

/-- **`lem:log` 2.1, map `F`.** For every `t`, the matrix of `q ↦ q∘F` on functions `ℤ/p^t → k`
(`k` a field of characteristic `p`, `p ≥ 3`) in the Mahler basis is unitriangular: its column `i`
(the coordinates of `C(F(z), i)`) has `1` in row `i` and `0` in every row `j > i`. -/
theorem lem_log_F (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) (t : ℕ) (k : Type*) [Field k] [CharP k p] :
    ∀ i j : Fin (p ^ t),
      LinearMap.toMatrix (chooseBasis (p ^ t) k) (chooseBasis (p ^ t) k)
          (LinearMap.funLeft k k (Ft p t)) i i = 1 ∧
      (i < j → LinearMap.toMatrix (chooseBasis (p ^ t) k) (chooseBasis (p ^ t) k)
          (LinearMap.funLeft k k (Ft p t)) j i = 0) := by
  intro i j
  have hc := column_unitri (p := p) k (Ft p t) i (choose_Ft p hp3 t i.isLt)
  simp only [LinearMap.toMatrix_apply, LinearMap.funLeft, coe_chooseBasis]
  exact ⟨hc.1, hc.2 j⟩

/-- **`lem:log` 2.1, map `L = F⁻¹`.** Same statement for `q ↦ q∘L`. -/
theorem lem_log_L (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) (t : ℕ) (k : Type*) [Field k] [CharP k p] :
    ∀ i j : Fin (p ^ t),
      LinearMap.toMatrix (chooseBasis (p ^ t) k) (chooseBasis (p ^ t) k)
          (LinearMap.funLeft k k (Lt p hp3 t)) i i = 1 ∧
      (i < j → LinearMap.toMatrix (chooseBasis (p ^ t) k) (chooseBasis (p ^ t) k)
          (LinearMap.funLeft k k (Lt p hp3 t)) j i = 0) := by
  intro i j
  have hc := column_unitri (p := p) k (Lt p hp3 t) i (choose_Lt p hp3 t i.isLt)
  simp only [LinearMap.toMatrix_apply, LinearMap.funLeft, coe_chooseBasis]
  exact ⟨hc.1, hc.2 j⟩

/-! ## Controls -/

/-- `F` on `ℤ/9` (`p = 3`, `t = 2`) is the permutation `0,1,5,3,4,8,6,7,2`. -/
example : (List.range 9).map (fun z => Fn 3 z % 9) = [0, 1, 5, 3, 4, 8, 6, 7, 2] := by decide

/-- The hypothesis `p ≥ 3` is needed: for `p = 2`, `t = 2`, `C(F(z), 2) ≡ 0` on `ℤ/4`, so it does
not have Mahler degree `2`. -/
example : ∀ z : ZMod (2 ^ 2), (((Ft 2 2 z).val.choose 2 : ℕ) : ZMod 2) = 0 := by decide

end LemaLog
