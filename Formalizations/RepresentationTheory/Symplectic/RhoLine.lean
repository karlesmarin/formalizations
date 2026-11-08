/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.RepresentationTheory.Symplectic.ResidueCapacity
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The ρ-line of `Sp(2m)`: the criterion, the value and the unit

For `x : List ℤ` the *pairs* of `x` are the values `(x, α)` for the positive roots `α` of `C_m`
(`ResidueCapacity.posRootVals`).  We put `F_x(X) = ∏_{a ∈ pairs x} (1 - X^a)` and
`N_q(x) = #{a ∈ pairs x : q ∣ a}`.

The character of `Sp(2m)` on the line `g_{p/q}` is *defined* here as `ζ^{-(λ,ρ)} · Q(ζ)` with
`F_ρ · Q = F_ℓ`, `ℓ = λ + ρ`.  That this is the character is formula (2) of the note (Weyl and the
bialternant); it is certified exactly in `anc/certificar_exacto.py` and is NOT formalised here.

## Main results

* `RhoLine.eval_quot`: value of `Q(ζ)` when `N_q x = N_q y` (note, Theorem `thm:valgen` core).
* `RhoLine.thm_crit`: Theorem 3.1 (`thm:crit`), `Q(ζ) ≠ 0 ↔ N_q x = N_q y`.
* `RhoLine.lem_unit`: Lemma 8.4 (`lem:unit`); `RhoLine.thm_valgen`: Theorem 8.3 (`thm:valgen`).

## References

* C. Marín, *Integer character values on the ρ-line of Sp(2m)*, Zenodo (2026),
  doi:10.5281/zenodo.22683560.
-/

@[expose] public section

open Polynomial Finset

namespace RhoLine

/-- The pairs `(x, α)`, `α > 0` a positive root of `C_m`: `2x_i`, `x_i ∓ x_j` (`i < j`). -/
def pairs (x : List ℤ) : List ℤ := ResidueCapacity.posRootVals x

/-- `∏_{a ∈ L} (1 - X^a)`, with `X^a` read as `X^{|a|}` (only positive `a` occur). -/
noncomputable def Fl (R : Type*) [CommRing R] (L : List ℤ) : R[X] :=
  (L.map fun a => (1 : R[X]) - X ^ a.natAbs).prod

/-- `F_x(X) = ∏_{a ∈ pairs x} (1 - X^a)`. -/
noncomputable def F (R : Type*) [CommRing R] (x : List ℤ) : R[X] := Fl R (pairs x)

/-- Number of entries of `L` divisible by `q`. -/
def Ncount (q : ℕ) (L : List ℤ) : ℕ := L.countP fun a => decide ((q : ℤ) ∣ a)

/-- `N_q(x) = #{a ∈ pairs x : q ∣ a}`. -/
def N (q : ℕ) (x : List ℤ) : ℕ := Ncount q (pairs x)

section Split

variable {R : Type*} [CommRing R]

/-- The cofactor of `(1 - X^q)^{N}`: `(1 - X^a)/(1 - X^q)` if `q ∣ a`, else `1 - X^a`. -/
noncomputable def Hl (R : Type*) [CommRing R] (q : ℕ) (L : List ℤ) : R[X] :=
  (L.map fun a => if (q : ℤ) ∣ a then ∑ i ∈ range (a.natAbs / q), ((X : R[X]) ^ q) ^ i
    else (1 : R[X]) - X ^ a.natAbs).prod

lemma Fl_cons (L : List ℤ) (a : ℤ) :
    Fl R (a :: L) = ((1 : R[X]) - X ^ a.natAbs) * Fl R L := rfl

lemma Hl_cons (q : ℕ) (L : List ℤ) (a : ℤ) :
    Hl R q (a :: L) = (if (q : ℤ) ∣ a then ∑ i ∈ range (a.natAbs / q), ((X : R[X]) ^ q) ^ i
      else (1 : R[X]) - X ^ a.natAbs) * Hl R q L := rfl

lemma Fl_split (q : ℕ) (L : List ℤ) :
    Fl R L = (1 - (X : R[X]) ^ q) ^ Ncount q L * Hl R q L := by
  induction L with
  | nil => simp [Fl, Hl, Ncount]
  | cons a L ih =>
    have ih' := ih
    by_cases h : (q : ℤ) ∣ a
    · have hq : q ∣ a.natAbs := Int.natCast_dvd.1 h
      have hmul : q * (a.natAbs / q) = a.natAbs := Nat.mul_div_cancel' hq
      have e : (1 : R[X]) - X ^ a.natAbs =
          (1 - X ^ q) * ∑ i ∈ range (a.natAbs / q), ((X : R[X]) ^ q) ^ i := by
        rw [mul_neg_geom_sum, ← pow_mul, hmul]
      have hc : Ncount q (a :: L) = Ncount q L + 1 := by
        simp [Ncount, h]
      rw [Fl_cons, Hl_cons, ite_eq_left h, hc, e, ih']
      ring
    · have hc : Ncount q (a :: L) = Ncount q L := by
        simp [Ncount, h]
      rw [Fl_cons, Hl_cons, ite_eq_right h, hc, ih']
      ring

end Split

section Eval

variable {K : Type*} [Field K]

/-- Evaluation at `ζ` of the cofactor `Hl`: `a/q` if `q ∣ a`, else `1 - ζ^a`. -/
def evalH (K : Type*) [Field K] (ζ : K) (q : ℕ) (L : List ℤ) : K :=
  (L.map fun a => if (q : ℤ) ∣ a then (((a.natAbs / q : ℕ)) : K) else 1 - ζ ^ a.natAbs).prod

lemma eval_Hl (q : ℕ) (ζ : K) (hζ : ζ ^ q = 1) (L : List ℤ) :
    (Hl K q L).eval ζ = evalH K ζ q L := by
  induction L with
  | nil => simp [Hl, evalH]
  | cons a L ih =>
    simp only [Hl, evalH, List.map_cons, List.prod_cons, eval_mul]
    simp only [Hl, evalH] at ih
    rw [ih]
    congr 1
    split_ifs with h
    · simp [eval_finsetSum, hζ]
    · simp

/-- The value factor `∏ (if q ∣ a then a else 1 - ζ^a)`. -/
def evalE (K : Type*) [Field K] (ζ : K) (q : ℕ) (L : List ℤ) : K :=
  (L.map fun a => if (q : ℤ) ∣ a then (a : K) else 1 - ζ ^ a.natAbs).prod

lemma evalE_eq (q : ℕ) (ζ : K) (L : List ℤ) (hpos : ∀ a ∈ L, 0 < a) :
    evalE K ζ q L = (q : K) ^ Ncount q L * evalH K ζ q L := by
  induction L with
  | nil => simp [evalE, evalH, Ncount]
  | cons a L ih =>
    have ih := ih fun b hb => hpos b (List.mem_cons_of_mem _ hb)
    have ha := hpos a (List.mem_cons_self ..)
    by_cases h : (q : ℤ) ∣ a
    · have hq : q ∣ a.natAbs := Int.natCast_dvd.1 h
      have hmul : q * (a.natAbs / q) = a.natAbs := Nat.mul_div_cancel' hq
      have hc : Ncount q (a :: L) = Ncount q L + 1 := by
        simp [Ncount, h]
      have haK : (a : K) = (q : K) * ((a.natAbs / q : ℕ) : K) := by
        have h0 : (a.natAbs : ℤ) = a := Int.natAbs_of_nonneg ha.le
        have h1 : (a : K) = ((a.natAbs : ℕ) : K) := by rw [← Int.cast_natCast, h0]
        have h2 : ((a.natAbs : ℕ) : K) = ((q * (a.natAbs / q) : ℕ) : K) := by rw [hmul]
        rw [h1, h2]; push_cast; ring
      simp only [evalE, evalH, List.map_cons, List.prod_cons, h, ite_true, hc] at ih ⊢
      rw [ih, haK, pow_succ]; ring
    · have hc : Ncount q (a :: L) = Ncount q L := by
        simp [Ncount, h]
      simp only [evalE, evalH, List.map_cons, List.prod_cons, h, ite_false, hc] at ih ⊢
      rw [ih]; ring

lemma evalE_split (q : ℕ) (ζ : K) (L : List ℤ) :
    evalE K ζ q L = (((L.filter fun a => (q : ℤ) ∣ a).map fun a : ℤ => (a : K)).prod) *
      ((L.filter fun a => ¬ (q : ℤ) ∣ a).map fun a => 1 - ζ ^ a.natAbs).prod := by
  induction L with
  | nil => simp [evalE]
  | cons a L ih =>
    simp only [evalE, List.map_cons, List.prod_cons] at ih ⊢
    by_cases h : (q : ℤ) ∣ a
    · simp [h, ih, mul_assoc]
    · simp [h, ih]
      ring

end Eval

section Quot

variable {K : Type*} [Field K] [CharZero K]

/-- **`eval_quot`.**  Let `F_y · Q = F_x` with `N_q x = N_q y`, all pairs positive, `ζ` a `q`-th root
of unity (`q ≥ 1`).  Then
`Q(ζ) · ∏_{q∣b} b · ∏_{q∤b} (1 - ζ^b) = ∏_{q∣a} a · ∏_{q∤a} (1 - ζ^a)`
(`b ∈ pairs y`, `a ∈ pairs x`).  (Note: Theorem `thm:valgen`, core step.) -/
theorem eval_quot (q : ℕ) (hq : 0 < q) (ζ : K) (hζ : ζ ^ q = 1) (x y : List ℤ)
    (hx : ∀ a ∈ pairs x, 0 < a) (hy : ∀ a ∈ pairs y, 0 < a) (Q : K[X])
    (hQ : F K y * Q = F K x) (hN : N q x = N q y) :
    Q.eval ζ * (((pairs y).filter fun b => (q : ℤ) ∣ b).map fun b : ℤ => (b : K)).prod *
        (((pairs y).filter fun b => ¬ (q : ℤ) ∣ b).map fun b => 1 - ζ ^ b.natAbs).prod =
      (((pairs x).filter fun a => (q : ℤ) ∣ a).map fun a : ℤ => (a : K)).prod *
        (((pairs x).filter fun a => ¬ (q : ℤ) ∣ a).map fun a => 1 - ζ ^ a.natAbs).prod := by
  have hu : (1 - (X : K[X]) ^ q) ≠ 0 := by
    intro h
    have := congrArg (Polynomial.coeff · q) h
    simp [coeff_X_pow, coeff_one, hq.ne'] at this
  unfold F at hQ
  rw [Fl_split q, Fl_split q] at hQ
  unfold N at hN
  rw [hN, mul_assoc] at hQ
  have hpow : (1 - (X : K[X]) ^ q) ^ Ncount q (pairs y) ≠ 0 := pow_ne_zero _ hu
  have hQ' : Hl K q (pairs y) * Q = Hl K q (pairs x) := by
    apply mul_left_cancel₀ hpow
    exact hQ
  have hev := congrArg (Polynomial.eval ζ) hQ'
  rw [eval_mul, eval_Hl q ζ hζ, eval_Hl q ζ hζ] at hev
  rw [mul_assoc, ← evalE_split, ← evalE_split, evalE_eq q ζ _ hx, evalE_eq q ζ _ hy]
  have hN' : Ncount q (pairs x) = Ncount q (pairs y) := hN
  rw [hN', ← hev]; ring

omit [CharZero K] in
lemma evalH_cons (q : ℕ) (ζ : K) (L : List ℤ) (a : ℤ) :
    evalH K ζ q (a :: L) =
      (if (q : ℤ) ∣ a then (((a.natAbs / q : ℕ)) : K) else 1 - ζ ^ a.natAbs) * evalH K ζ q L := rfl

/-- The cofactor does not vanish at a primitive `q`-th root when all entries are positive. -/
lemma evalH_ne_zero {q : ℕ} (hq : 0 < q) {ζ : K} (hζ : IsPrimitiveRoot ζ q) (L : List ℤ)
    (hpos : ∀ a ∈ L, 0 < a) : evalH K ζ q L ≠ 0 := by
  induction L with
  | nil => simp [evalH]
  | cons a L ih =>
    have ih := ih fun b hb => hpos b (List.mem_cons_of_mem _ hb)
    have ha := hpos a (List.mem_cons_self ..)
    rw [evalH_cons]
    refine mul_ne_zero ?_ ih
    split_ifs with h
    · have hq' : q ∣ a.natAbs := Int.natCast_dvd.1 h
      exact Nat.cast_ne_zero.2 (Nat.div_pos (Nat.le_of_dvd (Int.natAbs_pos.2 ha.ne') hq') hq).ne'
    · intro h0
      have h1 : ζ ^ a.natAbs = 1 := by
        have := sub_eq_zero.1 h0
        exact this.symm
      exact h (Int.natCast_dvd.2 ((hζ.pow_eq_one_iff_dvd _).1 h1))

lemma rootMultiplicity_pow' {p : K[X]} (hp : p ≠ 0) (x : K) (n : ℕ) :
    rootMultiplicity x (p ^ n) = n * rootMultiplicity x p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero n hp) hp), ih]
    ring

/-- **Theorem 3.1 (`thm:crit`).**  With `F_y · Q = F_x` (all pairs positive, `ζ` a primitive
`q`-th root of unity in a field of characteristic `0`): `N_q y ≤ N_q x`, and `Q(ζ) ≠ 0` iff
`N_q x = N_q y`.  Proof through `rootMultiplicity`: each `1 - X^a` vanishes at `ζ` to order `≥ 1`
if `q ∣ a` (here: the common factor `1 - X^q`) and `0` otherwise. -/
theorem thm_crit (q : ℕ) (hq : 0 < q) (ζ : K) (hζ : IsPrimitiveRoot ζ q) (x y : List ℤ)
    (hx : ∀ a ∈ pairs x, 0 < a) (hy : ∀ a ∈ pairs y, 0 < a) (Q : K[X])
    (hQ : F K y * Q = F K x) :
    N q y ≤ N q x ∧ (Q.eval ζ ≠ 0 ↔ N q x = N q y) := by
  have hζq : ζ ^ q = 1 := hζ.pow_eq_one
  have hHx : Hl K q (pairs x) ≠ 0 := fun h => evalH_ne_zero hq hζ _ hx
    (by rw [← eval_Hl q ζ hζq, h, eval_zero])
  have hHy : Hl K q (pairs y) ≠ 0 := fun h => evalH_ne_zero hq hζ _ hy
    (by rw [← eval_Hl q ζ hζq, h, eval_zero])
  have hu : (1 - (X : K[X]) ^ q) ≠ 0 := by
    intro h
    have := congrArg (Polynomial.coeff · q) h
    simp [coeff_X_pow, coeff_one, hq.ne'] at this
  unfold F at hQ
  rw [Fl_split q, Fl_split q, mul_assoc] at hQ
  have hR : (1 - (X : K[X]) ^ q) ^ Ncount q (pairs x) * Hl K q (pairs x) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hu) hHx
  have hL : (1 - (X : K[X]) ^ q) ^ Ncount q (pairs y) * (Hl K q (pairs y) * Q) ≠ 0 := by
    rw [hQ]; exact hR
  have hQne : Q ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul hL)
  have hHQ : Hl K q (pairs y) * Q ≠ 0 := right_ne_zero_of_mul hL
  have hnr : ∀ H : K[X], H ≠ 0 → H.eval ζ ≠ 0 → rootMultiplicity ζ H = 0 :=
    fun H _ h => rootMultiplicity_eq_zero h
  have hmx : rootMultiplicity ζ (Hl K q (pairs x)) = 0 :=
    hnr _ hHx (by rw [eval_Hl q ζ hζq]; exact evalH_ne_zero hq hζ _ hx)
  have hmy : rootMultiplicity ζ (Hl K q (pairs y)) = 0 :=
    hnr _ hHy (by rw [eval_Hl q ζ hζq]; exact evalH_ne_zero hq hζ _ hy)
  have hmu : 0 < rootMultiplicity ζ (1 - (X : K[X]) ^ q) := by
    rw [rootMultiplicity_pos hu]
    simp [IsRoot, hζq]
  have hm := congrArg (rootMultiplicity ζ) hQ
  rw [rootMultiplicity_mul hL, rootMultiplicity_mul hHQ, rootMultiplicity_mul hR,
    rootMultiplicity_pow' hu, rootMultiplicity_pow' hu, hmx, hmy] at hm
  have hN' : N q x = Ncount q (pairs x) := rfl
  have hN'' : N q y = Ncount q (pairs y) := rfl
  rw [hN', hN'']
  refine ⟨?_, ?_⟩
  · have : Ncount q (pairs y) * rootMultiplicity ζ (1 - (X : K[X]) ^ q) ≤
        Ncount q (pairs x) * rootMultiplicity ζ (1 - (X : K[X]) ^ q) := by omega
    exact Nat.le_of_mul_le_mul_right this hmu
  · have hpos := rootMultiplicity_pos hQne (x := ζ)
    constructor
    · intro h
      have h0 : rootMultiplicity ζ Q = 0 := rootMultiplicity_eq_zero (fun h' => h h')
      have : Ncount q (pairs x) * rootMultiplicity ζ (1 - (X : K[X]) ^ q) =
          Ncount q (pairs y) * rootMultiplicity ζ (1 - (X : K[X]) ^ q) := by omega
      exact Nat.eq_of_mul_eq_mul_right hmu this
    · intro h h0
      have h1 : 0 < rootMultiplicity ζ Q := hpos.2 h0
      rw [h] at hm
      omega

end Quot

/-! ## The bridge to `ResidueCapacity` (lists over `ZMod q`) -/

section Bridge

open ResidueCapacity

lemma map_posRootVals {G H : Type*} [AddCommGroup G] [AddCommGroup H] (φ : G →+ H)
    (x : List G) : (posRootVals x).map φ = posRootVals (x.map φ) := by
  induction x with
  | nil => simp [posRootVals]
  | cons a xs ih =>
    simp [posRootVals, List.map_flatMap, List.flatMap_map, ih]

/-- `ρ = (m, …, 1)` as integers. -/
def rhoZ (m : ℕ) : List ℤ := ((List.range m).reverse).map fun i => ((i + 1 : ℕ) : ℤ)

lemma rhoZ_length (m : ℕ) : (rhoZ m).length = m := by simp [rhoZ]

lemma rhoZ_cast (q m : ℕ) : (rhoZ m).map (Int.castAddHom (ZMod q)) = rho q m := by
  simp [rhoZ, rho, List.map_map, Function.comp_def]

lemma rhoZ_succ (m : ℕ) : rhoZ (m + 1) = ((m + 1 : ℕ) : ℤ) :: rhoZ m := by
  simp [rhoZ, List.range_succ]

lemma mem_rhoZ {m : ℕ} {b : ℤ} (h : b ∈ rhoZ m) : 1 ≤ b ∧ b ≤ m := by
  simp only [rhoZ, List.mem_map, List.mem_reverse, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  push_cast
  omega

/-- All pairs of `ρ` are positive. -/
lemma rhoZ_pairs_pos (m : ℕ) : ∀ a ∈ pairs (rhoZ m), 0 < a := by
  induction m with
  | zero => simp [pairs, rhoZ, posRootVals]
  | succ m ih =>
    intro a ha
    rw [pairs, rhoZ_succ] at ha
    simp only [posRootVals, List.mem_cons, List.mem_append, List.mem_flatMap] at ha
    rcases ha with (rfl | ⟨b, hb, hab⟩) | ha
    · rw [two_nsmul]; push_cast; omega
    · have := mem_rhoZ hb
      simp only [List.not_mem_nil, or_false] at hab
      rcases hab with rfl | rfl <;> push_cast <;> omega
    · exact ih a ha

lemma Nq_cast {q : ℕ} (l : List ℤ) :
    Nq (l.map (Int.castAddHom (ZMod q))) = N q l := by
  classical
  unfold Nq N Ncount pairs
  rw [← map_posRootVals, List.count_eq_countP, List.countP_map]
  refine List.countP_congr (fun a _ => ?_)
  simp [ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma coeff_Rl {G : Type*} [AddCommGroup G] [DecidableEq G] (L : List G) (g : G) :
    ((L.map fun v => s v + s (-v)).sum : AddMonoidAlgebra ℤ G).coeff g = o L g := by
  induction L with
  | nil => simp [o]
  | cons v L ih =>
    simp only [List.map_cons, List.sum_cons, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, s,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ih, o_cons]

lemma sum_o_mul {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] (f : G → ℝ)
    (hf : ∀ g, f (-g) = f g) (L : List G) :
    ∑ g, f g * (o L g : ℝ) = 2 * (L.map f).sum := by
  induction L with
  | nil => simp [o]
  | cons a L ih =>
    have e : ∀ g, f g * (o (a :: L) g : ℝ) = f g * (if a = g then 1 else 0) +
        f g * (if -a = g then 1 else 0) + f g * o L g := by
      intro g; rw [o_cons]; push_cast; ring
    simp only [e, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, ih, List.map_cons, List.sum_cons, hf]
    ring

/-- Equal residues `R x = R y` give equal sums of any even function over the pairs. -/
lemma sum_eq_of_R {q : ℕ} [NeZero q] (f : ZMod q → ℝ) (hf : ∀ g, f (-g) = f g)
    (x y : List (ZMod q)) (h : R x = R y) :
    ((posRootVals x).map f).sum = ((posRootVals y).map f).sum := by
  have hc : ∀ g, o (posRootVals x) g = o (posRootVals y) g := fun g => by
    rw [← coeff_Rl, ← coeff_Rl]
    exact congrArg (fun r : AddMonoidAlgebra ℤ (ZMod q) => r.coeff g) h
  have h1 := sum_o_mul f hf (posRootVals x)
  have h2 := sum_o_mul f hf (posRootVals y)
  simp only [hc] at h1
  linarith

/-- `g ↦ log ‖1 - ζ^g‖` (and `0` at `g = 0`) on `ZMod q`. -/
noncomputable def fz (q : ℕ) (ζ : ℂ) (g : ZMod q) : ℝ :=
  if g = 0 then 0 else Real.log ‖1 - ζ ^ g.val‖

lemma fz_even {q : ℕ} [NeZero q] {ζ : ℂ} (hζ : ζ ^ q = 1) (g : ZMod q) :
    fz q ζ (-g) = fz q ζ g := by
  by_cases hg : g = 0
  · simp [hg]
  · have hq : q ≠ 0 := NeZero.ne q
    have hng : -g ≠ 0 := neg_ne_zero.2 hg
    have hv : (-g).val = q - g.val := by rw [ZMod.neg_val, ite_eq_right hg]
    have hlt : g.val < q := ZMod.val_lt g
    have hprod : ζ ^ (q - g.val) * ζ ^ g.val = 1 := by
      rw [← pow_add, Nat.sub_add_cancel hlt.le, hζ]
    have e : 1 - ζ ^ (q - g.val) = ζ ^ (q - g.val) * (ζ ^ g.val - 1) := by
      linear_combination (-1 : ℂ) * hprod
    have hn : ‖ζ ^ (q - g.val)‖ = 1 := by
      rw [norm_pow, Complex.norm_eq_one_of_pow_eq_one hζ hq, one_pow]
    simp only [fz, hg, hng, ite_false, hv]
    rw [e, norm_mul, hn, one_mul, norm_sub_rev]

lemma fz_int {q : ℕ} [NeZero q] {ζ : ℂ} (hζ : ζ ^ q = 1) (a : ℤ) (ha : 0 < a) :
    fz q ζ (a : ZMod q) =
      if (q : ℤ) ∣ a then 0 else Real.log ‖1 - ζ ^ a.natAbs‖ := by
  by_cases h : (q : ℤ) ∣ a
  · have : (a : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd a q).2 h
    simp [fz, this, h]
  · have h0 : (a : ZMod q) ≠ 0 := fun h' => h ((ZMod.intCast_zmod_eq_zero_iff_dvd a q).1 h')
    have hc : (a : ZMod q) = ((a.natAbs : ℕ) : ZMod q) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg ha.le]
    have hv : (a : ZMod q).val = a.natAbs % q := by rw [hc, ZMod.val_natCast]
    simp only [fz, h0, h, ite_false]
    rw [hv, ← pow_eq_pow_mod _ hζ]

/-- Norm of the unit part as the exponential of a sum of `fz`. -/
lemma norm_unit {q : ℕ} [NeZero q] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ q) (L : List ℤ)
    (hpos : ∀ a ∈ L, 0 < a) :
    ‖((L.filter fun a => ¬ (q : ℤ) ∣ a).map fun a => 1 - ζ ^ a.natAbs).prod‖ =
      Real.exp ((L.map fun a : ℤ => fz q ζ (a : ZMod q)).sum) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ih := ih fun b hb => hpos b (List.mem_cons_of_mem _ hb)
    have ha := hpos a (List.mem_cons_self ..)
    by_cases h : (q : ℤ) ∣ a
    · rw [List.filter_cons_of_neg (by simp [h]), List.map_cons, List.sum_cons,
        fz_int hζ.pow_eq_one a ha, ite_eq_left h, zero_add]
      exact ih
    · have hne : 1 - ζ ^ a.natAbs ≠ 0 := by
        intro h0
        exact h (Int.natCast_dvd.2 ((hζ.pow_eq_one_iff_dvd _).1 (sub_eq_zero.1 h0).symm))
      have hpos' : 0 < ‖1 - ζ ^ a.natAbs‖ := norm_pos_iff.2 hne
      simp only [List.filter_cons, h, not_false_eq_true, decide_true, ite_true,
        List.map_cons, List.prod_cons, norm_mul, ih, List.sum_cons, fz_int hζ.pow_eq_one a ha,
        ite_false, Real.exp_add, Real.exp_log hpos']

/-- **Lemma 8.4 (`lem:unit`).**  For `ℓ` of length `m` with positive pairs, `d q = 2m + 2`, `ζ` a
primitive `q`-th root of unity in `ℂ`, and `N_q ℓ = N_q ρ`: the unit parts
`∏_{q ∤ a} (1 - ζ^a)` over the pairs of `ℓ` and of `ρ` have the same modulus.  Proof:
`N_q ℓ = N_q ρ` gives the capacities (`ResidueCapacity.conj_cap`), hence `ℛ_ℓ = ℛ_ρ`
(`ResidueCapacity.prop_res_cap`), so every even function has the same sum over the residues of the
pairs; apply it to `g ↦ log ‖1 - ζ^g‖`. -/
theorem lem_unit {q m d : ℕ} (hq : 0 < q) (hd : d * q = 2 * m + 2) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ q) (l : List ℤ) (hl : l.length = m)
    (hpl : ∀ a ∈ pairs l, 0 < a) (hN : N q l = N q (rhoZ m)) :
    ‖(((pairs l).filter fun a => ¬ (q : ℤ) ∣ a).map fun a => 1 - ζ ^ a.natAbs).prod‖ =
      ‖(((pairs (rhoZ m)).filter fun b => ¬ (q : ℤ) ∣ b).map
        fun b => 1 - ζ ^ b.natAbs).prod‖ := by
  have : NeZero q := ⟨hq.ne'⟩
  have hlen : (l.map (Int.castAddHom (ZMod q))).length = m := by simp [hl]
  have hNq : Nq (l.map (Int.castAddHom (ZMod q))) = Nq (rho q m) := by
    rw [← rhoZ_cast q m, Nq_cast, Nq_cast]; exact hN
  have hcap : Cap d (l.map (Int.castAddHom (ZMod q))) := (conj_cap hd _ hlen).2.1 hNq
  have hR := prop_res_cap hd _ hlen hcap
  have hsum := sum_eq_of_R (fz q ζ) (fz_even hζ.pow_eq_one) _ _ hR
  have h1 : ((pairs l).map fun a : ℤ => fz q ζ (a : ZMod q)).sum =
      ((pairs (rhoZ m)).map fun a : ℤ => fz q ζ (a : ZMod q)).sum := by
    rw [← map_posRootVals, ← rhoZ_cast q m, ← map_posRootVals, List.map_map, List.map_map] at hsum
    simpa [Function.comp_def, pairs] using hsum
  rw [norm_unit hζ _ hpl, norm_unit hζ _ (rhoZ_pairs_pos m), h1]

lemma norm_prod_int (L : List ℤ) (h : ∀ a ∈ L, 0 < a) :
    ‖(L.map fun a : ℤ => (a : ℂ)).prod‖ = (L.map fun a : ℤ => (a : ℝ)).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ih := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    have ha := h a (List.mem_cons_self ..)
    simp only [List.map_cons, List.prod_cons, norm_mul, ih, Complex.norm_intCast]
    rw [abs_of_pos (by exact_mod_cast ha)]

/-- **Theorem 8.3 (`thm:valgen`), modulo nothing.**  With `F_ρ · Q = F_ℓ` (so that the character on
the line is `ζ^{-(λ,ρ)} Q(ζ)`, of the same modulus as `Q(ζ)`), `d q = 2m + 2` and
`N_q ℓ = N_q ρ`:
`‖Q(ζ)‖ = (∏_{q ∣ a} a) / (∏_{q ∣ b} b)` over the pairs of `ℓ`, resp. `ρ`. -/
theorem thm_valgen {q m d : ℕ} (hq : 0 < q) (hd : d * q = 2 * m + 2) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ q) (l : List ℤ) (hl : l.length = m)
    (hpl : ∀ a ∈ pairs l, 0 < a) (hN : N q l = N q (rhoZ m)) (Q : ℂ[X])
    (hQ : F ℂ (rhoZ m) * Q = F ℂ l) :
    ‖Q.eval ζ‖ = (((pairs l).filter fun a => (q : ℤ) ∣ a).map fun a : ℤ => (a : ℝ)).prod /
      (((pairs (rhoZ m)).filter fun b => (q : ℤ) ∣ b).map fun b : ℤ => (b : ℝ)).prod := by
  have : NeZero q := ⟨hq.ne'⟩
  have hev := eval_quot q hq ζ hζ.pow_eq_one l (rhoZ m) hpl (rhoZ_pairs_pos m) Q hQ hN
  have hu := lem_unit hq hd hζ l hl hpl hN
  have hnorm := congrArg norm hev
  simp only [norm_mul] at hnorm
  rw [← hu] at hnorm
  have hUpos : 0 < ‖(((pairs l).filter fun a => ¬ (q : ℤ) ∣ a).map
      fun a => 1 - ζ ^ a.natAbs).prod‖ := by
    rw [norm_unit hζ _ hpl]; exact Real.exp_pos _
  have hPa := norm_prod_int ((pairs l).filter fun a => (q : ℤ) ∣ a)
    (fun a ha => hpl a (List.mem_filter.1 ha).1)
  have hPb := norm_prod_int ((pairs (rhoZ m)).filter fun a => (q : ℤ) ∣ a)
    (fun a ha => rhoZ_pairs_pos m a (List.mem_filter.1 ha).1)
  rw [hPa, hPb] at hnorm
  have hPbpos : 0 < (((pairs (rhoZ m)).filter fun b => (q : ℤ) ∣ b).map
      fun b : ℤ => (b : ℝ)).prod := by
    apply List.prod_pos
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
    exact_mod_cast rhoZ_pairs_pos m b (List.mem_filter.1 hb).1
  rw [eq_div_iff hPbpos.ne']
  have := mul_right_cancel₀ hUpos.ne' (by linarith [hnorm] :
    ‖Q.eval ζ‖ * (((pairs (rhoZ m)).filter fun b => (q : ℤ) ∣ b).map fun b : ℤ => (b : ℝ)).prod *
      ‖(((pairs l).filter fun a => ¬ (q : ℤ) ∣ a).map fun a => 1 - ζ ^ a.natAbs).prod‖ =
    (((pairs l).filter fun a => (q : ℤ) ∣ a).map fun a : ℤ => (a : ℝ)).prod *
      ‖(((pairs l).filter fun a => ¬ (q : ℤ) ∣ a).map fun a => 1 - ζ ^ a.natAbs).prod‖)
  exact this

end Bridge

end RhoLine
