/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
-- encaje: Teorema 7.1 (thm:signo) de characters_at_aP.tex: el valor con signo en la recta de ρ de Sp(2m)
module

public import Formalizations.RepresentationTheory.Symplectic.RhoLine
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The ρ-line of `Sp(2m)`: the value with its sign

With `F_ρ · Q = F_ℓ`, `ζ = exp(2πi p/q)`, `gcd(p,q) = 1`, `d q = 2m+2`, `N_q ℓ = N_q ρ`
and `c = (ℓ - ρ, ρ)`, the character on the line `ζ^{-c} · Q(ζ)` equals
`(-1)^E · ∏_{q ∣ a} a / ∏_{q ∣ b} b` with `E = Σ ⌊p a / q⌋ - Σ ⌊p b / q⌋` over the pairs of
`ℓ` and `ρ` (note, Theorem 7.1, `thm:signo`).  Floors are integer divisions by `q > 0`.

## Main result

* `RhoLine.thm_signo`.

## References

* C. Marín, *Integer character values on the ρ-line of Sp(2m)*, Zenodo (2026),
  doi:10.5281/zenodo.22683560.
-/

@[expose] public section

open Polynomial Finset Complex

namespace RhoLine

/-- `Σ_i (|x| - i) x_i` (0-indexed): the weighted sum with weights `(m, …, 1)`. -/
def wsum : List ℤ → ℤ
  | [] => 0
  | a :: xs => ((xs.length + 1 : ℕ) : ℤ) * a + wsum xs

lemma sum_flatMap_pair (a : ℤ) (xs : List ℤ) :
    (xs.flatMap fun b => [a - b, a + b]).sum = 2 * a * xs.length := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    simp only [List.flatMap_cons, List.sum_append, ih, List.sum_cons, List.sum_nil,
      List.length_cons]
    push_cast; ring

lemma length_flatMap_pair (a : ℤ) (xs : List ℤ) :
    (xs.flatMap fun b => [a - b, a + b]).length = 2 * xs.length := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, List.length_nil]
    omega

/-- `Σ_{a ∈ pairs x} a = 2 · Σ_i (m - i) x_i`. -/
lemma sum_pairs (x : List ℤ) : (pairs x).sum = 2 * wsum x := by
  induction x with
  | nil => simp [pairs, ResidueCapacity.posRootVals, wsum]
  | cons a xs ih =>
    have ih' : (ResidueCapacity.posRootVals xs).sum = 2 * wsum xs := ih
    simp only [pairs, ResidueCapacity.posRootVals, List.sum_cons, List.sum_append,
      sum_flatMap_pair, ih', wsum, two_nsmul]
    push_cast; ring

lemma length_pairs (x : List ℤ) : (pairs x).length = x.length ^ 2 := by
  induction x with
  | nil => simp [pairs, ResidueCapacity.posRootVals]
  | cons a xs ih =>
    have ih' : (ResidueCapacity.posRootVals xs).length = xs.length ^ 2 := ih
    simp only [pairs, ResidueCapacity.posRootVals, List.length_cons, List.length_append,
      length_flatMap_pair, ih']
    ring

/-- `c = (ℓ - ρ, ρ) = Σ_i (ℓ_i - ρ_i) ρ_i` through `wsum`. -/
lemma c_eq (m : ℕ) (l : List ℤ) (hl : l.length = m) :
    (List.zipWith (fun a b => (a - b) * b) l (rhoZ m)).sum = wsum l - wsum (rhoZ m) := by
  induction m generalizing l with
  | zero =>
    have : l = [] := List.length_eq_zero_iff.1 hl
    subst this
    simp [rhoZ, wsum]
  | succ m ih =>
    match l, hl with
    | a :: l', hl =>
      have hl' : l'.length = m := by simpa using hl
      rw [rhoZ_succ]
      simp only [List.zipWith_cons_cons, List.sum_cons, wsum, ih l' hl', hl', rhoZ_length]
      push_cast
      ring

lemma natAbs_sum (L : List ℤ) (h : ∀ a ∈ L, 0 < a) :
    (((L.map Int.natAbs).sum : ℕ) : ℤ) = L.sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ih := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    have ha := h a (List.mem_cons_self ..)
    simp only [List.map_cons, List.sum_cons]
    rw [Nat.cast_add, ih, Int.natAbs_of_nonneg ha.le]

lemma filter_neg_length (q : ℕ) (L : List ℤ) :
    (L.filter fun a => ¬ (q : ℤ) ∣ a).length + Ncount q L = L.length := by
  induction L with
  | nil => simp [Ncount]
  | cons a L ih =>
    by_cases h : (q : ℤ) ∣ a
    · simp only [List.filter_cons, h, not_true_eq_false, decide_false, Bool.false_eq_true,
        ite_false, List.length_cons]
      have hc : Ncount q (a :: L) = Ncount q L + 1 := by simp [Ncount, h]
      omega
    · simp only [List.filter_cons, h, not_false_eq_true, decide_true, ite_true, List.length_cons]
      have hc : Ncount q (a :: L) = Ncount q L := by simp [Ncount, h]
      omega

/-! ## The phase of the unit factors -/

/-- `w = exp(π i p / q)`, so that `ζ = exp(2π i p / q) = w²`. -/
noncomputable def wC (p q : ℕ) : ℂ := Complex.exp (((Real.pi * p / q : ℝ) : ℂ) * I)

lemma norm_wC (p q : ℕ) : ‖wC p q‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma wC_ne_zero (p q : ℕ) : wC p q ≠ 0 := Complex.exp_ne_zero _

lemma wC_pow (p q n : ℕ) :
    wC p q ^ n = Complex.exp (((n * (Real.pi * p / q) : ℝ) : ℂ) * I) := by
  rw [wC, ← Complex.exp_nat_mul]; congr 1; push_cast; ring

lemma wC_pow_q {q : ℕ} (hq : 0 < q) (p : ℕ) : wC p q ^ q = (-1) ^ p := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have e : (((q * (Real.pi * p / q) : ℝ) : ℂ)) * I = p * (Real.pi * I) := by
    push_cast; field_simp
  rw [wC_pow, e, Complex.exp_nat_mul, Complex.exp_pi_mul_I]

/-- For `q ∣ a`: the factor `(-1)^{pa/q} · w^a` is `1`. -/
lemma div_phase {q : ℕ} (hq : 0 < q) (p : ℕ) (a : ℤ) (ha : 0 < a) (h : (q : ℤ) ∣ a) :
    (-1 : ℂ) ^ ((p : ℤ) * a / q) * wC p q ^ a.natAbs = 1 := by
  obtain ⟨t, ht⟩ := h
  have ht0 : 0 ≤ t := by
    by_contra hneg
    push Not at hneg
    have : (q : ℤ) * t < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hq) hneg
    omega
  obtain ⟨T, rfl⟩ := Int.eq_ofNat_of_zero_le ht0
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have e1 : (p : ℤ) * a / q = ((p * T : ℕ) : ℤ) := by
    rw [ht, show (p : ℤ) * (q * T) = q * ((p * T : ℕ) : ℤ) by push_cast; ring]
    exact Int.mul_ediv_cancel_left _ hq0
  have e2 : a.natAbs = q * T := by rw [ht]; simp [Int.natAbs_mul]
  rw [e1, zpow_natCast, e2, pow_mul (wC p q) q T, wC_pow_q hq, ← pow_mul, ← pow_add, ← two_mul, pow_mul,
    neg_one_sq, one_pow]

/-- For `q ∤ N` and `gcd(p, q) = 1`: `1 - ζ^N = (-i) · (-1)^{⌊pN/q⌋} · (2 s) · w^N`, `s > 0`. -/
lemma unit_factor {p q : ℕ} (hq : 0 < q) (hpq : p.Coprime q) (N : ℕ) (hN : ¬ q ∣ N) :
    ∃ s : ℝ, 0 < s ∧
      1 - (wC p q ^ 2) ^ N = (-I) * (-1) ^ (p * N / q) * (2 * (s : ℂ)) * wC p q ^ N := by
  have hr : p * N % q ≠ 0 := fun h =>
    hN (hpq.symm.dvd_of_dvd_mul_left (Nat.dvd_of_mod_eq_zero h))
  have hdiv : p * N = q * (p * N / q) + p * N % q := (Nat.div_add_mod _ _).symm
  have hrpos : 0 < p * N % q := Nat.pos_of_ne_zero hr
  have hrlt : p * N % q < q := Nat.mod_lt _ hq
  generalize p * N / q = k at hdiv ⊢
  generalize p * N % q = r at hdiv hrpos hrlt
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hr' : (r : ℝ) = p * N - q * k := by
    have : (p : ℝ) * N = q * k + r := by exact_mod_cast hdiv
    linarith
  have hy : (N : ℝ) * (Real.pi * p / q) = Real.pi * r / q + k * Real.pi := by
    rw [hr']; field_simp; ring
  have hsr : (r : ℝ) < q := by exact_mod_cast hrlt
  refine ⟨Real.sin (Real.pi * r / q), Real.sin_pos_of_pos_of_lt_pi
    (by have : (0 : ℝ) < r := by exact_mod_cast hrpos
        positivity)
    (by rw [div_lt_iff₀ hqpos]; nlinarith [Real.pi_pos]), ?_⟩
  have h1 : wC p q ^ N = Complex.exp ((((N : ℝ) * (Real.pi * p / q) : ℝ) : ℂ) * I) := wC_pow p q N
  have h2 : (wC p q ^ 2) ^ N = (wC p q ^ N) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [h2, h1]
  generalize hyd : (N : ℝ) * (Real.pi * p / q) = y at hy ⊢
  have hprod : Complex.exp ((y : ℂ) * I) * Complex.exp (-(y : ℂ) * I) = 1 := by
    rw [← Complex.exp_add]; simp
  have hsin : Complex.sin (y : ℂ) =
      (Complex.exp (-(y : ℂ) * I) - Complex.exp ((y : ℂ) * I)) * I / 2 := by
    rw [Complex.sin]
  have hreal : Real.sin y = (-1) ^ k * Real.sin (Real.pi * r / q) := by
    rw [hy]; exact Real.sin_add_nat_mul_pi _ _
  have hX : (Complex.exp (-(y : ℂ) * I) - Complex.exp ((y : ℂ) * I)) * I / 2 -
      (-1) ^ k * ((Real.sin (Real.pi * r / q) : ℝ) : ℂ) = 0 := by
    rw [← hsin, ← Complex.ofReal_sin, hreal]; push_cast; ring
  linear_combination (-1) * hprod + (-2 * I * Complex.exp ((y : ℂ) * I)) * hX +
    (Complex.exp ((y : ℂ) * I) * (Complex.exp (-(y : ℂ) * I) - Complex.exp ((y : ℂ) * I))) *
      Complex.I_sq

/-- The unit part of the pairs, as `r · (-i)^u · (-1)^T · w^S` with `r > 0`. -/
lemma phase {p q : ℕ} (hq : 0 < q) (hpq : p.Coprime q) (L : List ℤ) (hpos : ∀ a ∈ L, 0 < a) :
    ∃ r : ℝ, 0 < r ∧
      (((L.filter fun a => ¬ (q : ℤ) ∣ a).map fun a => 1 - (wC p q ^ 2) ^ a.natAbs).prod =
        (r : ℂ) * (-I) ^ (L.filter fun a => ¬ (q : ℤ) ∣ a).length *
          (-1 : ℂ) ^ (L.map fun a => (p : ℤ) * a / q).sum *
            wC p q ^ (L.map Int.natAbs).sum) := by
  induction L with
  | nil => exact ⟨1, one_pos, by simp⟩
  | cons a L ih =>
    obtain ⟨r, hr, hL⟩ := ih fun b hb => hpos b (List.mem_cons_of_mem _ hb)
    have ha := hpos a (List.mem_cons_self ..)
    by_cases h : (q : ℤ) ∣ a
    · refine ⟨r, hr, ?_⟩
      have hd := div_phase hq p a ha h
      rw [List.filter_cons_of_neg (by simp [h]), List.map_cons, List.map_cons, List.sum_cons,
        List.sum_cons, zpow_add₀ (by norm_num), pow_add, hL]
      linear_combination (-((r : ℂ) * (-I) ^ (L.filter fun a => ¬ (q : ℤ) ∣ a).length *
        (-1 : ℂ) ^ (L.map fun a => (p : ℤ) * a / q).sum *
          wC p q ^ (L.map Int.natAbs).sum)) * hd
    · obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le ha.le
      have hN : ¬ q ∣ N := fun h' => h (Int.natCast_dvd_natCast.2 h')
      obtain ⟨s, hs, hs'⟩ := unit_factor hq hpq N hN
      refine ⟨2 * s * r, by positivity, ?_⟩
      have hx : (p : ℤ) * (N : ℤ) / (q : ℤ) = ((p * N / q : ℕ) : ℤ) := by
        rw [Int.natCast_div]; push_cast; rfl
      rw [List.filter_cons_of_pos (by simpa using h), List.map_cons, List.prod_cons,
        List.length_cons, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, hL]
      simp only [Int.natAbs_natCast, hx]
      rw [zpow_add₀ (by norm_num), zpow_natCast, hs', pow_succ, pow_add]
      push_cast; ring

lemma norm_phase {p q : ℕ} (r : ℝ) (hr : 0 < r) (u : ℕ) (T : ℤ) (S : ℕ) :
    ‖(r : ℂ) * (-I) ^ u * (-1 : ℂ) ^ T * wC p q ^ S‖ = r := by
  simp [norm_pow, norm_zpow, norm_wC, abs_of_pos hr]

/-- **Theorem 7.1 (`thm:signo`).**  Let `d q = 2m + 2`, `gcd(p, q) = 1`, `ζ = exp(2π i p / q)`,
`ℓ` of length `m` with positive pairs and `N_q ℓ = N_q ρ`, and `F_ρ · Q = F_ℓ`.  With
`c = (ℓ - ρ, ρ) = Σ_i (ℓ_i - ρ_i) ρ_i`,
`ζ^{-c} · Q(ζ) = (-1)^E · (∏_{q ∣ a} a) / (∏_{q ∣ b} b)`,
`E = Σ_{a ∈ pairs ℓ} ⌊p a / q⌋ - Σ_{b ∈ pairs ρ} ⌊p b / q⌋` (floors as integer division by `q`). -/
theorem thm_signo {q m d p : ℕ} (hq : 0 < q) (hd : d * q = 2 * m + 2) (hpq : p.Coprime q)
    {ζ : ℂ} (hζ : ζ = Complex.exp (2 * Real.pi * I * ((p : ℂ) / q)))
    (l : List ℤ) (hl : l.length = m) (hpl : ∀ a ∈ pairs l, 0 < a)
    (hN : N q l = N q (rhoZ m)) (Q : ℂ[X]) (hQ : F ℂ (rhoZ m) * Q = F ℂ l) :
    ζ ^ (-(List.zipWith (fun a b => (a - b) * b) l (rhoZ m)).sum) * Q.eval ζ =
      (-1 : ℂ) ^ (((pairs l).map fun a => (p : ℤ) * a / q).sum -
          ((pairs (rhoZ m)).map fun a => (p : ℤ) * a / q).sum) *
        ((((pairs l).filter fun a => (q : ℤ) ∣ a).map fun a : ℤ => (a : ℂ)).prod /
          (((pairs (rhoZ m)).filter fun b => (q : ℤ) ∣ b).map fun b : ℤ => (b : ℂ)).prod) := by
  have hprim : IsPrimitiveRoot ζ q := by
    rw [hζ]; exact Complex.isPrimitiveRoot_exp_of_coprime p q hq.ne' hpq
  have hw : ζ = wC p q ^ 2 := by
    rw [hζ, wC, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have : NeZero q := ⟨hq.ne'⟩
  have hev := eval_quot q hq ζ hprim.pow_eq_one l (rhoZ m) hpl (rhoZ_pairs_pos m) Q hQ hN
  have hu := lem_unit hq hd hprim l hl hpl hN
  have hB : (((pairs (rhoZ m)).filter fun b => (q : ℤ) ∣ b).map fun b : ℤ => (b : ℂ)).prod ≠ 0 := by
    apply List.prod_ne_zero
    intro h0
    obtain ⟨b, hb, hb0⟩ := List.mem_map.1 h0
    have := rhoZ_pairs_pos m b (List.mem_filter.1 hb).1
    have : b = 0 := by exact_mod_cast hb0
    omega
  have hul : ((pairs l).filter fun a => ¬ (q : ℤ) ∣ a).length =
      ((pairs (rhoZ m)).filter fun a => ¬ (q : ℤ) ∣ a).length := by
    have h1 := filter_neg_length q (pairs l)
    have h2 := filter_neg_length q (pairs (rhoZ m))
    have h3 : (pairs l).length = (pairs (rhoZ m)).length := by
      rw [length_pairs, length_pairs, hl, rhoZ_length]
    have h4 : Ncount q (pairs l) = Ncount q (pairs (rhoZ m)) := hN
    omega
  obtain ⟨rl, hrl, hVl⟩ := phase (p := p) hq hpq (pairs l) hpl
  obtain ⟨rr, hrr, hVr⟩ := phase (p := p) hq hpq (pairs (rhoZ m)) (rhoZ_pairs_pos m)
  have hS : (((pairs l).map Int.natAbs).sum : ℤ) =
      (((pairs (rhoZ m)).map Int.natAbs).sum : ℤ) +
        2 * (List.zipWith (fun a b => (a - b) * b) l (rhoZ m)).sum := by
    rw [natAbs_sum _ hpl, natAbs_sum _ (rhoZ_pairs_pos m), sum_pairs, sum_pairs, c_eq m l hl]
    ring
  subst hw
  rw [hVl, hVr] at hu hev
  rw [norm_phase rl hrl, norm_phase rr hrr] at hu
  subst hu
  rw [hul] at hev
  generalize (((pairs l).map Int.natAbs).sum) = Sl at hS hev
  generalize (((pairs (rhoZ m)).map Int.natAbs).sum) = Sr at hS hev
  generalize ((pairs l).map fun a => (p : ℤ) * a / q).sum = Tl at hev ⊢
  generalize ((pairs (rhoZ m)).map fun a => (p : ℤ) * a / q).sum = Tr at hev ⊢
  generalize (List.zipWith (fun a b => (a - b) * b) l (rhoZ m)).sum = c at hS ⊢
  generalize ((((pairs l).filter fun a => (q : ℤ) ∣ a).map fun a : ℤ => (a : ℂ)).prod) = A at hev ⊢
  generalize ((((pairs (rhoZ m)).filter fun b => (q : ℤ) ∣ b).map fun b : ℤ => (b : ℂ)).prod) = B
    at hev hB ⊢
  have hU : (-I : ℂ) ^ ((pairs (rhoZ m)).filter fun a => ¬ (q : ℤ) ∣ a).length ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.2 Complex.I_ne_zero)
  generalize (-I : ℂ) ^ ((pairs (rhoZ m)).filter fun a => ¬ (q : ℤ) ∣ a).length = U at hev hU
  have hw0 := wC_ne_zero p q
  have e1 : wC p q ^ Sl = wC p q ^ Sr * (wC p q ^ 2) ^ c := by
    have : (wC p q) ^ (Sl : ℤ) = wC p q ^ (Sr : ℤ) * (wC p q ^ (2 : ℤ)) ^ c := by
      rw [← zpow_mul, ← zpow_add₀ hw0, hS]
    simpa [zpow_natCast] using this
  rw [e1] at hev
  have hy0 : (wC p q ^ 2) ^ c ≠ 0 := zpow_ne_zero _ (pow_ne_zero _ hw0)
  rw [zpow_neg, zpow_sub₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  generalize (wC p q ^ 2) ^ c = y at hev hy0 ⊢
  have hs : (-1 : ℂ) ^ Tr ≠ 0 := zpow_ne_zero _ (by norm_num)
  generalize (-1 : ℂ) ^ Tr = sr at hev hs ⊢
  generalize (-1 : ℂ) ^ Tl = sl at hev ⊢
  generalize Q.eval (wC p q ^ 2) = Qv at hev ⊢
  have hwS : wC p q ^ Sr ≠ 0 := pow_ne_zero _ hw0
  generalize wC p q ^ Sr = wr at hev hwS
  have hk : Qv * B * sr = A * sl * y := by
    apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.2 hrr.ne') hU) hwS)
    linear_combination hev
  field_simp
  linear_combination hk

end RhoLine
