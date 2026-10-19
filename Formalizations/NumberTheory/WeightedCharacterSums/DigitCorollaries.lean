/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Finset.Prod
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Zify
public import Mathlib.Tactic.Linarith

/-!
# Digit recursion over a commutative ring, and its corollaries for quadratic characters

The digit recursion of `SegmentoII.digit_recursion`, for `χ : ℕ → R` with values in any
commutative ring `R` (the hypotheses are bundled in `DigitosII.Hyp`), and the consequences drawn
from it for real characters: families of zeros of `S m = ∑_{n ≤ m} n χ(n)`, the block
construction, and the identities behind the weighted half sum. Where the paper uses the class
number `h(−q)`, the statements here use `T_q = ∑_{r<q} r χ(r)` (which is `q B_{1,χ}`).

## Main results

* `DigitosII.digit_recursion`, `DigitosII.zero_step`, `DigitosII.zeros_from_digits`: the digit
  recursion and the propagation of zeros, over `R`.
* `DigitosII.cor_digitos_a` – `DigitosII.cor_digitos_f_neg`: the corollaries (a)–(f) of the digit
  recursion (counts and explicit families of zeros, values at `(q^j − 1)/2`).
* `DigitosII.prop_bloques`: concatenation of digit blocks, with `T_q = −q h` as a hypothesis.
* `DigitosII.diag`: the two identities `4 χ(2) T = 2 (1 − χ(2)) T_f` and
  `f χ(2) C = (1 − 2 χ(2)) T_f` for `f = 2c + 1` and `χ` odd.
* `DigitosII.cor_orden_iff`, `DigitosII.cor_orden_zeros`, `DigitosII.cor_orden_trivial_on_two`:
  for `χ` with values in a domain with `2 ≠ 0` and `B_{1,χ} ≠ 0` as a hypothesis.

## References

* C. Marín, *Zeros of weighted partial sums of completely multiplicative functions: Dirichlet
  characters, the Euler factor at 2 and Conrey's sine series*, Zenodo (2026),
  doi:10.5281/zenodo.22847374.
-/

@[expose] public section

open Finset

namespace DigitosII

section Ring

variable {R : Type*} [CommRing R]

/-! ## Objects (those of `SegmentoII`, generalised from `ℤ` to a commutative ring) -/

/-- `S m = ∑_{n=1}^{m} n χ(n)`. -/
def S (χ : ℕ → R) (m : ℕ) : R := ∑ n ∈ Icc 1 m, (n : R) * χ n

/-- `C r = ∑_{n=1}^{r} χ(n)`. -/
def C (χ : ℕ → R) (r : ℕ) : R := ∑ n ∈ Icc 1 r, χ n

/-- `T r = ∑_{n=1}^{r} n χ(n)` (same as `S`; used for `r < q`). -/
def T (χ : ℕ → R) (r : ℕ) : R := ∑ n ∈ Icc 1 r, (n : R) * χ n

/-- `T_q = T (q-1) = ∑_{r<q} r χ(r)`; for a Dirichlet character modulo `q` this is `q B_{1,χ}`. -/
def Tq (χ : ℕ → R) (q : ℕ) : R := T χ (q - 1)

/-- The hypotheses of `thm:digitos`: `χ` completely multiplicative, periodic modulo `q` on the
residues `1, …, q-1`, `χ(q) = s`, and `∑_{r=1}^{q-1} χ(r) = 0`. -/
structure Hyp (q : ℕ) (χ : ℕ → R) (s : R) : Prop where
  two_le : 2 ≤ q
  mul : ∀ a b, χ (a * b) = χ a * χ b
  per : ∀ j r, 1 ≤ r → r < q → χ (j * q + r) = χ r
  at_q : χ q = s
  sum0 : C χ (q - 1) = 0

lemma S_zero (χ : ℕ → R) : S χ 0 = 0 := by simp [S]
lemma T_zero (χ : ℕ → R) : T χ 0 = 0 := by simp [T]
lemma C_zero (χ : ℕ → R) : C χ 0 = 0 := by simp [C]

lemma S_succ (χ : ℕ → R) (n : ℕ) : S χ (n + 1) = S χ n + ((n : R) + 1) * χ (n + 1) := by
  unfold S; rw [Finset.sum_Icc_succ_top (by omega)]; push_cast; ring

lemma T_succ (χ : ℕ → R) (n : ℕ) : T χ (n + 1) = T χ n + ((n : R) + 1) * χ (n + 1) :=
  S_succ χ n

lemma C_succ (χ : ℕ → R) (n : ℕ) : C χ (n + 1) = C χ n + χ (n + 1) := by
  unfold C; rw [Finset.sum_Icc_succ_top (by omega)]

lemma S_eq_T (χ : ℕ → R) (n : ℕ) : S χ n = T χ n := rfl

lemma T_range (χ : ℕ → R) (n : ℕ) : T χ n = ∑ i ∈ range n, ((i : R) + 1) * χ (i + 1) := by
  induction n with
  | zero => simp [T]
  | succ n ih => rw [T_succ, ih, sum_range_succ]

lemma C_range (χ : ℕ → R) (n : ℕ) : C χ n = ∑ i ∈ range n, χ (i + 1) := by
  induction n with
  | zero => simp [C]
  | succ n ih => rw [C_succ, ih, sum_range_succ]

/-! ## Theorem `thm:digitos` over a commutative ring -/

private lemma step_r {q : ℕ} {χ : ℕ → R} {s : R} (h : Hyp q χ s) (k r : ℕ) (hr : r + 1 < q)
    (ih : S χ (q * k + r) = s * q * S χ k + k * (Tq χ q + q * C χ r) + T χ r) :
    S χ (q * k + (r + 1)) = s * q * S χ k + k * (Tq χ q + q * C χ (r + 1)) + T χ (r + 1) := by
  have hχ : χ (q * k + r + 1) = χ (r + 1) := by
    rw [mul_comm q k, add_assoc]; exact h.per k (r + 1) (by omega) hr
  have e : q * k + (r + 1) = (q * k + r) + 1 := by omega
  rw [e, S_succ, C_succ, T_succ, hχ, ih]
  push_cast; ring

private lemma step_k {q : ℕ} {χ : ℕ → R} {s : R} (h : Hyp q χ s) (k : ℕ)
    (ih : S χ (q * k + (q - 1)) = s * q * S χ k + k * (Tq χ q + q * C χ (q - 1)) + T χ (q - 1)) :
    S χ (q * (k + 1) + 0) = s * q * S χ (k + 1) + ((k + 1 : ℕ) : R) * (Tq χ q + q * C χ 0)
      + T χ 0 := by
  have hq := h.two_le
  have e : q * (k + 1) + 0 = (q * k + (q - 1)) + 1 := by
    rw [Nat.mul_succ]; omega
  have hχ : χ (q * k + (q - 1) + 1) = s * χ (k + 1) := by
    rw [← e, add_zero, h.mul, h.at_q]
  have hcast : ((q * k + (q - 1) : ℕ) : R) + 1 = (q : R) * ((k : R) + 1) := by
    have h2 : q * k + (q - 1) + 1 = q * (k + 1) := by rw [← e, add_zero]
    have := congrArg (Nat.cast : ℕ → R) h2
    push_cast at this ⊢
    exact this
  have hTq : Tq χ q = T χ (q - 1) := rfl
  rw [e, S_succ, hχ, ih, hcast, S_succ, C_zero, T_zero, h.sum0, hTq]
  push_cast; ring

/-- **`thm:digitos` (4.1)**, for `χ` with values in a commutative ring. For `r < q`:
`S (q k + r) = s q S k + k (T_q + q C r) + T r`. -/
theorem digit_recursion {q : ℕ} {χ : ℕ → R} {s : R} (h : Hyp q χ s) (k r : ℕ) (hr : r < q) :
    S χ (q * k + r) = s * q * S χ k + k * (Tq χ q + q * C χ r) + T χ r := by
  have fill : ∀ k, (S χ (q * k + 0) = s * q * S χ k + k * (Tq χ q + q * C χ 0) + T χ 0) →
      ∀ r, r < q → S χ (q * k + r) = s * q * S χ k + k * (Tq χ q + q * C χ r) + T χ r := by
    intro k h0 r
    induction r with
    | zero => intro _; exact h0
    | succ r ihr => intro hr; exact step_r h k r hr (ihr (by omega))
  revert r
  induction k with
  | zero =>
    apply fill 0
    simp [S_zero, T_zero, C_zero]
  | succ k ih =>
    apply fill (k + 1)
    exact step_k h k (ih (q - 1) (by have := h.two_le; omega))

/-- The case `r = 0`: `S (q k) = s q S k + k T_q`. -/
lemma digit_zero {q : ℕ} {χ : ℕ → R} {s : R} (h : Hyp q χ s) (k : ℕ) :
    S χ (q * k) = s * q * S χ k + k * Tq χ q := by
  have := digit_recursion h k 0 (by have := h.two_le; omega)
  rw [add_zero, C_zero, T_zero] at this
  rw [this]; ring

/-- The digit set `R_q = {r < q : T_q + q C r = 0 = T r}`. -/
def InR (χ : ℕ → R) (q r : ℕ) : Prop := r < q ∧ Tq χ q + (q : R) * C χ r = 0 ∧ T χ r = 0

/-- First statement of `cor:digitos`, one step. -/
theorem zero_step {q : ℕ} {χ : ℕ → R} {s : R} (h : Hyp q χ s) (k r : ℕ)
    (hk : S χ k = 0) (hR : InR χ q r) : S χ (q * k + r) = 0 := by
  obtain ⟨hr, h1, h2⟩ := hR
  rw [digit_recursion h k r hr, hk, h1, h2]
  ring

/-- First statement of `cor:digitos`: every `m` whose base-`q` digits all lie in `R_q` has
`S m = 0`, for every value of `s`. -/
theorem zeros_from_digits {q : ℕ} {χ : ℕ → R} {s : R} (h : Hyp q χ s) (m : ℕ)
    (hm : ∀ d ∈ Nat.digits q m, InR χ q d) : S χ m = 0 := by
  have hq := h.two_le
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · exact S_zero χ
    · rw [Nat.digits_def' (by omega) hpos] at hm
      have hlt : m / q < m := Nat.div_lt_self hpos (by omega)
      have h0 := ih (m / q) hlt (fun d hd => hm d (List.mem_cons_of_mem _ hd))
      have hR := hm (m % q) List.mem_cons_self
      have := zero_step h (m / q) (m % q) h0 hR
      rwa [Nat.div_add_mod] at this

/-! ## `cor:digitos` (d) and (e) -/

/-- **`cor:digitos` (d)**, first sentence: for every `q` and `s`, if `S(q k) = 0` and
`C r = T r = 0`, then `S(q k + r) = 0`. -/
theorem cor_digitos_d {q : ℕ} {χ : ℕ → R} {s : R} (h : Hyp q χ s) {k r : ℕ} (hr : r < q)
    (hk : S χ (q * k) = 0) (hC : C χ r = 0) (hT : T χ r = 0) : S χ (q * k + r) = 0 := by
  have e0 := digit_zero h k
  rw [digit_recursion h k r hr, hC, hT]
  linear_combination hk - e0

/-- **`cor:digitos` (d)**, second sentence: when `q > 4` (the paper: `q > 3`, `q` an odd prime) and
`χ(2) = χ(3) = -1`, the digit `r = 4` qualifies, since `1 - 2 - 3 + 4 = 0`. -/
theorem cor_digitos_d_four {q : ℕ} {χ : ℕ → R} {s : R} (h : Hyp q χ s) (hq : 4 < q)
    (h1 : χ 1 = 1) (h2 : χ 2 = -1) (h3 : χ 3 = -1) {k : ℕ} (hk : S χ (q * k) = 0) :
    S χ (q * k + 4) = 0 := by
  have h4 : χ 4 = 1 := by
    have := h.mul 2 2
    rw [h2] at this
    simpa using this
  refine cor_digitos_d h hq hk ?_ ?_
  · simp [C_range, sum_range_succ, h1, h2, h3, h4]
  · simp [T_range, sum_range_succ, h1, h2, h3, h4]; norm_num

/-- **`cor:digitos` (e)**: if `s = -1`, then `S(q² m) = q² S(m)`. -/
theorem cor_digitos_e {q : ℕ} {χ : ℕ → R} (h : Hyp q χ (-1)) (m : ℕ) :
    S χ (q ^ 2 * m) = (q : R) ^ 2 * S χ m := by
  rw [show q ^ 2 * m = q * (q * m) by ring, digit_zero h, digit_zero h]
  push_cast; ring

/-- **`cor:digitos` (e)**, second clause: a single zero of `S` gives infinitely many,
`S(q^{2i} m) = 0` for every `i`. -/
theorem cor_digitos_e_zeros {q : ℕ} {χ : ℕ → R} (h : Hyp q χ (-1)) {m : ℕ} (hm : S χ m = 0)
    (i : ℕ) : S χ (q ^ (2 * i) * m) = 0 := by
  induction i with
  | zero => simpa using hm
  | succ i ih =>
    rw [show q ^ (2 * (i + 1)) * m = q ^ 2 * (q ^ (2 * i) * m) by ring, cor_digitos_e h, ih,
      mul_zero]

/-! ## `prop:bloques` -/

/-- With `s = 1` and `T_q = -q h`, `thm:digitos` reads `S(q k + r) = q S k + q k D(r) + T r`,
`D(r) = C(r) - h`. -/
lemma digit_D {q : ℕ} {χ : ℕ → R} {h : R} (H : Hyp q χ 1) (hT : Tq χ q = -(q : R) * h)
    (k r : ℕ) (hr : r < q) :
    S χ (q * k + r) = q * S χ k + q * k * (C χ r - h) + T χ r := by
  rw [digit_recursion H k r hr, hT]; ring

/-- Appending the digits of `B` (little-endian list `ds`, `B = ofDigits q ds`, `L = |ds|`) to `k`:
`S(q^L k + B) = q^L S k + q^L k ∑ D(d_i) + S(B)`. -/
lemma block_append {q : ℕ} {χ : ℕ → R} {h : R} (H : Hyp q χ 1) (hT : Tq χ q = -(q : R) * h)
    (ds : List ℕ) (hds : ∀ d ∈ ds, d < q) (k : ℕ) :
    S χ (q ^ ds.length * k + Nat.ofDigits q ds)
      = (q : R) ^ ds.length * S χ k
        + (q : R) ^ ds.length * k * (ds.map (fun d => C χ d - h)).sum
        + S χ (Nat.ofDigits q ds) := by
  induction ds with
  | nil => simp [S_zero]
  | cons d ds ih =>
    have hd : d < q := hds d List.mem_cons_self
    have ih := ih (fun x hx => hds x (List.mem_cons_of_mem _ hx))
    have e : q ^ (d :: ds).length * k + Nat.ofDigits q (d :: ds)
        = q * (q ^ ds.length * k + Nat.ofDigits q ds) + d := by
      simp only [List.length_cons, Nat.ofDigits_cons]; ring
    have eB : Nat.ofDigits q (d :: ds) = q * Nat.ofDigits q ds + d := by
      simp only [Nat.ofDigits_cons]; ring
    rw [e, eB, digit_D H hT _ d hd, digit_D H hT _ d hd, ih]
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    push_cast; ring

/-- **`prop:bloques` (4.4).** Let `s = 1` and `T_q = -q h` (for `q ≡ 3 mod 4`, `q > 3`, `h = h(-q)`
this is the class number formula). If the base-`q` digits `ds` of `B` (little-endian, leading
zeros allowed) have `∑ D(d_i) = 0` and `S(B) = h B`, then, with `Q = q^L`, every
`m_t = q B (1 + Q + … + Q^{t-1})` is a zero of `S`. -/
theorem prop_bloques {q : ℕ} {χ : ℕ → R} {h : R} (H : Hyp q χ 1) (hT : Tq χ q = -(q : R) * h)
    (ds : List ℕ) (hds : ∀ d ∈ ds, d < q) (hD : (ds.map (fun d => C χ d - h)).sum = 0)
    (hB : S χ (Nat.ofDigits q ds) = h * ((Nat.ofDigits q ds : ℕ) : R)) (t : ℕ) :
    S χ (q * (Nat.ofDigits q ds * ∑ i ∈ range t, (q ^ ds.length) ^ i)) = 0 := by
  set B := Nat.ofDigits q ds
  set Q := q ^ ds.length
  -- `S(k_t) = h k_t` along `k_t = B (1 + Q + … + Q^{t-1})`
  have key : ∀ t, S χ (B * ∑ i ∈ range t, Q ^ i) = h * ((B * ∑ i ∈ range t, Q ^ i : ℕ) : R) := by
    intro t
    induction t with
    | zero => simp [S_zero]
    | succ t ih =>
      have e : B * ∑ i ∈ range (t + 1), Q ^ i = Q * (B * ∑ i ∈ range t, Q ^ i) + B := by
        rw [sum_range_succ', mul_add, mul_sum, mul_sum, mul_sum]
        simp only [pow_succ, pow_zero, mul_one]
        congr 1
        refine sum_congr rfl (fun i _ => ?_)
        ring
      have hQ : ((Q : ℕ) : R) = (q : R) ^ ds.length := by simp [Q]
      rw [e, block_append H hT ds hds, ih, hD, hB]
      push_cast; rw [hQ]; ring
  have h0 := digit_D H hT (B * ∑ i ∈ range t, Q ^ i) 0 (by have := H.two_le; omega)
  rw [add_zero] at h0
  rw [h0, key t, C_zero, T_zero]
  push_cast; ring

/-! ## The identities of `thm:diag` -/

/-- Reflection: if `χ(q-1) = ε`, then `χ(q-b) = ε χ(b)` for `1 ≤ b < q`. -/
lemma reflect {q : ℕ} {χ : ℕ → R} {ε : R} (hmul : ∀ a b, χ (a * b) = χ a * χ b)
    (hper : ∀ j r, 1 ≤ r → r < q → χ (j * q + r) = χ r) (hε : χ (q - 1) = ε)
    {b : ℕ} (hb1 : 1 ≤ b) (hbq : b < q) : χ (q - b) = ε * χ b := by
  have e : (q - 1) * b = (b - 1) * q + (q - b) := by
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    zify [show 1 ≤ q' + 1 by omega, show 1 ≤ b' + 1 by omega, show b' + 1 ≤ q' + 1 by omega]
    ring
  rw [← hper (b - 1) (q - b) (by omega) (by omega), ← e, hmul, hε]

lemma sum_range_two_mul {M : Type*} [AddCommMonoid M] (g : ℕ → M) (c : ℕ) :
    ∑ i ∈ range (2 * c), g i = ∑ j ∈ range c, (g (2 * j) + g (2 * j + 1)) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [show 2 * (c + 1) = 2 * c + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, add_assoc]

/-- **The identities in the proof of `thm:diag`** (Kanemitsu–Kuzumaki, Kučera), for `f = 2c+1`
odd and `χ` completely multiplicative, periodic modulo `f` on the residues and odd
(`χ(f-1) = -1`), with values in any commutative ring. Here `T c = ∑_{n ≤ (f-1)/2} n χ(n)`,
`C c = ∑_{n ≤ (f-1)/2} χ(n)` and `T_f = ∑_{a<f} a χ(a) = f B_{1,χ}`:
  `4 χ(2) T = 2 (1 - χ(2)) T_f`   (i.e. `T = (f/2) B_{1,χ} (χ(2)^{-1} - 1)`),
  `f χ(2) C = (1 - 2 χ(2)) T_f`   (i.e. `C = (χ(2)^{-1} - 2) B_{1,χ}`),
and `∑_{a<f} χ(a) = 0`. -/
theorem diag {c : ℕ} {χ : ℕ → R} (hmul : ∀ a b, χ (a * b) = χ a * χ b)
    (hper : ∀ j r, 1 ≤ r → r < 2 * c + 1 → χ (j * (2 * c + 1) + r) = χ r)
    (hodd : χ (2 * c) = -1) :
    4 * χ 2 * T χ c = 2 * (1 - χ 2) * Tq χ (2 * c + 1) ∧
    (2 * (c : R) + 1) * χ 2 * C χ c = (1 - 2 * χ 2) * Tq χ (2 * c + 1) ∧
    C χ (2 * c) = 0 := by
  have hev : ∀ n, χ (2 * n) = χ 2 * χ n := fun n => hmul 2 n
  have hrefl : ∀ j, j < c → χ (2 * (c - 1 - j) + 1) = -(χ 2 * χ (j + 1)) := by
    intro j hj
    have := reflect (q := 2 * c + 1) (ε := -1) hmul hper hodd (b := 2 * (j + 1)) (by omega)
      (by omega)
    rw [show 2 * c + 1 - 2 * (j + 1) = 2 * (c - 1 - j) + 1 by omega, hev] at this
    rw [this]; ring
  have hcast : ∀ j, j < c → ((c - 1 - j : ℕ) : R) = (c : R) - 1 - j := by
    intro j hj
    have e : c - 1 - j + 1 + j = c := by omega
    have := congrArg (Nat.cast : ℕ → R) e
    push_cast at this
    linear_combination this
  have hA : Tq χ (2 * c + 1) = T χ (2 * c) := rfl
  -- `T_f` = odd part + even part
  have eA : Tq χ (2 * c + 1)
      = ∑ j ∈ range c, (2 * (j : R) + 1) * χ (2 * j + 1) + 2 * χ 2 * T χ c := by
    rw [hA, T_range, sum_range_two_mul, T_range, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl (fun j _ => ?_)
    rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, hev]
    push_cast; ring
  -- odd part, by reflection `b ↦ f - b`
  have eO : ∑ j ∈ range c, (2 * (j : R) + 1) * χ (2 * j + 1)
      = -((2 * (c : R) + 1) * χ 2 * C χ c) + 2 * χ 2 * T χ c := by
    rw [← sum_range_reflect (fun j => (2 * (j : R) + 1) * χ (2 * j + 1)) c, C_range, T_range,
      mul_sum, mul_sum, ← sum_neg_distrib, ← sum_add_distrib]
    refine sum_congr rfl (fun j hj => ?_)
    have hj' : j < c := mem_range.mp hj
    rw [hrefl j hj', hcast j hj']
    ring
  have eOu : ∑ j ∈ range c, χ (2 * j + 1) = -(χ 2 * C χ c) := by
    rw [← sum_range_reflect (fun j => χ (2 * j + 1)) c, C_range, mul_sum, ← sum_neg_distrib]
    refine sum_congr rfl (fun j hj => ?_)
    rw [hrefl j (mem_range.mp hj)]
  -- `χ(2) T_f = ∑ a χ(2a)`, split at `a = c`
  have e2 : χ 2 * Tq χ (2 * c + 1)
      = χ 2 * T χ c + ∑ i ∈ range c, ((c : R) + i + 1) * χ (2 * i + 1) := by
    rw [hA, T_range, show 2 * c = c + c by ring, sum_range_add, mul_add, T_range]
    congr 1
    rw [mul_sum]
    refine sum_congr rfl (fun i hi => ?_)
    have hi' : i < c := mem_range.mp hi
    have hχ : χ 2 * χ (c + i + 1) = χ (2 * i + 1) := by
      rw [← hev, show 2 * (c + i + 1) = 1 * (2 * c + 1) + (2 * i + 1) by ring,
        hper 1 (2 * i + 1) (by omega) (by omega)]
    push_cast
    linear_combination ((c : R) + i + 1) * hχ
  have e5 : 2 * ∑ i ∈ range c, ((c : R) + i + 1) * χ (2 * i + 1)
      = ∑ j ∈ range c, (2 * (j : R) + 1) * χ (2 * j + 1)
        + (2 * (c : R) + 1) * ∑ j ∈ range c, χ (2 * j + 1) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl (fun i _ => ?_)
    ring
  refine ⟨?_, ?_, ?_⟩
  · linear_combination 2 * e2 + e5 + (2 * (c : R) + 1) * eOu - 2 * eA - eO
  · linear_combination 2 * e2 + e5 + (2 * (c : R) + 1) * eOu - eA
  · rw [C_range, sum_range_two_mul, sum_add_distrib]
    have : ∑ j ∈ range c, χ (2 * j + 1 + 1) = χ 2 * C χ c := by
      rw [C_range, mul_sum]
      refine sum_congr rfl (fun j _ => ?_)
      rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, hev]
    rw [this]
    linear_combination eOu

/-- `(f^j - 1)/2` with `f = 2c+1`: `2 m_j + 1 = f^j`. -/
lemma two_half_pow (c j : ℕ) : 2 * (((2 * c + 1) ^ j - 1) / 2) + 1 = (2 * c + 1) ^ j := by
  obtain ⟨Y, hY⟩ : Odd ((2 * c + 1) ^ j) := Odd.pow ⟨c, rfl⟩
  rw [hY, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ two_pos]

/-- `m_{j+1} = f m_j + c`: the base-`f` digits of `(f^j - 1)/2` are all `c = (f-1)/2`. -/
lemma half_pow_succ (c j : ℕ) :
    ((2 * c + 1) ^ (j + 1) - 1) / 2 = (2 * c + 1) * (((2 * c + 1) ^ j - 1) / 2) + c := by
  obtain ⟨Y, hY⟩ : Odd ((2 * c + 1) ^ j) := Odd.pow ⟨c, rfl⟩
  have e : (2 * Y + 1) * (2 * c + 1) = 2 * ((2 * c + 1) * Y + c) + 1 := by ring
  rw [pow_succ, hY, e, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ two_pos, Nat.add_sub_cancel,
    Nat.mul_div_cancel_left _ two_pos]

end Ring

/-! ## `cor:orden` (4.5): `χ` with values in an integral domain -/

section Domain

variable {R : Type*} [CommRing R] [IsDomain R]

omit [IsDomain R] in
/-- The hypotheses of `thm:digitos` hold for an odd `χ` (the sum `∑ χ(r) = 0` is automatic). -/
lemma hyp_of_odd {c : ℕ} (hc : 1 ≤ c) {χ : ℕ → R} {s : R}
    (hmul : ∀ a b, χ (a * b) = χ a * χ b)
    (hper : ∀ j r, 1 ≤ r → r < 2 * c + 1 → χ (j * (2 * c + 1) + r) = χ r)
    (hodd : χ (2 * c) = -1) (hs : χ (2 * c + 1) = s) : Hyp (2 * c + 1) χ s :=
  ⟨by omega, hmul, hper, hs, (diag hmul hper hodd).2.2⟩

/-- **`cor:orden` (4.5)**, the equivalence. `q` odd, `χ` completely multiplicative, periodic
modulo `q` on the residues, odd (`χ(q-1) = -1`), with values in an integral domain where `2 ≠ 0`,
and `T_q = q B_{1,χ} ≠ 0` (for a primitive odd character this is `L(0,χ) ≠ 0`; here a
hypothesis). Then `S((q-1)/2) = 0 ↔ χ(2) = 1`. -/
theorem cor_orden_iff {q : ℕ} (hq : q % 2 = 1) {χ : ℕ → R} (h2R : (2 : R) ≠ 0)
    (hmul : ∀ a b, χ (a * b) = χ a * χ b)
    (hper : ∀ j r, 1 ≤ r → r < q → χ (j * q + r) = χ r)
    (hodd : χ (q - 1) = -1) (hA : Tq χ q ≠ 0) :
    S χ ((q - 1) / 2) = 0 ↔ χ 2 = 1 := by
  obtain ⟨c, rfl⟩ : ∃ c, q = 2 * c + 1 := ⟨q / 2, by omega⟩
  rw [show (2 * c + 1 - 1) / 2 = c by omega]
  rw [show 2 * c + 1 - 1 = 2 * c by omega] at hodd
  have dT := (diag hmul hper hodd).1
  rw [S_eq_T]
  constructor
  · intro hT0
    rw [hT0, mul_zero, eq_comm, mul_eq_zero, mul_eq_zero] at dT
    rcases dT with (h | h) | h
    · exact absurd h h2R
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h hA
  · intro h2
    rw [h2, sub_self, mul_zero, zero_mul, mul_one] at dT
    have h4 : (4 : R) ≠ 0 := by
      rw [show (4 : R) = 2 * 2 by norm_num]; exact mul_ne_zero h2R h2R
    exact (mul_eq_zero.mp dT).resolve_left h4

/-- **`cor:orden` (4.5)**, the zeros: if moreover `χ(2) = 1`, then `(q-1)/2 ∈ R_q` and
`S((q^j - 1)/2) = 0` for every `j` (for every value `s = χ(q)`; `B_{1,χ} ≠ 0` is not needed). -/
theorem cor_orden_zeros {q : ℕ} (hq : q % 2 = 1) (hq3 : 3 ≤ q) {χ : ℕ → R} {s : R}
    (h2R : (2 : R) ≠ 0)
    (hmul : ∀ a b, χ (a * b) = χ a * χ b)
    (hper : ∀ j r, 1 ≤ r → r < q → χ (j * q + r) = χ r)
    (hodd : χ (q - 1) = -1) (hs : χ q = s) (h2 : χ 2 = 1) (j : ℕ) :
    S χ ((q ^ j - 1) / 2) = 0 := by
  obtain ⟨c, rfl⟩ : ∃ c, q = 2 * c + 1 := ⟨q / 2, by omega⟩
  rw [show 2 * c + 1 - 1 = 2 * c by omega] at hodd
  have H := hyp_of_odd (by omega) hmul hper hodd hs
  obtain ⟨dT, dU, -⟩ := diag hmul hper hodd
  rw [h2] at dT dU
  have hR : InR χ (2 * c + 1) c := by
    refine ⟨by omega, ?_, ?_⟩
    · push_cast; linear_combination dU
    · have h4 : (4 : R) ≠ 0 := by
        rw [show (4 : R) = 2 * 2 by norm_num]; exact mul_ne_zero h2R h2R
      have : (4 : R) * T χ c = 0 := by linear_combination dT
      exact (mul_eq_zero.mp this).resolve_left h4
  induction j with
  | zero => simp [S_zero]
  | succ j ih => rw [half_pow_succ]; exact zero_step H _ c ih hR

omit [IsDomain R] in
/-- **`cor:orden` (4.5)**, last sentence: given `χ(1) = 1`, `χ(2) = 1` iff `χ` is trivial on the
powers of `2`. -/
theorem cor_orden_trivial_on_two {χ : ℕ → R} (hmul : ∀ a b, χ (a * b) = χ a * χ b)
    (h1 : χ 1 = 1) : χ 2 = 1 ↔ ∀ k, χ (2 ^ k) = 1 := by
  have hp : ∀ k, χ (2 ^ k) = χ 2 ^ k := by
    intro k
    induction k with
    | zero => simpa using h1
    | succ k ih => rw [pow_succ, hmul, ih, pow_succ]
  constructor
  · intro h k; rw [hp, h, one_pow]
  · intro h; simpa using h 1

end Domain

/-- **`cor:digitos` (d)**, third sentence: for `q = 3` and `s = -1` (with `χ(2) = -1`),
`S(3k) = 0` implies `S(3k + 4) = 0`. -/
theorem cor_digitos_d_three {χ : ℕ → ℤ} (h : Hyp 3 χ (-1)) (h1 : χ 1 = 1) (h2 : χ 2 = -1)
    {k : ℕ} (hk : S χ (3 * k) = 0) : S χ (3 * k + 4) = 0 := by
  have hT : Tq χ 3 = -1 := by
    simp [Tq, T_range, sum_range_succ, h1, h2]
  have e0 := digit_zero h k
  rw [hk, hT] at e0
  push_cast at e0
  have hdvd : (3 : ℤ) ∣ (k : ℤ) := ⟨-S χ k, by linarith⟩
  obtain ⟨j, rfl⟩ := Int.natCast_dvd_natCast.mp hdvd
  have c1 : χ (3 * (3 * j) + 1) = 1 := by
    rw [show 3 * (3 * j) + 1 = (3 * j) * 3 + 1 by ring, h.per _ 1 (by norm_num) (by norm_num), h1]
  have c2 : χ (3 * (3 * j) + 1 + 1) = -1 := by
    rw [show 3 * (3 * j) + 1 + 1 = (3 * j) * 3 + 2 by ring, h.per _ 2 (by norm_num) (by norm_num),
      h2]
  have c3 : χ (3 * (3 * j) + 1 + 1 + 1) = -1 := by
    rw [show 3 * (3 * j) + 1 + 1 + 1 = 3 * (j * 3 + 1) by ring, h.mul, h.at_q,
      h.per _ 1 (by norm_num) (by norm_num), h1]; norm_num
  have c4 : χ (3 * (3 * j) + 1 + 1 + 1 + 1) = 1 := by
    rw [show 3 * (3 * j) + 1 + 1 + 1 + 1 = (3 * j + 1) * 3 + 1 by ring,
      h.per _ 1 (by norm_num) (by norm_num), h1]
  rw [show 3 * (3 * j) + 4 = 3 * (3 * j) + 1 + 1 + 1 + 1 by ring, S_succ, S_succ, S_succ, S_succ,
    hk, c1, c2, c3, c4]
  push_cast; ring


/-! ## `cor:digitos` (a), (b), (c), (f), with `T_q = q B_{1,χ}` in place of `h(-q)` -/

section Optional

variable {R : Type*} [CommRing R]

/-- The sequence of `cor:digitos` (c): `z_0 = q`, `z_{i+1} = q (z_i + 1)`. -/
def zseq (q : ℕ) : ℕ → ℕ
  | 0 => q
  | i + 1 => q * (zseq q i + 1)

lemma dvd_zseq (q i : ℕ) : q ∣ zseq q i := by
  cases i with
  | zero => exact dvd_refl q
  | succ i => exact dvd_mul_right q _

lemma S_one (χ : ℕ → R) : S χ 1 = χ 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, S_succ, S_zero]; push_cast; ring

/-- **`cor:digitos` (c)**, `q > 3`: with `s = 1`, `χ(1) = 1` and `T_q = -q` (that is
`B_{1,χ} = -1`; for `q ≡ 3 mod 4`, `q > 3` this is `h(-q) = 1`), `S` vanishes along
`z_0 = q`, `z_{i+1} = q (z_i + 1)`. -/
theorem cor_digitos_c {q : ℕ} {χ : ℕ → R} (H : Hyp q χ 1) (h1 : χ 1 = 1)
    (hT : Tq χ q = -(q : R)) (i : ℕ) : S χ (zseq q i) = 0 := by
  induction i with
  | zero =>
    have := digit_zero H 1
    rw [mul_one] at this
    simp only [zseq]
    rw [this, S_one, h1, hT]; push_cast; ring
  | succ i ih =>
    obtain ⟨w, hw⟩ := dvd_zseq q i
    have hχ : χ (zseq q i + 1) = 1 := by
      rw [hw, mul_comm, H.per w 1 le_rfl (by have := H.two_le; omega), h1]
    simp only [zseq]
    rw [digit_zero H, S_succ, ih, hχ, hT]; push_cast; ring

/-- **`cor:digitos` (c)**, `q = 3`: with `s = 1`, `χ(1) = 1`, `χ(2) = -1`, `S` vanishes along
`z_0 = 27`, `z_{i+1} = 27 (z_i + 1)`. -/
theorem cor_digitos_c_three {χ : ℕ → R} (H : Hyp 3 χ 1) (h1 : χ 1 = 1) (h2 : χ 2 = -1)
    (i : ℕ) : S χ (zseq 27 i) = 0 := by
  have hT : Tq χ 3 = -1 := by norm_num [Tq, T_range, sum_range_succ, h1, h2]
  have key : ∀ k, S χ (27 * k) = 27 * S χ k - 27 * k := by
    intro k
    rw [show 27 * k = 3 * (3 * (3 * k)) by ring, digit_zero H, digit_zero H, digit_zero H, hT]
    push_cast; ring
  induction i with
  | zero =>
    have := key 1
    simp only [mul_one, Nat.cast_one, S_one, h1] at this
    simp only [zseq]
    rw [this]; ring
  | succ i ih =>
    obtain ⟨w, hw⟩ := dvd_zseq 27 i
    have hχ : χ (zseq 27 i + 1) = 1 := by
      rw [hw, show 27 * w + 1 = (9 * w) * 3 + 1 by ring, H.per _ 1 le_rfl (by norm_num), h1]
    simp only [zseq]
    rw [key, S_succ, ih, hχ]; push_cast; ring

end Optional

/-- An even `χ` (`χ(q-1) = 1`) with `∑ χ(r) = 0` has `T_q = 0`. -/
lemma Tq_even {q : ℕ} {χ : ℕ → ℤ} {s : ℤ} (H : Hyp q χ s) (heven : χ (q - 1) = 1) :
    Tq χ q = 0 := by
  have hq := H.two_le
  have e : ∑ i ∈ range (q - 1), ((i : ℤ) + 1) * χ (i + 1)
      = ∑ i ∈ range (q - 1), ((q : ℤ) - (i + 1)) * χ (i + 1) := by
    rw [← sum_range_reflect (fun i => ((i : ℤ) + 1) * χ (i + 1)) (q - 1)]
    refine sum_congr rfl (fun i hi => ?_)
    have hi' : i < q - 1 := mem_range.mp hi
    have hc : ((q - 1 - 1 - i : ℕ) : ℤ) = (q : ℤ) - 2 - i := by omega
    rw [show q - 1 - 1 - i + 1 = q - (i + 1) by omega,
      reflect H.mul H.per heven (by omega) (by omega), hc]
    ring
  have e2 : ∑ i ∈ range (q - 1), ((q : ℤ) - (i + 1)) * χ (i + 1)
      = (q : ℤ) * ∑ i ∈ range (q - 1), χ (i + 1)
        - ∑ i ∈ range (q - 1), ((i : ℤ) + 1) * χ (i + 1) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl (fun i _ => ?_)
    ring
  have h0 := H.sum0
  rw [C_range] at h0
  rw [e2, h0] at e
  show T χ (q - 1) = 0
  rw [T_range]
  linarith

/-- The numbers of at most `J` base-`q` digits, all in `{0, q-1}`. -/
def G (q : ℕ) : ℕ → Finset ℕ
  | 0 => {0}
  | J + 1 => (G q J ×ˢ ({0, q - 1} : Finset ℕ)).image (fun p => q * p.1 + p.2)

lemma zero_mem_G (q J : ℕ) : 0 ∈ G q J := by
  induction J with
  | zero => simp [G]
  | succ J ih =>
    simp only [G, mem_image, mem_product, mem_insert, mem_singleton]
    exact ⟨(0, 0), ⟨ih, Or.inl rfl⟩, by simp⟩

lemma G_card {q : ℕ} (hq : 2 ≤ q) (J : ℕ) : (G q J).card = 2 ^ J := by
  induction J with
  | zero => simp [G]
  | succ J ih =>
    simp only [G]
    rw [card_image_of_injOn, card_product, ih, card_pair (by omega), pow_succ]
    rintro ⟨a, d⟩ hp ⟨a', d'⟩ hp' heq
    simp only [coe_product, Set.mem_prod, mem_coe, mem_insert, mem_singleton] at hp hp'
    simp only at heq
    have hd : d < q := by omega
    have hd' : d' < q := by omega
    have e1 : d = d' := by
      have := congrArg (· % q) heq
      simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hd'] using this
    have e2 : a = a' := by
      have := congrArg (· / q) heq
      simpa [Nat.mul_add_div (by omega : q > 0), Nat.div_eq_of_lt hd, Nat.div_eq_of_lt hd']
        using this
    rw [e1, e2]

/-- **`cor:digitos` (a)**, the digits: for `χ` even (`χ(q-1) = 1`; for a quadratic `χ` this is
`q ≡ 1 mod 4`), `0, q-1 ∈ R_q`. -/
theorem cor_digitos_a_digits {q : ℕ} {χ : ℕ → ℤ} {s : ℤ} (H : Hyp q χ s)
    (heven : χ (q - 1) = 1) : InR χ q 0 ∧ InR χ q (q - 1) := by
  have hq := H.two_le
  have hT := Tq_even H heven
  refine ⟨⟨by omega, by rw [C_zero, hT]; ring, T_zero χ⟩, ⟨by omega, by rw [H.sum0, hT]; ring, hT⟩⟩

lemma G_spec {q : ℕ} {χ : ℕ → ℤ} {s : ℤ} (H : Hyp q χ s) (heven : χ (q - 1) = 1) (J : ℕ) :
    ∀ x ∈ G q J, x < q ^ J ∧ S χ x = 0 := by
  have hq := H.two_le
  obtain ⟨R0, Rq⟩ := cor_digitos_a_digits H heven
  induction J with
  | zero =>
    intro x hx
    simp only [G, mem_singleton] at hx
    subst hx
    exact ⟨by simp, S_zero χ⟩
  | succ J ih =>
    intro x hx
    simp only [G, mem_image, mem_product, mem_insert, mem_singleton] at hx
    obtain ⟨⟨a, d⟩, ⟨ha, hd⟩, rfl⟩ := hx
    obtain ⟨ha1, ha2⟩ := ih a ha
    have hR : InR χ q d := by
      rcases hd with rfl | rfl
      · exact R0
      · exact Rq
    refine ⟨?_, zero_step H a d ha2 hR⟩
    have hdq : d < q := hR.1
    calc q * a + d < q * a + q := by omega
      _ = q * (a + 1) := by ring
      _ ≤ q * q ^ J := Nat.mul_le_mul_left q ha1
      _ = q ^ (J + 1) := by ring

/-- **`cor:digitos` (a)**, the count: for `χ` even, `S` has at least `2^J - 1` zeros in
`(0, q^J)`. -/
theorem cor_digitos_a {q : ℕ} {χ : ℕ → ℤ} {s : ℤ} (H : Hyp q χ s) (heven : χ (q - 1) = 1)
    (J : ℕ) : 2 ^ J - 1 ≤ ((Ioo 0 (q ^ J)).filter (fun m => S χ m = 0)).card := by
  have hsub : (G q J).erase 0 ⊆ (Ioo 0 (q ^ J)).filter (fun m => S χ m = 0) := by
    intro x hx
    obtain ⟨hx0, hxG⟩ := mem_erase.mp hx
    obtain ⟨h1, h2⟩ := G_spec H heven J x hxG
    exact mem_filter.mpr ⟨mem_Ioo.mpr ⟨Nat.pos_of_ne_zero hx0, h1⟩, h2⟩
  have := card_le_card hsub
  rwa [card_erase_of_mem (zero_mem_G q J), G_card H.two_le] at this

/-- **`cor:digitos` (b)**: `χ` odd with `χ(2) = 1` (for a quadratic `χ`: `q ≡ 7 mod 8`) has
`S((q^j - 1)/2) = 0` for every `j`, for every `s`. The case `R = ℤ` of `cor_orden_zeros`. -/
theorem cor_digitos_b {q : ℕ} (hq : q % 2 = 1) (hq3 : 3 ≤ q) {χ : ℕ → ℤ} {s : ℤ}
    (hmul : ∀ a b, χ (a * b) = χ a * χ b)
    (hper : ∀ j r, 1 ≤ r → r < q → χ (j * q + r) = χ r)
    (hodd : χ (q - 1) = -1) (hs : χ q = s) (h2 : χ 2 = 1) (j : ℕ) :
    S χ ((q ^ j - 1) / 2) = 0 :=
  cor_orden_zeros hq hq3 two_ne_zero hmul hper hodd hs h2 j

/-- **`cor:digitos` (f)**: `χ` odd with `χ(2) = -1` (for a quadratic `χ`: `q ≡ 3 mod 8`):
`S((q^{j+1} - 1)/2) = -T_q q^j (1 + s + … + s^j)`. With `T_q = -q h(-q)` (and `h(-3) = 1/3`,
where `T_3 = -1`) this is the paper's `h(-q) q^{j+1} (1 + … + s^j)`. -/
theorem cor_digitos_f {q : ℕ} (hq : q % 2 = 1) (hq3 : 3 ≤ q) {χ : ℕ → ℤ} {s : ℤ}
    (hmul : ∀ a b, χ (a * b) = χ a * χ b)
    (hper : ∀ j r, 1 ≤ r → r < q → χ (j * q + r) = χ r)
    (hodd : χ (q - 1) = -1) (hs : χ q = s) (h2 : χ 2 = -1) (j : ℕ) :
    S χ ((q ^ (j + 1) - 1) / 2) = -Tq χ q * (q : ℤ) ^ j * ∑ i ∈ range (j + 1), s ^ i := by
  obtain ⟨c, rfl⟩ : ∃ c, q = 2 * c + 1 := ⟨q / 2, by omega⟩
  rw [show 2 * c + 1 - 1 = 2 * c by omega] at hodd
  have H := hyp_of_odd (by omega) hmul hper hodd hs
  obtain ⟨dT, dU, -⟩ := diag hmul hper hodd
  rw [h2] at dT dU
  have hTc : T χ c = -Tq χ (2 * c + 1) := by linarith
  have hCc : (2 * (c : ℤ) + 1) * C χ c = -3 * Tq χ (2 * c + 1) := by linear_combination -dU
  induction j with
  | zero =>
    rw [zero_add, pow_one, show (2 * c + 1 - 1) / 2 = c by omega, S_eq_T, hTc]
    simp
  | succ j ih =>
    have hm := two_half_pow c (j + 1)
    have hm' : 2 * ((((2 * c + 1) ^ (j + 1) - 1) / 2 : ℕ) : ℤ) + 1 = (2 * (c : ℤ) + 1) ^ (j + 1) := by
      exact_mod_cast hm
    rw [half_pow_succ, digit_recursion H _ c (by omega), ih, hTc, sum_range_succ' _ (j + 1)]
    generalize ((2 * c + 1) ^ (j + 1) - 1) / 2 = m at hm' ⊢
    simp only [pow_succ, pow_zero, ← sum_mul]
    push_cast
    linear_combination (m : ℤ) * hCc - Tq χ (2 * c + 1) * hm'

lemma alt_sum (i : ℕ) : ∑ l ∈ range (2 * i), (-1 : ℤ) ^ l = 0 := by
  rw [sum_range_two_mul]
  simp [pow_succ, pow_mul]

/-- **`cor:digitos` (f)**, `s = -1`: `S((q^{2i} - 1)/2) = 0` for every `i`. -/
theorem cor_digitos_f_neg {q : ℕ} (hq : q % 2 = 1) (hq3 : 3 ≤ q) {χ : ℕ → ℤ}
    (hmul : ∀ a b, χ (a * b) = χ a * χ b)
    (hper : ∀ j r, 1 ≤ r → r < q → χ (j * q + r) = χ r)
    (hodd : χ (q - 1) = -1) (hs : χ q = -1) (h2 : χ 2 = -1) (i : ℕ) :
    S χ ((q ^ (2 * i) - 1) / 2) = 0 := by
  cases i with
  | zero => simp [S_zero]
  | succ i =>
    rw [show 2 * (i + 1) = (2 * i + 1) + 1 by ring,
      cor_digitos_f hq hq3 hmul hper hodd hs h2 (2 * i + 1),
      show 2 * i + 1 + 1 = 2 * (i + 1) by ring, alt_sum, mul_zero]

end DigitosII

