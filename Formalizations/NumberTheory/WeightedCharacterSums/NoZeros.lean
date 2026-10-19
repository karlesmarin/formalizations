/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.NumberTheory.WeightedCharacterSums.DigitRecursion
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.LinearCombination

/-!
# `∑_{n ≤ m} n χ(n)` has no positive zero for `q = 179` and `q = 227`

Let `χ : ℕ → ℤ` be completely multiplicative with `χ(n) = (n | q)` (Legendre symbol) for `q ∤ n`
and `χ(q) = 1`. For `q = 179` and `q = 227`, `S(m) = ∑_{n ≤ m} n χ(n)` never vanishes for
`m ≥ 1`. The proof is a finite certificate (a cone `U`, rays `H`, a set `R` of states) whose
validity is a decidable proposition checked by `decide +kernel`; a general theorem turns a valid
certificate into the non-vanishing of `S`, through the digit recursion of
`SegmentoII.digit_recursion`.

The certificate data in the file are witnesses only: everything about them is checked in the
kernel. Negative controls (`q = 59`, which has zeros, and corrupted certificates) are rejected by
the checker.

## Main results

* `SegmentoIISinCeros.no_zero_of_valid`: a valid certificate gives `S χ m ≠ 0` for all `m ≥ 1`.
* `SegmentoIISinCeros.valid179`, `SegmentoIISinCeros.valid227`: the certificates, by
  `decide +kernel`.
* `SegmentoIISinCeros.S_ne_zero_179`, `SegmentoIISinCeros.S_ne_zero_227`: the theorem for every
  `χ` satisfying the hypotheses (names as cited by the paper's blueprint).
* `SegmentoIISinCeros.leg_eq_legendreSym`: the computable symbol `leg` is Mathlib's
  `legendreSym` off the multiples of `q` (Euler's criterion).
* `SegmentoIISinCeros.chi0_spec`: the explicit `chi0 q` satisfies the hypotheses, so they are
  not vacuous; `S_ne_zero_179_legendreSym`, `S_chi0_ne_zero_179` and their `227` versions.

## References

* C. Marín, *Zeros of weighted partial sums of completely multiplicative functions: Dirichlet
  characters, the Euler factor at 2 and Conrey's sine series*, Zenodo (2026),
  doi:10.5281/zenodo.22847374.
-/

@[expose] public section

open Finset

namespace SegmentoIISinCeros

/-! ## §1 Digit recursion

The sums `S`, `C`, `T`, `Tq` and the digit recursion are those of
`Formalizations.NumberTheory.WeightedCharacterSums.DigitRecursion`. -/

open SegmentoII (S C T Tq S_zero T_zero C_zero S_succ T_succ C_succ digit_recursion)

/-! ## §2 Computable Legendre symbol and the residue table -/

/-- Legendre symbol of a residue `x` (`0 ≤ x < q`) by Euler's criterion `x^((q-1)/2) mod q`. -/
def legRes (q x : ℕ) : ℤ :=
  if x = 0 then 0 else if Nat.pow x ((q - 1) / 2) % q = 1 then 1 else -1

/-- `leg q n = (n | q)` computed on the residue `n % q`. -/
def leg (q n : ℕ) : ℤ := legRes q (n % q)

lemma leg_periodic (q j r : ℕ) : leg q (j * q + r) = leg q r := by
  unfold leg; rw [add_comm, Nat.add_mul_mod_self_right]

/-- The table `tab` lists `(r, C r - h, T r)` for `r = r₀, r₀+1, …, q-1`, built incrementally
from `leg`. `chain q r d t tab = true` checks it starting at `(r, d, t)`. -/
def chain (q : ℕ) : ℕ → ℤ → ℤ → List (ℕ × ℤ × ℤ) → Bool
  | r, _, _, [] => r == q
  | r, d, t, (r', d', t') :: rest =>
      r' == r && d' == d && t' == t &&
        chain q (r + 1) (d + leg q (r + 1)) (t + ((r : ℤ) + 1) * leg q (r + 1)) rest

/-- Soundness of the table: every `(r, C χ r - h, T χ r)`, `r₀ ≤ r < q`, is in `tab`. -/
theorem chain_sound (q : ℕ) (χ : ℕ → ℤ) (hleg : ∀ n, n % q ≠ 0 → χ n = leg q n) (h : ℤ) :
    ∀ (l : List (ℕ × ℤ × ℤ)) (r : ℕ), chain q r (C χ r - h) (T χ r) l = true →
      ∀ r', r ≤ r' → r' < q → (r', C χ r' - h, T χ r') ∈ l := by
  intro l
  induction l with
  | nil =>
    intro r hc r' h1 h2
    simp only [chain, beq_iff_eq] at hc
    omega
  | cons x rest ih =>
    intro r hc r' h1 h2
    obtain ⟨r0, d0, t0⟩ := x
    simp only [chain, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨e1, e2⟩, e3⟩, hrest⟩ := hc
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · subst e1 e2 e3; exact List.mem_cons_self ..
    · apply List.mem_cons_of_mem
      have hr1 : r + 1 < q := by omega
      have hχ : χ (r + 1) = leg q (r + 1) := hleg _ (by rw [Nat.mod_eq_of_lt hr1]; omega)
      have eC : C χ (r + 1) - h = C χ r - h + leg q (r + 1) := by rw [C_succ, hχ]; ring
      have eT : T χ (r + 1) = T χ r + ((r : ℤ) + 1) * leg q (r + 1) := by rw [T_succ, hχ]
      apply ih (r + 1) (by rw [eC, eT]; exact hrest) r' (by omega) h2

/-! ## §3 The certificate predicate and the analytic lemmas -/

/-- The cone `U = {(a,b) : b(a+b) ≤ 0}`. -/
abbrev inU (a b : ℤ) : Prop := b * (a + b) ≤ 0

/-- The three rays `H`. -/
abbrev inH (a b : ℤ) : Prop := (23 ≤ a ∧ (b = 0 ∨ b = -a)) ∨ (a ≤ -23 ∧ 2 * b = -a)

/-- `W = R ∪ H`. -/
abbrev inW (R : List (ℤ × ℤ)) (a b : ℤ) : Prop := (a, b) ∈ R ∨ inH a b

/-- Per-entry facts of the residue table `e = (r, D r, T r)`. -/
abbrev EntryOK (q : ℕ) (h P : ℤ) (c : ℕ) (e : ℕ × ℤ × ℤ) : Prop :=
  e.1 < q ∧
  (e.1 = 0 → e.2.1 = -h ∧ e.2.2 = 0) ∧
  (e.1 ≠ 0 → 0 < e.2.2 + P * e.1 ∧ e.2.2 - 12 * e.1 < 0) ∧
  (e.1 + 1 = q → e.2.1 = -h ∧ e.2.2 = -(q : ℤ) * h) ∧
  (e.1 + 1 ≠ q → 0 < q * e.2.1 - e.2.2 + P * ((q : ℤ) - 1 - e.1) ∧
      q * e.2.1 - e.2.2 - 12 * ((q : ℤ) - 1 - e.1) < 0) ∧
  -6 ≤ e.2.1 ∧ e.2.1 ≤ 10 ∧
  (e.1 = c → e.2.1 = 2 * h ∧ e.2.2 = q * h) ∧
  (e.1 ≠ c →
    (2 ≤ 2 * (e.1 : ℤ) - q + 1 ∧
      -(13 * (2 * (e.1 : ℤ) - q + 1 - 1)) < 2 * e.2.2 - q * e.2.1 ∧
      2 * e.2.2 - q * e.2.1 < 13 * (2 * (e.1 : ℤ) - q + 1 - 1)) ∨
    (2 * (e.1 : ℤ) - q + 1 ≤ -2 ∧
      -(13 * (-(2 * (e.1 : ℤ) - q + 1) - 1)) < 2 * e.2.2 - q * e.2.1 ∧
      2 * e.2.2 - q * e.2.1 < 13 * (-(2 * (e.1 : ℤ) - q + 1) - 1)))

/-- Strip point `(a,b)`: every integral transition stays in `U`; accepting edges are listed. -/
abbrev StripPt (q : ℕ) (tab : List (ℕ × ℤ × ℤ)) (padres : List (ℤ × ℤ)) (a b : ℤ) : Prop :=
  inU a b → ∀ e ∈ tab, (b - e.2.2 - a * e.1) % (q : ℤ) = 0 →
    inU (a + e.2.1) ((b - e.2.2 - a * e.1) / q) ∧
    (e.1 ≠ 0 → (b - e.2.2 - a * e.1) / q = 0 → (a, b) ∈ padres)

/-- The finite strip `-12 < a < P`, `|b| ≤ 11` (enough: `U` forces `b` between `0` and `-a`). -/
abbrev StripOK (q : ℕ) (tab : List (ℕ × ℤ × ℤ)) (padres : List (ℤ × ℤ)) (P : ℤ) : Prop :=
  ∀ i ∈ List.range 24, ∀ j ∈ List.range 23,
    -11 + (i : ℤ) < P → StripPt q tab padres (-11 + i) (-11 + j)

/-- Backward closure of `R` inside `U`: every `U`-predecessor `G_r(p)` of `p ∈ R` is in `R ∪ H`. -/
abbrev BackOK (q : ℕ) (tab : List (ℕ × ℤ × ℤ)) (R : List (ℤ × ℤ)) : Prop :=
  ∀ p ∈ R, ∀ e ∈ tab, inU (p.1 - e.2.1) (q * p.2 + e.2.2 + (p.1 - e.2.1) * e.1) →
    inW R (p.1 - e.2.1) (q * p.2 + e.2.2 + (p.1 - e.2.1) * e.1)

/-- The whole certificate. -/
abbrev Valid (q : ℕ) (h P : ℤ) (c : ℕ) (tab : List (ℕ × ℤ × ℤ)) (R padres : List (ℤ × ℤ)) :
    Prop :=
  chain q 0 (-h) 0 tab = true ∧ (∀ e ∈ tab, EntryOK q h P c e) ∧
  0 ≤ P ∧ P ≤ 12 ∧ 0 ≤ h ∧ 2 * c + 1 = q ∧
  StripOK q tab padres P ∧ (∀ p ∈ padres, inW R p.1 p.2) ∧ BackOK q tab R ∧ (0, 0) ∉ R

-- `Valid` is a 10-fold conjunction; its `Decidable` instance needs a larger synthesis budget.
set_option synthInstance.maxSize 4096

/-- The Bool checker is the decision procedure of `Valid`. -/
def check (q : ℕ) (h P : ℤ) (c : ℕ) (tab : List (ℕ × ℤ × ℤ)) (R padres : List (ℤ × ℤ)) :
    Bool := decide (Valid q h P c tab R padres)

theorem check_sound {q : ℕ} {h P : ℤ} {c : ℕ} {tab : List (ℕ × ℤ × ℤ)} {R padres : List (ℤ × ℤ)}
    (hc : check q h P c tab R padres = true) : Valid q h P c tab R padres :=
  of_decide_eq_true hc

lemma U_pos {a b : ℤ} (hU : inU a b) (ha : 0 ≤ a) : b ≤ 0 ∧ 0 ≤ a + b := by
  constructor <;> by_contra hc <;> push Not at hc <;> nlinarith

lemma U_neg {a b : ℤ} (hU : inU a b) (ha : a ≤ 0) : 0 ≤ b ∧ a + b ≤ 0 := by
  constructor <;> by_contra hc <;> push Not at hc <;> nlinarith

section Analytic

variable {q : ℕ} {h P : ℤ} {c : ℕ} {tab : List (ℕ × ℤ × ℤ)} {R padres : List (ℤ × ℤ)}

/-- Strip coordinates. -/
lemma strip_of {q : ℕ} {tab : List (ℕ × ℤ × ℤ)} {padres : List (ℤ × ℤ)} {P a b : ℤ}
    (hS : StripOK q tab padres P) (hP : P ≤ 12) (hU : inU a b) (h1 : -12 < a) (h2 : a < P) :
    StripPt q tab padres a b := by
  have hb : -11 ≤ b ∧ b ≤ 11 := by
    rcases le_total 0 a with ha | ha
    · have := U_pos hU ha; constructor <;> linarith
    · have := U_neg hU ha; constructor <;> linarith
  have hi : (a + 11).toNat < 24 := by omega
  have hj : (b + 11).toNat < 23 := by omega
  have ea : -11 + (((a + 11).toNat : ℕ) : ℤ) = a := by omega
  have eb : -11 + (((b + 11).toNat : ℕ) : ℤ) = b := by omega
  have := hS _ (List.mem_range.2 hi) _ (List.mem_range.2 hj) (by rw [ea]; exact h2)
  rwa [ea, eb] at this

lemma emod_div_of_mul {q : ℕ} (hq : 0 < q) {x y : ℤ} (hx : (q : ℤ) * y = x) :
    x % q = 0 ∧ x / q = y := by
  subst hx
  refine ⟨Int.mul_emod_right _ _, Int.mul_ediv_cancel_left _ (by omega)⟩

/-- Forward invariance of `U`. -/
theorem fwd (hV : Valid q h P c tab R padres) {r : ℕ} {d t a b b' : ℤ} (he : (r, d, t) ∈ tab)
    (hU : inU a b) (hstep : (q : ℤ) * b' = b - t - a * r) : inU (a + d) b' := by
  obtain ⟨-, hE, hP0, hP12, -, -, hS, -, -, -⟩ := hV
  obtain ⟨hrq, h0, h1, hlast, hmid, hd1, hd2, -, -⟩ := hE _ he
  simp only at hrq h0 h1 hlast hmid hd1 hd2
  have hq : (0 : ℤ) < q := by omega
  have hr0 : (0 : ℤ) ≤ r := by omega
  have hs0 : (0 : ℤ) ≤ (q : ℤ) - 1 - r := by omega
  have key : (q : ℤ) * (a + d + b') = (a + b) + a * ((q : ℤ) - 1 - r) + (q * d - t) := by
    linear_combination hstep
  by_cases hA : P ≤ a
  · obtain ⟨hb, hab⟩ := U_pos hU (by linarith)
    have hb' : b' ≤ 0 := by
      by_cases hr : r = 0
      · subst hr; obtain ⟨-, ht⟩ := h0 rfl; simp at hstep; nlinarith
      · obtain ⟨h1a, -⟩ := h1 hr
        nlinarith [mul_le_mul_of_nonneg_right hA hr0]
    have hsum : 0 ≤ a + d + b' := by
      by_cases hl : r + 1 = q
      · obtain ⟨hd, ht⟩ := hlast hl
        have : (q : ℤ) - 1 - r = 0 := by omega
        rw [this, hd, ht] at key; nlinarith
      · obtain ⟨hm, -⟩ := hmid hl
        nlinarith [mul_le_mul_of_nonneg_right hA hs0]
    show b' * (a + d + b') ≤ 0
    nlinarith
  by_cases hB : a ≤ -12
  · obtain ⟨hb, hab⟩ := U_neg hU (by linarith)
    have hb' : 0 ≤ b' := by
      by_cases hr : r = 0
      · subst hr; obtain ⟨-, ht⟩ := h0 rfl; simp at hstep; nlinarith
      · obtain ⟨-, h1b⟩ := h1 hr
        nlinarith [mul_le_mul_of_nonneg_right hB hr0]
    have hsum : a + d + b' ≤ 0 := by
      by_cases hl : r + 1 = q
      · obtain ⟨hd, ht⟩ := hlast hl
        have : (q : ℤ) - 1 - r = 0 := by omega
        rw [this, hd, ht] at key; nlinarith
      · obtain ⟨-, hm⟩ := hmid hl
        nlinarith [mul_le_mul_of_nonneg_right hB hs0]
    show b' * (a + d + b') ≤ 0
    nlinarith
  push Not at hA hB
  have hpt := strip_of hS hP12 hU hB hA
  obtain ⟨hmod, hdiv⟩ := emod_div_of_mul (by omega) hstep
  have := (hpt hU _ he hmod).1
  simp only at this
  rwa [hdiv] at this

/-- Accepting edges start in `R ∪ H`. -/
theorem acc (hV : Valid q h P c tab R padres) {r : ℕ} {d t a b : ℤ} (he : (r, d, t) ∈ tab)
    (hr : r ≠ 0) (hU : inU a b) (hstep : (q : ℤ) * 0 = b - t - a * r) : inW R a b := by
  obtain ⟨-, hE, hP0, hP12, -, -, hS, hpad, -, -⟩ := hV
  obtain ⟨hrq, -, h1, -, -, -, -, -, -⟩ := hE _ he
  simp only at hrq h1
  obtain ⟨h1a, h1b⟩ := h1 hr
  have hr0 : (0 : ℤ) ≤ r := by omega
  by_cases hA : P ≤ a
  · obtain ⟨hb, -⟩ := U_pos hU (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hA hr0]
  by_cases hB : a ≤ -12
  · obtain ⟨hb, -⟩ := U_neg hU (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hB hr0]
  push Not at hA hB
  have hpt := strip_of hS hP12 hU hB hA
  obtain ⟨hmod, hdiv⟩ := emod_div_of_mul (by omega) hstep
  have := (hpt hU _ he hmod).2 hr hdiv
  exact hpad _ this

/-- Backward closure of the rays `H` relative to `U`. -/
theorem back_H (hV : Valid q h P c tab R padres) {r : ℕ} {d t a b A B : ℤ}
    (he : (r, d, t) ∈ tab) (hU : inU a b) (hA : A = a + d) (hstep : (q : ℤ) * B = b - t - a * r)
    (hH : inH A B) : inH a b := by
  obtain ⟨-, hE, hP0, hP12, hh, hc, -, -, -, -⟩ := hV
  obtain ⟨hrq, h0, h1, hlast, hmid, hd1, hd2, hcen, hoff⟩ := hE _ he
  simp only at hrq h0 h1 hlast hmid hd1 hd2 hcen hoff
  have hr0 : (0 : ℤ) ≤ r := by omega
  have hs0 : (0 : ℤ) ≤ (q : ℤ) - 1 - r := by omega
  rcases hH with ⟨hA23, hB0 | hBA⟩ | ⟨hA23, hB2⟩
  · -- ray (A, 0), A ≥ 23
    have ha : 13 ≤ a := by linarith
    obtain ⟨hb, -⟩ := U_pos hU (by linarith)
    by_cases hr : r = 0
    · subst hr
      obtain ⟨hd, ht⟩ := h0 rfl
      rw [hB0, ht] at hstep; simp at hstep
      left; exact ⟨by linarith, Or.inl (by linarith)⟩
    · obtain ⟨h1a, -⟩ := h1 hr
      have hPa : P ≤ a := by linarith
      rw [hB0] at hstep
      nlinarith [mul_le_mul_of_nonneg_right hPa hr0]
  · -- ray (A, -A), A ≥ 23
    have ha : 13 ≤ a := by linarith
    obtain ⟨-, hab⟩ := U_pos hU (by linarith)
    have key : (0 : ℤ) = (a + b) + a * ((q : ℤ) - 1 - r) + (q * d - t) := by
      have : (q : ℤ) * (A + B) = 0 := by rw [hBA]; ring
      linear_combination hstep - this + (q : ℤ) * hA
    by_cases hl : r + 1 = q
    · obtain ⟨hd, ht⟩ := hlast hl
      have h3 : (q : ℤ) - 1 - r = 0 := by omega
      rw [h3, hd, ht] at key
      left; exact ⟨by linarith, Or.inr (by linarith)⟩
    · obtain ⟨hm, -⟩ := hmid hl
      have hPa : P ≤ a := by linarith
      nlinarith [mul_le_mul_of_nonneg_right hPa hs0]
  · -- middle ray (A, -A/2), A ≤ -23
    have ha : a ≤ -17 := by linarith
    obtain ⟨hb, hab⟩ := U_neg hU (by linarith)
    have key : a + 2 * b = a * (2 * (r : ℤ) - q + 1) + (2 * t - q * d) := by
      linear_combination (-2 : ℤ) * hstep - (q : ℤ) * hA + (q : ℤ) * hB2
    by_cases hrc : r = c
    · obtain ⟨hd, ht⟩ := hcen hrc
      have hk : 2 * (r : ℤ) - q + 1 = 0 := by subst hrc; omega
      rw [hk, hd, ht] at key
      right; exact ⟨by linarith, by linarith⟩
    · rcases hoff hrc with ⟨hk, hM1, hM2⟩ | ⟨hk, hM1, hM2⟩
      · nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ 2 * (r : ℤ) - q + 1 - 1)
          (by linarith : (0 : ℤ) ≤ -(a + 13))]
      · nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ -(2 * (r : ℤ) - q + 1 + 1))
          (by linarith : (0 : ℤ) ≤ -(a + 13))]

/-- Backward closure of `R ∪ H` relative to `U`. -/
theorem back (hV : Valid q h P c tab R padres) {r : ℕ} {d t a b A B : ℤ}
    (he : (r, d, t) ∈ tab) (hU : inU a b) (hA : A = a + d) (hstep : (q : ℤ) * B = b - t - a * r)
    (hW : inW R A B) : inW R a b := by
  rcases hW with hR | hH
  · have hB := hV.2.2.2.2.2.2.2.2.1 _ hR _ he
    simp only at hB
    have e1 : A - d = a := by linarith
    have e2 : (q : ℤ) * B + t + a * r = b := by linarith
    rw [e1, e2] at hB
    exact hB hU
  · exact Or.inr (back_H hV he hU hA hstep hH)

end Analytic

/-! ## §4 Valid certificate ⇒ no positive zero -/

theorem no_zero_of_valid (q : ℕ) (hq : 2 ≤ q) (χ : ℕ → ℤ)
    (hmul : ∀ a b, χ (a * b) = χ a * χ b)
    (hleg : ∀ n, n % q ≠ 0 → χ n = leg q n) (hχq : χ q = 1)
    {h P : ℤ} {c : ℕ} {tab : List (ℕ × ℤ × ℤ)} {R padres : List (ℤ × ℤ)}
    (hV : Valid q h P c tab R padres) (m : ℕ) (hm : 0 < m) : S χ m ≠ 0 := by
  -- the table is the true table
  have hmem : ∀ r, r < q → (r, C χ r - h, T χ r) ∈ tab := by
    intro r hr
    have h0 : chain q 0 (C χ 0 - h) (T χ 0) tab = true := by
      rw [C_zero, T_zero, zero_sub]; exact hV.1
    exact chain_sound q χ hleg h tab 0 h0 r (Nat.zero_le _) hr
  have hlastE := (hV.2.1 _ (hmem (q - 1) (by omega))).2.2.2.1 (by simp only; omega)
  simp only at hlastE
  obtain ⟨hCl, hTl⟩ := hlastE
  have hsum0 : C χ (q - 1) = 0 := by linarith
  have hper : ∀ j r, 1 ≤ r → r < q → χ (j * q + r) = χ r := by
    intro j r h1 h2
    rw [hleg _ (by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2]; omega),
      hleg _ (by rw [Nat.mod_eq_of_lt h2]; omega), leg_periodic]
  have hdig : ∀ j r, r < q →
      S χ (q * j + r) = q * S χ j + q * j * (C χ r - h) + T χ r := by
    intro j r hr
    rw [digit_recursion q hq χ 1 hmul hper hχq hsum0 j r hr, Tq, hTl]
    ring
  -- main induction
  have main : ∀ k, ∀ a b : ℤ, inU a b → ¬ inW R a b → S χ k + a * k = b → 0 < k → False := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro a b hU hW hk hpos
      have hk' : q * (k / q) + k % q = k := Nat.div_add_mod k q
      have hrq : k % q < q := Nat.mod_lt _ (by omega)
      set j := k / q with hj
      set r := k % q with hr
      set d := C χ r - h
      set t := T χ r
      have he : (r, d, t) ∈ tab := hmem r hrq
      set b' := S χ j + (a + d) * j with hb'
      have hcast : (k : ℤ) = q * j + r := by exact_mod_cast hk'.symm
      have hSk : S χ k = q * S χ j + q * j * d + t := by rw [← hk']; exact hdig j r hrq
      have hstep : (q : ℤ) * b' = b - t - a * r := by
        rw [← hk, hSk, hcast, hb']; ring
      have hU' : inU (a + d) b' := fwd hV he hU hstep
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · have hb0 : b' = 0 := by rw [hb', hj0]; simp [S_zero]
        have hr0 : r ≠ 0 := by
          intro h0; rw [hj0, h0] at hk'; omega
        rw [hb0] at hstep
        exact hW (acc hV he hr0 hU hstep)
      · have hjk : j < k := Nat.div_lt_self hpos (by omega)
        refine ih j hjk (a + d) b' hU' ?_ rfl hjpos
        intro hW'
        exact hW (back hV he hU rfl hstep hW')
  intro hS0
  refine main m 0 0 (by simp) ?_ (by simp [hS0]) hm
  rintro (h00 | hH)
  · exact hV.2.2.2.2.2.2.2.2.2 h00
  · rcases hH with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega

/-! ## §5 Data and the kernel-checked certificates -/

-- Certificate data, produced by a backward search outside Lean. It is only a witness: its
-- validity is checked by the kernel below.
def R179 : List (Int × Int) := [(-22, 11), (-20, 10), (-16, 8), (-14, 7), (-12, 6), (-10, 5), (-9, 1), (-9, 2), (-9, 7), (-9, 8), (-8, 1), (-8, 7), (-7, 1), (-7, 6), (-6, 1), (-6, 3), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-2, 1), (-2, 2), (-1, 0), (1, -1), (1, 0), (2, -2), (2, 0), (3, -3), (4, 0), (5, -5), (6, -6), (6, 0), (7, -7), (7, 0), (8, -8), (9, 0), (10, -10), (11, -11), (11, 0), (12, -12), (12, 0), (13, -13), (14, 0), (15, -15), (16, -16), (16, 0), (17, -17), (17, 0), (18, -18), (19, 0), (20, -20), (21, -21), (21, 0), (22, -22), (22, 0)]
def padres179 : List (Int × Int) := [(-10, 5), (-6, 1), (-4, 2), (-3, 0), (-3, 2), (-2, 1), (-2, 2), (-1, 0), (1, -1), (1, 0), (2, -2), (2, 0), (5, -5)]
def R227 : List (Int × Int) := [(-20, 2), (-20, 10), (-20, 18), (-19, 0), (-19, 19), (-18, 0), (-18, 9), (-18, 18), (-16, 8), (-15, 2), (-15, 4), (-15, 5), (-15, 10), (-15, 11), (-15, 13), (-14, 0), (-14, 7), (-14, 14), (-13, 0), (-13, 13), (-11, 2), (-11, 9), (-10, 4), (-10, 5), (-10, 6), (-9, 0), (-9, 2), (-9, 7), (-9, 9), (-8, 0), (-8, 4), (-8, 8), (-7, 1), (-7, 3), (-7, 4), (-7, 6), (-6, 2), (-6, 3), (-6, 4), (-4, 0), (-4, 4), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, 0), (-2, 2), (-1, 0), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (3, -3), (3, -2), (3, -1), (3, 0), (4, 0), (5, -5), (5, -4), (5, -1), (6, -6), (6, 0), (7, -7), (7, -6), (7, -4), (7, -3), (7, -1), (7, 0), (8, -8), (8, 0), (9, -5), (9, -4), (9, 0), (10, -10), (11, -11), (11, -10), (11, -8), (11, -3), (11, -1), (11, 0), (12, -12), (12, -10), (12, -6), (12, -2), (12, 0), (13, -13), (13, -12), (13, -1), (13, 0), (14, -12), (14, -2), (14, 0), (15, -15), (15, -9), (15, -8), (15, -7), (15, -6), (16, -16), (16, 0), (17, -17), (17, -11), (17, -6), (17, 0), (18, -18), (18, -11), (18, -7), (18, 0), (19, -14), (19, -5), (19, 0), (20, -20), (21, -21), (21, 0), (22, -22), (22, -19), (22, -16), (22, -12), (22, -10), (22, -6), (22, -3), (22, 0), (25, -17), (25, -8), (26, -18), (26, -16), (26, -10), (26, -8), (27, -17), (27, -10), (30, -26), (30, -4), (33, -27), (33, -6), (34, -31), (34, -3), (39, -35), (39, -4), (42, -39), (42, -28), (42, -14), (42, -3), (43, -38), (43, -33), (43, -10), (43, -5), (45, -42), (45, -39), (45, -6), (45, -3), (47, -43), (47, -29), (47, -18), (47, -4), (48, -37), (48, -28), (48, -20), (48, -11), (51, -48), (51, -3), (52, -31), (52, -21)]
def padres227 : List (Int × Int) := [(-10, 5), (-7, 1), (-6, 2), (-6, 3), (-3, 0), (-3, 1), (-2, 2), (-1, 0), (5, -5), (7, -4)]

-- Residue tables (r, C r - h, T r), 0 <= r < q, h = 5. Untrusted: checked by `chain`.
def tab179 : List (ℕ × ℤ × ℤ) := [(0, -5, 0), (1, -4, 1), (2, -5, -1), (3, -4, 2), (4, -3, 6), (5, -2, 11), (6, -3, 5), (7, -4, -2), (8, -5, -10), (9, -4, -1), (10, -5, -11), (11, -6, -22), (12, -5, -10), (13, -4, 3), (14, -3, 17), (15, -2, 32), (16, -1, 48), (17, 0, 65), (18, -1, 47), (19, 0, 66), (20, 1, 86), (21, 0, 65), (22, 1, 87), (23, 0, 64), (24, -1, 40), (25, 0, 65), (26, -1, 39), (27, 0, 66), (28, -1, 38), (29, 0, 67), (30, -1, 37), (31, 0, 68), (32, -1, 36), (33, -2, 3), (34, -3, -31), (35, -4, -66), (36, -3, -30), (37, -4, -67), (38, -5, -105), (39, -4, -66), (40, -5, -106), (41, -6, -147), (42, -5, -105), (43, -4, -62), (44, -5, -106), (45, -4, -61), (46, -3, -15), (47, -2, 32), (48, -1, 80), (49, 0, 129), (50, -1, 79), (51, 0, 130), (52, 1, 182), (53, 0, 129), (54, -1, 75), (55, -2, 20), (56, -1, 76), (57, 0, 133), (58, -1, 75), (59, 0, 134), (60, 1, 194), (61, 2, 255), (62, 1, 193), (63, 0, 130), (64, 1, 194), (65, 2, 259), (66, 3, 325), (67, 4, 392), (68, 5, 460), (69, 4, 391), (70, 5, 461), (71, 4, 390), (72, 3, 318), (73, 2, 245), (74, 3, 319), (75, 4, 394), (76, 5, 470), (77, 6, 547), (78, 5, 469), (79, 4, 390), (80, 5, 470), (81, 6, 551), (82, 7, 633), (83, 8, 716), (84, 7, 632), (85, 8, 717), (86, 7, 631), (87, 8, 718), (88, 9, 806), (89, 10, 895), (90, 9, 805), (91, 8, 714), (92, 7, 622), (93, 8, 715), (94, 7, 621), (95, 8, 716), (96, 7, 620), (97, 6, 523), (98, 5, 425), (99, 4, 326), (100, 5, 426), (101, 6, 527), (102, 5, 425), (103, 4, 322), (104, 3, 218), (105, 2, 113), (106, 3, 219), (107, 4, 326), (108, 5, 434), (109, 4, 325), (110, 5, 435), (111, 4, 324), (112, 3, 212), (113, 2, 99), (114, 1, -15), (115, 0, -130), (116, 1, -14), (117, 2, 103), (118, 1, -15), (119, 0, -134), (120, -1, -254), (121, 0, -133), (122, -1, -255), (123, -2, -378), (124, -1, -254), (125, 0, -129), (126, 1, -3), (127, 0, -130), (128, -1, -258), (129, 0, -129), (130, -1, -259), (131, -2, -390), (132, -3, -522), (133, -4, -655), (134, -5, -789), (135, -4, -654), (136, -5, -790), (137, -6, -927), (138, -5, -789), (139, -4, -650), (140, -5, -790), (141, -4, -649), (142, -3, -507), (143, -4, -650), (144, -3, -506), (145, -2, -361), (146, -1, -215), (147, 0, -68), (148, -1, -216), (149, 0, -67), (150, -1, -217), (151, 0, -66), (152, -1, -218), (153, 0, -65), (154, -1, -219), (155, 0, -64), (156, 1, 92), (157, 0, -65), (158, 1, 93), (159, 0, -66), (160, -1, -226), (161, 0, -65), (162, -1, -227), (163, -2, -390), (164, -3, -554), (165, -4, -719), (166, -5, -885), (167, -6, -1052), (168, -5, -884), (169, -4, -715), (170, -5, -885), (171, -4, -714), (172, -3, -542), (173, -2, -369), (174, -3, -543), (175, -4, -718), (176, -5, -894), (177, -4, -717), (178, -5, -895)]
def tab227 : List (ℕ × ℤ × ℤ) := [(0, -5, 0), (1, -4, 1), (2, -5, -1), (3, -4, 2), (4, -3, 6), (5, -4, 1), (6, -5, -5), (7, -4, 2), (8, -5, -6), (9, -4, 3), (10, -3, 13), (11, -2, 24), (12, -1, 36), (13, -2, 23), (14, -3, 9), (15, -4, -6), (16, -3, 10), (17, -4, -7), (18, -5, -25), (19, -4, -6), (20, -5, -26), (21, -4, -5), (22, -5, -27), (23, -4, -4), (24, -5, -28), (25, -4, -3), (26, -3, 23), (27, -2, 50), (28, -1, 78), (29, 0, 107), (30, 1, 137), (31, 0, 106), (32, -1, 74), (33, 0, 107), (34, 1, 141), (35, 0, 106), (36, 1, 142), (37, 0, 105), (38, -1, 67), (39, -2, 28), (40, -1, 68), (41, -2, 27), (42, -3, -15), (43, -2, 28), (44, -1, 72), (45, -2, 27), (46, -3, -19), (47, -2, 28), (48, -1, 76), (49, 0, 125), (50, -1, 75), (51, -2, 24), (52, -3, -28), (53, -2, 25), (54, -3, -29), (55, -4, -84), (56, -5, -140), (57, -4, -83), (58, -5, -141), (59, -4, -82), (60, -5, -142), (61, -6, -203), (62, -5, -141), (63, -4, -78), (64, -3, -14), (65, -2, 51), (66, -3, -15), (67, -4, -82), (68, -5, -150), (69, -4, -81), (70, -3, -11), (71, -2, 60), (72, -3, -12), (73, -2, 61), (74, -1, 135), (75, 0, 210), (76, 1, 286), (77, 2, 363), (78, 3, 441), (79, 4, 520), (80, 3, 440), (81, 4, 521), (82, 5, 603), (83, 4, 520), (84, 5, 604), (85, 6, 689), (86, 5, 603), (87, 6, 690), (88, 5, 602), (89, 6, 691), (90, 7, 781), (91, 6, 690), (92, 7, 782), (93, 6, 689), (94, 5, 595), (95, 4, 500), (96, 3, 404), (97, 4, 501), (98, 3, 403), (99, 4, 502), (100, 5, 602), (101, 6, 703), (102, 7, 805), (103, 8, 908), (104, 9, 1012), (105, 8, 907), (106, 7, 801), (107, 6, 694), (108, 7, 802), (109, 8, 911), (110, 9, 1021), (111, 8, 910), (112, 9, 1022), (113, 10, 1135), (114, 9, 1021), (115, 8, 906), (116, 9, 1022), (117, 8, 905), (118, 7, 787), (119, 6, 668), (120, 7, 788), (121, 8, 909), (122, 9, 1031), (123, 8, 908), (124, 7, 784), (125, 6, 659), (126, 5, 533), (127, 4, 406), (128, 3, 278), (129, 4, 407), (130, 3, 277), (131, 4, 408), (132, 5, 540), (133, 6, 673), (134, 7, 807), (135, 6, 672), (136, 7, 808), (137, 6, 671), (138, 5, 533), (139, 6, 672), (140, 5, 532), (141, 6, 673), (142, 5, 531), (143, 4, 388), (144, 5, 532), (145, 4, 387), (146, 3, 241), (147, 4, 388), (148, 3, 240), (149, 2, 91), (150, 1, -59), (151, 0, -210), (152, -1, -362), (153, -2, -515), (154, -3, -669), (155, -2, -514), (156, -3, -670), (157, -4, -827), (158, -5, -985), (159, -4, -826), (160, -3, -666), (161, -2, -505), (162, -3, -667), (163, -4, -830), (164, -5, -994), (165, -6, -1159), (166, -5, -993), (167, -4, -826), (168, -5, -994), (169, -4, -825), (170, -5, -995), (171, -4, -824), (172, -3, -652), (173, -2, -479), (174, -3, -653), (175, -2, -478), (176, -1, -302), (177, 0, -125), (178, -1, -303), (179, -2, -482), (180, -3, -662), (181, -2, -481), (182, -1, -299), (183, -2, -482), (184, -3, -666), (185, -2, -481), (186, -1, -295), (187, -2, -482), (188, -1, -294), (189, 0, -105), (190, 1, 85), (191, 0, -106), (192, 1, 86), (193, 0, -107), (194, -1, -301), (195, 0, -106), (196, 1, 90), (197, 0, -107), (198, -1, -305), (199, -2, -504), (200, -3, -704), (201, -4, -905), (202, -5, -1107), (203, -4, -904), (204, -5, -1108), (205, -4, -903), (206, -5, -1109), (207, -4, -902), (208, -5, -1110), (209, -4, -901), (210, -3, -691), (211, -4, -902), (212, -3, -690), (213, -2, -477), (214, -1, -263), (215, -2, -478), (216, -3, -694), (217, -4, -911), (218, -5, -1129), (219, -4, -910), (220, -5, -1130), (221, -4, -909), (222, -3, -687), (223, -4, -910), (224, -5, -1134), (225, -4, -909), (226, -5, -1135)]

theorem valid179 : Valid 179 5 7 89 tab179 R179 padres179 := by decide +kernel

theorem valid227 : Valid 227 5 8 113 tab227 R227 padres227 := by decide +kernel

/-- **No positive zero, q = 179.** -/
theorem S_ne_zero_179 (χ : ℕ → ℤ) (hmul : ∀ a b, χ (a * b) = χ a * χ b)
    (hleg : ∀ n, n % 179 ≠ 0 → χ n = leg 179 n) (hq : χ 179 = 1) (m : ℕ) (hm : 1 ≤ m) :
    S χ m ≠ 0 :=
  no_zero_of_valid 179 (by omega) χ hmul hleg hq valid179 m hm

/-- **No positive zero, q = 227.** -/
theorem S_ne_zero_227 (χ : ℕ → ℤ) (hmul : ∀ a b, χ (a * b) = χ a * χ b)
    (hleg : ∀ n, n % 227 ≠ 0 → χ n = leg 227 n) (hq : χ 227 = 1) (m : ℕ) (hm : 1 ≤ m) :
    S χ m ≠ 0 :=
  no_zero_of_valid 227 (by omega) χ hmul hleg hq valid227 m hm

/-! ## §6 Negative controls: the checker can fail
`q = 59` has positive zeros; its backward set `R59` (|R| = 43) contains the origin, and deleting
the origin breaks closure.
Corrupting one point of `R179` or one table entry also makes the checker answer `false`. -/

-- Control data for q = 59 (from the same backward search).
def tab59 : List (ℕ × ℤ × ℤ) := [(0, -3, 0), (1, -2, 1), (2, -3, -1), (3, -2, 2), (4, -1, 6), (5, 0, 11), (6, -1, 5), (7, 0, 12), (8, -1, 4), (9, 0, 13), (10, -1, 3), (11, -2, -8), (12, -1, 4), (13, -2, -9), (14, -3, -23), (15, -2, -8), (16, -1, 8), (17, 0, 25), (18, -1, 7), (19, 0, 26), (20, 1, 46), (21, 2, 67), (22, 3, 89), (23, 2, 66), (24, 1, 42), (25, 2, 67), (26, 3, 93), (27, 4, 120), (28, 5, 148), (29, 6, 177), (30, 5, 147), (31, 4, 116), (32, 3, 84), (33, 2, 51), (34, 1, 17), (35, 2, 52), (36, 3, 88), (37, 2, 51), (38, 1, 13), (39, 0, -26), (40, -1, -66), (41, 0, -25), (42, -1, -67), (43, -2, -110), (44, -3, -154), (45, -2, -109), (46, -1, -63), (47, -2, -110), (48, -1, -62), (49, 0, -13), (50, -1, -63), (51, 0, -12), (52, -1, -64), (53, 0, -11), (54, -1, -65), (55, -2, -120), (56, -3, -176), (57, -2, -119), (58, -3, -177)]
def R59 : List (ℤ × ℤ) := [(-20, 10), (-18, 9), (-14, 7), (-12, 6), (-8, 4), (-6, 0), (-6, 3), (-5, 5), (-4, 1), (-3, 0), (-2, 1), (-2, 2), (-1, 0), (0, 0), (1, -1), (2, 0), (3, -3), (3, 0), (4, -4), (5, 0), (6, -6), (6, 0), (7, -7), (8, 0), (9, -9), (9, 0), (10, -10), (11, 0), (12, -12), (12, 0), (13, -13), (14, 0), (15, -15), (15, 0), (16, -16), (17, 0), (18, -18), (18, 0), (19, -19), (20, 0), (21, -21), (21, 0), (22, -22)]
def padres59 : List (ℤ × ℤ) := [(-6, 3), (-4, 1), (-2, 1), (-1, 0), (3, -3)]

example : check 59 3 4 29 tab59 R59 padres59 = false := by decide +kernel
example : check 59 3 4 29 tab59 (R59.erase (0, 0)) padres59 = false := by decide +kernel
example : check 179 5 7 89 tab179 (R179.erase (-22, 11)) padres179 = false := by decide +kernel
example : check 179 5 7 89 (tab179.set 5 (5, -1, 0)) R179 padres179 = false := by decide +kernel

/-! ## §7 Bridge to Mathlib's `legendreSym`, and non-vacuity -/

/-- `leg` is Mathlib's Legendre symbol off the multiples of `q` (Euler's criterion). -/
theorem leg_eq_legendreSym (q : ℕ) [hq : Fact q.Prime] (hq2 : q ≠ 2) (n : ℕ) (hn : n % q ≠ 0) :
    leg q n = legendreSym q n := by
  have hq1 : 2 < q := lt_of_le_of_ne hq.out.two_le (Ne.symm hq2)
  have : Fact (2 < q) := ⟨hq1⟩
  have hodd : (q - 1) / 2 = q / 2 := by
    rcases hq.out.eq_two_or_odd' with h | ⟨k, hk⟩
    · exact absurd h hq2
    · omega
  set x := n % q with hx
  have hxq : x < q := Nat.mod_lt _ (by omega)
  have hL : legendreSym q n = legendreSym q x := by
    rw [legendreSym.mod q (n : ℤ), hx]; push_cast; rfl
  have hx0 : ((x : ℤ) : ZMod q) ≠ 0 := by
    intro h
    have : ((x : ℕ) : ZMod q) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hn (Nat.eq_zero_of_dvd_of_lt this hxq)
  have hpow := legendreSym.eq_pow q (x : ℤ)
  have hcast : ((x : ℤ) : ZMod q) ^ (q / 2) = ((x ^ (q / 2) : ℕ) : ZMod q) := by push_cast; rfl
  rw [hcast] at hpow
  unfold leg legRes
  rw [← hx, ite_eq_right hn, hL, hodd]
  change (if x ^ (q / 2) % q = 1 then (1 : ℤ) else -1) = _
  rcases legendreSym.eq_one_or_neg_one q hx0 with h1 | h1
  · rw [h1] at hpow ⊢
    have : ((1 : ℕ) : ZMod q) = ((x ^ (q / 2) : ℕ) : ZMod q) := by push_cast at hpow ⊢; exact hpow
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega : 1 < q)] at this
    rw [ite_eq_left this.symm]
  · rw [h1] at hpow ⊢
    rw [ite_eq_right]
    intro h
    have : ((x ^ (q / 2) : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by
      rw [ZMod.natCast_eq_natCast_iff', h, Nat.mod_eq_of_lt (by omega : 1 < q)]
    rw [← hpow] at this
    push_cast at this
    exact ZMod.neg_one_ne_one this

/-- The completely multiplicative extension: `χ₀ n = leg q (n / q^{v_q(n)})`, `χ₀ 0 = 0`. -/
def chi0 (q n : ℕ) : ℤ := if n = 0 then 0 else leg q (ordCompl[q] n)

/-- Non-vacuity: `chi0 q` satisfies the hypotheses of the main theorem. -/
theorem chi0_spec (q : ℕ) [hq : Fact q.Prime] (hq2 : q ≠ 2) :
    (∀ a b, chi0 q (a * b) = chi0 q a * chi0 q b) ∧
    (∀ n, n % q ≠ 0 → chi0 q n = leg q n) ∧ chi0 q q = 1 := by
  have hp := hq.out
  have hlegmul : ∀ a b, ¬ q ∣ a → ¬ q ∣ b → leg q (a * b) = leg q a * leg q b := by
    intro a b ha hb
    have hab : ¬ q ∣ a * b := fun h => (hp.dvd_mul.1 h).elim ha hb
    rw [leg_eq_legendreSym q hq2 _ (fun h => hab (Nat.dvd_of_mod_eq_zero h)),
      leg_eq_legendreSym q hq2 _ (fun h => ha (Nat.dvd_of_mod_eq_zero h)),
      leg_eq_legendreSym q hq2 _ (fun h => hb (Nat.dvd_of_mod_eq_zero h))]
    push_cast
    exact legendreSym.mul q _ _
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [chi0]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp [chi0]
    unfold chi0
    rw [ite_eq_right (by positivity), ite_eq_right (by omega), ite_eq_right (by omega), Nat.ordCompl_mul]
    exact hlegmul _ _ (Nat.not_dvd_ordCompl hp (by omega)) (Nat.not_dvd_ordCompl hp (by omega))
  · intro n hn
    have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    unfold chi0
    rw [ite_eq_right hn0, (Nat.ordCompl_eq_self_iff_zero_or_not_dvd n hp).2
      (Or.inr (fun h => hn (Nat.mod_eq_zero_of_dvd h)))]
  · unfold chi0
    rw [ite_eq_right hp.ne_zero]
    have : ordCompl[q] q = 1 := by simpa using Nat.ordCompl_self_pow (k := 1) hp
    rw [this, leg_eq_legendreSym q hq2 1 (by rw [Nat.mod_eq_of_lt hp.one_lt]; omega)]
    simp [legendreSym.at_one]

instance : Fact (Nat.Prime 179) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 227) := ⟨by norm_num⟩

/-- **No positive zero, q = 179**, stated with Mathlib's `legendreSym`. -/
theorem S_ne_zero_179_legendreSym (χ : ℕ → ℤ) (hmul : ∀ a b, χ (a * b) = χ a * χ b)
    (hleg : ∀ n : ℕ, ¬ 179 ∣ n → χ n = legendreSym 179 n) (hq : χ 179 = 1) (m : ℕ)
    (hm : 1 ≤ m) : S χ m ≠ 0 :=
  S_ne_zero_179 χ hmul (fun n hn => by
    rw [hleg n (fun h => hn (Nat.mod_eq_zero_of_dvd h)), leg_eq_legendreSym 179 (by omega) n hn])
    hq m hm

/-- **No positive zero, q = 227**, stated with Mathlib's `legendreSym`. -/
theorem S_ne_zero_227_legendreSym (χ : ℕ → ℤ) (hmul : ∀ a b, χ (a * b) = χ a * χ b)
    (hleg : ∀ n : ℕ, ¬ 227 ∣ n → χ n = legendreSym 227 n) (hq : χ 227 = 1) (m : ℕ)
    (hm : 1 ≤ m) : S χ m ≠ 0 :=
  S_ne_zero_227 χ hmul (fun n hn => by
    rw [hleg n (fun h => hn (Nat.mod_eq_zero_of_dvd h)), leg_eq_legendreSym 227 (by omega) n hn])
    hq m hm

/-- The hypotheses are satisfiable: the theorem applies to the explicit `chi0 179`. -/
theorem S_chi0_ne_zero_179 (m : ℕ) (hm : 1 ≤ m) : S (chi0 179) m ≠ 0 :=
  let h := chi0_spec 179 (by omega)
  S_ne_zero_179 _ h.1 h.2.1 h.2.2 m hm

/-- The hypotheses are satisfiable: the theorem applies to the explicit `chi0 227`. -/
theorem S_chi0_ne_zero_227 (m : ℕ) (hm : 1 ≤ m) : S (chi0 227) m ≠ 0 :=
  let h := chi0_spec 227 (by omega)
  S_ne_zero_227 _ h.1 h.2.1 h.2.2 m hm

end SegmentoIISinCeros

