/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases

/-!
# The maximum of five numbers with two hidden ReLU layers (Bakaev–Brunck–Hertrich–Stade–Yehudayoff)

A ReLU network with two hidden layers computes `max(x₁,…,x₅)` exactly: `max(x₁,…,x₅) = M(x)`, where
`M` is half of an explicit signed sum of nine nested maxima (Bakaev, Brunck, Hertrich, Stade and
Yehudayoff, arXiv:2505.14338, Claim 4 and Proposition 3). This refutes for `n = 5` the conjecture of
Hertrich, Basu, Di Summa and Skutella that the maximum of `n` numbers needs `⌈log₂ n⌉` hidden layers
(here 3). `Rep n k` is the class of functions `ℝⁿ → ℝ` computed with `k` hidden layers; it is closed
under affine combinations, and `max f g = f + ReLU(g − f)` raises the depth by one.

## Main results

* `ReLUDepth.max_eq_M`: Claim 4: max of five numbers = M
* `ReLUDepth.max5_two_hidden_layers`: MAX5 is computed with two hidden ReLU layers

## References

* E. Bakaev, F. Brunck, C. Hertrich, J. Stade, A. Yehudayoff, «Better neural network expressivity: subdividing the simplex», arXiv:2505.14338 v3 (2026), ec. (2), Claim 4, Prop. 3.
-/

@[expose] public section

open Finset

namespace ReLUDepth

/-- Functions `ℝⁿ → ℝ` computable by a ReLU network with `k` hidden layers. -/
def Rep (n : ℕ) : ℕ → Set ((Fin n → ℝ) → ℝ)
  | 0 => {f | ∃ (a : Fin n → ℝ) (c : ℝ), ∀ x, f x = c + ∑ i, a i * x i}
  | k + 1 => {f | ∃ (m : ℕ) (g : Fin m → (Fin n → ℝ) → ℝ) (w : Fin m → ℝ) (c : ℝ),
      (∀ j, g j ∈ Rep n k) ∧ ∀ x, f x = c + ∑ j, w j * max 0 (g j x)}

/-- The function `M` of equation (2): half of `P₁+P₂+P₃+P₄+Q−R₁₃−R₁₄−R₂₃−R₂₄`, each term written as in the paper
(nested maxima, the form a two-hidden-layer network computes). -/
noncomputable def M (x : Fin 5 → ℝ) : ℝ :=
  let x1 := x 0; let x2 := x 1; let x3 := x 2; let x4 := x 3; let x5 := x 4
  (1 / 2 : ℝ) *
    (max (max (2 * x5) (x1 + x2)) (max x1 x3 + max x1 x4)
      + max (max (2 * x5) (x1 + x2)) (max x2 x3 + max x2 x4)
      + max (max (2 * x5) (x3 + x4)) (max x3 x1 + max x3 x2)
      + max (max (2 * x5) (x3 + x4)) (max x4 x1 + max x4 x2)
      + max (2 * x5) (max (x1 + x2) (x3 + x4))
      - max (max (2 * x5) (x1 + x3)) (max (x1 + x2) (x3 + x4))
      - max (max (2 * x5) (x1 + x4)) (max (x1 + x2) (x3 + x4))
      - max (max (2 * x5) (x2 + x3)) (max (x1 + x2) (x3 + x4))
      - max (max (2 * x5) (x2 + x4)) (max (x1 + x2) (x3 + x4)))

/-! ### Closure properties of `Rep` -/

theorem const_mem {n : ℕ} (k : ℕ) (c : ℝ) : (fun _ => c) ∈ Rep n k := by
  cases k with
  | zero => exact ⟨0, c, fun x => by simp⟩
  | succ k =>
    exact ⟨0, fun j => Fin.elim0 j, fun j => Fin.elim0 j, c, fun j => Fin.elim0 j, fun x => by simp⟩

theorem add_mem {n : ℕ} (k : ℕ) {f g : (Fin n → ℝ) → ℝ} (hf : f ∈ Rep n k) (hg : g ∈ Rep n k) :
    (fun x => f x + g x) ∈ Rep n k := by
  cases k with
  | zero =>
    obtain ⟨a, c, ha⟩ := hf
    obtain ⟨b, d, hb⟩ := hg
    refine ⟨fun i => a i + b i, c + d, fun x => ?_⟩
    simp only [ha, hb, add_mul, Finset.sum_add_distrib]
    ring
  | succ k =>
    obtain ⟨m, g1, w1, c, hg1, h1⟩ := hf
    obtain ⟨m', g2, w2, d, hg2, h2⟩ := hg
    refine ⟨m + m', Fin.append g1 g2, Fin.append w1 w2, c + d, fun j => ?_, fun x => ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa using hg1 i
      · simpa using hg2 i
    · simp only [h1, h2, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
      ring

theorem smul_mem {n : ℕ} (k : ℕ) (r : ℝ) {f : (Fin n → ℝ) → ℝ} (hf : f ∈ Rep n k) :
    (fun x => r * f x) ∈ Rep n k := by
  cases k with
  | zero =>
    obtain ⟨a, c, ha⟩ := hf
    refine ⟨fun i => r * a i, r * c, fun x => ?_⟩
    simp only [ha]
    rw [mul_add, Finset.mul_sum]
    simp only [mul_assoc]
  | succ k =>
    obtain ⟨m, g1, w1, c, hg1, h1⟩ := hf
    refine ⟨m, g1, fun j => r * w1 j, r * c, hg1, fun x => ?_⟩
    simp only [h1, Finset.mul_sum, mul_add, mul_assoc]

theorem sub_mem {n : ℕ} (k : ℕ) {f g : (Fin n → ℝ) → ℝ} (hf : f ∈ Rep n k) (hg : g ∈ Rep n k) :
    (fun x => f x - g x) ∈ Rep n k := by
  have := add_mem k hf (smul_mem k (-1) hg)
  simpa [sub_eq_add_neg] using this

theorem neg_mem {n : ℕ} (k : ℕ) {f : (Fin n → ℝ) → ℝ} (hf : f ∈ Rep n k) :
    (fun x => - f x) ∈ Rep n k := by
  have := smul_mem k (-1) hf
  simpa using this

theorem relu_id (t : ℝ) : max 0 t - max 0 (-t) = t := by
  rcases le_total 0 t with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

/-- Affine maps are in `Rep n k` for every `k`. -/
theorem affine_mem {n : ℕ} (k : ℕ) (a : Fin n → ℝ) (c : ℝ) :
    (fun x : Fin n → ℝ => c + ∑ i, a i * x i) ∈ Rep n k := by
  induction k with
  | zero => exact ⟨a, c, fun x => rfl⟩
  | succ k ih =>
    refine ⟨2, ![fun x => c + ∑ i, a i * x i, fun x => -(c + ∑ i, a i * x i)], ![1, -1], 0,
      ?_, fun x => ?_⟩
    · intro j
      fin_cases j
      · exact ih
      · simpa using neg_mem k ih
    · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      have := relu_id (c + ∑ i, a i * x i)
      linarith

theorem coord_mem {n : ℕ} (k : ℕ) (i : Fin n) : (fun x : Fin n → ℝ => x i) ∈ Rep n k := by
  have := affine_mem (n := n) k (Pi.single i 1) 0
  convert this using 1
  funext x
  simp [Pi.single_apply]

/-- `Rep n k ⊆ Rep n (k+1)`. -/
theorem mono_mem {n : ℕ} (k : ℕ) {f : (Fin n → ℝ) → ℝ} (hf : f ∈ Rep n k) :
    f ∈ Rep n (k + 1) := by
  refine ⟨2, ![f, fun x => - f x], ![1, -1], 0, ?_, fun x => ?_⟩
  · intro j
    fin_cases j
    · exact hf
    · exact neg_mem k hf
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    have := relu_id (f x)
    linarith

theorem relu_mem {n : ℕ} (k : ℕ) {f : (Fin n → ℝ) → ℝ} (hf : f ∈ Rep n k) :
    (fun x => max 0 (f x)) ∈ Rep n (k + 1) :=
  ⟨1, fun _ => f, fun _ => 1, 0, fun _ => hf, fun x => by simp⟩

/-- `max f g = f + ReLU (g - f)` raises the depth by one. -/
theorem max_mem {n : ℕ} (k : ℕ) {f g : (Fin n → ℝ) → ℝ} (hf : f ∈ Rep n k) (hg : g ∈ Rep n k) :
    (fun x => max (f x) (g x)) ∈ Rep n (k + 1) := by
  have h := add_mem (k + 1) (mono_mem k hf) (relu_mem k (sub_mem k hg hf))
  refine (by
    convert h using 2 with x
    have : max (f x) (g x) = f x + max 0 (g x - f x) := by
      rcases le_total (f x) (g x) with h | h
      · rw [max_eq_right h, max_eq_right (by linarith)]; ring
      · rw [max_eq_left h, max_eq_left (by linarith)]; ring
    exact this)

/-! ### `M` has two hidden layers -/

theorem M_mem : M ∈ Rep 5 2 := by
  have c : ∀ i : Fin 5, (fun x : Fin 5 → ℝ => x i) ∈ Rep 5 0 := fun i => coord_mem 0 i
  have c1 : ∀ i : Fin 5, (fun x : Fin 5 → ℝ => x i) ∈ Rep 5 1 := fun i => coord_mem 1 i
  have e2 : (fun x : Fin 5 → ℝ => 2 * x 4) ∈ Rep 5 1 := smul_mem 1 2 (c1 4)
  have s : ∀ i j : Fin 5, (fun x : Fin 5 → ℝ => x i + x j) ∈ Rep 5 1 :=
    fun i j => add_mem 1 (c1 i) (c1 j)
  -- level 1 pieces
  have m1 : ∀ i j : Fin 5, (fun x : Fin 5 → ℝ => max (x i) (x j)) ∈ Rep 5 1 :=
    fun i j => max_mem 0 (c i) (c j)
  have r1 : ∀ i j : Fin 5, (fun x : Fin 5 → ℝ => max (x i) (x j)) ∈ Rep 5 1 := m1
  have mm : ∀ i j k l : Fin 5, (fun x : Fin 5 → ℝ => max (x i) (x j) + max (x k) (x l)) ∈ Rep 5 1 :=
    fun i j k l => add_mem 1 (m1 i j) (m1 k l)
  have q : ∀ i j k l : Fin 5, (fun x : Fin 5 → ℝ => max (x i + x j) (x k + x l)) ∈ Rep 5 1 := by
    intro i j k l
    have a : (fun x : Fin 5 → ℝ => x i + x j) ∈ Rep 5 0 := add_mem 0 (c i) (c j)
    have b : (fun x : Fin 5 → ℝ => x k + x l) ∈ Rep 5 0 := add_mem 0 (c k) (c l)
    exact max_mem 0 a b
  have e0 : (fun x : Fin 5 → ℝ => 2 * x 4) ∈ Rep 5 0 := smul_mem 0 2 (c 4)
  have u : ∀ i j : Fin 5, (fun x : Fin 5 → ℝ => max (2 * x 4) (x i + x j)) ∈ Rep 5 1 := by
    intro i j
    exact max_mem 0 e0 (add_mem 0 (c i) (c j))
  -- level 2 terms
  have P : ∀ i j k p q' : Fin 5,
      (fun x : Fin 5 → ℝ => max (max (2 * x 4) (x i + x j)) (max (x k) (x p) + max (x k) (x q')))
        ∈ Rep 5 2 := by
    intro i j k p q'
    exact max_mem 1 (u i j) (mm k p k q')
  have R : ∀ i j : Fin 5, (fun x : Fin 5 → ℝ =>
      max (max (2 * x 4) (x i + x j)) (max (x 0 + x 1) (x 2 + x 3))) ∈ Rep 5 2 := by
    intro i j
    exact max_mem 1 (u i j) (q 0 1 2 3)
  have Q : (fun x : Fin 5 → ℝ => max (2 * x 4) (max (x 0 + x 1) (x 2 + x 3))) ∈ Rep 5 2 :=
    max_mem 1 e2 (q 0 1 2 3)
  have h12 := smul_mem 2 (1 / 2 : ℝ)
    (sub_mem 2 (sub_mem 2 (sub_mem 2 (sub_mem 2
      (add_mem 2 (add_mem 2 (add_mem 2 (add_mem 2 (P 0 1 0 2 3) (P 0 1 1 2 3)) (P 2 3 2 0 1))
        (P 2 3 3 0 1)) Q)
      (R 0 2)) (R 0 3)) (R 1 2)) (R 1 3))
  convert h12 using 1
  funext x
  simp only [M]

/-! ### Claim 4: `M = max` -/

/-- The nine terms of `M`, as functions of the five coordinates. -/
noncomputable def P1 (a b c d e : ℝ) : ℝ := max (max (2 * e) (a + b)) (max a c + max a d)
noncomputable def P2 (a b c d e : ℝ) : ℝ := max (max (2 * e) (a + b)) (max b c + max b d)
noncomputable def P3 (a b c d e : ℝ) : ℝ := max (max (2 * e) (c + d)) (max c a + max c b)
noncomputable def P4 (a b c d e : ℝ) : ℝ := max (max (2 * e) (c + d)) (max d a + max d b)
noncomputable def Q (a b c d e : ℝ) : ℝ := max (2 * e) (max (a + b) (c + d))
noncomputable def R13 (a b c d e : ℝ) : ℝ := max (max (2 * e) (a + c)) (max (a + b) (c + d))
noncomputable def R14 (a b c d e : ℝ) : ℝ := max (max (2 * e) (a + d)) (max (a + b) (c + d))
noncomputable def R23 (a b c d e : ℝ) : ℝ := max (max (2 * e) (b + c)) (max (a + b) (c + d))
noncomputable def R24 (a b c d e : ℝ) : ℝ := max (max (2 * e) (b + d)) (max (a + b) (c + d))

theorem M_eq (x : Fin 5 → ℝ) :
    M x = (1 / 2 : ℝ) * (P1 (x 0) (x 1) (x 2) (x 3) (x 4) + P2 (x 0) (x 1) (x 2) (x 3) (x 4)
      + P3 (x 0) (x 1) (x 2) (x 3) (x 4) + P4 (x 0) (x 1) (x 2) (x 3) (x 4)
      + Q (x 0) (x 1) (x 2) (x 3) (x 4) - R13 (x 0) (x 1) (x 2) (x 3) (x 4)
      - R14 (x 0) (x 1) (x 2) (x 3) (x 4) - R23 (x 0) (x 1) (x 2) (x 3) (x 4)
      - R24 (x 0) (x 1) (x 2) (x 3) (x 4)) := rfl

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! Case analysis: which coordinate is maximal (the paper reduces the four cases to one by symmetry). -/

theorem e_P1 (a b c d e : ℝ) (ha : a ≤ e) (hb : b ≤ e) (hc : c ≤ e) (hd : d ≤ e) :
    P1 a b c d e = 2 * e := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

theorem e_P2 (a b c d e : ℝ) (ha : a ≤ e) (hb : b ≤ e) (hc : c ≤ e) (hd : d ≤ e) :
    P2 a b c d e = 2 * e := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

theorem e_P3 (a b c d e : ℝ) (ha : a ≤ e) (hb : b ≤ e) (hc : c ≤ e) (hd : d ≤ e) :
    P3 a b c d e = 2 * e := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

theorem e_P4 (a b c d e : ℝ) (ha : a ≤ e) (hb : b ≤ e) (hc : c ≤ e) (hd : d ≤ e) :
    P4 a b c d e = 2 * e := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

theorem e_Q (a b c d e : ℝ) (ha : a ≤ e) (hb : b ≤ e) (hc : c ≤ e) (hd : d ≤ e) :
    Q a b c d e = 2 * e := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

theorem e_R13 (a b c d e : ℝ) (ha : a ≤ e) (hb : b ≤ e) (hc : c ≤ e) (hd : d ≤ e) :
    R13 a b c d e = 2 * e := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

theorem e_R14 (a b c d e : ℝ) (ha : a ≤ e) (hb : b ≤ e) (hc : c ≤ e) (hd : d ≤ e) :
    R14 a b c d e = 2 * e := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

theorem e_R23 (a b c d e : ℝ) (ha : a ≤ e) (hb : b ≤ e) (hc : c ≤ e) (hd : d ≤ e) :
    R23 a b c d e = 2 * e := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

theorem e_R24 (a b c d e : ℝ) (ha : a ≤ e) (hb : b ≤ e) (hc : c ≤ e) (hd : d ≤ e) :
    R24 a b c d e = 2 * e := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

/-- `e` maximal. -/
theorem case_e (a b c d e : ℝ) (ha : a ≤ e) (hb : b ≤ e) (hc : c ≤ e) (hd : d ≤ e) :
    (1 / 2 : ℝ) * (P1 a b c d e + P2 a b c d e + P3 a b c d e + P4 a b c d e + Q a b c d e
      - R13 a b c d e - R14 a b c d e - R23 a b c d e - R24 a b c d e) = e := by
  rw [e_P1 a b c d e ha hb hc hd, e_P2 a b c d e ha hb hc hd, e_P3 a b c d e ha hb hc hd,
    e_P4 a b c d e ha hb hc hd, e_Q a b c d e ha hb hc hd, e_R13 a b c d e ha hb hc hd,
    e_R14 a b c d e ha hb hc hd, e_R23 a b c d e ha hb hc hd, e_R24 a b c d e ha hb hc hd]
  ring

theorem a_P1 (a b c d e : ℝ) (hb : b ≤ a) (hc : c ≤ a) (hd : d ≤ a) (he : e ≤ a) :
    P1 a b c d e = 2 * a := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

theorem a_P2 (a b c d e : ℝ) (hb : b ≤ a) (hc : c ≤ a) (hd : d ≤ a) (he : e ≤ a) :
    P2 a b c d e = R23 a b c d e := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

theorem a_P3 (a b c d e : ℝ) (hb : b ≤ a) (hc : c ≤ a) (hd : d ≤ a) (he : e ≤ a) :
    P3 a b c d e = R13 a b c d e := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

theorem a_P4 (a b c d e : ℝ) (hb : b ≤ a) (hc : c ≤ a) (hd : d ≤ a) (he : e ≤ a) :
    P4 a b c d e = R14 a b c d e := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

theorem a_R24 (a b c d e : ℝ) (hb : b ≤ a) (hc : c ≤ a) (hd : d ≤ a) (he : e ≤ a) :
    R24 a b c d e = Q a b c d e := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

/-- `a` maximal. -/
theorem case_a (a b c d e : ℝ) (hb : b ≤ a) (hc : c ≤ a) (hd : d ≤ a) (he : e ≤ a) :
    (1 / 2 : ℝ) * (P1 a b c d e + P2 a b c d e + P3 a b c d e + P4 a b c d e + Q a b c d e
      - R13 a b c d e - R14 a b c d e - R23 a b c d e - R24 a b c d e) = a := by
  rw [a_P1 a b c d e hb hc hd he, a_P2 a b c d e hb hc hd he, a_P3 a b c d e hb hc hd he, a_P4 a b c d e hb hc hd he, a_R24 a b c d e hb hc hd he]
  ring

theorem b_P2 (a b c d e : ℝ) (ha : a ≤ b) (hc : c ≤ b) (hd : d ≤ b) (he : e ≤ b) :
    P2 a b c d e = 2 * b := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

theorem b_P1 (a b c d e : ℝ) (ha : a ≤ b) (hc : c ≤ b) (hd : d ≤ b) (he : e ≤ b) :
    P1 a b c d e = R13 a b c d e := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

theorem b_P3 (a b c d e : ℝ) (ha : a ≤ b) (hc : c ≤ b) (hd : d ≤ b) (he : e ≤ b) :
    P3 a b c d e = R23 a b c d e := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

theorem b_P4 (a b c d e : ℝ) (ha : a ≤ b) (hc : c ≤ b) (hd : d ≤ b) (he : e ≤ b) :
    P4 a b c d e = R24 a b c d e := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

theorem b_R14 (a b c d e : ℝ) (ha : a ≤ b) (hc : c ≤ b) (hd : d ≤ b) (he : e ≤ b) :
    R14 a b c d e = Q a b c d e := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

/-- `b` maximal. -/
theorem case_b (a b c d e : ℝ) (ha : a ≤ b) (hc : c ≤ b) (hd : d ≤ b) (he : e ≤ b) :
    (1 / 2 : ℝ) * (P1 a b c d e + P2 a b c d e + P3 a b c d e + P4 a b c d e + Q a b c d e
      - R13 a b c d e - R14 a b c d e - R23 a b c d e - R24 a b c d e) = b := by
  rw [b_P2 a b c d e ha hc hd he, b_P1 a b c d e ha hc hd he, b_P3 a b c d e ha hc hd he, b_P4 a b c d e ha hc hd he, b_R14 a b c d e ha hc hd he]
  ring

theorem c_P3 (a b c d e : ℝ) (ha : a ≤ c) (hb : b ≤ c) (hd : d ≤ c) (he : e ≤ c) :
    P3 a b c d e = 2 * c := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

theorem c_P4 (a b c d e : ℝ) (ha : a ≤ c) (hb : b ≤ c) (hd : d ≤ c) (he : e ≤ c) :
    P4 a b c d e = R14 a b c d e := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

theorem c_P1 (a b c d e : ℝ) (ha : a ≤ c) (hb : b ≤ c) (hd : d ≤ c) (he : e ≤ c) :
    P1 a b c d e = R13 a b c d e := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

theorem c_P2 (a b c d e : ℝ) (ha : a ≤ c) (hb : b ≤ c) (hd : d ≤ c) (he : e ≤ c) :
    P2 a b c d e = R23 a b c d e := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

theorem c_R24 (a b c d e : ℝ) (ha : a ≤ c) (hb : b ≤ c) (hd : d ≤ c) (he : e ≤ c) :
    R24 a b c d e = Q a b c d e := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

/-- `c` maximal. -/
theorem case_c (a b c d e : ℝ) (ha : a ≤ c) (hb : b ≤ c) (hd : d ≤ c) (he : e ≤ c) :
    (1 / 2 : ℝ) * (P1 a b c d e + P2 a b c d e + P3 a b c d e + P4 a b c d e + Q a b c d e
      - R13 a b c d e - R14 a b c d e - R23 a b c d e - R24 a b c d e) = c := by
  rw [c_P3 a b c d e ha hb hd he, c_P4 a b c d e ha hb hd he, c_P1 a b c d e ha hb hd he, c_P2 a b c d e ha hb hd he, c_R24 a b c d e ha hb hd he]
  ring

theorem d_P4 (a b c d e : ℝ) (ha : a ≤ d) (hb : b ≤ d) (hc : c ≤ d) (he : e ≤ d) :
    P4 a b c d e = 2 * d := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

theorem d_P3 (a b c d e : ℝ) (ha : a ≤ d) (hb : b ≤ d) (hc : c ≤ d) (he : e ≤ d) :
    P3 a b c d e = R13 a b c d e := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

theorem d_P2 (a b c d e : ℝ) (ha : a ≤ d) (hb : b ≤ d) (hc : c ≤ d) (he : e ≤ d) :
    P2 a b c d e = R24 a b c d e := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

theorem d_P1 (a b c d e : ℝ) (ha : a ≤ d) (hb : b ≤ d) (hc : c ≤ d) (he : e ≤ d) :
    P1 a b c d e = R14 a b c d e := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

theorem d_R23 (a b c d e : ℝ) (ha : a ≤ d) (hb : b ≤ d) (hc : c ≤ d) (he : e ≤ d) :
    R23 a b c d e = Q a b c d e := by
  simp only [P1, P2, P3, P4, Q, R13, R14, R23, R24, max_def]
  split_ifs <;> linarith

/-- `d` maximal. -/
theorem case_d (a b c d e : ℝ) (ha : a ≤ d) (hb : b ≤ d) (hc : c ≤ d) (he : e ≤ d) :
    (1 / 2 : ℝ) * (P1 a b c d e + P2 a b c d e + P3 a b c d e + P4 a b c d e + Q a b c d e
      - R13 a b c d e - R14 a b c d e - R23 a b c d e - R24 a b c d e) = d := by
  rw [d_P4 a b c d e ha hb hc he, d_P3 a b c d e ha hb hc he, d_P2 a b c d e ha hb hc he, d_P1 a b c d e ha hb hc he, d_R23 a b c d e ha hb hc he]
  ring

theorem max_eq_M (x : Fin 5 → ℝ) : M x = Finset.univ.sup' Finset.univ_nonempty x := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty x
  have hle : ∀ j, x j ≤ Finset.univ.sup' Finset.univ_nonempty x :=
    fun j => Finset.le_sup' x (Finset.mem_univ j)
  rw [M_eq, hi]
  have h : ∀ j, x j ≤ x i := fun j => by rw [← hi]; exact hle j
  fin_cases i
  · exact case_a _ _ _ _ _ (h 1) (h 2) (h 3) (h 4)
  · exact case_b _ _ _ _ _ (h 0) (h 2) (h 3) (h 4)
  · exact case_c _ _ _ _ _ (h 0) (h 1) (h 3) (h 4)
  · exact case_d _ _ _ _ _ (h 0) (h 1) (h 2) (h 4)
  · exact case_e _ _ _ _ _ (h 0) (h 1) (h 2) (h 3)

theorem max5_two_hidden_layers :
    (fun x : Fin 5 → ℝ => Finset.univ.sup' Finset.univ_nonempty x) ∈ Rep 5 2 := by
  have : (fun x : Fin 5 → ℝ => Finset.univ.sup' Finset.univ_nonempty x) = M := by
    funext x
    exact (max_eq_M x).symm
  rw [this]
  exact M_mem

end ReLUDepth


end
