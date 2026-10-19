/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Abel

/-!
# The type-C residue identity and the capacity criterion

For a vector `x ∈ ℤ^m`, taken through its reduction modulo `q` as a list over `ZMod q` (or over a
finite abelian group `G`), the residue `R x` of the type-C positive roots in `ℤ[G]` satisfies
`2 R x + 2m = P(x)² + P(2x)`. Counting classes gives `4 N + 2m = ∑_g o(g)² + ∑_{2g = 0} o(g)`,
where `o(g)` is the multiplicity of `g`. Hence `N_q(x) ≥ N_q(ρ)` with equality iff `x` meets the
capacities `o(g) ≤ d` (`d q = 2m + 2`), and then `R x = R ρ`.

## Main results

* `ResidueCapacity.eq_res`: the residue identity.
* `ResidueCapacity.four_N`: the class count.
* `ResidueCapacity.cap_criterion_gen`, `ResidueCapacity.conj_cap`: the capacity criterion.
* `ResidueCapacity.prop_res_cap`: `R x = R ρ` under the capacities.

## References

* C. Marín, *Integer character values on the ρ-line of Sp(2m)*, Zenodo (2026),
  doi:10.5281/zenodo.22683560.
-/

@[expose] public section

open Finset

namespace ResidueCapacity

variable {G : Type*} [AddCommGroup G]

local notation "A" => AddMonoidAlgebra ℤ G

/-- The basis element `X^g` of `ℤ[G]`. -/
noncomputable abbrev s (g : G) : AddMonoidAlgebra ℤ G := AddMonoidAlgebra.single g 1

lemma s_mul (a b : G) : s a * s b = s (a + b) := by
  simp [s, AddMonoidAlgebra.single_mul_single]

lemma s_zero : s (0 : G) = 1 := rfl

/-- `P_x = Σ_i (X^{x_i} + X^{-x_i})`. -/
noncomputable def P : List G → AddMonoidAlgebra ℤ G
  | [] => 0
  | a :: xs => s a + s (-a) + P xs

/-- The values `(x,α)` for the positive roots `α` of `C_m`, listed recursively:
for `x = (a, x₂, …)` the roots `2e₁`, then `e₁ - e_j, e₁ + e_j` (`j > 1`), then those of the tail. -/
def posRootVals : List G → List G
  | [] => []
  | a :: xs => (2 • a) :: (xs.flatMap fun b => [a - b, a + b]) ++ posRootVals xs

/-- `ℛ_x = Σ_{α ∈ Φ(C_m)} X^{(x,α)}`, with `Φ = Φ⁺ ∪ -Φ⁺`. -/
noncomputable def R (x : List G) : AddMonoidAlgebra ℤ G :=
  ((posRootVals x).map fun v => s v + s (-v)).sum

lemma cross (a : G) (xs : List G) :
    (s a + s (-a)) * P xs =
      ((xs.flatMap fun b => [a - b, a + b]).map fun v => s v + s (-v)).sum := by
  induction xs with
  | nil => simp [P]
  | cons b xs ih =>
    simp only [P, List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [← ih]
    have e : (s a + s (-a)) * (s b + s (-b)) = s (a - b) + s (-(a - b)) + (s (a + b) + s (-(a + b))) := by
      simp only [add_mul, mul_add, s_mul]
      rw [show a + -b = a - b by abel, show -a + b = -(a - b) by abel,
        show -a + -b = -(a + b) by abel]
      abel
    rw [mul_add, e, ih]

theorem eq_res (x : List G) :
    2 • R x + (2 * x.length) • (1 : AddMonoidAlgebra ℤ G) =
      P x ^ 2 + P (x.map fun a => 2 • a) := by
  induction x with
  | nil => simp [R, P, posRootVals]
  | cons a xs ih =>
    have hR : R (a :: xs) = s (2 • a) + s (-(2 • a)) +
        ((xs.flatMap fun b => [a - b, a + b]).map fun v => s v + s (-v)).sum + R xs := by
      simp [R, posRootVals, List.sum_append, add_assoc]
    have hsq : (s a + s (-a)) ^ 2 = s (2 • a) + s (-(2 • a)) + 2 • (1 : AddMonoidAlgebra ℤ G) := by
      rw [sq]
      simp only [add_mul, mul_add, s_mul]
      rw [show a + a = 2 • a by rw [two_nsmul], show -a + -a = -(2 • a) by rw [two_nsmul]; abel,
        show a + -a = 0 by abel, show -a + a = 0 by abel, s_zero]
      rw [two_nsmul (1 : AddMonoidAlgebra ℤ G)]; abel
    rw [hR, ← cross]
    simp only [P, List.map_cons, List.length_cons]
    simp only [nsmul_eq_mul (α := AddMonoidAlgebra ℤ G), Nat.cast_ofNat, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one] at ih hsq ⊢
    linear_combination ih - hsq

/-! ## Part 2: occupancies and the count `N_q` -/

section Count

variable [DecidableEq G]

/-- Coefficient of `P_x` at `g`: `o_x(g) = #{i : x_i = g} + #{i : -x_i = g}`. -/
def o (x : List G) (g : G) : ℤ :=
  (x.map fun b => (if b = g then (1 : ℤ) else 0) + (if -b = g then 1 else 0)).sum

/-- `N_q(x) = #{α > 0 : (x,α) ≡ 0}`. -/
def Nq (x : List G) : ℕ := (posRootVals x).count 0

@[simp] lemma o_nil (g : G) : o [] g = 0 := rfl

lemma o_cons (a : G) (xs : List G) (g : G) :
    o (a :: xs) g = ((if a = g then (1 : ℤ) else 0) + (if -a = g then 1 else 0)) + o xs g := by
  simp [o]

lemma o_neg (x : List G) (g : G) : o x (-g) = o x g := by
  induction x with
  | nil => rfl
  | cons a xs ih =>
    rw [o_cons, o_cons, ih]
    have h1 : (a = -g) ↔ (-a = g) := by rw [neg_eq_iff_eq_neg]
    have h2 : (-a = -g) ↔ (a = g) := neg_inj
    simp only [h1, h2]; ring

lemma o_sum [Fintype G] (x : List G) : ∑ g, o x g = 2 * x.length := by
  induction x with
  | nil => simp
  | cons a xs ih =>
    simp only [o_cons, Finset.sum_add_distrib, ih, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      List.length_cons]
    push_cast; ring

lemma o_nonneg (x : List G) (g : G) : 0 ≤ o x g := by
  induction x with
  | nil => simp
  | cons a xs ih =>
    rw [o_cons]
    have : (0 : ℤ) ≤ (if a = g then 1 else 0) := by split_ifs <;> norm_num
    have : (0 : ℤ) ≤ (if -a = g then 1 else 0) := by split_ifs <;> norm_num
    linarith

omit [DecidableEq G] in
lemma fixed_iff (a : G) : (2 • a = 0) ↔ (-a = a) := by
  rw [two_nsmul, neg_eq_iff_add_eq_zero, eq_comm]

lemma o_fixed_even (x : List G) (g : G) (hg : 2 • g = 0) : Even (o x g) := by
  have hn : -g = g := (fixed_iff g).1 hg
  induction x with
  | nil => simp
  | cons a xs ih =>
    rw [o_cons]
    have : (-a = g) ↔ (a = g) := by
      rw [neg_eq_iff_eq_neg, hn]
    simp only [this]
    exact (by split_ifs <;> decide : Even ((if a = g then (1 : ℤ) else 0) +
      (if a = g then 1 else 0))).add ih

omit [AddCommGroup G] in
lemma count_eq_sum (l : List G) (a : G) :
    (l.count a : ℤ) = (l.map fun v => if v = a then (1 : ℤ) else 0).sum := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.count_cons, List.map_cons, List.sum_cons, ← ih]
    by_cases h : b = a <;> simp [h, add_comm]

lemma cross_count (a : G) (xs : List G) :
    ((xs.flatMap fun b => [a - b, a + b]).map fun v => if v = 0 then (1 : ℤ) else 0).sum =
      o xs a := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, o_cons]
    have h1 : (a - b = 0) ↔ (b = a) := by rw [sub_eq_zero, eq_comm]
    have h2 : (a + b = 0) ↔ (-b = a) :=
      ⟨fun h => (eq_neg_of_add_eq_zero_left h).symm, fun h => by rw [← h]; abel⟩
    simp [h1, h2]

lemma Nq_cons (a : G) (xs : List G) :
    (Nq (a :: xs) : ℤ) = (if 2 • a = 0 then 1 else 0) + o xs a + Nq xs := by
  simp only [Nq, count_eq_sum, posRootVals, List.cons_append, List.map_cons, List.sum_cons,
    List.map_append, List.sum_append, cross_count]
  ring

variable [Fintype G]

lemma sum_u_mul (a : G) (f : G → ℤ) :
    ∑ g, ((if a = g then (1 : ℤ) else 0) + (if -a = g then 1 else 0)) * f g = f a + f (-a) := by
  simp [add_mul, Finset.sum_add_distrib]

lemma sum_u_sq (a : G) :
    ∑ g, ((if a = g then (1 : ℤ) else 0) + (if -a = g then 1 else 0)) ^ 2 =
      2 + 2 * (if 2 • a = 0 then 1 else 0) := by
  by_cases h : -a = a
  · have hf : 2 • a = 0 := (fixed_iff a).2 h
    simp only [h, hf, ite_true]
    have : ∀ g : G, ((if a = g then (1 : ℤ) else 0) + (if a = g then 1 else 0)) ^ 2 =
        4 * (if a = g then 1 else 0) := by intro g; split_ifs <;> norm_num
    simp only [this, ← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ, ite_true]; norm_num
  · have hf : ¬ 2 • a = 0 := fun h' => h ((fixed_iff a).1 h')
    simp only [hf, ite_false]
    have : ∀ g : G, ((if a = g then (1 : ℤ) else 0) + (if -a = g then 1 else 0)) ^ 2 =
        (if a = g then 1 else 0) + (if -a = g then 1 else 0) := by
      intro g
      rcases eq_or_ne a g with h1 | h1 <;> rcases eq_or_ne (-a) g with h2 | h2
      · exact absurd (h2.trans h1.symm) h
      · rw [ite_eq_left h1, ite_eq_right h2]; norm_num
      · rw [ite_eq_right h1, ite_eq_left h2]; norm_num
      · rw [ite_eq_right h1, ite_eq_right h2]; norm_num
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]; norm_num

lemma sum_fix_u (a : G) :
    ∑ g, (if 2 • g = 0 then ((if a = g then (1 : ℤ) else 0) + (if -a = g then 1 else 0)) else 0) =
      2 * (if 2 • a = 0 then 1 else 0) := by
  have e : ∀ g : G, (if 2 • g = 0 then ((if a = g then (1 : ℤ) else 0) +
      (if -a = g then 1 else 0)) else 0) =
      ((if a = g then (1 : ℤ) else 0) + (if -a = g then 1 else 0)) *
        (if 2 • g = 0 then 1 else 0) := by
    intro g; split_ifs <;> simp
  simp only [e, sum_u_mul]
  have : (2 • (-a) = 0) ↔ (2 • a = 0) := by rw [smul_neg, neg_eq_zero]
  simp only [this]; ring

/-- Key identity (equivalent to `eq:Nclases` of the paper):
`4 N_q(x) + 2m = Σ_g o_x(g)² + Σ_{2g=0} o_x(g)`. -/
theorem four_N (x : List G) :
    4 * (Nq x : ℤ) + 2 * x.length =
      ∑ g, (o x g ^ 2 + if 2 • g = 0 then o x g else 0) := by
  induction x with
  | nil => simp [Nq, posRootVals]
  | cons a xs ih =>
    rw [Nq_cons]
    have e : ∀ g : G, (o (a :: xs) g ^ 2 + if 2 • g = 0 then o (a :: xs) g else 0) =
        (o xs g ^ 2 + if 2 • g = 0 then o xs g else 0) +
        2 * (((if a = g then (1 : ℤ) else 0) + (if -a = g then 1 else 0)) * o xs g) +
        ((if a = g then (1 : ℤ) else 0) + (if -a = g then 1 else 0)) ^ 2 +
        (if 2 • g = 0 then ((if a = g then (1 : ℤ) else 0) + (if -a = g then 1 else 0)) else 0) := by
      intro g; rw [o_cons]; split_ifs <;> ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, ← ih, sum_u_mul, sum_u_sq, sum_fix_u,
      o_neg, List.length_cons]
    push_cast; ring


end Count

/-! ## Part 3: capacities and the criterion `N_q(x) = r_q` (Corollary `conj:cap`) -/

section Capacity

variable [DecidableEq G]

/-- Folded occupancy `n_c`: number of entries of `x` lying in the folded class `{g, -g}`. -/
def occ (x : List G) (g : G) : ℕ := x.countP fun a => decide (a = g ∨ a = -g)

/-- `o_x(g) = 2 n_c` on a fixed class (`2g = 0`), `o_x(g) = n_c` on a non-fixed one. -/
lemma o_eq_occ (x : List G) (g : G) :
    o x g = if 2 • g = 0 then 2 * (occ x g : ℤ) else (occ x g : ℤ) := by
  induction x with
  | nil => simp [occ]
  | cons a xs ih =>
    rw [o_cons, ih]
    have h1 : (-a = g) ↔ (a = -g) := neg_eq_iff_eq_neg
    by_cases hg : 2 • g = 0
    · have hn : -g = g := (fixed_iff g).1 hg
      rw [hn] at h1
      simp only [occ, List.countP_cons, hg, ite_true, hn, or_self, h1,
        decide_eq_true_eq]
      split_ifs <;> push_cast <;> ring
    · have hne : -g ≠ g := fun h => hg ((fixed_iff g).2 h)
      simp only [occ, List.countP_cons, hg, ite_false, h1, decide_eq_true_eq]
      have hx : ¬ (a = g ∧ a = -g) := fun ⟨h1, h2⟩ => hne (h2.symm.trans h1)
      by_cases ha : a = g <;> by_cases hb : a = -g
      · exact absurd ⟨ha, hb⟩ hx
      · rw [ite_eq_left ha, ite_eq_right hb, ite_eq_left (Or.inl ha)]; push_cast; ring
      · rw [ite_eq_right ha, ite_eq_left hb, ite_eq_left (Or.inr hb)]; push_cast; ring
      · rw [ite_eq_right ha, ite_eq_right hb, ite_eq_right (by tauto)]; push_cast; ring

/-- The capacities of Corollary `conj:cap`: each non-fixed folded class holds at most `d`
entries and each fixed class (`2g = 0`, i.e. `g = -g`) at most `⌊d/2⌋`. -/
def Cap (d : ℕ) (x : List G) : Prop :=
  ∀ g : G, (2 • g ≠ 0 → occ x g ≤ d) ∧ (2 • g = 0 → occ x g ≤ d / 2)

/-- The capacities say exactly `o_x(g) ≤ d` for every `g`. -/
lemma cap_iff (d : ℕ) (x : List G) : Cap d x ↔ ∀ g, o x g ≤ d := by
  refine forall_congr' fun g => ?_
  rw [o_eq_occ]
  by_cases hg : 2 • g = 0
  · simp [hg]; omega
  · simp [hg]

/-- `ε(d) = 1` for `d` even, `0` for `d` odd. -/
def eps (d : ℕ) : ℤ := if Even d then 1 else 0

/-- Per-class slack of the cost `n² + [2g=0] n` above its supporting line of slope `2d-1`. -/
def slack (d : ℕ) (g : G) (n : ℤ) : ℤ :=
  if 2 • g = 0 then (n - d + 1) ^ 2 - eps d else (n - d) * (n - d + 1)

/-- Per-class intercept of that supporting line. -/
def cst (d : ℕ) (g : G) : ℤ :=
  if 2 • g = 0 then ((d : ℤ) - 1) ^ 2 - eps d else (d : ℤ) * (d - 1)

lemma cost_eq (d : ℕ) (g : G) (n : ℤ) :
    (n ^ 2 + if 2 • g = 0 then n else 0) = slack d g n + (2 * d - 1) * n - cst d g := by
  unfold slack cst; split_ifs <;> ring

lemma slack_nonneg (d : ℕ) (x : List G) (g : G) : 0 ≤ slack d g (o x g) := by
  unfold slack eps
  by_cases hg : 2 • g = 0
  · obtain ⟨k, hk⟩ := o_fixed_even x g hg
    rw [ite_eq_left hg]
    split_ifs with hd
    · obtain ⟨j, hj⟩ := hd
      have : 1 ≤ o x g - d + 1 ∨ o x g - d + 1 ≤ -1 := by omega
      rcases this with h | h <;> nlinarith
    · nlinarith [sq_nonneg (o x g - d + 1)]
  · rw [ite_eq_right hg]
    rcases le_or_gt 0 (o x g - d) with h | h
    · nlinarith
    · have : o x g - d + 1 ≤ 0 := by omega
      nlinarith

lemma le_of_slack_zero (d : ℕ) (g : G) (n : ℤ) (h : slack d g n = 0) : n ≤ d := by
  unfold slack eps at h
  split_ifs at h with hg hd
  · by_contra hc
    have : n - d + 1 ≥ 2 := by omega
    nlinarith
  · by_contra hc
    have : n - d + 1 ≥ 2 := by omega
    nlinarith
  · rcases mul_eq_zero.1 h with h | h <;> omega

/-- `bump c g = [g = c] + [g = -c]` (the coefficient of `X^c + X^{-c}` at `g`). -/
def bump (c g : G) : ℤ := (if c = g then 1 else 0) + (if -c = g then 1 else 0)

variable [Fintype G]

lemma sum_deficit (d : ℕ) (x : List G)
    (hcard : (Fintype.card G : ℤ) * d = 2 * x.length + 2) :
    ∑ h, ((d : ℤ) - o x h) = 2 := by
  rw [Finset.sum_sub_distrib, o_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  linarith

lemma slack_eq_zero_of_cap (d : ℕ) (x : List G)
    (hcard : (Fintype.card G : ℤ) * d = 2 * x.length + 2) (hcap : ∀ g, o x g ≤ d) (g : G) :
    slack d g (o x g) = 0 := by
  have hsum := sum_deficit d x hcard
  have h1 := Finset.single_le_sum (f := fun h => (d : ℤ) - o x h)
    (fun i _ => sub_nonneg.2 (hcap i)) (Finset.mem_univ g)
  have hle2 : (d : ℤ) - o x g ≤ 2 := by linarith
  have hg0 := hcap g
  unfold slack eps
  by_cases hg : 2 • g = 0
  · obtain ⟨k, hk⟩ := o_fixed_even x g hg
    rw [ite_eq_left hg]
    split_ifs with hd
    · obtain ⟨j, hj⟩ := hd
      have : o x g = d ∨ o x g = d - 2 := by omega
      rcases this with h | h <;> rw [h] <;> ring
    · obtain ⟨j, hj⟩ := Nat.not_even_iff_odd.1 hd
      have : o x g = d - 1 := by omega
      rw [this]; ring
  · rw [ite_eq_right hg]
    have hne : g ≠ -g := fun h => hg ((fixed_iff g).2 h.symm)
    have hp := Finset.sum_le_sum_of_subset_of_nonneg (f := fun h => (d : ℤ) - o x h)
      (Finset.subset_univ {g, -g}) (fun i _ _ => sub_nonneg.2 (hcap i))
    rw [Finset.sum_pair hne] at hp
    rw [o_neg] at hp
    have : 2 * ((d : ℤ) - o x g) ≤ 2 := by linarith
    have : o x g = d ∨ o x g = d - 1 := by omega
    rcases this with h | h <;> rw [h] <;> ring

lemma four_N_slack (d : ℕ) (x : List G) :
    4 * (Nq x : ℤ) + 2 * x.length =
      ∑ g, slack d g (o x g) + (2 * d - 1) * (2 * x.length) - ∑ g : G, cst d g := by
  rw [four_N]
  simp only [cost_eq d, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, o_sum]

/-- Generic form of the capacity criterion: if a reference vector `y` meets the capacities and
`|G| · d = 2m + 2`, then `N(y) ≤ N(x)` for every `x` of the same length, with equality iff `x`
meets the capacities. -/
theorem cap_criterion_gen (d : ℕ) (x y : List G) (hlen : x.length = y.length)
    (hcard : (Fintype.card G : ℤ) * d = 2 * y.length + 2) (hy : ∀ g, o y g ≤ d) :
    Nq y ≤ Nq x ∧ (Nq x = Nq y ↔ ∀ g, o x g ≤ d) := by
  have hx' : (Fintype.card G : ℤ) * d = 2 * x.length + 2 := by rw [hlen]; exact hcard
  have hy0 : ∑ g, slack d g (o y g) = 0 :=
    Finset.sum_eq_zero fun g _ => slack_eq_zero_of_cap d y hcard hy g
  have ex := four_N_slack d x
  have ey := four_N_slack d y
  rw [hy0, ← hlen] at ey
  have hnn : 0 ≤ ∑ g, slack d g (o x g) := Finset.sum_nonneg fun g _ => slack_nonneg d x g
  have key : 4 * ((Nq x : ℤ) - Nq y) = ∑ g, slack d g (o x g) := by linarith
  refine ⟨by exact_mod_cast (by linarith : (Nq y : ℤ) ≤ Nq x), ?_⟩
  constructor
  · intro h g
    have h0 : ∑ g, slack d g (o x g) = 0 := by rw [← key, h]; ring
    exact le_of_slack_zero d g _
      ((Finset.sum_eq_zero_iff_of_nonneg fun g _ => slack_nonneg d x g).1 h0 g (Finset.mem_univ g))
  · intro hc
    have h0 : ∑ g, slack d g (o x g) = 0 :=
      Finset.sum_eq_zero fun g _ => slack_eq_zero_of_cap d x hx' hc g
    have : (Nq x : ℤ) = Nq y := by linarith
    exact_mod_cast this

/-! ### Shape of the occupancies under the capacities -/

/-- `d` even: exactly one folded class `{c, -c}` falls short, `o_x = d - [g=c] - [g=-c]`. -/
lemma shape_even (d : ℕ) (x : List G) (hcard : (Fintype.card G : ℤ) * d = 2 * x.length + 2)
    (hcap : ∀ g, o x g ≤ d) (hd : Even d) :
    ∃ c, ∀ g, o x g = d - bump c g := by
  have hsum := sum_deficit d x hcard
  obtain ⟨c, hc⟩ : ∃ c, 0 < (d : ℤ) - o x c := by
    by_contra hne
    push Not at hne
    have : ∑ h, ((d : ℤ) - o x h) = 0 :=
      Finset.sum_eq_zero fun h _ => le_antisymm (hne h) (by linarith [hcap h])
    linarith
  refine ⟨c, ?_⟩
  obtain ⟨j, hj⟩ := hd
  have hf : ∀ g, bump c g ≤ (d : ℤ) - o x g := by
    intro g
    unfold bump
    by_cases hcf : 2 • c = 0
    · have hn : -c = c := (fixed_iff c).1 hcf
      obtain ⟨k, hk⟩ := o_fixed_even x c hcf
      by_cases hg : c = g
      · subst hg
        simp only [hn, ite_true]
        omega
      · simp only [hn, hg, ite_false]
        linarith [hcap g]
    · have hne : -c ≠ c := fun h => hcf ((fixed_iff c).2 h)
      by_cases hg : c = g
      · subst hg
        simp only [hne, ite_true, ite_false]
        omega
      · by_cases hg' : -c = g
        · subst hg'
          simp only [hg, ite_true, ite_false]
          rw [o_neg]
          omega
        · simp only [hg, hg', ite_false]
          linarith [hcap g]
  have hfs : ∑ g, bump c g = 2 := by
    unfold bump
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
    norm_num
  have heq := (Finset.sum_eq_sum_iff_of_le (fun g _ => hf g)).1 (by rw [hfs, hsum])
  intro g
  have := heq g (Finset.mem_univ g)
  linarith

/-- `d` odd: the capacities are saturated, `o_x = d - [2g = 0]`, provided `G` has at least two
fixed points (true for `ZMod q`, `q` even). -/
lemma shape_odd (d : ℕ) (x : List G) (hcard : (Fintype.card G : ℤ) * d = 2 * x.length + 2)
    (hcap : ∀ g, o x g ≤ d) (hd : ¬ Even d)
    (hfix : 2 ≤ ∑ g : G, (if 2 • g = 0 then (1 : ℤ) else 0)) :
    ∀ g, o x g = d - (if 2 • g = 0 then 1 else 0) := by
  have hsum := sum_deficit d x hcard
  obtain ⟨j, hj⟩ := Nat.not_even_iff_odd.1 hd
  have hf : ∀ g, (if 2 • g = 0 then (1 : ℤ) else 0) ≤ (d : ℤ) - o x g := by
    intro g
    split_ifs with hg
    · obtain ⟨k, hk⟩ := o_fixed_even x g hg
      have := hcap g
      omega
    · linarith [hcap g]
  have hle : ∑ g : G, (if 2 • g = 0 then (1 : ℤ) else 0) ≤ ∑ g, ((d : ℤ) - o x g) :=
    Finset.sum_le_sum fun g _ => hf g
  have heq := (Finset.sum_eq_sum_iff_of_le (fun g _ => hf g)).1 (by linarith)
  intro g
  have := heq g (Finset.mem_univ g)
  linarith

/-! ### `P_x` through its coefficients -/

lemma P_eq_sum (x : List G) : P x = ∑ g, (o x g) • s g := by
  induction x with
  | nil => simp [P]
  | cons a xs ih =>
    simp only [P, o_cons, add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, ih]

lemma P2_eq_sum (x : List G) : P (x.map fun a => 2 • a) = ∑ g, (o x g) • s (2 • g) := by
  induction x with
  | nil => simp [P]
  | cons a xs ih =>
    simp only [List.map_cons, P, o_cons, add_smul, Finset.sum_add_distrib, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, ih, smul_neg]

omit [DecidableEq G] in
lemma T_mul_s (c : G) : (∑ g, s g) * s c = ∑ g : G, s g := by
  rw [Finset.sum_mul]
  simp only [s_mul]
  exact Equiv.sum_comp (Equiv.addRight c) s

omit [DecidableEq G] in
lemma T_mul_T :
    (∑ g : G, s g) * (∑ g, s g) = (Fintype.card G : AddMonoidAlgebra ℤ G) * ∑ g, s g := by
  rw [Finset.sum_mul]
  have : ∀ g : G, s g * ∑ h, s h = ∑ h : G, s h := fun g => by rw [mul_comm, T_mul_s]
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- `d` even: with `P_x = d·T - X^c - X^{-c}`, the value of `P_x² + P_x(X²)` does not depend
on `c`. -/
lemma val_even (d : ℕ) (x : List G) (c : G) (h : ∀ g, o x g = d - bump c g) :
    P x ^ 2 + P (x.map fun a => 2 • a) =
      ((d : AddMonoidAlgebra ℤ G) * (d : AddMonoidAlgebra ℤ G) *
          (Fintype.card G : AddMonoidAlgebra ℤ G) - 4 * (d : AddMonoidAlgebra ℤ G)) *
          (∑ g, s g) + 2 + (d : AddMonoidAlgebra ℤ G) * ∑ g, s (2 • g) := by
  have hP : P x = (d : AddMonoidAlgebra ℤ G) * (∑ g, s g) - s c - s (-c) := by
    rw [P_eq_sum]
    simp only [h, bump, sub_smul, add_smul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      ← Finset.mul_sum, zsmul_eq_mul, Int.cast_natCast]
    abel
  have hP2 : P (x.map fun a => 2 • a) =
      (d : AddMonoidAlgebra ℤ G) * (∑ g, s (2 • g)) - s (2 • c) - s (2 • -c) := by
    rw [P2_eq_sum]
    simp only [h, bump, sub_smul, add_smul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      ← Finset.mul_sum, zsmul_eq_mul, Int.cast_natCast]
    abel
  have hTa := T_mul_s c
  have hTb := T_mul_s (-c)
  have hTT := T_mul_T (G := G)
  have haa : s c * s c = s (2 • c) := by rw [s_mul, two_nsmul]
  have hbb : s (-c) * s (-c) = s (2 • -c) := by rw [s_mul, two_nsmul]
  have hab : s c * s (-c) = 1 := by rw [s_mul, add_neg_cancel, s_zero]
  rw [hP, hP2]
  linear_combination ((d : AddMonoidAlgebra ℤ G) * d) * hTT - 2 * (d : AddMonoidAlgebra ℤ G) * hTa
    - 2 * (d : AddMonoidAlgebra ℤ G) * hTb + haa + hbb + 2 * hab

omit [DecidableEq G] [Fintype G] [AddCommGroup G] in
/-- `ℤ[G]` is torsion-free: `2a = 2b → a = b`. -/
lemma two_smul_cancel {a b : AddMonoidAlgebra ℤ G} (h : 2 • a = 2 • b) : a = b := by
  rw [two_nsmul, two_nsmul] at h
  refine AddMonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  have hg := congrArg (fun f : AddMonoidAlgebra ℤ G => f.coeff g) h
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at hg
  omega

end Capacity

/-! ## Part 4: `G = ZMod q`, the vector `ρ`, and the paper's statements -/

section ZModq

/-- `ρ = (m, m-1, …, 1)`, reduced mod `q`. -/
def rho (q m : ℕ) : List (ZMod q) :=
  ((List.range m).reverse).map fun i => ((i + 1 : ℕ) : ZMod q)

lemma rho_length (q m : ℕ) : (rho q m).length = m := by simp [rho]

lemma rho_succ (q m : ℕ) : rho q (m + 1) = ((m + 1 : ℕ) : ZMod q) :: rho q m := by
  simp [rho, List.range_succ]

lemma o_rho (q m : ℕ) (g : ZMod q) :
    o (rho q m) g = ∑ i ∈ Finset.range m,
      ((if ((i + 1 : ℕ) : ZMod q) = g then (1 : ℤ) else 0) +
        (if -((i + 1 : ℕ) : ZMod q) = g then 1 else 0)) := by
  induction m with
  | zero => simp [rho]
  | succ m ih => rw [rho_succ, o_cons, ih, Finset.sum_range_succ]; ring

lemma sum_ite_card {ι : Type*} (t : Finset ι) (p : ι → Prop) [DecidablePred p] :
    (∑ i ∈ t, if p i then (1 : ℤ) else 0) = ((t.filter p).card : ℤ) := by
  rw [Finset.card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- Every residue class mod `q` meets `{±1, …, ±m}` (an interval of `dq - 2` integers) at most
`d` times. -/
lemma card_bound {q m d : ℕ} [NeZero q] (hd : d * q = 2 * m + 2) (g : ZMod q) :
    ((Finset.range m).filter (fun i => ((i + 1 : ℕ) : ZMod q) = g)).card +
      ((Finset.range m).filter (fun i => -((i + 1 : ℕ) : ZMod q) = g)).card ≤ d := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have h1 : ((Finset.range m).filter (fun i => ((i + 1 : ℕ) : ZMod q) = g)).image
      (fun i => m + (i + 1)) ⊆
      (Finset.range (2 * m + 1)).filter (fun j : ℕ => (j : ZMod q) = g + m) := by
    intro j hj
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨i, ⟨hi, hig⟩, rfl⟩ := hj
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [Nat.cast_add, hig, add_comm]
  have h2 : ((Finset.range m).filter (fun i => -((i + 1 : ℕ) : ZMod q) = g)).image
      (fun i => m - (i + 1)) ⊆
      (Finset.range (2 * m + 1)).filter (fun j : ℕ => (j : ZMod q) = g + m) := by
    intro j hj
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨i, ⟨hi, hig⟩, rfl⟩ := hj
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [Nat.cast_sub (by omega : i + 1 ≤ m), ← hig]
    ring
  have hdisj : Disjoint
      (((Finset.range m).filter (fun i => ((i + 1 : ℕ) : ZMod q) = g)).image
        (fun i => m + (i + 1)))
      (((Finset.range m).filter (fun i => -((i + 1 : ℕ) : ZMod q) = g)).image
        (fun i => m - (i + 1))) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hj1 hj2
    obtain ⟨i, _, rfl⟩ := hj1
    obtain ⟨i', ⟨hi', _⟩, h⟩ := hj2
    omega
  have hcA := Finset.card_image_of_injOn (s := (Finset.range m).filter
    (fun i => ((i + 1 : ℕ) : ZMod q) = g)) (f := fun i => m + (i + 1))
    (fun a _ b _ h => by simp only at h; omega)
  have hcB := Finset.card_image_of_injOn (s := (Finset.range m).filter
    (fun i => -((i + 1 : ℕ) : ZMod q) = g)) (f := fun i => m - (i + 1))
    (fun a ha b hb h => by
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha hb h
      omega)
  have hT : ((Finset.range (2 * m + 1)).filter (fun j : ℕ => (j : ZMod q) = g + m)).card ≤ d := by
    have := Finset.card_le_card_of_injOn (fun j => j / q)
      (s := (Finset.range (2 * m + 1)).filter (fun j : ℕ => (j : ZMod q) = g + m))
      (t := Finset.range d)
      (fun j hj => by
        simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq,
          Finset.coe_range, Set.mem_Iio] at hj ⊢
        exact (Nat.div_lt_iff_lt_mul hq).2 (by rw [hd]; omega))
      (fun j1 hj1 j2 hj2 hdiv => by
        simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hj1 hj2 hdiv
        have hmod : j1 % q = j2 % q :=
          (ZMod.natCast_eq_natCast_iff' j1 j2 q).1 (hj1.2.trans hj2.2.symm)
        calc j1 = q * (j1 / q) + j1 % q := (Nat.div_add_mod j1 q).symm
          _ = q * (j2 / q) + j2 % q := by rw [hdiv, hmod]
          _ = j2 := Nat.div_add_mod j2 q)
    simpa using this
  calc _ = (((Finset.range m).filter (fun i => ((i + 1 : ℕ) : ZMod q) = g)).image
        (fun i => m + (i + 1)) ∪
        ((Finset.range m).filter (fun i => -((i + 1 : ℕ) : ZMod q) = g)).image
        (fun i => m - (i + 1))).card := by
          rw [Finset.card_union_of_disjoint hdisj, hcA, hcB]
    _ ≤ _ := Finset.card_le_card (Finset.union_subset h1 h2)
    _ ≤ d := hT

/-- `ρ` meets the capacities: `o_ρ(g) ≤ d` for every residue `g`. -/
lemma o_rho_le {q m d : ℕ} [NeZero q] (hd : d * q = 2 * m + 2) (g : ZMod q) :
    o (rho q m) g ≤ d := by
  rw [o_rho, Finset.sum_add_distrib, sum_ite_card, sum_ite_card]
  exact_mod_cast card_bound hd g

lemma card_hyp {q m d : ℕ} [NeZero q] (hd : d * q = 2 * m + 2) (x : List (ZMod q))
    (hx : x.length = m) : (Fintype.card (ZMod q) : ℤ) * d = 2 * x.length + 2 := by
  rw [ZMod.card, hx]
  have : q * d = 2 * m + 2 := by rw [mul_comm]; exact hd
  exact_mod_cast this

/-- `ZMod q` with `q` even has the two fixed points `0` and `q/2`. -/
lemma two_fixed {q : ℕ} [NeZero q] (hq : Even q) :
    2 ≤ ∑ g : ZMod q, (if 2 • g = 0 then (1 : ℤ) else 0) := by
  obtain ⟨k, hk⟩ := hq
  have hk0 : 0 < k := by have := NeZero.ne q; omega
  have hne : (0 : ZMod q) ≠ ((k : ℕ) : ZMod q) := by
    intro h
    have h' : ((0 : ℕ) : ZMod q) = ((k : ℕ) : ZMod q) := by rw [Nat.cast_zero]; exact h
    have := (ZMod.natCast_eq_natCast_iff' 0 k q).1 h'
    rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hfk : 2 • ((k : ℕ) : ZMod q) = 0 := by
    rw [two_nsmul, ← Nat.cast_add, ← hk, ZMod.natCast_self]
  have := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun g : ZMod q => if 2 • g = 0 then (1 : ℤ) else 0)
    (Finset.subset_univ {0, ((k : ℕ) : ZMod q)}) (fun i _ _ => by split_ifs <;> norm_num)
  rw [Finset.sum_pair hne] at this
  simp only [smul_zero, ite_true, hfk] at this
  linarith

/-- **Corollary `conj:cap`.** Let `q ∣ 2m+2`, `d = (2m+2)/q` (hypothesis `d * q = 2m + 2`), and
let `x` be any vector of length `m` over `ZMod q` (e.g. `ℓ = λ + ρ` reduced mod `q`; `Nq x` is
then `N_q(ℓ) = #{α > 0 : q ∣ (ℓ, α)}`). Then `N_q(ρ) ≤ N_q(x)`, and `N_q(x) = r_q = N_q(ρ)` iff
each non-fixed folded class mod `q` holds at most `d` entries and each fixed class at most
`⌊d/2⌋` (`Cap d x`). -/
theorem conj_cap {q m d : ℕ} [NeZero q] (hd : d * q = 2 * m + 2)
    (x : List (ZMod q)) (hx : x.length = m) :
    Nq (rho q m) ≤ Nq x ∧ (Nq x = Nq (rho q m) ↔ Cap d x) := by
  rw [cap_iff]
  exact cap_criterion_gen d x (rho q m) (by rw [hx, rho_length])
    (card_hyp hd (rho q m) (rho_length q m)) (o_rho_le hd)

/-- **Proposition `prop:res`, second half.** For `q ∣ 2m+2` (`d * q = 2m+2`) and every `x` of
length `m` over `ZMod q` meeting the capacities of `conj:cap`, `ℛ_x = ℛ_ρ` in `ℤ[ZMod q]`. -/
theorem prop_res_cap {q m d : ℕ} [NeZero q] (hd : d * q = 2 * m + 2)
    (x : List (ZMod q)) (hx : x.length = m) (hcap : Cap d x) :
    R x = R (rho q m) := by
  rw [cap_iff] at hcap
  have hcx := card_hyp hd x hx
  have hcr := card_hyp hd (rho q m) (rho_length q m)
  have key : P x ^ 2 + P (x.map fun a => 2 • a) =
      P (rho q m) ^ 2 + P ((rho q m).map fun a => 2 • a) := by
    by_cases hev : Even d
    · obtain ⟨c, hc⟩ := shape_even d x hcx hcap hev
      obtain ⟨c', hc'⟩ := shape_even d (rho q m) hcr (o_rho_le hd) hev
      rw [val_even d x c hc, val_even d _ c' hc']
    · have hqe : Even q := by
        have : Even (d * q) := by rw [hd]; exact ⟨m + 1, by ring⟩
        exact (Nat.even_mul.1 this).resolve_left hev
      have h2 := two_fixed hqe
      have e1 := shape_odd d x hcx hcap hev h2
      have e2 := shape_odd d (rho q m) hcr (o_rho_le hd) hev h2
      have : ∀ g, o x g = o (rho q m) g := fun g => by rw [e1, e2]
      rw [P_eq_sum x, P_eq_sum (rho q m), P2_eq_sum x, P2_eq_sum (rho q m)]
      simp only [this]
  have h1 := eq_res x
  have h2 := eq_res (rho q m)
  rw [hx] at h1
  rw [rho_length] at h2
  apply two_smul_cancel
  have : 2 • R x + (2 * m) • (1 : AddMonoidAlgebra ℤ (ZMod q)) =
      2 • R (rho q m) + (2 * m) • (1 : AddMonoidAlgebra ℤ (ZMod q)) := by
    rw [h1, h2, key]
  exact add_right_cancel this

end ZModq

end ResidueCapacity
