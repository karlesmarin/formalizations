/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.RepresentationTheory.Symplectic.ResidueCapacity
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Tactic.IntervalCases

/-!
# The survivor count of type `C` for every `q` (Theorem `thm:cuenta`)

For `x ∈ (ℤ/q)^m` let `N_q(x)` be the number of positive roots of `C_m` vanishing at `x` mod `q`
(`ResidueCapacity.Nq`), and `S(m,q) = #{x : N_q(x) = N_q(ρ)}`.  Write `m = u q + v`, `f = 1` or `2`
(`q` odd or even), `a = (q - f)/2`.  The proof is the marginal-cost argument: `N_q` depends only on
the occupancies of the folded classes `{c, -c}`, the minimal occupancy profiles are the
minimisers of a separable convex cost (Lagrange / supporting line), `ρ` attains the minimum, and
the vectors with a given profile are counted by a multinomial times `2^(rows in non-fixed classes)`.

## Main results

* `SurvivorCount.Nq_profile_sum`: `4 N_q(x) = Σ_g (4 n_g² if 2g = 0, n_g (n_g - 1) otherwise)`.
* `SurvivorCount.cost_eq_two_Nq`: the same by folded classes, `2 N_q = Σ_class (n² ·2 | n(n-1))`.
* `SurvivorCount.fibre_count`: vectors with prescribed fibre occupancies (multinomial count).
* `SurvivorCount.min_profile_case1`, `min_profile_case2`: `N_q(x) = r_q` iff the occupancies are
  in the allowed sets (every `q`, no divisibility hypothesis).
* `SurvivorCount.thm_cuenta_le`, `thm_cuenta_gt`: Theorem 11.1 (`thm:cuenta`), both cases,
  multiplied by the denominators.

## References

* C. Marín, *Integer character values on the ρ-line of Sp(2m)*, Zenodo (2026),
  doi:10.5281/zenodo.22683560; `characters_at_aP.tex`, Theorem 11.1.
-/

@[expose] public section

open Finset

namespace SurvivorCount

open ResidueCapacity

section Stage1

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- **Stage 1.** `4 N_q(x) = Σ_g (4 n_g²  if 2g = 0, n_g (n_g - 1) otherwise)`, `n_g = occ x g`.
Summing over classes: a non-fixed class `{g,-g}` contributes `4·C(n,2)` (two elements `g`), a fixed
one `4 n²`. -/
theorem Nq_profile_sum (x : List G) :
    4 * (Nq x : ℤ) = ∑ g : G, (if 2 • g = 0 then 4 * (occ x g : ℤ) ^ 2
      else (occ x g : ℤ) * ((occ x g : ℤ) - 1)) := by
  have h := four_N x
  have ho := o_sum x
  calc 4 * (Nq x : ℤ) = ∑ g : G, ((o x g ^ 2 + if 2 • g = 0 then o x g else 0) - o x g) := by
        rw [Finset.sum_sub_distrib, ho]; linarith
    _ = _ := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [o_eq_occ]
        split_ifs <;> ring

end Stage1

/-! ## Part A: counting maps with prescribed fibre sizes -/

section Fibre

variable {X K : Type*} [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K] (φ : X → K)

/-- Occupancy of class `k` by the row vector `x`. -/
def prof {m : ℕ} (x : Fin m → X) (k : K) : ℕ := (univ.filter fun i => φ (x i) = k).card

/-- Size of the fibre of `φ` over `k`. -/
def wt (k : K) : ℕ := (univ.filter fun a : X => φ a = k).card

lemma prof_cons {m : ℕ} (x0 : X) (x' : Fin m → X) (k : K) :
    prof φ (Fin.cons x0 x' : Fin (m + 1) → X) k = (if φ x0 = k then 1 else 0) + prof φ x' k := by
  unfold prof
  rw [Fin.card_filter_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  split_ifs <;> omega

lemma prof_cons_eq_iff {m : ℕ} (x0 : X) (x' : Fin m → X) (n : K → ℕ) :
    prof φ (Fin.cons x0 x' : Fin (m + 1) → X) = n ↔
      (1 ≤ n (φ x0) ∧ prof φ x' = Function.update n (φ x0) (n (φ x0) - 1)) := by
  constructor
  · intro h
    have h1 := congrFun h (φ x0)
    rw [prof_cons] at h1
    simp only [if_true] at h1
    refine ⟨by omega, funext fun k => ?_⟩
    have h2 := congrFun h k
    rw [prof_cons] at h2
    by_cases hk : k = φ x0
    · subst hk; simp only [Function.update_self]; omega
    · rw [Function.update_of_ne hk]
      have : ¬ φ x0 = k := fun e => hk e.symm
      simp only [this, if_false] at h2; omega
  · rintro ⟨h1, h2⟩
    funext k
    rw [prof_cons, h2]
    by_cases hk : k = φ x0
    · subst hk; simp only [Function.update_self, if_true]; omega
    · have : ¬ φ x0 = k := fun e => hk e.symm
      rw [Function.update_of_ne hk]; simp [this]

theorem fibre_count (m : ℕ) (n : K → ℕ) (hn : ∑ k, n k = m) :
    (univ.filter fun x : Fin m → X => prof φ x = n).card * ∏ k, (n k).factorial =
      m.factorial * ∏ k, (wt φ k) ^ (n k) := by
  induction m generalizing n with
  | zero =>
    have hz : n = 0 := by
      funext k
      have := (Finset.sum_eq_zero_iff.1 hn) k (Finset.mem_univ k)
      simpa using this
    subst hz
    have : (univ.filter fun x : Fin 0 → X => prof φ x = 0) = univ := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      funext k; simp [prof]
    rw [this]; simp
  | succ m ih =>
    -- count via the splitting `x = cons x0 x'`
    have hcount : (univ.filter fun x : Fin (m + 1) → X => prof φ x = n).card =
        ∑ x0 : X, if 1 ≤ n (φ x0) then
          (univ.filter fun x' : Fin m → X =>
            prof φ x' = Function.update n (φ x0) (n (φ x0) - 1)).card else 0 := by
      rw [Finset.card_filter]
      rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ => X)) (fun p : X × (Fin m → X) =>
        if prof φ (Fin.cons p.1 p.2 : Fin (m + 1) → X) = n then 1 else 0)
        (fun x => if prof φ x = n then 1 else 0) (fun p => by rfl)]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x0 _ => ?_
      simp only [prof_cons_eq_iff]
      by_cases h1 : 1 ≤ n (φ x0)
      · simp only [h1, true_and, if_true]
        rw [Finset.card_filter]
      · simp [h1]
    have hsum : ∀ k, 1 ≤ n k →
        ∑ j, (Function.update n k (n k - 1)) j = m := by
      intro k hk
      have h1 : ∑ j, n j = ∑ j, (Function.update n k (n k - 1)) j + 1 := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k),
          ← Finset.add_sum_erase _ (fun j => (Function.update n k (n k - 1)) j) (Finset.mem_univ k)]
        have : ∑ j ∈ univ.erase k, n j = ∑ j ∈ univ.erase k, (Function.update n k (n k - 1)) j :=
          Finset.sum_congr rfl fun j hj => by
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
        rw [this, Function.update_self]; omega
      omega
    have hprodf : ∀ k, 1 ≤ n k →
        ∏ j, (n j).factorial =
          n k * ∏ j, ((Function.update n k (n k - 1)) j).factorial := by
      intro k hk
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
        ← Finset.mul_prod_erase _ (fun j => ((Function.update n k (n k - 1)) j).factorial)
          (Finset.mem_univ k)]
      have : ∏ j ∈ univ.erase k, (n j).factorial =
          ∏ j ∈ univ.erase k, ((Function.update n k (n k - 1)) j).factorial :=
        Finset.prod_congr rfl fun j hj => by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [this, Function.update_self]
      obtain ⟨t, ht⟩ : ∃ t, n k = t + 1 := ⟨n k - 1, by omega⟩
      rw [ht, Nat.add_sub_cancel, Nat.factorial_succ]
      ring
    have hprodw : ∀ k, 1 ≤ n k →
        ∏ j, (wt φ j) ^ (n j) =
          wt φ k * ∏ j, (wt φ j) ^ ((Function.update n k (n k - 1)) j) := by
      intro k hk
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
        ← Finset.mul_prod_erase _ (fun j => (wt φ j) ^ ((Function.update n k (n k - 1)) j))
          (Finset.mem_univ k)]
      have : ∏ j ∈ univ.erase k, (wt φ j) ^ (n j) =
          ∏ j ∈ univ.erase k, (wt φ j) ^ ((Function.update n k (n k - 1)) j) :=
        Finset.prod_congr rfl fun j hj => by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [this, Function.update_self]
      obtain ⟨t, ht⟩ : ∃ t, n k = t + 1 := ⟨n k - 1, by omega⟩
      rw [ht, Nat.add_sub_cancel, pow_succ]
      ring
    -- group by the class of `x0`
    have hgroup : ∀ g : K → ℕ, ∑ x0 : X, g (φ x0) = ∑ k, wt φ k * g k := by
      intro g
      rw [← Finset.sum_fiberwise univ φ (fun x0 => g (φ x0))]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_congr rfl (fun x0 hx0 => by rw [(Finset.mem_filter.1 hx0).2] : ∀ x0 ∈
        univ.filter (fun x0 => φ x0 = k), g (φ x0) = g k)]
      simp [wt]
    rw [hcount]
    have hg := hgroup (fun k : K => if 1 ≤ n k then
          (univ.filter fun x' : Fin m → X =>
            prof φ x' = Function.update n k (n k - 1)).card else 0)
    rw [hg, Finset.sum_mul]
    have hterm : ∀ k : K, wt φ k * (if 1 ≤ n k then
          (univ.filter fun x' : Fin m → X =>
            prof φ x' = Function.update n k (n k - 1)).card else 0) * ∏ j, (n j).factorial =
        n k * (m.factorial * ∏ j, (wt φ j) ^ (n j)) := by
      intro k
      by_cases hk : 1 ≤ n k
      · simp only [hk, if_true]
        have := ih _ (hsum k hk)
        rw [hprodf k hk]
        have e2 := hprodw k hk
        calc wt φ k * (univ.filter fun x' : Fin m → X =>
              prof φ x' = Function.update n k (n k - 1)).card *
              (n k * ∏ j, ((Function.update n k (n k - 1)) j).factorial)
            = wt φ k * n k * ((univ.filter fun x' : Fin m → X =>
              prof φ x' = Function.update n k (n k - 1)).card *
              ∏ j, ((Function.update n k (n k - 1)) j).factorial) := by ring
          _ = wt φ k * n k * (m.factorial *
              ∏ j, (wt φ j) ^ ((Function.update n k (n k - 1)) j)) := by rw [this]
          _ = n k * (m.factorial * (wt φ k * ∏ j, (wt φ j) ^ ((Function.update n k (n k - 1)) j))) := by ring
          _ = _ := by rw [← e2]
      · have : n k = 0 := by omega
        simp [hk, this]
    rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.sum_mul, hn]
    rw [Nat.factorial_succ]
    ring

end Fibre

/-! ## Part B: the marginal-cost (Lagrange) argument for the minimal profiles -/

section Cost

/-- Twice the cost of `n` rows in a class of weight `wk` (`wk = 1`: fixed class, cost `n²`;
`wk = 2`: non-fixed class, cost `C(n,2)`). -/
def c2 (wk n : ℕ) : ℤ := if wk = 1 then 2 * (n : ℤ) ^ 2 else (n : ℤ) * ((n : ℤ) - 1)

/-- The allowed occupancies (minimisers of cost minus a line of slope `t = 2b + ε`). -/
def Al (t b ε wk n : ℕ) : Prop :=
  if wk = 1 then (n = b ∨ (ε = 1 ∧ n = b + 1)) else (n = t ∨ n = t + 1)

/-- The slack of `n` above the supporting line. -/
def sl (t b ε wk n : ℕ) : ℤ :=
  if wk = 1 then 2 * ((n : ℤ) - b) * ((n : ℤ) - b - ε) else ((n : ℤ) - t) * ((n : ℤ) - t - 1)

lemma slack_eq {t b ε wk : ℕ} (ht : t = 2 * b + ε) (r : ℕ) (hr : Al t b ε wk r) (n : ℕ) :
    c2 wk n - c2 wk r - 2 * (t : ℤ) * ((n : ℤ) - r) = sl t b ε wk n := by
  unfold c2 sl Al at *
  subst ht
  by_cases hw : wk = 1
  · simp only [hw, ite_true] at hr ⊢
    rcases hr with h | ⟨h1, h2⟩
    · subst h; push_cast; ring
    · subst h1; subst h2; push_cast; ring
  · simp only [hw, ite_false] at hr ⊢
    rcases hr with h | h <;> subst h <;> push_cast <;> ring

lemma sl_nonneg {t b ε wk : ℕ} (hε : ε ≤ 1) (n : ℕ) : 0 ≤ sl t b ε wk n := by
  unfold sl
  by_cases hw : wk = 1
  · simp only [hw, ite_true]
    interval_cases ε
    · push_cast; nlinarith [sq_nonneg ((n : ℤ) - b)]
    · push_cast
      rcases le_or_gt (n : ℤ) b with h | h
      · nlinarith
      · nlinarith
  · simp only [hw, ite_false]
    rcases le_or_gt (n : ℤ) t with h | h
    · nlinarith
    · nlinarith

lemma sl_eq_zero_iff {t b ε wk : ℕ} (hε : ε ≤ 1) (n : ℕ) : sl t b ε wk n = 0 ↔ Al t b ε wk n := by
  unfold sl Al
  by_cases hw : wk = 1
  · simp only [hw, ite_true]
    interval_cases ε
    · simp only [Nat.cast_zero, sub_zero, mul_eq_zero, OfNat.ofNat_ne_zero, false_or, or_self,
        sub_eq_zero]
      simp
    · simp only [Nat.cast_one, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
      constructor
      · rintro (h | h)
        · left; omega
        · right; exact ⟨by trivial, by omega⟩
      · rintro (h | ⟨_, h⟩)
        · left; omega
        · right; omega
  · simp only [hw, ite_false, mul_eq_zero, sub_eq_zero]
    constructor
    · rintro (h | h)
      · left; omega
      · right; omega
    · rintro (h | h)
      · left; omega
      · right; omega

variable {K : Type*} [Fintype K]

/-- Total (doubled) cost of a profile. -/
def cost (w : K → ℕ) (n : K → ℕ) : ℤ := ∑ k, c2 (w k) (n k)

/-- Lagrange: against a reference profile with allowed occupancies, with the same number of
rows, every profile costs at least as much, with equality iff it is allowed everywhere. -/
theorem cost_ge {t b ε : ℕ} (hε : ε ≤ 1) (ht : t = 2 * b + ε) (w : K → ℕ) (n nref : K → ℕ)
    (hsum : ∑ k, n k = ∑ k, nref k) (href : ∀ k, Al t b ε (w k) (nref k)) :
    cost w nref ≤ cost w n ∧ (cost w n = cost w nref ↔ ∀ k, Al t b ε (w k) (n k)) := by
  have key : cost w n - cost w nref = ∑ k, sl t b ε (w k) (n k) := by
    have h1 : ∀ k, c2 (w k) (n k) - c2 (w k) (nref k) =
        sl t b ε (w k) (n k) + 2 * (t : ℤ) * ((n k : ℤ) - nref k) := fun k => by
      have := slack_eq ht (nref k) (href k) (n k)
      linarith
    unfold cost
    rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_sub_distrib]
    have : ∑ k, (n k : ℤ) = ∑ k, (nref k : ℤ) := by exact_mod_cast hsum
    rw [this]; ring
  have hnn : 0 ≤ ∑ k, sl t b ε (w k) (n k) := Finset.sum_nonneg fun k _ => sl_nonneg hε _
  refine ⟨by linarith, ?_⟩
  constructor
  · intro h
    have h0 : ∑ k, sl t b ε (w k) (n k) = 0 := by rw [← key, h]; ring
    intro k
    exact (sl_eq_zero_iff hε _).1
      ((Finset.sum_eq_zero_iff_of_nonneg fun k _ => sl_nonneg hε _).1 h0 k (Finset.mem_univ k))
  · intro h
    have h0 : ∑ k, sl t b ε (w k) (n k) = 0 :=
      Finset.sum_eq_zero fun k _ => (sl_eq_zero_iff hε _).2 (h k)
    linarith

/-- Base occupancy: `b` in a fixed class (weight 1), `t` in a non-fixed one. -/
def base (t b : ℕ) (w : K → ℕ) (k : K) : ℕ := if w k = 1 then b else t

/-- The minimal profiles: base plus one extra row on each class of `S`. -/
def refS [DecidableEq K] (t b : ℕ) (w : K → ℕ) (S : Finset K) (k : K) : ℕ :=
  base t b w k + if k ∈ S then 1 else 0

/-- Where an extra row is allowed: non-fixed classes, and fixed ones too when `ε = 1`. -/
def Ek [DecidableEq K] (ε : ℕ) (w : K → ℕ) : Finset K := univ.filter fun k => w k = 2 ∨ ε = 1

variable [DecidableEq K] {t b ε : ℕ} {w : K → ℕ}

lemma refS_Al (hw : ∀ k, w k = 1 ∨ w k = 2) {S : Finset K} (hS : S ⊆ Ek ε w) (k : K) :
    Al t b ε (w k) (refS t b w S k) := by
  unfold Al refS base
  by_cases h1 : w k = 1
  · simp only [h1, ite_true]
    by_cases hk : k ∈ S
    · have := hS hk
      simp only [Ek, Finset.mem_filter, Finset.mem_univ, true_and, h1] at this
      right; exact ⟨this.resolve_left (by omega), by simp [hk]⟩
    · left; simp [hk]
  · simp only [h1, ite_false]
    by_cases hk : k ∈ S
    · right; simp [hk]
    · left; simp [hk]

lemma exists_S (hw : ∀ k, w k = 1 ∨ w k = 2) (n : K → ℕ) (h : ∀ k, Al t b ε (w k) (n k)) :
    ∃ S ⊆ Ek ε w, n = refS t b w S := by
  refine ⟨Finset.univ.filter fun k => n k = base t b w k + 1, ?_, ?_⟩
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    simp only [Ek, Finset.mem_filter, Finset.mem_univ, true_and]
    have := h k
    unfold Al at this
    unfold base at hk
    by_cases h1 : w k = 1
    · simp only [h1, ite_true] at this hk
      right
      rcases this with h2 | ⟨h2, _⟩
      · omega
      · exact h2
    · left; rcases hw k with h2 | h2
      · exact absurd h2 h1
      · exact h2
  · funext k
    have := h k
    have hα : n k = base t b w k ∨ n k = base t b w k + 1 := by
      unfold Al at this
      unfold base
      by_cases h1 : w k = 1
      · simp only [h1, ite_true] at this ⊢
        omega
      · simp only [h1, ite_false] at this ⊢
        omega
    have hb : refS t b w (Finset.univ.filter fun k => n k = base t b w k + 1) k =
        base t b w k + if n k = base t b w k + 1 then 1 else 0 := by
      unfold refS; simp
    rw [hb]
    by_cases hc : n k = base t b w k + 1
    · rw [if_pos hc]; omega
    · rw [if_neg hc]; omega

lemma sum_refS (S : Finset K) : ∑ k, refS t b w S k = ∑ k, base t b w k + S.card := by
  unfold refS
  rw [Finset.sum_add_distrib]
  simp

lemma refS_inj {S S' : Finset K} (h : refS t b w S = refS t b w S') : S = S' := by
  ext k
  have := congrFun h k
  unfold refS at this
  by_cases h1 : k ∈ S <;> by_cases h2 : k ∈ S' <;> simp_all

lemma prod_factorial_refS (S : Finset K) :
    ∏ k, (refS t b w S k).factorial =
      (∏ k, (base t b w k).factorial) * ∏ k ∈ S, (base t b w k + 1) := by
  have h : ∀ k, (refS t b w S k).factorial =
      (base t b w k).factorial * (if k ∈ S then base t b w k + 1 else 1) := by
    intro k; unfold refS
    by_cases hk : k ∈ S
    · simp [hk, Nat.factorial_succ, mul_comm]
    · simp [hk]
  rw [Finset.prod_congr rfl fun k _ => h k, Finset.prod_mul_distrib, Finset.prod_ite_mem,
    Finset.univ_inter]

lemma prod_pow_refS (S : Finset K) :
    ∏ k, (w k) ^ (refS t b w S k) = (∏ k, (w k) ^ (base t b w k)) * ∏ k ∈ S, w k := by
  have h : ∀ k, (w k) ^ (refS t b w S k) =
      (w k) ^ (base t b w k) * (if k ∈ S then w k else 1) := by
    intro k; unfold refS
    by_cases hk : k ∈ S
    · simp [hk, pow_succ]
    · simp [hk]
  rw [Finset.prod_congr rfl fun k _ => h k, Finset.prod_mul_distrib, Finset.prod_ite_mem,
    Finset.univ_inter]

end Cost

section Total

variable {X K : Type*} [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K] (φ : X → K)

lemma prof_sum {m : ℕ} (x : Fin m → X) : ∑ k, prof φ x k = m := by
  have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin m)))
    (t := (Finset.univ : Finset K)) (f := fun i => φ (x i)) (fun i _ => Finset.mem_univ _)
  simpa [prof] using this.symm

/-- The set of vectors reaching the minimum cost is the disjoint union, over the minimal
profiles `refS S` (`S ⊆ E`, `|S| = e`), of the sets of vectors with that exact profile. -/
theorem count_min_set {t b ε : ℕ} (hw : ∀ k, wt φ k = 1 ∨ wt φ k = 2) (hε : ε ≤ 1)
    (ht : t = 2 * b + ε) {m e : ℕ} (hme : ∑ k, base t b (wt φ) k + e = m)
    (nρ : K → ℕ) (hρsum : ∑ k, nρ k = m) (hρ : ∀ k, Al t b ε (wt φ k) (nρ k)) :
    (univ.filter fun x : Fin m → X => cost (wt φ) (prof φ x) = cost (wt φ) nρ).card =
      ∑ S ∈ (Ek ε (wt φ)).powersetCard e,
        (univ.filter fun x : Fin m → X => prof φ x = refS t b (wt φ) S).card := by
  have hset : (univ.filter fun x : Fin m → X => cost (wt φ) (prof φ x) = cost (wt φ) nρ) =
      ((Ek ε (wt φ)).powersetCard e).biUnion
        (fun S => univ.filter fun x : Fin m → X => prof φ x = refS t b (wt φ) S) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_powersetCard]
    have hcg := cost_ge hε ht (wt φ) (prof φ x) nρ ((prof_sum φ x).trans hρsum.symm) hρ
    constructor
    · intro h
      obtain ⟨S, hS, hxS⟩ := exists_S hw _ (hcg.2.1 h)
      refine ⟨S, ⟨hS, ?_⟩, hxS⟩
      have h1 := prof_sum φ x
      rw [hxS, sum_refS] at h1
      omega
    · rintro ⟨S, ⟨hS, _⟩, hxS⟩
      exact hcg.2.2 (fun k => by rw [hxS]; exact refS_Al hw hS k)
  rw [hset, Finset.card_biUnion]
  intro S _ S' _ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
  exact hne (refS_inj (hx.symm.trans hx'))

/-- Fixed (weight 1) and non-fixed (weight 2) classes partition `K`. -/
lemma card_split (hw : ∀ k, wt φ k = 1 ∨ wt φ k = 2) {a f : ℕ}
    (ha : (univ.filter fun k => wt φ k = 2).card = a)
    (hf : (univ.filter fun k => wt φ k = 1).card = f) : Fintype.card K = f + a := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset K))
    (fun k => wt φ k = 1)
  have hne : (univ.filter fun k => ¬ wt φ k = 1) = univ.filter fun k => wt φ k = 2 := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h1; exact (hw k).resolve_left h1
    · intro h2; omega
  rw [hne, ha, hf] at h
  simpa using h.symm

lemma sum_base {t b : ℕ} (hw : ∀ k, wt φ k = 1 ∨ wt φ k = 2) {a f : ℕ}
    (ha : (univ.filter fun k => wt φ k = 2).card = a)
    (hf : (univ.filter fun k => wt φ k = 1).card = f) :
    ∑ k, base t b (wt φ) k = b * f + t * a := by
  have hne : (univ.filter fun k => ¬ wt φ k = 1) = univ.filter fun k => wt φ k = 2 := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h1; exact (hw k).resolve_left h1
    · intro h2; omega
  unfold base
  rw [Finset.sum_ite, hne]
  simp [ha, hf, mul_comm]

lemma prod_base_fact {t b : ℕ} (hw : ∀ k, wt φ k = 1 ∨ wt φ k = 2) {a f : ℕ}
    (ha : (univ.filter fun k => wt φ k = 2).card = a)
    (hf : (univ.filter fun k => wt φ k = 1).card = f) :
    ∏ k, (base t b (wt φ) k).factorial = (b.factorial) ^ f * (t.factorial) ^ a := by
  have hne : (univ.filter fun k => ¬ wt φ k = 1) = univ.filter fun k => wt φ k = 2 := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h1; exact (hw k).resolve_left h1
    · intro h2; omega
  have : ∀ k, (base t b (wt φ) k).factorial =
      if wt φ k = 1 then b.factorial else t.factorial := fun k => by unfold base; split_ifs <;> rfl
  rw [Finset.prod_congr rfl fun k _ => this k, Finset.prod_ite, hne]
  simp [ha, hf]

lemma prod_w_base {t b : ℕ} (hw : ∀ k, wt φ k = 1 ∨ wt φ k = 2) {a : ℕ}
    (ha : (univ.filter fun k => wt φ k = 2).card = a) :
    ∏ k, (wt φ k) ^ (base t b (wt φ) k) = 2 ^ (t * a) := by
  have : ∀ k, (wt φ k) ^ (base t b (wt φ) k) = if wt φ k = 1 then 1 else 2 ^ t := fun k => by
    unfold base
    by_cases h1 : wt φ k = 1
    · simp [h1]
    · have := (hw k).resolve_left h1
      simp [h1, this]
  rw [Finset.prod_congr rfl fun k _ => this k, Finset.prod_ite]
  have hne : (univ.filter fun k => ¬ wt φ k = 1) = univ.filter fun k => wt φ k = 2 := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h1; exact (hw k).resolve_left h1
    · intro h2; omega
  rw [hne, Finset.prod_const_one, Finset.prod_const, ha, one_mul, pow_mul]

/-- Per-profile identity: `count(refS S) · ∏ base! · ∏_S (base+1) = m! · ∏ w^base · ∏_S w`. -/
lemma count_refS {t b : ℕ} {m : ℕ} (S : Finset K)
    (hm : ∑ k, refS t b (wt φ) S k = m) :
    (univ.filter fun x : Fin m → X => prof φ x = refS t b (wt φ) S).card *
      ((∏ k, (base t b (wt φ) k).factorial) * ∏ k ∈ S, (base t b (wt φ) k + 1)) =
    m.factorial * ((∏ k, (wt φ k) ^ (base t b (wt φ) k)) * ∏ k ∈ S, wt φ k) := by
  have := fibre_count φ m (refS t b (wt φ) S) hm
  rwa [prod_factorial_refS, prod_pow_refS] at this

/-- **Closed count, case `v ≤ a`.** -/
theorem total_case1 {u a f v m : ℕ} (hw : ∀ k, wt φ k = 1 ∨ wt φ k = 2)
    (ha : (univ.filter fun k => wt φ k = 2).card = a)
    (hf : (univ.filter fun k => wt φ k = 1).card = f) (hv : v ≤ a)
    (hm : u * f + 2 * u * a + v = m)
    (nρ : K → ℕ) (hρsum : ∑ k, nρ k = m) (hρ : ∀ k, Al (2 * u) u 0 (wt φ k) (nρ k)) :
    (univ.filter fun x : Fin m → X =>
        cost (wt φ) (prof φ x) = cost (wt φ) nρ).card *
      ((u.factorial) ^ f * ((2 * u).factorial) ^ a * (2 * u + 1) ^ v) =
    m.factorial * 2 ^ (2 * u * a + v) * a.choose v := by
  have hsb := sum_base φ (t := 2 * u) (b := u) hw ha hf
  rw [count_min_set φ hw (Nat.zero_le 1) (by ring : 2 * u = 2 * u + 0) (e := v)
    (by rw [hsb]; omega) nρ hρsum hρ, Finset.sum_mul]
  have hE : Ek 0 (wt φ) = univ.filter fun k => wt φ k = 2 := by
    ext k; simp [Ek]
  have hterm : ∀ S ∈ (Ek 0 (wt φ)).powersetCard v,
      (univ.filter fun x : Fin m → X => prof φ x = refS (2 * u) u (wt φ) S).card *
        ((u.factorial) ^ f * ((2 * u).factorial) ^ a * (2 * u + 1) ^ v) =
      m.factorial * 2 ^ (2 * u * a + v) := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    have hSE := hS.1
    have hcard := hS.2
    have hsum : ∑ k, refS (2 * u) u (wt φ) S k = m := by
      rw [sum_refS, hsb, hcard]; omega
    have := count_refS φ (t := 2 * u) (b := u) S hsum
    rw [prod_base_fact φ hw ha hf, prod_w_base φ (t := 2 * u) (b := u) hw ha] at this
    have h1 : ∏ k ∈ S, (base (2 * u) u (wt φ) k + 1) = (2 * u + 1) ^ v := by
      rw [Finset.prod_congr rfl (g := fun _ => 2 * u + 1), Finset.prod_const, hcard]
      intro k hk
      have := hSE hk
      rw [hE] at this
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      unfold base; simp [this]
    have h2 : ∏ k ∈ S, wt φ k = 2 ^ v := by
      rw [Finset.prod_congr rfl (g := fun _ => 2), Finset.prod_const, hcard]
      intro k hk
      have := hSE hk
      rw [hE] at this
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    rw [h1, h2] at this
    calc _ = (univ.filter fun x : Fin m → X => prof φ x = refS (2 * u) u (wt φ) S).card *
          (((u.factorial) ^ f * ((2 * u).factorial) ^ a) * (2 * u + 1) ^ v) := by ring
      _ = m.factorial * (2 ^ (2 * u * a) * 2 ^ v) := this
      _ = _ := by ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard, hE, ha]
  simp only [smul_eq_mul]
  ring

/-- **Closed count, case `v > a`** (`e = v - a` extra rows, any classes). -/
theorem total_case2 {u a f e m : ℕ} (hw : ∀ k, wt φ k = 1 ∨ wt φ k = 2)
    (ha : (univ.filter fun k => wt φ k = 2).card = a)
    (hf : (univ.filter fun k => wt φ k = 1).card = f)
    (hm : u * f + (2 * u + 1) * a + e = m)
    (nρ : K → ℕ) (hρsum : ∑ k, nρ k = m) (hρ : ∀ k, Al (2 * u + 1) u 1 (wt φ k) (nρ k)) :
    (univ.filter fun x : Fin m → X =>
        cost (wt φ) (prof φ x) = cost (wt φ) nρ).card *
      ((u.factorial) ^ f * ((2 * u + 1).factorial) ^ a * (u + 1) ^ e) =
    m.factorial * 2 ^ ((2 * u + 1) * a) * (a + f).choose e := by
  have hsb := sum_base φ (t := 2 * u + 1) (b := u) hw ha hf
  rw [count_min_set φ hw le_rfl (by ring : 2 * u + 1 = 2 * u + 1) (e := e)
    (by rw [hsb]; omega) nρ hρsum hρ, Finset.sum_mul]
  have hE : Ek 1 (wt φ) = univ := by
    ext k; simp [Ek]
  have hterm : ∀ S ∈ (Ek 1 (wt φ)).powersetCard e,
      (univ.filter fun x : Fin m → X => prof φ x = refS (2 * u + 1) u (wt φ) S).card *
        ((u.factorial) ^ f * ((2 * u + 1).factorial) ^ a * (u + 1) ^ e) =
      m.factorial * 2 ^ ((2 * u + 1) * a) := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    have hcard := hS.2
    have hsum : ∑ k, refS (2 * u + 1) u (wt φ) S k = m := by
      rw [sum_refS, hsb, hcard]; omega
    have := count_refS φ (t := 2 * u + 1) (b := u) S hsum
    rw [prod_base_fact φ hw ha hf, prod_w_base φ (t := 2 * u + 1) (b := u) hw ha] at this
    have h1 : ∏ k ∈ S, (base (2 * u + 1) u (wt φ) k + 1) = (u + 1) ^ e * ∏ k ∈ S, wt φ k := by
      rw [← hcard, ← Finset.prod_const, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      unfold base
      rcases hw k with h | h <;> simp [h] <;> ring
    have hpos : 0 < ∏ k ∈ S, wt φ k :=
      Finset.prod_pos fun k _ => by rcases hw k with h | h <;> omega
    rw [h1] at this
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    calc _ = (univ.filter fun x : Fin m → X => prof φ x = refS (2 * u + 1) u (wt φ) S).card *
          (((u.factorial) ^ f * ((2 * u + 1).factorial) ^ a) *
            ((u + 1) ^ e * ∏ k ∈ S, wt φ k)) := by ring
      _ = m.factorial * (2 ^ ((2 * u + 1) * a) * ∏ k ∈ S, wt φ k) := this
      _ = _ := by ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard, hE,
    Finset.card_univ, card_split φ hw ha hf]
  simp only [smul_eq_mul]
  rw [add_comm f a]
  ring

end Total

/-! ## Part C: the folded classes of an abelian group and the bridge to `N_q` -/

section Fold

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- The folded classes `{g, -g}` as a type. -/
abbrev Cls (G : Type*) [AddCommGroup G] [DecidableEq G] [Fintype G] : Type _ :=
  {s : Finset G // s ∈ (Finset.univ : Finset G).image (fun g => ({g, -g} : Finset G))}

/-- The class of `g`. -/
def cls (g : G) : Cls G := ⟨{g, -g}, Finset.mem_image_of_mem _ (Finset.mem_univ g)⟩

lemma cls_eq_iff (g h : G) : cls h = cls g ↔ (h = g ∨ h = -g) := by
  unfold cls
  rw [Subtype.mk.injEq]
  constructor
  · intro e
    have : h ∈ ({g, -g} : Finset G) := by rw [← e]; simp
    simpa using this
  · rintro (rfl | rfl)
    · rfl
    · rw [neg_neg, Finset.pair_comm]

lemma cls_surj (k : Cls G) : ∃ g, cls g = k := by
  obtain ⟨s, hs⟩ := k
  obtain ⟨g, _, hg⟩ := Finset.mem_image.1 hs
  exact ⟨g, Subtype.ext hg⟩

lemma wt_cls (g : G) : wt (cls (G := G)) (cls g) = if 2 • g = 0 then 1 else 2 := by
  unfold wt
  have h1 : (univ.filter fun h : G => cls h = cls g) = {g, -g} := by
    ext h; simp [cls_eq_iff]
  rw [h1]
  by_cases h : 2 • g = 0
  · have : -g = g := (fixed_iff g).1 h
    simp [h, this]
  · have hne : g ≠ -g := fun e => h ((fixed_iff g).2 e.symm)
    rw [if_neg h, Finset.card_pair hne]

lemma wt_cases (k : Cls G) : wt (cls (G := G)) k = 1 ∨ wt (cls (G := G)) k = 2 := by
  obtain ⟨g, rfl⟩ := cls_surj k
  rw [wt_cls]
  split_ifs <;> simp

lemma sum_cls_group (H : Cls G → ℤ) :
    ∑ g : G, H (cls g) = ∑ k, (wt (cls (G := G)) k : ℤ) * H k := by
  rw [← Finset.sum_fiberwise univ (cls (G := G)) (fun g => H (cls g))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_congr rfl (fun g hg => by rw [(Finset.mem_filter.1 hg).2] : ∀ g ∈
    univ.filter (fun g => cls g = k), H (cls g) = H k)]
  simp [wt]

lemma countP_ofFn' {m : ℕ} (x : Fin m → G) (p : G → Bool) :
    (List.ofFn x).countP p = (univ.filter fun i => p (x i) = true).card := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.countP_cons, ih (fun i => x i.succ), Fin.card_filter_univ_succ]
    by_cases h : p (x 0) = true <;> simp [h]

lemma occ_ofFn {m : ℕ} (x : Fin m → G) (g : G) :
    occ (List.ofFn x) g = prof (cls (G := G)) x (cls g) := by
  unfold occ prof
  rw [countP_ofFn']
  congr 1
  ext i
  simp [cls_eq_iff]

/-- The bridge: the doubled cost of the folded profile is `2 N_q`. -/
theorem cost_eq_two_Nq {m : ℕ} (x : Fin m → G) :
    cost (wt (cls (G := G))) (prof (cls (G := G)) x) = 2 * (Nq (List.ofFn x) : ℤ) := by
  have h := Nq_profile_sum (List.ofFn x)
  let H : Cls G → ℤ := fun k => if wt (cls (G := G)) k = 1 then
    4 * (prof (cls (G := G)) x k : ℤ) ^ 2 else
    (prof (cls (G := G)) x k : ℤ) * ((prof (cls (G := G)) x k : ℤ) - 1)
  have h1 : ∀ g : G, (if 2 • g = 0 then 4 * (occ (List.ofFn x) g : ℤ) ^ 2
      else (occ (List.ofFn x) g : ℤ) * ((occ (List.ofFn x) g : ℤ) - 1)) = H (cls g) := by
    intro g
    simp only [H, occ_ofFn, wt_cls]
    by_cases hg : 2 • g = 0 <;> simp [hg]
  rw [Finset.sum_congr rfl fun g _ => h1 g, sum_cls_group] at h
  have h2 : ∀ k : Cls G, (wt (cls (G := G)) k : ℤ) * H k =
      2 * c2 (wt (cls (G := G)) k) (prof (cls (G := G)) x k) := by
    intro k
    simp only [H, c2]
    rcases wt_cases k with hk | hk <;> simp [hk] <;> ring
  rw [Finset.sum_congr rfl fun k _ => h2 k, ← Finset.mul_sum] at h
  unfold cost
  linarith

end Fold

/-! ## Part D: `G = ZMod q` -/

section ZMod

/-- `f = 1` for `q` odd, `f = 2` for `q` even: the number of fixed classes. -/
def fq (q : ℕ) : ℕ := if q % 2 = 0 then 2 else 1

/-- `a = (q - f)/2`: the number of non-fixed classes. -/
def aq (q : ℕ) : ℕ := (q - fq q) / 2

variable {q : ℕ} [NeZero q]

lemma two_smul_eq_zero_iff (g : ZMod q) : 2 • g = 0 ↔ (g.val = 0 ∨ 2 * g.val = q) := by
  have hlt := ZMod.val_lt g
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have e : 2 • g = ((2 * g.val : ℕ) : ZMod q) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val, two_nsmul, two_mul]
  rw [e, ZMod.natCast_eq_zero_iff]
  constructor
  · rintro ⟨c, hc⟩
    have hc2 : c < 2 := by
      by_contra hcon
      have : q * 2 ≤ q * c := Nat.mul_le_mul_left q (by omega)
      omega
    interval_cases c
    · left; omega
    · right; omega
  · rintro (h | h)
    · exact ⟨0, by omega⟩
    · exact ⟨1, by omega⟩

lemma fixed_card : (Finset.univ.filter fun g : ZMod q => 2 • g = 0).card = fq q := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  unfold fq
  by_cases h : q % 2 = 0
  · rw [if_pos h]
    have hs : (Finset.univ.filter fun g : ZMod q => 2 • g = 0) =
        {0, ((q / 2 : ℕ) : ZMod q)} := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, two_smul_eq_zero_iff]
      constructor
      · rintro (h1 | h1)
        · left; exact (ZMod.val_eq_zero g).1 h1
        · right
          rw [← ZMod.natCast_zmod_val g]
          congr 1; omega
      · rintro (h1 | h1)
        · left; rw [h1]; simp
        · right
          rw [h1, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
          omega
    rw [hs, Finset.card_pair]
    intro h0
    have := congrArg ZMod.val h0
    rw [ZMod.val_zero, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at this
    omega
  · rw [if_neg h]
    have hs : (Finset.univ.filter fun g : ZMod q => 2 • g = 0) = {0} := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        two_smul_eq_zero_iff]
      constructor
      · rintro (h1 | h1)
        · exact (ZMod.val_eq_zero g).1 h1
        · omega
      · rintro rfl; left; simp
    rw [hs]; simp

/-- Number of fixed classes. -/
lemma card_fixed_classes :
    (Finset.univ.filter fun k : Cls (ZMod q) => wt (cls (G := ZMod q)) k = 1).card = fq q := by
  have h := sum_cls_group (G := ZMod q) (fun k => if wt (cls (G := ZMod q)) k = 1 then 1 else 0)
  have h1 : ∀ g : ZMod q, (if wt (cls (G := ZMod q)) (cls g) = 1 then (1 : ℤ) else 0) =
      if 2 • g = 0 then 1 else 0 := fun g => by
    rw [wt_cls]; by_cases hg : 2 • g = 0 <;> simp [hg]
  rw [Finset.sum_congr rfl fun g _ => h1 g] at h
  have h2 : ∀ k : Cls (ZMod q), (wt (cls (G := ZMod q)) k : ℤ) *
      (if wt (cls (G := ZMod q)) k = 1 then 1 else 0) =
      if wt (cls (G := ZMod q)) k = 1 then 1 else 0 := fun k => by
    by_cases hk : wt (cls (G := ZMod q)) k = 1 <;> simp [hk]
  rw [Finset.sum_congr rfl fun k _ => h2 k] at h
  simp only [Finset.sum_boole] at h
  have h3 := fixed_card (q := q)
  have h' : ((Finset.univ.filter fun k : Cls (ZMod q) =>
      wt (cls (G := ZMod q)) k = 1).card : ℤ) = (fq q : ℤ) := by
    rw [← h]; exact_mod_cast h3
  exact_mod_cast h'

/-- `q = f + 2a`. -/
lemma card_split_q :
    q = fq q + 2 * aq q := by
  have h := sum_cls_group (G := ZMod q) (fun _ => (1 : ℤ))
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one] at h
  have hf := card_fixed_classes (q := q)
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Cls (ZMod q))))
    (fun k => wt (cls (G := ZMod q)) k = 1)
  have hne : (Finset.univ.filter fun k : Cls (ZMod q) => ¬ wt (cls (G := ZMod q)) k = 1) =
      Finset.univ.filter fun k => wt (cls (G := ZMod q)) k = 2 := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h1; exact (wt_cases k).resolve_left h1
    · intro h2; omega
  have hsum : ∑ k : Cls (ZMod q), (wt (cls (G := ZMod q)) k : ℤ) =
      (fq q : ℤ) + 2 * ((Finset.univ.filter fun k : Cls (ZMod q) =>
        wt (cls (G := ZMod q)) k = 2).card : ℤ) := by
    have : ∀ k : Cls (ZMod q), (wt (cls (G := ZMod q)) k : ℤ) =
        (if wt (cls (G := ZMod q)) k = 1 then 1 else 0) +
        2 * (if wt (cls (G := ZMod q)) k = 2 then 1 else 0) := fun k => by
      rcases wt_cases k with hk | hk <;> simp [hk]
    rw [Finset.sum_congr rfl fun k _ => this k, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_boole]
    rw [hf]
  have hq2 : (q : ℤ) = (fq q : ℤ) + 2 * ((Finset.univ.filter fun k : Cls (ZMod q) =>
        wt (cls (G := ZMod q)) k = 2).card : ℤ) := by rw [← hsum, ← h]
  have hq3 : q = fq q + 2 * (Finset.univ.filter fun k : Cls (ZMod q) =>
        wt (cls (G := ZMod q)) k = 2).card := by exact_mod_cast hq2
  unfold aq
  omega

/-- Number of non-fixed classes. -/
lemma card_nf_classes :
    (Finset.univ.filter fun k : Cls (ZMod q) => wt (cls (G := ZMod q)) k = 2).card = aq q := by
  have hf := card_fixed_classes (q := q)
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Cls (ZMod q))))
    (fun k => wt (cls (G := ZMod q)) k = 1)
  have hne : (Finset.univ.filter fun k : Cls (ZMod q) => ¬ wt (cls (G := ZMod q)) k = 1) =
      Finset.univ.filter fun k => wt (cls (G := ZMod q)) k = 2 := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h1; exact (wt_cases k).resolve_left h1
    · intro h2; omega
  have hq := card_split_q (q := q)
  have h := sum_cls_group (G := ZMod q) (fun _ => (1 : ℤ))
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one] at h
  have hsum : ∑ k : Cls (ZMod q), (wt (cls (G := ZMod q)) k : ℤ) =
      (fq q : ℤ) + 2 * ((Finset.univ.filter fun k : Cls (ZMod q) =>
        wt (cls (G := ZMod q)) k = 2).card : ℤ) := by
    have : ∀ k : Cls (ZMod q), (wt (cls (G := ZMod q)) k : ℤ) =
        (if wt (cls (G := ZMod q)) k = 1 then 1 else 0) +
        2 * (if wt (cls (G := ZMod q)) k = 2 then 1 else 0) := fun k => by
      rcases wt_cases k with hk | hk <;> simp [hk]
    rw [Finset.sum_congr rfl fun k _ => this k, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_boole]
    rw [hf]
  have : (q : ℤ) = (fq q : ℤ) + 2 * ((Finset.univ.filter fun k : Cls (ZMod q) =>
        wt (cls (G := ZMod q)) k = 2).card : ℤ) := by rw [← hsum, ← h]
  have : q = fq q + 2 * (Finset.univ.filter fun k : Cls (ZMod q) =>
        wt (cls (G := ZMod q)) k = 2).card := by exact_mod_cast this
  omega

/-- `N(g) = #{i ∈ [1,m] : i ≡ g}`. -/
def Ncnt (q m : ℕ) (g : ZMod q) : ℕ :=
  ((Finset.range m).filter fun i => ((i + 1 : ℕ) : ZMod q) = g).card

lemma Ncnt_eq (m : ℕ) (g : ZMod q) :
    Ncnt q m g = m / q + if g ≠ 0 ∧ g.val ≤ m % q then 1 else 0 := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hlt := ZMod.val_lt g
  have hiff : ∀ i : ℕ, ((i + 1 : ℕ) : ZMod q) = g ↔ i ≡ g.val + (q - 1) [MOD q] := by
    intro i
    have hg : ((g.val : ℕ) : ZMod q) = g := ZMod.natCast_zmod_val g
    have h0 : (((i + 1 : ℕ) : ZMod q) = g) ↔ (((i + 1 : ℕ) : ZMod q) = ((g.val : ℕ) : ZMod q)) := by
      rw [hg]
    rw [h0, ZMod.natCast_eq_natCast_iff]
    constructor
    · intro h
      have h1 := h.add_right (q - 1)
      calc i ≡ i + q [MOD q] := (Nat.add_modEq_right).symm
        _ = i + 1 + (q - 1) := by omega
        _ ≡ g.val + (q - 1) [MOD q] := h1
    · intro h
      have h1 := h.add_right 1
      calc i + 1 ≡ g.val + (q - 1) + 1 [MOD q] := h1
        _ = g.val + q := by omega
        _ ≡ g.val [MOD q] := Nat.add_modEq_right
  unfold Ncnt
  rw [Finset.filter_congr (fun i _ => hiff i), ← Nat.count_eq_card_filter_range,
    Nat.count_modEq_card m hq]
  have hmod := Nat.mod_lt m hq
  congr 1
  by_cases h0 : g = 0
  · have hv : g.val = 0 := by rw [h0]; simp
    have : (g.val + (q - 1)) % q = q - 1 := by
      rw [hv, zero_add]; exact Nat.mod_eq_of_lt (by omega)
    rw [this]
    simp [h0]
    omega
  · have hv : g.val ≠ 0 := fun h => h0 ((ZMod.val_eq_zero g).1 h)
    have : (g.val + (q - 1)) % q = g.val - 1 := by
      rw [show g.val + (q - 1) = (g.val - 1) + q by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [this]
    simp only [h0, ne_eq, not_false_eq_true, true_and]
    by_cases hc : g.val ≤ m % q
    · simp [hc]; omega
    · simp [hc]; omega

lemma o_rho_Ncnt (m : ℕ) (g : ZMod q) :
    o (rho q m) g = (Ncnt q m g : ℤ) + (Ncnt q m (-g) : ℤ) := by
  rw [o_rho, Finset.sum_add_distrib, sum_ite_card, sum_ite_card]
  unfold Ncnt
  congr 3
  ext i
  simp only [Finset.mem_filter, neg_eq_iff_eq_neg]

lemma occ_rho (m : ℕ) (g : ZMod q) :
    occ (rho q m) g = if 2 • g = 0 then Ncnt q m g else Ncnt q m g + Ncnt q m (-g) := by
  have h1 := o_rho_Ncnt m g
  have h2 := o_eq_occ (rho q m) g
  by_cases h : 2 • g = 0
  · have hn : -g = g := (fixed_iff g).1 h
    rw [if_pos h]
    rw [if_pos h, h1, hn] at h2
    omega
  · rw [if_neg h]
    rw [if_neg h, h1] at h2
    omega

/-- `ρ` as a vector `(1, 2, …, m)` (order is irrelevant for occupancies). -/
def rhoV (q m : ℕ) : Fin m → ZMod q := fun i => ((i.val + 1 : ℕ) : ZMod q)

lemma ofFn_val_map {α : Type*} (f : ℕ → α) (m : ℕ) :
    List.ofFn (fun i : Fin m => f i.val) = (List.range m).map f := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ', List.range_succ, List.map_append]
    simp only [Fin.val_castSucc, Fin.val_last, List.concat_eq_append, List.map_cons,
      List.map_nil]
    rw [ih]

lemma occ_rhoV (m : ℕ) (g : ZMod q) : occ (List.ofFn (rhoV q m)) g = occ (rho q m) g := by
  unfold rhoV
  rw [ofFn_val_map (fun i => ((i + 1 : ℕ) : ZMod q)) m]
  unfold occ rho
  rw [List.map_reverse, List.countP_reverse]

lemma val_neg' (g : ZMod q) : (-g).val = if g.val = 0 then 0 else q - g.val := by
  by_cases h : g = 0
  · subst h; simp
  · haveI : NeZero g := ⟨h⟩
    rw [ZMod.val_neg_of_ne_zero]
    have : g.val ≠ 0 := fun h' => h ((ZMod.val_eq_zero g).1 h')
    rw [if_neg this]

lemma fq_cases (q : ℕ) : fq q = 1 ∨ fq q = 2 := by unfold fq; split_ifs <;> simp

/-- The occupancies of `ρ` in case `v ≤ a`. -/
lemma rho_Al_case1 (m : ℕ) (hv : m % q ≤ aq q) (g : ZMod q) :
    Al (2 * (m / q)) (m / q) 0 (if 2 • g = 0 then 1 else 2) (occ (rho q m) g) := by
  have hq := card_split_q (q := q)
  have hf := fq_cases q
  have hlt := ZMod.val_lt g
  have hmod := Nat.mod_lt m (Nat.pos_of_ne_zero (NeZero.ne q))
  have hD := two_smul_eq_zero_iff g
  have hg0 : (g = 0) ↔ g.val = 0 := (ZMod.val_eq_zero g).symm
  rw [occ_rho, Ncnt_eq, Ncnt_eq]
  unfold Al
  by_cases hg : 2 • g = 0
  · rw [if_pos hg, if_pos hg, if_pos rfl]
    have hc := hD.1 hg
    simp only [ne_eq, hg0]
    split_ifs <;> omega
  · rw [if_neg hg, if_neg hg, if_neg (by omega)]
    have hc := mt hD.2 hg
    simp only [ne_eq, hg0, neg_eq_zero, val_neg']
    split_ifs <;> omega

/-- The occupancies of `ρ` in case `v > a`. -/
lemma rho_Al_case2 (m : ℕ) (hv : aq q < m % q) (g : ZMod q) :
    Al (2 * (m / q) + 1) (m / q) 1 (if 2 • g = 0 then 1 else 2) (occ (rho q m) g) := by
  have hq := card_split_q (q := q)
  have hf := fq_cases q
  have hlt := ZMod.val_lt g
  have hmod := Nat.mod_lt m (Nat.pos_of_ne_zero (NeZero.ne q))
  have hD := two_smul_eq_zero_iff g
  have hg0 : (g = 0) ↔ g.val = 0 := (ZMod.val_eq_zero g).symm
  rw [occ_rho, Ncnt_eq, Ncnt_eq]
  unfold Al
  by_cases hg : 2 • g = 0
  · rw [if_pos hg, if_pos hg, if_pos rfl]
    have hc := hD.1 hg
    simp only [ne_eq, hg0]
    split_ifs <;> first | omega | simp
  · rw [if_neg hg, if_neg hg, if_neg (by omega)]
    have hc := mt hD.2 hg
    simp only [ne_eq, hg0, neg_eq_zero, val_neg']
    split_ifs <;> omega

/-! ### Stage 2 and the assembly -/

lemma Nq_rho_eq (m : ℕ) : Nq (rho q m) = Nq (List.ofFn (rhoV q m)) := by
  have h1 := Nq_profile_sum (rho q m)
  have h2 := Nq_profile_sum (List.ofFn (rhoV q m))
  simp only [occ_rhoV] at h2
  have : (4 : ℤ) * (Nq (rho q m) : ℤ) = 4 * (Nq (List.ofFn (rhoV q m)) : ℤ) := by rw [h1, h2]
  exact_mod_cast (by omega : (Nq (rho q m) : ℤ) = Nq (List.ofFn (rhoV q m)))

/-- The number of survivors: `#{x ∈ (ℤ/q)^m : N_q(x) = r_q}`, `r_q = N_q(ρ)`. -/
def surv (m q : ℕ) [NeZero q] : ℕ :=
  (Finset.univ.filter fun x : Fin m → ZMod q => Nq (List.ofFn x) = Nq (rho q m)).card

lemma Nq_eq_iff_cost (m : ℕ) (x : Fin m → ZMod q) :
    Nq (List.ofFn x) = Nq (rho q m) ↔
      cost (wt (cls (G := ZMod q))) (prof (cls (G := ZMod q)) x) =
        cost (wt (cls (G := ZMod q))) (prof (cls (G := ZMod q)) (rhoV q m)) := by
  rw [cost_eq_two_Nq, cost_eq_two_Nq, Nq_rho_eq]
  omega

/-- **Stage 2, case `v ≤ a`** (`m = u q + v`). `N_q(x) = r_q` iff every fixed class carries `u`
rows and every non-fixed class `2u` or `2u + 1` (and then exactly `v` of them carry `2u + 1`, by
the total `m`). -/
theorem min_profile_case1 (m : ℕ) (hv : m % q ≤ aq q) (x : Fin m → ZMod q) :
    Nq (List.ofFn x) = Nq (rho q m) ↔
      ∀ g : ZMod q, Al (2 * (m / q)) (m / q) 0 (if 2 • g = 0 then 1 else 2)
        (occ (List.ofFn x) g) := by
  have hρ : ∀ k : Cls (ZMod q), Al (2 * (m / q)) (m / q) 0 (wt (cls (G := ZMod q)) k)
      (prof (cls (G := ZMod q)) (rhoV q m) k) := by
    intro k
    obtain ⟨g, rfl⟩ := cls_surj k
    rw [wt_cls, ← occ_ofFn, occ_rhoV]
    exact rho_Al_case1 m hv g
  have hcg := cost_ge (t := 2 * (m / q)) (b := m / q) (ε := 0) (Nat.zero_le 1) (by ring)
    (wt (cls (G := ZMod q))) (prof (cls (G := ZMod q)) x) (prof (cls (G := ZMod q)) (rhoV q m))
    ((prof_sum _ x).trans (prof_sum _ _).symm) hρ
  rw [Nq_eq_iff_cost, hcg.2]
  constructor
  · intro h g
    have := h (cls g)
    rwa [wt_cls, ← occ_ofFn] at this
  · intro h k
    obtain ⟨g, rfl⟩ := cls_surj k
    rw [wt_cls, ← occ_ofFn]
    exact h g

/-- **Stage 2, case `v > a`.** `N_q(x) = r_q` iff every fixed class carries `u` or `u + 1` rows
and every non-fixed class `2u + 1` or `2u + 2`. -/
theorem min_profile_case2 (m : ℕ) (hv : aq q < m % q) (x : Fin m → ZMod q) :
    Nq (List.ofFn x) = Nq (rho q m) ↔
      ∀ g : ZMod q, Al (2 * (m / q) + 1) (m / q) 1 (if 2 • g = 0 then 1 else 2)
        (occ (List.ofFn x) g) := by
  have hρ : ∀ k : Cls (ZMod q), Al (2 * (m / q) + 1) (m / q) 1 (wt (cls (G := ZMod q)) k)
      (prof (cls (G := ZMod q)) (rhoV q m) k) := by
    intro k
    obtain ⟨g, rfl⟩ := cls_surj k
    rw [wt_cls, ← occ_ofFn, occ_rhoV]
    exact rho_Al_case2 m hv g
  have hcg := cost_ge (t := 2 * (m / q) + 1) (b := m / q) (ε := 1) le_rfl (by ring)
    (wt (cls (G := ZMod q))) (prof (cls (G := ZMod q)) x) (prof (cls (G := ZMod q)) (rhoV q m))
    ((prof_sum _ x).trans (prof_sum _ _).symm) hρ
  rw [Nq_eq_iff_cost, hcg.2]
  constructor
  · intro h g
    have := h (cls g)
    rwa [wt_cls, ← occ_ofFn] at this
  · intro h k
    obtain ⟨g, rfl⟩ := cls_surj k
    rw [wt_cls, ← occ_ofFn]
    exact h g

lemma surv_eq (m : ℕ) : surv m q =
    (Finset.univ.filter fun x : Fin m → ZMod q =>
      cost (wt (cls (G := ZMod q))) (prof (cls (G := ZMod q)) x) =
        cost (wt (cls (G := ZMod q))) (prof (cls (G := ZMod q)) (rhoV q m))).card := by
  unfold surv
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Nq_eq_iff_cost m x

/-- **Theorem 11.1 (`thm:cuenta`), case `v ≤ a`**, multiplied by the denominator:
`S · ((2u+1)!)^v ((2u)!)^(a-v) (u!)^f = m! 2^(2ua+v) C(a,v)`. -/
theorem thm_cuenta_le (m : ℕ) (hv : m % q ≤ aq q) :
    surv m q * (((2 * (m / q) + 1).factorial) ^ (m % q) *
        ((2 * (m / q)).factorial) ^ (aq q - m % q) * ((m / q).factorial) ^ (fq q)) =
      m.factorial * 2 ^ (2 * (m / q) * aq q + m % q) * (aq q).choose (m % q) := by
  have hq := card_split_q (q := q)
  have he : q * (m / q) + m % q = m := Nat.div_add_mod m q
  have hρ : ∀ k : Cls (ZMod q), Al (2 * (m / q)) (m / q) 0 (wt (cls (G := ZMod q)) k)
      (prof (cls (G := ZMod q)) (rhoV q m) k) := by
    intro k
    obtain ⟨g, rfl⟩ := cls_surj k
    rw [wt_cls, ← occ_ofFn, occ_rhoV]
    exact rho_Al_case1 m hv g
  have key := total_case1 (cls (G := ZMod q)) (u := m / q) (a := aq q) (f := fq q) (v := m % q)
    (m := m) wt_cases card_nf_classes card_fixed_classes hv
    (by
      calc m / q * fq q + 2 * (m / q) * aq q + m % q = (m / q) * (fq q + 2 * aq q) + m % q := by ring
        _ = m := by rw [← hq]; linarith)
    (prof (cls (G := ZMod q)) (rhoV q m)) (prof_sum _ _) hρ
  rw [← surv_eq] at key
  obtain ⟨d, hd⟩ : ∃ d, aq q = m % q + d := ⟨aq q - m % q, by omega⟩
  have hd' : aq q - m % q = d := by omega
  rw [hd'] at *
  rw [← key]
  have h2 : (2 * (m / q) + 1).factorial = (2 * (m / q) + 1) * (2 * (m / q)).factorial :=
    Nat.factorial_succ _
  rw [h2, hd, mul_pow, pow_add]
  ring

/-- **Theorem 11.1 (`thm:cuenta`), case `v > a`**, multiplied by the denominator:
`S · ((2u+1)!)^a (u!)^f (u+1)^(v-a) = m! 2^(a(2u+1)) C(a+f, v-a)`. -/
theorem thm_cuenta_gt (m : ℕ) (hv : aq q < m % q) :
    surv m q * (((2 * (m / q) + 1).factorial) ^ (aq q) * ((m / q).factorial) ^ (fq q) *
        (m / q + 1) ^ (m % q - aq q)) =
      m.factorial * 2 ^ (aq q * (2 * (m / q) + 1)) * (aq q + fq q).choose (m % q - aq q) := by
  have hq := card_split_q (q := q)
  have he : q * (m / q) + m % q = m := Nat.div_add_mod m q
  have hρ : ∀ k : Cls (ZMod q), Al (2 * (m / q) + 1) (m / q) 1 (wt (cls (G := ZMod q)) k)
      (prof (cls (G := ZMod q)) (rhoV q m) k) := by
    intro k
    obtain ⟨g, rfl⟩ := cls_surj k
    rw [wt_cls, ← occ_ofFn, occ_rhoV]
    exact rho_Al_case2 m hv g
  have key := total_case2 (cls (G := ZMod q)) (u := m / q) (a := aq q) (f := fq q)
    (e := m % q - aq q) (m := m) wt_cases card_nf_classes card_fixed_classes
    (by
      have : m / q * fq q + (2 * (m / q) + 1) * aq q + (m % q - aq q) =
          (m / q) * (fq q + 2 * aq q) + m % q := by
        zify [hv.le]; ring
      rw [this, ← hq]; linarith)
    (prof (cls (G := ZMod q)) (rhoV q m)) (prof_sum _ _) hρ
  rw [← surv_eq] at key
  rw [mul_comm (aq q) (2 * (m / q) + 1), ← key]
  ring

/-- Sanity check against the exhaustive enumeration of the note: `S_{C_2}(7) = 24`. -/
example : surv 2 7 = 24 := by
  have h := thm_cuenta_le (q := 7) 2 (by decide)
  norm_num [aq, fq, Nat.factorial, Nat.choose] at h
  omega

/-- Sanity check: `S_{C_3}(5) = 72`. -/
example : surv 3 5 = 72 := by
  have h := thm_cuenta_gt (q := 5) 3 (by decide)
  norm_num [aq, fq, Nat.factorial, Nat.choose] at h
  omega

end ZMod

end SurvivorCount
