/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Consecutive quadratic residues: Λ(2, 2) = 9 (Erdős Problem 436, Lehmer–Lehmer 1962)

For a prime `p`, let `r(p)` be the least `n ≥ 1` such that `n` and `n + 1` are both quadratic
residues modulo `p`. Lehmer and Lehmer (1962) showed that `limsup r(p) = 9`: for `p > 10` one of the
pairs `(1, 2)`, `(4, 5)`, `(9, 10)` works, and when `2, 3, 5, 7` are all non-residues no smaller
pair does, which happens for infinitely many primes by Dirichlet's theorem and quadratic
reciprocity. This closes the `sorry` of `erdos_436.variants.two_two` in
google-deepmind/formal-conjectures (definitions copied literally, Apache-2.0).

## Main results

* `Erdos436.r_le_nine`: for every prime p > 10, r(2, 2, p) ≤ 9
* `Erdos436.r_eq_nine`: r(2, 2, p) = 9 for every prime p ≡ 43 (mod 840)
* `Erdos436.erdos_436.variants.two_two`: Λ(2, 2) = 9 (formal-conjectures erdos_436.variants.two_two)

## References

* D. H. Lehmer, E. Lehmer, «On runs of residues», Proc. Amer. Math. Soc. 13 (1962) 102–106.
* google-deepmind/formal-conjectures, FormalConjectures/ErdosProblems/436.lean (Apache-2.0): definiciones y enunciado.
-/

@[expose] public section

open Filter

namespace Erdos436

/-- `IsPowerResidue k p a`: `p ∤ a` and `a ≡ x^k (mod p)` for some `x`. -/
def IsPowerResidue (k p a : ℕ) : Prop :=
  (a : ZMod p) ≠ 0 ∧ ∃ x : ZMod p, x ^ k = a

/-- `r k m p`: the least `r ≥ 1` with `r, …, r + m − 1` all `k`-th power residues mod `p`, or `⊤`. -/
noncomputable def r (k m p : ℕ) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : 1 ≤ n ∧ ∀ i < m, IsPowerResidue k p (n + i)), (n : ℕ∞)

/-- `Λ(k, m) = limsup_{p → ∞} r(k, m, p)` over the primes. -/
noncomputable def runLimsup (k m : ℕ) : ℕ∞ :=
  limsup (r k m) (atTop ⊓ 𝓟 {p | p.Prime})

lemma natCast_ne_zero {p : ℕ} (hlt : 10 < p) {a : ℕ} (h1 : 1 ≤ a) (h10 : a ≤ 10) :
    (a : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have := Nat.le_of_dvd (by omega) h
  omega

lemma isPR_iff {p : ℕ} [Fact p.Prime] {a : ℕ} (ha : (a : ZMod p) ≠ 0) :
    IsPowerResidue 2 p a ↔ legendreSym p (a : ℤ) = 1 := by
  have ha' : ((a : ℤ) : ZMod p) ≠ 0 := by simpa using ha
  rw [legendreSym.eq_one_iff p ha']
  constructor
  · rintro ⟨_, x, hx⟩
    exact ⟨x, by simp only [Int.cast_natCast]; rw [← hx]; ring⟩
  · rintro ⟨x, hx⟩
    exact ⟨ha, x, by simp only [Int.cast_natCast] at hx; rw [hx]; ring⟩

lemma L_mul {p : ℕ} [Fact p.Prime] (a b : ℕ) :
    legendreSym p ((a * b : ℕ) : ℤ) = legendreSym p (a : ℤ) * legendreSym p (b : ℤ) := by
  push_cast
  exact legendreSym.mul p _ _

lemma L_sq {p : ℕ} [Fact p.Prime] (a : ℕ) (ha : (a : ZMod p) ≠ 0) :
    legendreSym p (a : ℤ) * legendreSym p (a : ℤ) = 1 := by
  have ha' : ((a : ℤ) : ZMod p) ≠ 0 := by simpa using ha
  rcases legendreSym.eq_one_or_neg_one p ha' with h | h <;> rw [h] <;> norm_num

lemma r_le {p : ℕ} (n : ℕ) (hn : 1 ≤ n) (h : ∀ i < 2, IsPowerResidue 2 p (n + i)) :
    r 2 2 p ≤ (n : ℕ∞) :=
  iInf₂_le n ⟨hn, h⟩

lemma r_le_nine {p : ℕ} (hp : p.Prime) (hlt : 10 < p) : r 2 2 p ≤ 9 := by
  have := Fact.mk hp
  have nz : ∀ a : ℕ, 1 ≤ a → a ≤ 10 → (a : ZMod p) ≠ 0 := fun a h1 h2 => natCast_ne_zero hlt h1 h2
  have pr : ∀ a : ℕ, 1 ≤ a → a ≤ 10 → (IsPowerResidue 2 p a ↔ legendreSym p (a : ℤ) = 1) :=
    fun a h1 h2 => isPR_iff (nz a h1 h2)
  have L1 : legendreSym p ((1 : ℕ) : ℤ) = 1 := by simp
  have L4 : legendreSym p ((4 : ℕ) : ℤ) = 1 := by
    have := L_mul (p := p) 2 2
    rw [show (2 * 2 : ℕ) = 4 from rfl] at this
    rw [this]; exact L_sq 2 (nz 2 (by norm_num) (by norm_num))
  have L9 : legendreSym p ((9 : ℕ) : ℤ) = 1 := by
    have := L_mul (p := p) 3 3
    rw [show (3 * 3 : ℕ) = 9 from rfl] at this
    rw [this]; exact L_sq 3 (nz 3 (by norm_num) (by norm_num))
  have key : ∀ n : ℕ, 1 ≤ n → n + 1 ≤ 10 →
      legendreSym p (n : ℤ) = 1 → legendreSym p ((n + 1 : ℕ) : ℤ) = 1 → r 2 2 p ≤ (n : ℕ∞) := by
    intro n h1 h2 ha hb
    apply r_le n h1
    intro i hi
    interval_cases i
    · exact (pr n h1 (by omega)).2 ha
    · exact (pr (n + 1) (by omega) h2).2 hb
  by_cases h2 : legendreSym p ((2 : ℕ) : ℤ) = 1
  · have := key 1 le_rfl (by norm_num) L1 h2
    exact this.trans (by norm_num)
  · by_cases h5 : legendreSym p ((5 : ℕ) : ℤ) = 1
    · have := key 4 (by norm_num) (by norm_num) L4 h5
      exact this.trans (by norm_num)
    · have e2 : legendreSym p ((2 : ℕ) : ℤ) = -1 := by
        rcases legendreSym.eq_one_or_neg_one p (a := ((2 : ℕ) : ℤ))
          (by simpa using nz 2 (by norm_num) (by norm_num)) with h | h
        · exact absurd h h2
        · exact h
      have e5 : legendreSym p ((5 : ℕ) : ℤ) = -1 := by
        rcases legendreSym.eq_one_or_neg_one p (a := ((5 : ℕ) : ℤ))
          (by simpa using nz 5 (by norm_num) (by norm_num)) with h | h
        · exact absurd h h5
        · exact h
      have L10 : legendreSym p ((10 : ℕ) : ℤ) = 1 := by
        have := L_mul (p := p) 2 5
        rw [show (2 * 5 : ℕ) = 10 from rfl] at this
        rw [this, e2, e5]; norm_num
      have := key 9 (by norm_num) (by norm_num) L9 L10
      exact this

lemma r_ge_nine {p : ℕ} (hp : p.Prime) (hlt : 10 < p)
    (h2 : ¬ IsSquare (2 : ZMod p)) (h3 : ¬ IsSquare (3 : ZMod p))
    (h5 : ¬ IsSquare (5 : ZMod p)) (h7 : ¬ IsSquare (7 : ZMod p)) : 9 ≤ r 2 2 p := by
  have := Fact.mk hp
  have nz : ∀ a : ℕ, 1 ≤ a → a ≤ 10 → (a : ZMod p) ≠ 0 := fun a h1 h2 => natCast_ne_zero hlt h1 h2
  have nr : ∀ a : ℕ, 1 ≤ a → a ≤ 10 → ¬ IsSquare (a : ZMod p) → ¬ IsPowerResidue 2 p a := by
    intro a h1 h2 hs ⟨_, x, hx⟩
    exact hs ⟨x, by rw [← hx]; ring⟩
  have n2 := nr 2 (by norm_num) (by norm_num) (by exact_mod_cast h2)
  have n3 := nr 3 (by norm_num) (by norm_num) (by exact_mod_cast h3)
  have n5 := nr 5 (by norm_num) (by norm_num) (by exact_mod_cast h5)
  have n7 := nr 7 (by norm_num) (by norm_num) (by exact_mod_cast h7)
  have n8 : ¬ IsPowerResidue 2 p 8 := by
    rw [isPR_iff (nz 8 (by norm_num) (by norm_num))]
    have e2 : legendreSym p ((2 : ℕ) : ℤ) = -1 := by
      rw [legendreSym.eq_neg_one_iff]; simpa using h2
    have := L_mul (p := p) 2 4
    have h4 : legendreSym p ((4 : ℕ) : ℤ) = 1 := by
      have := L_mul (p := p) 2 2
      rw [show (2 * 2 : ℕ) = 4 from rfl] at this
      rw [this]; exact L_sq 2 (nz 2 (by norm_num) (by norm_num))
    rw [show (2 * 4 : ℕ) = 8 from rfl] at this
    rw [this, e2, h4]; norm_num
  refine le_iInf₂ fun n hn => ?_
  obtain ⟨h1, hi⟩ := hn
  have a0 := hi 0 (by norm_num)
  have a1 := hi 1 (by norm_num)
  simp only [add_zero] at a0
  by_contra hlt9
  have : n ≤ 8 := by
    by_contra hc
    exact hlt9 (by exact_mod_cast (by omega : 9 ≤ n))
  interval_cases n
  · exact n2 a1
  · exact n2 a0
  · exact n3 a0
  · exact n5 a1
  · exact n5 a0
  · exact n7 a1
  · exact n7 a0
  · exact n8 a0

lemma nonres_of_mod {p : ℕ} (hp : p.Prime) (hm : p % 840 = 43) :
    ¬ IsSquare (2 : ZMod p) ∧ ¬ IsSquare (3 : ZMod p) ∧ ¬ IsSquare (5 : ZMod p) ∧
      ¬ IsSquare (7 : ZMod p) := by
  have := Fact.mk hp
  have hp2 : p ≠ 2 := by omega
  have h4 : p % 4 = 3 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ZMod.exists_sq_eq_two_iff hp2]; omega
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have key := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three (p := 3) (q := p) (by norm_num) h4
      (by omega)
    have e : ((3 : ℕ) : ZMod p) = 3 := by norm_cast
    have e1 : (p : ZMod 3) = 1 := by
      rw [show (1 : ZMod 3) = ((1 : ℕ) : ZMod 3) by norm_cast, ZMod.natCast_eq_natCast_iff']
      omega
    rw [← e]
    exact key.1 (by rw [e1]; exact ⟨1, by simp⟩)
  · have h35 : ¬ IsSquare (3 : ZMod 5) := by decide
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have key := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p) (by norm_num) hp2
    have e : ((p : ℕ) : ZMod 5) = 3 := by
      rw [show (3 : ZMod 5) = ((3 : ℕ) : ZMod 5) by norm_cast, ZMod.natCast_eq_natCast_iff']
      omega
    have e5 : ((5 : ℕ) : ZMod p) = 5 := by norm_cast
    rw [← e5]
    intro h
    have h' := key.2 h
    rw [e] at h'
    exact h35 h'
  · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have key := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three (p := 7) (q := p) (by norm_num) h4
      (by omega)
    have e : ((7 : ℕ) : ZMod p) = 7 := by norm_cast
    have e1 : (p : ZMod 7) = 1 := by
      rw [show (1 : ZMod 7) = ((1 : ℕ) : ZMod 7) by norm_cast, ZMod.natCast_eq_natCast_iff']
      omega
    rw [← e]
    exact key.1 (by rw [e1]; exact ⟨1, by simp⟩)

lemma r_eq_nine {p : ℕ} (hp : p.Prime) (hm : p % 840 = 43) : r 2 2 p = 9 := by
  have hlt : 10 < p := by omega
  obtain ⟨a, b, c, d⟩ := nonres_of_mod hp hm
  exact le_antisymm (r_le_nine hp hlt) (r_ge_nine hp hlt a b c d)

/-- **Lehmer–Lehmer (1962): `Λ(2, 2) = 9`** (the statement `erdos_436.variants.two_two` of formal-conjectures). -/
theorem erdos_436.variants.two_two : runLimsup 2 2 = 9 := by
  unfold runLimsup
  apply le_antisymm
  · refine limsup_le_of_le (by isBoundedDefault) ?_
    rw [eventually_inf_principal]
    filter_upwards [eventually_gt_atTop 10] with p hp hpp
    exact r_le_nine hpp hp
  · refine le_limsup_of_frequently_le ?_ (by isBoundedDefault)
    rw [frequently_inf_principal, frequently_atTop]
    intro N
    have hu : IsUnit (43 : ZMod 840) := ⟨⟨43, 547, by decide, by decide⟩, rfl⟩
    obtain ⟨q, hq, hqp, hqm⟩ := Nat.forall_exists_prime_gt_and_eq_mod (q := 840) hu N
    refine ⟨q, hq.le, hqp, ?_⟩
    have hm : q % 840 = 43 := by
      rw [show (43 : ZMod 840) = ((43 : ℕ) : ZMod 840) by norm_cast,
        ZMod.natCast_eq_natCast_iff'] at hqm
      simpa using hqm
    rw [r_eq_nine hqp hm]


end Erdos436
