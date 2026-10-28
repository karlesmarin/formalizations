/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# Fibonacci numbers modulo m: periodic zeros and even Pisano periods

For `m ≥ 1` the zeros of `Fₙ mod m` are periodic (`m ∣ Fₙ ↔ d ∣ n` for the least `d > 0` with
`m ∣ F_d`, from `gcd(F_a, F_b) = F_gcd(a,b)`), the sequence `Fₙ mod m` is periodic (the pair
`(Fₙ, Fₙ₊₁) mod m` returns to `(0, 1)`: pigeonhole and the invertibility of the recurrence), and for
`m > 2` every period is even: Cassini's identity `F_{π+1} F_{π−1} − F_π² = (−1)^π` at a period gives
`(−1)^π ≡ 1 (mod m)` (Singerman's determinant argument).

## Main results

* `Pisano.dvd_fib_iff`: m ∣ Fₙ ↔ d ∣ n for some d > 0
* `Pisano.exists_period`: Fₙ mod m is periodic
* `Pisano.even_of_period`: every period is even when m > 2
* `Pisano.fib_mod_periodicity`: the three parts together (Theorem of the Day)

## References

* R. Whitty, Theorem of the Day, «A Theorem on Modular Fibonacci Periodicity» (Binomial/PeriodicFib).
* D. D. Wall, Fibonacci series modulo m, Amer. Math. Monthly 67 (1960), 525–532.
-/

@[expose] public section

namespace Pisano

/-- The pair `(Fₙ, Fₙ₊₁)` in `ZMod m`. -/
def pair (m n : ℕ) : ZMod m × ZMod m := ((Nat.fib n : ZMod m), (Nat.fib (n + 1) : ZMod m))

theorem pair_succ (m n : ℕ) :
    pair m (n + 1) = ((pair m n).2, (pair m n).1 + (pair m n).2) := by
  simp only [pair, Nat.fib_add_two, Nat.cast_add]

theorem pair_zero (m : ℕ) : pair m 0 = (0, 1) := by simp [pair]

/-- Backward invertibility: equal successors have equal predecessors. -/
theorem pair_eq_of_succ_eq {m i j : ℕ} (h : pair m (i + 1) = pair m (j + 1)) :
    pair m i = pair m j := by
  rw [pair_succ, pair_succ] at h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  ext
  · have := h2; rw [h1] at this; simpa using this
  · exact h1

theorem exists_return (m : ℕ) [NeZero m] : ∃ π, 0 < π ∧ pair m π = pair m 0 := by
  obtain ⟨i, j, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite (pair m)
  have key : ∀ i j, i < j → pair m i = pair m j → ∃ π, 0 < π ∧ pair m π = pair m 0 := by
    intro i
    induction i with
    | zero => intro j hj h; exact ⟨j, hj, h.symm⟩
    | succ i ih =>
      intro j hj h
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      exact ih j' (by omega) (pair_eq_of_succ_eq h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact key i j hlt h
  · exact key j i hgt h.symm

theorem exists_period (m : ℕ) (hm : 0 < m) :
    ∃ π, 0 < π ∧ ∀ n, Nat.fib (n + π) ≡ Nat.fib n [MOD m] := by
  have : NeZero m := ⟨hm.ne'⟩
  obtain ⟨π, hπ, h⟩ := exists_return m
  refine ⟨π, hπ, fun n => ?_⟩
  have : ∀ n, pair m (n + π) = pair m n := by
    intro n
    induction n with
    | zero => simpa [pair_zero] using h
    | succ n ih =>
      rw [show n + 1 + π = (n + π) + 1 by omega, pair_succ, pair_succ, ih]
  have h1 := congrArg Prod.fst (this n)
  simp only [pair] at h1
  exact (ZMod.natCast_eq_natCast_iff _ _ _).1 h1

theorem dvd_fib_iff (m : ℕ) (hm : 0 < m) :
    ∃ d, 0 < d ∧ ∀ n, m ∣ Nat.fib n ↔ d ∣ n := by
  obtain ⟨π, hπ, hper⟩ := exists_period m hm
  have hex : ∃ d, 0 < d ∧ m ∣ Nat.fib d := by
    refine ⟨π, hπ, ?_⟩
    have := hper 0
    simp only [zero_add, Nat.fib_zero] at this
    exact (Nat.modEq_zero_iff_dvd).1 this
  classical
  let d := Nat.find hex
  have hd : 0 < d ∧ m ∣ Nat.fib d := Nat.find_spec hex
  refine ⟨d, hd.1, fun n => ⟨fun hn => ?_, fun hdn => ?_⟩⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · exact dvd_zero _
    · have hg : m ∣ Nat.fib (Nat.gcd n d) := by
        rw [Nat.fib_gcd]; exact Nat.dvd_gcd hn hd.2
      have hgpos : 0 < Nat.gcd n d := Nat.gcd_pos_of_pos_left _ hnpos
      have hle : d ≤ Nat.gcd n d := Nat.find_min' hex ⟨hgpos, hg⟩
      have hle2 : Nat.gcd n d ≤ d := Nat.gcd_le_right _ hd.1
      have : Nat.gcd n d = d := le_antisymm hle2 hle
      rw [← this]; exact Nat.gcd_dvd_left _ _
  · exact hd.2.trans (Nat.fib_dvd d n hdn)

/-- Cassini in `ℤ`: `F_{n+2} F_n − F_{n+1}² = (−1)^(n+1)`. -/
theorem cassini (n : ℕ) :
    (Nat.fib (n + 2) : ℤ) * Nat.fib n - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e1 : (Nat.fib (n + 1 + 2) : ℤ) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
      rw [show n + 1 + 2 = (n + 1) + 2 by rfl, Nat.fib_add_two]; push_cast; ring
    have e2 : (Nat.fib (n + 2) : ℤ) = Nat.fib n + Nat.fib (n + 1) := by
      rw [Nat.fib_add_two]; push_cast; ring
    rw [e1, show n + 1 + 1 = n + 2 by rfl, pow_succ _ (n + 1)]
    linear_combination (-1 : ℤ) * ih - (Nat.fib (n + 2) : ℤ) * e2

theorem even_of_period (m : ℕ) (hm : 2 < m) (π : ℕ) (hπ : 0 < π)
    (hper : ∀ n, Nat.fib (n + π) ≡ Nat.fib n [MOD m]) : Even π := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨k, rfl⟩ : ∃ k, π = k + 1 := ⟨π - 1, by omega⟩
  have z0 : ((Nat.fib (k + 1) : ℕ) : ZMod m) = 0 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 (hper 0)
    simpa using this
  have z1 : ((Nat.fib (k + 2) : ℕ) : ZMod m) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 (hper 1)
    simpa [show 1 + (k + 1) = k + 2 by omega] using this
  have z2 : ((Nat.fib k : ℕ) : ZMod m) = 1 := by
    have : ((Nat.fib (k + 2) : ℕ) : ZMod m) = Nat.fib k + Nat.fib (k + 1) := by
      rw [Nat.fib_add_two]; push_cast; ring
    rw [z0, z1] at this; simpa using this.symm
  have hc := congrArg (Int.cast : ℤ → ZMod m) (cassini k)
  push_cast at hc
  rw [z0, z1, z2, hodd.neg_one_pow] at hc
  have h2 : ((2 : ℕ) : ZMod m) = 0 := by
    push_cast
    linear_combination hc
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem fib_mod_periodicity (m : ℕ) (hm : 0 < m) :
    (∃ d, 0 < d ∧ ∀ n, m ∣ Nat.fib n ↔ d ∣ n) ∧
    (∃ π, 0 < π ∧ ∀ n, Nat.fib (n + π) ≡ Nat.fib n [MOD m]) ∧
    (2 < m → ∀ π, 0 < π → (∀ n, Nat.fib (n + π) ≡ Nat.fib n [MOD m]) → Even π) :=
  ⟨dvd_fib_iff m hm, exists_period m hm, fun h2 π hπ hper => even_of_period m h2 π hπ hper⟩


end Pisano
