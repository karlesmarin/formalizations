/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The symplectic alphabet of a power of the Kostant element

For zeta a primitive t-th root of unity in a field, t = 2m+2, k a natural number, d = gcd(k,t) and q
= t/d, the multiset A = {zeta^(jk), zeta^(-jk) : 1 <= j <= m} (counted with multiplicity) equals d
times the multiset of q-th roots of unity minus two copies of 1 (d even) or minus {1} and {-1} (d
odd). Equality is of multisets with multiplicities. The ambient field is arbitrary (the paper works
over C); no characteristic hypothesis is needed. The additive forms A + 2{1} = d.mu_q and A + {1} +
{-1} = d.mu_q are also proved. Nothing about Lie theory or characters is formalized.

## Main results

* `KostantAlphabet.alphabet_eq_even`: A = d.mu_q - 2.{1} for d even
* `KostantAlphabet.alphabet_eq_odd`: A = d.mu_q - {1} - {-1} for d odd
* `KostantAlphabet.alphabet_add_even`: additive form, d even
* `KostantAlphabet.alphabet_add_odd`: additive form, d odd

## References

* C. Marín, *Integer character values on the ρ-line of Sp(2m)*, Zenodo (2026),
  doi:10.5281/zenodo.22683561, `prop:alph`.
-/

@[expose] public section

namespace KostantAlphabet

open Multiset Polynomial

variable {F : Type*} [Field F]

/-- The alphabet `{ζ^{±jk} : j = 1..m}` as a multiset. -/
def alphabet (ζ : F) (m k : ℕ) : Multiset F :=
  (range m).map (fun j => ζ ^ ((j + 1) * k)) + (range m).map (fun j => (ζ ^ ((j + 1) * k))⁻¹)

lemma map_range_reflect {α : Type*} (g : ℕ → α) (n : ℕ) :
    (range n).map (fun i => g (n - 1 - i)) = (range n).map g := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
    have e1 : (range (n + 1)).map (fun i => g (n + 1 - 1 - i)) =
        g n ::ₘ (range n).map (fun i => g (n - 1 - i)) := by
      rw [show n + 1 = 1 + n from add_comm _ _, range_add, map_add, map_map]
      have h0 : range 1 = {0} := rfl
      rw [h0, map_singleton, singleton_add]
      congr 1
      · simp
      · apply map_congr rfl
        intro i _
        simp only [Function.comp]
        congr 1
        omega
    rw [e1, ih, range_succ, map_cons]

lemma map_range_mul {α : Type*} (f : ℕ → α) (q : ℕ) (hf : ∀ e, f (e + q) = f e) (n : ℕ) :
    (range (q * n)).map f = n • (range q).map f := by
  have key : ∀ n i : ℕ, f (q * n + i) = f i := by
    intro n i
    induction n with
    | zero => simp
    | succ n ih2 => rw [Nat.mul_succ, add_assoc, add_comm q, ← add_assoc, hf, ih2]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, range_add, map_add, ih, map_map, succ_nsmul]
    congr 1
    apply map_congr rfl
    intro i _
    exact key n i

lemma full_period {ζ : F} {t : ℕ} (ht : 0 < t) (hζ : IsPrimitiveRoot ζ t) (k : ℕ) :
    (range t).map (fun e => ζ ^ (k * e)) = (k.gcd t) • nthRoots (t / k.gcd t) (1 : F) := by
  have hω : IsPrimitiveRoot (ζ ^ k) (t / t.gcd k) :=
    hζ.pow_div_gcd k (Nat.gcd_pos_of_pos_left _ ht).ne'
  rw [Nat.gcd_comm] at hω
  have htq : t = (t / k.gcd t) * k.gcd t := (Nat.div_mul_cancel (Nat.gcd_dvd_right k t)).symm
  generalize t / k.gcd t = q at hω htq
  have hf : ∀ e, (fun e => ζ ^ (k * e)) (e + q) = (fun e => ζ ^ (k * e)) e := by
    intro e
    simp only
    rw [mul_add, pow_add, pow_mul ζ k q, hω.pow_eq_one, mul_one]
  have h1 := map_range_mul (fun e => ζ ^ (k * e)) q hf (k.gcd t)
  rw [← htq] at h1
  rw [h1, hω.nthRoots_eq (α := 1) (one_pow q)]
  congr 1
  apply map_congr rfl
  intro e _
  simp [pow_mul]

lemma decomposition {ζ : F} {t m : ℕ} (k : ℕ) (hm : t = 2 * m + 2) (hζ : IsPrimitiveRoot ζ t) :
    (range t).map (fun e => ζ ^ (k * e)) =
      {(1 : F)} + {ζ ^ (k * (m + 1))} + alphabet ζ m k := by
  have hr : range t = range (1 + m) + (range (1 + m)).map ((1 + m) + ·) := by
    rw [← range_add]; congr 1; omega
  have h0 : range 1 = {0} := rfl
  have hrefl := map_range_reflect (fun j : ℕ => (ζ ^ ((j + 1) * k))⁻¹) m
  have hb : (range m).map (fun i => ζ ^ (k * (1 + m + (1 + i)))) =
      (range m).map (fun j => (ζ ^ ((j + 1) * k))⁻¹) := by
    rw [← hrefl]
    apply map_congr rfl
    intro i hi
    have hi' := mem_range.1 hi
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_add]
    have : k * (1 + m + (1 + i)) + (m - 1 - i + 1) * k = t * k := by
      have e : m - 1 - i + 1 = m - i := by omega
      rw [e]
      have : 1 + m + (1 + i) + (m - i) = t := by omega
      rw [← this]; ring
    rw [this, pow_mul, hζ.pow_eq_one, one_pow]
  rw [hr, Multiset.map_add, map_map, range_add 1 m, Multiset.map_add, Multiset.map_add, map_map,
    map_map, h0, map_singleton]
  simp only [Function.comp, singleton_add]
  have ha : (range m).map (fun x => ζ ^ (k * (1 + x))) =
      (range m).map (fun j => ζ ^ ((j + 1) * k)) :=
    map_congr rfl (fun i _ => by congr 1; ring)
  rw [hb, ha, Multiset.map_singleton, show 1 + m + 0 = m + 1 by ring, mul_zero, pow_zero]
  unfold alphabet
  simp only [← singleton_add]
  abel

lemma half_value {ζ : F} {t m : ℕ} (k : ℕ) (hm : t = 2 * m + 2) (hζ : IsPrimitiveRoot ζ t) :
    (Even (k.gcd t) → ζ ^ (k * (m + 1)) = 1) ∧ (Odd (k.gcd t) → ζ ^ (k * (m + 1)) = -1) := by
  have ht : 0 < t := by omega
  have hω : IsPrimitiveRoot (ζ ^ k) (t / t.gcd k) :=
    hζ.pow_div_gcd k (Nat.gcd_pos_of_pos_left _ ht).ne'
  rw [Nat.gcd_comm] at hω
  have htq : t = (t / k.gcd t) * k.gcd t := (Nat.div_mul_cancel (Nat.gcd_dvd_right k t)).symm
  generalize t / k.gcd t = q at hω htq
  generalize k.gcd t = d at htq ⊢
  have hx : ζ ^ (k * (m + 1)) = (ζ ^ k) ^ (m + 1) := pow_mul _ _ _
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; omega
    · exact h
  constructor
  · rintro ⟨e, he⟩
    subst he
    have h2 : m + 1 = q * e := by
      have : q * (e + e) = q * e + q * e := mul_add _ _ _
      omega
    rw [hx, h2, pow_mul, hω.pow_eq_one, one_pow]
  · intro hodd
    have hsq : ζ ^ (k * (m + 1)) * ζ ^ (k * (m + 1)) = 1 := by
      rw [← pow_add, ← mul_add, show m + 1 + (m + 1) = t by omega, mul_comm, pow_mul,
        hζ.pow_eq_one, one_pow]
    rcases mul_self_eq_one_iff.1 hsq with h | h
    · exfalso
      rw [hx] at h
      obtain ⟨c, hc⟩ := hω.dvd_of_pow_eq_one _ h
      obtain ⟨e, he⟩ := hodd
      rw [he] at htq
      have h3 : q * (2 * c) = 2 * (q * c) := by ring
      have : q * (2 * e + 1) = q * (2 * c) := by omega
      have := Nat.eq_of_mul_eq_mul_left hq this
      omega
    · exact h

/-- **The alphabet of `a_P^k`** (additive form, `d` even): `A + 2·{1} = d·μ_q`. -/
theorem alphabet_add_even {ζ : F} {t m : ℕ} (k : ℕ) (hm : t = 2 * m + 2)
    (hζ : IsPrimitiveRoot ζ t) (hd : Even (k.gcd t)) :
    alphabet ζ m k + 2 • {(1 : F)} = (k.gcd t) • nthRoots (t / k.gcd t) (1 : F) := by
  rw [← full_period (by omega) hζ k, decomposition k hm hζ, (half_value k hm hζ).1 hd]
  simp only [two_nsmul]; abel

/-- **The alphabet of `a_P^k`** (additive form, `d` odd): `A + {1} + {-1} = d·μ_q`. -/
theorem alphabet_add_odd {ζ : F} {t m : ℕ} (k : ℕ) (hm : t = 2 * m + 2)
    (hζ : IsPrimitiveRoot ζ t) (hd : Odd (k.gcd t)) :
    alphabet ζ m k + {(1 : F)} + {(-1 : F)} = (k.gcd t) • nthRoots (t / k.gcd t) (1 : F) := by
  rw [← full_period (by omega) hζ k, decomposition k hm hζ, (half_value k hm hζ).2 hd]
  abel

variable [DecidableEq F]

/-- **Proposition (alphabet), `d` even:** `A = d·μ_q − 2·{1}` as multisets. -/
theorem alphabet_eq_even {ζ : F} {t m : ℕ} (k : ℕ) (hm : t = 2 * m + 2)
    (hζ : IsPrimitiveRoot ζ t) (hd : Even (k.gcd t)) :
    alphabet ζ m k = (k.gcd t) • nthRoots (t / k.gcd t) (1 : F) - (2 : ℕ) • ({1} : Multiset F) := by
  rw [← alphabet_add_even k hm hζ hd, Multiset.add_sub_cancel_right]

/-- **Proposition (alphabet), `d` odd:** `A = d·μ_q − {1} − {-1}` as multisets. -/
theorem alphabet_eq_odd {ζ : F} {t m : ℕ} (k : ℕ) (hm : t = 2 * m + 2)
    (hζ : IsPrimitiveRoot ζ t) (hd : Odd (k.gcd t)) :
    alphabet ζ m k = (k.gcd t) • nthRoots (t / k.gcd t) (1 : F) - ({1} : Multiset F) - {-1} := by
  rw [← alphabet_add_odd k hm hζ hd, add_right_comm (alphabet ζ m k), Multiset.add_sub_cancel_right, Multiset.add_sub_cancel_right]

end KostantAlphabet
