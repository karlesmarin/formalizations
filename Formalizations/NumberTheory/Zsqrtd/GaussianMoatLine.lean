/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.PrimesCongruentOne
public import Mathlib.NumberTheory.SumTwoSquares
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Zify
public import Mathlib.Tactic.Cases
public import Mathlib.Tactic.NthRewrite

/-!
# Lines of Gaussian integers far from every Gaussian prime

Every straight line through two distinct Gaussian integers `z ≠ w` contains Gaussian integers at
arbitrarily large distance from every Gaussian prime: for every `R` there is `t : ℤ` such that
`z + t (w - z)` has squared distance `> R` from all Gaussian primes (Gethner–Wagon–Wick, 1998); so
no walk to infinity with bounded steps stays on a line. The point is built by the Chinese remainder
theorem: for each offset `u` in the box of radius `R`, a prime `p ≡ 1 (mod 4)` larger than
everything relevant splits in `ℤ[i]` and one of its Gaussian factors is made to divide
`z + t (w - z) + u`, with a norm too large for that Gaussian integer to be prime.

## Main results

* `GaussianMoat.exists_far_from_primes_on_line`: every line through two Gaussian integers has points far from all Gaussian primes
* `GaussianMoat.norm_eq_of_dvd_prime`: a Gaussian prime divisible by a Gaussian integer of prime norm has that norm

## References

* E. Gethner, S. Wagon and B. Wick, *A stroll through the Gaussian primes*, Amer. Math. Monthly 105 (1998), 327–337.
* The general moat question (Gordon 1962; Erdős problem 952) is settled in OpenAI, *Bounded-Step Walks on Gaussian Primes* (2026), with a Lean proof in openai/math; that is a different statement and is not used here.
-/

@[expose] public section

namespace GaussianMoat

/-- If `π` has prime norm `p` then every integer-coefficient Gaussian integer is congruent modulo
`π` to a rational integer (`ℤ → ℤ[i]/(π)` is onto). -/
theorem exists_int_dvd_sub {π : GaussianInt} {p : ℕ} (hp : p.Prime) (hπ : π.norm = p)
    (g : GaussianInt) : ∃ n : ℤ, π ∣ g - n := by
  obtain ⟨a, b⟩ := π
  have hab : a * a + b * b = (p : ℤ) := by
    have := hπ
    simp only [Zsqrtd.norm_def] at this
    linarith
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp1 : (1 : ℤ) < p := by exact_mod_cast hp.one_lt
  have hnd : ¬ (p : ℤ) ∣ b := by
    intro ⟨c, hc⟩
    have hc0 : c = 0 := by
      by_contra hne
      have h1 : 1 ≤ c * c := by
        rcases lt_or_gt_of_ne hne with h | h <;> nlinarith
      subst hc
      have h2 : (p : ℤ) * p ≤ p * p * (c * c) := by nlinarith [mul_self_nonneg (p : ℤ)]
      nlinarith [mul_self_nonneg a]
    subst hc0
    simp only [mul_zero] at hc
    subst hc
    have hn : (p : ℤ) = a.natAbs * a.natAbs := by
      rw [← hab]; simp
    have hn' : p = a.natAbs * a.natAbs := by exact_mod_cast hn
    have hd : a.natAbs ∣ p := ⟨a.natAbs, hn'⟩
    rcases (Nat.dvd_prime hp).1 hd with h | h
    · rw [h] at hn'; omega
    · rw [h] at hn'; nlinarith [hp.one_lt]
  obtain ⟨x, y, hxy⟩ : IsCoprime b (p : ℤ) :=
    ((Irreducible.coprime_iff_not_dvd hpi.irreducible).2 hnd).symm
  have key : (⟨0, 1⟩ : GaussianInt) - ((-a * x : ℤ) : GaussianInt) =
      (⟨a, b⟩ : GaussianInt) * ((x : GaussianInt) + ⟨0, 1⟩ * (y : GaussianInt) * ⟨a, -b⟩) := by
    apply Zsqrtd.ext
    · simp; ring
    · simp; linear_combination (-1 : ℤ) * (y * hab + hxy)
  have hi : (⟨a, b⟩ : GaussianInt) ∣ (⟨0, 1⟩ : GaussianInt) - ((-a * x : ℤ) : GaussianInt) :=
    ⟨_, key⟩
  refine ⟨g.re + g.im * (-a * x), ?_⟩
  have e : g - ((g.re + g.im * (-a * x) : ℤ) : GaussianInt) =
      (g.im : GaussianInt) * ((⟨0, 1⟩ : GaussianInt) - ((-a * x : ℤ) : GaussianInt)) := by
    apply Zsqrtd.ext <;> simp
  rw [e]
  exact Dvd.dvd.mul_left hi _

/-- A Gaussian prime divisible by an element of prime norm `p` has norm `p`. -/
theorem norm_eq_of_dvd_prime {π g : GaussianInt} {p : ℕ} (hp : p.Prime) (hπ : π.norm = p)
    (hg : Prime g) (hd : π ∣ g) : g.norm = p := by
  obtain ⟨h, rfl⟩ := hd
  rcases hg.irreducible.isUnit_or_isUnit rfl with hu | hu
  · have := (Zsqrtd.norm_eq_one_iff' (by norm_num) π).2 hu
    rw [hπ] at this
    have h1 : (1 : ℤ) < p := by exact_mod_cast hp.one_lt
    omega
  · have := (Zsqrtd.norm_eq_one_iff' (by norm_num) h).2 hu
    rw [Zsqrtd.norm_mul, this, mul_one, hπ]

/-- Norm growth along an arithmetic progression of Gaussian integers. -/
theorem exists_norm_gt (a e : GaussianInt) (he : e ≠ 0) (L : ℤ) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → L < (a + (k : GaussianInt) * e).norm := by
  have hn : 1 ≤ e.re * e.re + e.im * e.im := by
    by_contra hlt
    apply he
    have h1 : e.re * e.re + e.im * e.im = 0 := by
      nlinarith [mul_self_nonneg e.re, mul_self_nonneg e.im]
    have h2 : e.re = 0 := by nlinarith [mul_self_nonneg e.re, mul_self_nonneg e.im]
    have h3 : e.im = 0 := by nlinarith [mul_self_nonneg e.re, mul_self_nonneg e.im]
    exact Zsqrtd.ext h2 h3
  refine ⟨(2 * |a.re * e.re + a.im * e.im| + |L| + 1).toNat, fun k hk => ?_⟩
  have hk' : 2 * |a.re * e.re + a.im * e.im| + |L| + 1 ≤ (k : ℤ) := by
    have := Int.self_le_toNat (2 * |a.re * e.re + a.im * e.im| + |L| + 1)
    omega
  have hs1 := neg_abs_le (a.re * e.re + a.im * e.im)
  have hs2 := abs_nonneg (a.re * e.re + a.im * e.im)
  have hL := le_abs_self L
  have hL2 := abs_nonneg L
  have hk0 : (0 : ℤ) ≤ k := by linarith
  have e1 : (a + (k : GaussianInt) * e).norm = (a.re * a.re + a.im * a.im)
      + 2 * k * (a.re * e.re + a.im * e.im) + k * k * (e.re * e.re + e.im * e.im) := by
    simp [Zsqrtd.norm_def]; ring
  rw [e1]
  set s := a.re * e.re + a.im * e.im
  have hNa : 0 ≤ a.re * a.re + a.im * a.im := by
    nlinarith [mul_self_nonneg a.re, mul_self_nonneg a.im]
  have h3 : (k : ℤ) * k ≤ k * k * (e.re * e.re + e.im * e.im) := by
    nlinarith [mul_self_nonneg (k : ℤ)]
  have h4 : (k : ℤ) * (|L| + 1) ≤ k * (k - 2 * |s|) := by
    apply mul_le_mul_of_nonneg_left _ hk0; linarith
  nlinarith

/-- Inductive CRT construction: for every finite set `S` of offsets there is a progression
`t + k M` along which, for each `u ∈ S`, the point `z + (t + k M) d + u` is divisible by a Gaussian
integer of prime norm `q ≤ M`. -/
theorem exists_modulus (z d : GaussianInt) (hd : d ≠ 0) (S : Finset GaussianInt) :
    ∃ t M : ℤ, 0 < M ∧ ∀ u ∈ S, ∃ (π : GaussianInt) (q : ℕ), q.Prime ∧ π.norm = q ∧
      (q : ℤ) ≤ M ∧ ∀ k : ℤ, π ∣ z + ((t + k * M : ℤ) : GaussianInt) * d + u := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, 1, one_pos, by simp⟩
  | insert u0 S _ ih =>
    obtain ⟨t, M, hM, H⟩ := ih
    obtain ⟨p, hpp, hgt, hmod⟩ :=
      Nat.exists_prime_gt_modEq_one (k := 4) (M.toNat + d.norm.toNat) (by norm_num)
    have := Fact.mk hpp
    have hp4 : p % 4 ≠ 3 := by unfold Nat.ModEq at hmod; omega
    obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq hp4
    have hab' : (a : ℤ) * a + b * b = p := by
      have : ((a : ℤ)) ^ 2 + (b : ℤ) ^ 2 = p := by exact_mod_cast hab
      nlinarith
    obtain ⟨π, hπdef⟩ : ∃ π : GaussianInt, π = ⟨a, b⟩ := ⟨_, rfl⟩
    have hπ : π.norm = p := by
      rw [hπdef]; simp only [Zsqrtd.norm_def]; linarith
    have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpp
    have hpM : M < p := by omega
    have hdpos : 0 < d.norm := by
      have := GaussianInt.norm_pos.2 hd
      exact this
    have hpd : d.norm < p := by omega
    have hπp : π ∣ (p : GaussianInt) :=
      ⟨⟨a, -b⟩, by rw [hπdef]; apply Zsqrtd.ext <;> simp <;> linarith⟩
    obtain ⟨A', hA'⟩ := exists_int_dvd_sub hpp hπ (z + u0 + (t : GaussianInt) * d)
    obtain ⟨d', hd'⟩ := exists_int_dvd_sub hpp hπ d
    have hpd' : ¬ (p : ℤ) ∣ d' := by
      intro h
      have h1 : π ∣ (d' : GaussianInt) := by
        obtain ⟨c, hc⟩ := h
        exact dvd_trans hπp ⟨c, by rw [hc]; push_cast; ring⟩
      have h2 : π ∣ d := by
        have : d = (d - d') + d' := by ring
        rw [this]; exact dvd_add hd' h1
      obtain ⟨h, hh⟩ := h2
      have h3 : d.norm = p * h.norm := by rw [hh, Zsqrtd.norm_mul, hπ]
      have h4 : (p : ℤ) ∣ d.norm := ⟨_, h3⟩
      have := Int.le_of_dvd hdpos h4
      omega
    have hpMd : ¬ (p : ℤ) ∣ M * d' := by
      intro h
      rcases hpi.dvd_or_dvd h with h | h
      · have := Int.le_of_dvd hM h; omega
      · exact hpd' h
    obtain ⟨x, y, hxy⟩ : IsCoprime (M * d') (p : ℤ) :=
      ((Irreducible.coprime_iff_not_dvd hpi.irreducible).2 hpMd).symm
    have e2 : A' + (-A' * x) * M * d' = A' * y * p := by linear_combination (-A') * hxy
    refine ⟨t + (-A' * x) * M, M * p, mul_pos hM (by exact_mod_cast hpp.pos), ?_⟩
    intro u hu
    have hMp : M ≤ M * p := by
      have : (1 : ℤ) ≤ p := by exact_mod_cast hpp.one_le
      nlinarith
    rcases Finset.mem_insert.1 hu with rfl | hu
    · refine ⟨π, p, hpp, hπ, by nlinarith, fun k => ?_⟩
      have e3 : ((A' * y * p : ℤ) : GaussianInt) = ((A' + (-A' * x) * M * d' : ℤ) : GaussianInt) := by
        rw [e2]
      have key : z + ((t + -A' * x * M + k * (M * p) : ℤ) : GaussianInt) * d + u =
          (z + u + (t : GaussianInt) * d - A') + ((-A' * x * M : ℤ) : GaussianInt) * (d - d')
            + ((A' * y * p : ℤ) : GaussianInt) + ((k * M : ℤ) : GaussianInt) * (p : GaussianInt) * d := by
        rw [e3]; push_cast; ring
      rw [key]
      refine dvd_add (dvd_add (dvd_add hA' (Dvd.dvd.mul_left hd' _)) ?_) ?_
      · push_cast; exact Dvd.dvd.mul_left hπp _
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hπp _) _
    · obtain ⟨π', q, hq, hqn, hqM, Hk⟩ := H u hu
      refine ⟨π', q, hq, hqn, le_trans hqM hMp, fun k => ?_⟩
      have := Hk (-A' * x + k * p)
      convert this using 4
      push_cast; ring

/-- **Gethner–Wagon–Wick (1998).** Every straight line through two distinct Gaussian integers `z ≠ w`
contains Gaussian integers at arbitrarily large distance from every Gaussian prime: for every `R`
there is `t : ℤ` such that `z + t (w - z)` has squared distance `> R` from every Gaussian prime. -/
theorem exists_far_from_primes_on_line (z w : GaussianInt) (hzw : z ≠ w) (R : ℕ) :
    ∃ t : ℤ, ∀ π : GaussianInt, Prime π → (R : ℤ) < (z + t * (w - z) - π).norm := by
  classical
  have hd0 : w - z ≠ 0 := sub_ne_zero.2 (Ne.symm hzw)
  obtain ⟨d, hd⟩ : ∃ d : GaussianInt, d = w - z := ⟨_, rfl⟩
  rw [← hd] at hd0 ⊢
  obtain ⟨S, hS⟩ : ∃ S : Finset GaussianInt, S = (Finset.Icc (-(R : ℤ)) R ×ˢ
      Finset.Icc (-(R : ℤ)) R).image (fun q => (⟨q.1, q.2⟩ : GaussianInt)) := ⟨_, rfl⟩
  obtain ⟨t, M, hM, H⟩ := exists_modulus z d hd0 S
  have he : ((M : ℤ) : GaussianInt) * d ≠ 0 :=
    mul_ne_zero ((Int.cast_ne_zero).2 hM.ne') hd0
  have hK : ∀ u : GaussianInt, ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      M < (z + ((t + (k : ℤ) * M : ℤ) : GaussianInt) * d + u).norm := by
    intro u
    obtain ⟨K, hK⟩ := exists_norm_gt (z + (t : GaussianInt) * d + u) (M * d) he M
    refine ⟨K, fun k hk => ?_⟩
    have := hK k hk
    convert this using 2
    push_cast; ring
  choose Kf hKf using hK
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ, K = S.sup Kf := ⟨_, rfl⟩
  refine ⟨t + (K : ℤ) * M, fun π hπ => ?_⟩
  by_contra hle
  push Not at hle
  obtain ⟨u, hu⟩ : ∃ u : GaussianInt, u = π - (z + ((t + (K : ℤ) * M : ℤ) : GaussianInt) * d) :=
    ⟨_, rfl⟩
  have hu_norm : u.norm ≤ R := by
    have : u = -(z + ((t + (K : ℤ) * M : ℤ) : GaussianInt) * d - π) := by rw [hu]; ring
    rw [this, Zsqrtd.norm_neg]; exact hle
  have hre : u.re * u.re + u.im * u.im ≤ R := by
    have := hu_norm
    simp only [Zsqrtd.norm_def] at this
    linarith
  have hR : (0 : ℤ) ≤ R := by positivity
  have huS : u ∈ S := by
    rw [hS, Finset.mem_image]
    refine ⟨(u.re, u.im), ?_, rfl⟩
    simp only [Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      nlinarith [mul_self_nonneg u.re, mul_self_nonneg u.im]
  obtain ⟨π', q, hq, hqn, hqM, Hk⟩ := H u huS
  have hdv := Hk (K : ℤ)
  have hsum : z + ((t + (K : ℤ) * M : ℤ) : GaussianInt) * d + u = π := by rw [hu]; ring
  rw [hsum] at hdv
  have hn := norm_eq_of_dvd_prime hq hqn hπ hdv
  have hbig := hKf u K (hKdef ▸ Finset.le_sup huS)
  rw [hsum, hn] at hbig
  omega

end GaussianMoat
