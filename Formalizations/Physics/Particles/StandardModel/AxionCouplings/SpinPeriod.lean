/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Tactic.Ring

/-!
# Integrality of periods on spin four-manifolds

Arithmetic certificates for the quantization of couplings `p A + q B + r C` whose three periods
`A`, `B`, `C` run over `ℤ` on a general four-manifold, while on a spin four-manifold the
intersection form is even, so that the third period runs over `2ℤ`. The geometric realization of
the period triples and the evenness of the intersection pairing are inputs, not formalized. `t`
is a common denominator in applications (nonzero); the statements remain valid as divisibility
statements at `t = 0`.

## Main results

* `universal_basis`, `spin_basis`: the periods lie in `t ℤ` iff `t ∣ p, q, r`, respectively
  `t ∣ p, q, 2r`.
* `universal_implies_spin`, `half_square_spin`, `half_square_not_universal`: the spin condition
  is strictly weaker.
* `q6_congruence`, `q6_implies_six`: for the `q = 6` row of Table 1 of Choi–Forslund–Lam–Shao
  (with `A = c₂(E₂)`, `B = c₂(E₃)`, `C = c₁(E₃)²` and mathematical sign conventions for Chern
  classes) the spin condition is `18 K₂ + 24 K₃ + K₁ ≡ 0 (mod 36)`, and it forces `6 ∣ K₁`.

## References

* Y. Choi, M. Forslund, H. T. Lam, S.-H. Shao, *Quantization of axion-gauge couplings and
  non-invertible higher symmetries*, Phys. Rev. Lett. 132 (2024) 121601, arXiv:2309.03937,
  Table 1.
-/

@[expose] public section

namespace AxionCouplings.SpinPeriod

/-- `p a + q b + r c ∈ t ℤ` for all integer periods. -/
def universalPeriods (p q r t : Int) : Prop :=
  ∀ a b c : Int, ∃ k : Int, p*a + q*b + r*c = t*k

/-- `p a + q b + 2 r c ∈ t ℤ` for all integer periods (even third period). -/
def spinPeriods (p q r t : Int) : Prop :=
  ∀ a b c : Int, ∃ k : Int, p*a + q*b + 2*r*c = t*k

/-- The integral basis criterion on a general four-manifold. -/
theorem universal_basis (p q r t : Int) :
    universalPeriods p q r t ↔ ∃ x y z : Int, p=t*x ∧ q=t*y ∧ r=t*z := by
  constructor
  · intro h
    obtain ⟨x,hx⟩ := h 1 0 0
    obtain ⟨y,hy⟩ := h 0 1 0
    obtain ⟨z,hz⟩ := h 0 0 1
    exact ⟨x,y,z, by simpa using hx, by simpa using hy, by simpa using hz⟩
  · rintro ⟨x,y,z,hx,hy,hz⟩ a b c
    refine ⟨x*a+y*b+z*c, ?_⟩
    grind

/-- The integral basis criterion on a spin four-manifold. -/
theorem spin_basis (p q r t : Int) :
    spinPeriods p q r t ↔ ∃ x y z : Int, p=t*x ∧ q=t*y ∧ 2*r=t*z := by
  constructor
  · intro h
    obtain ⟨x,hx⟩ := h 1 0 0
    obtain ⟨y,hy⟩ := h 0 1 0
    obtain ⟨z,hz⟩ := h 0 0 1
    exact ⟨x,y,z, by simpa using hx, by simpa using hy, by simpa using hz⟩
  · rintro ⟨x,y,z,hx,hy,hz⟩ a b c
    refine ⟨x*a+y*b+z*c, ?_⟩
    grind

/-- The general condition implies the spin condition. -/
theorem universal_implies_spin (p q r t : Int) (h : universalPeriods p q r t) :
    spinPeriods p q r t := by
  intro a b c
  obtain ⟨k,hk⟩ := h a b (2*c)
  exact ⟨k, by grind⟩

/-- Half of the square satisfies the spin condition. -/
theorem half_square_spin : spinPeriods 0 0 1 2 := by
  intro a b c
  exact ⟨c, by simp⟩

/-- Half of the square does not satisfy the general condition. -/
theorem half_square_not_universal : ¬ universalPeriods 0 0 1 2 := by
  intro h
  obtain ⟨k,hk⟩ := h 0 0 1
  simp at hk
  omega

/-- The spin condition for the `q = 6` row. -/
theorem q6_congruence (K2 K3 K1 : Int) :
    spinPeriods (-72*K2) (-72*K3) (18*K2+24*K3+K1) 72 ↔
      ∃ k : Int, 18*K2+24*K3+K1=36*k := by
  rw [spin_basis]
  constructor
  · rintro ⟨x,y,z,hx,hy,hz⟩
    exact ⟨z, by omega⟩
  · rintro ⟨k,hk⟩
    refine ⟨-K2,-K3,k,?_,?_,?_⟩ <;> grind

/-- The `q = 6` spin condition forces `6 ∣ K₁`. -/
theorem q6_implies_six (K2 K3 K1 k : Int)
    (h : 18*K2+24*K3+K1=36*k) : ∃ j : Int, K1=6*j := by
  exact ⟨6*k-3*K2-4*K3, by omega⟩

end AxionCouplings.SpinPeriod
