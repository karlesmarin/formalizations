/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.Group

/-!
# Quasi-complete Latin squares from terraces (Bailey)

For a finite group `G` and orderings `a, b : Fin |G| ≃ G`, the Cayley table
`L(a, b) i j = a i * b j` is quasi-complete (every unordered pair of distinct symbols is adjacent
exactly twice horizontally and exactly twice vertically) if and only if `a⁻¹` and `b` are terraces:
for every `g ≠ 1`, `g` and `g⁻¹` together occur exactly twice among the successive quotients
(Theorem of the Day; R. A. Bailey 1984). Proof: horizontal neighbours `(a_i b_j, a_i b_{j+1})` have
quotient `b_j⁻¹ b_{j+1}`, vertical ones `a_i a_{i+1}⁻¹`, and for each fixed column or row the map to
the first symbol is a bijection.

## Main results

* `Bailey.quasiComplete_iff`: Bailey's theorem: L(a, b) quasi-complete iff a⁻¹ and b are terraces

## References

* R. Whitty, Theorem of the Day, «Bailey's Theorem on Latin Squares» (Bailey).
* R. A. Bailey, «Quasi-complete Latin squares: construction and randomization», J. Roy. Statist. Soc. B 46 (1984) 323–334.
-/

@[expose] public section

open scoped Classical

namespace Bailey

variable {G : Type*} [Group G] [Fintype G]

/-- Número de posiciones `k` (con `k + 1 < |G|`) cuya diferencia sucesiva `s k⁻¹ * s (k+1)` es `g`. -/
noncomputable def diffCount (s : Fin (Fintype.card G) ≃ G) (g : G) : ℕ :=
  (Finset.univ.filter fun k : Fin (Fintype.card G) =>
    ∃ h : (k : ℕ) + 1 < Fintype.card G, (s k)⁻¹ * s ⟨k + 1, h⟩ = g).card

/-- Terraza: para todo `g ≠ 1`, `g` y `g⁻¹` aparecen, juntos, exactamente dos veces entre las diferencias
sucesivas (una involución aparece, pues, una sola vez). -/
def IsTerrace (s : Fin (Fintype.card G) ≃ G) : Prop :=
  ∀ g : G, g ≠ 1 → diffCount s g + diffCount s g⁻¹ = 2

/-- Cuadrado casi completo: cada par no ordenado `{x, y}` de símbolos distintos aparece exactamente dos veces
como vecinos horizontales y exactamente dos veces como vecinos verticales. -/
def IsQuasiComplete (L : Fin (Fintype.card G) → Fin (Fintype.card G) → G) : Prop :=
  ∀ x y : G, x ≠ y →
    (Finset.univ.filter fun p : Fin (Fintype.card G) × Fin (Fintype.card G) =>
        ∃ h : (p.2 : ℕ) + 1 < Fintype.card G, ({L p.1 p.2, L p.1 ⟨p.2 + 1, h⟩} : Finset G) = {x, y}).card = 2 ∧
    (Finset.univ.filter fun p : Fin (Fintype.card G) × Fin (Fintype.card G) =>
        ∃ h : (p.1 : ℕ) + 1 < Fintype.card G, ({L p.1 p.2, L ⟨p.1 + 1, h⟩ p.2} : Finset G) = {x, y}).card = 2

omit [Group G] [Fintype G] in
theorem pair_iff {u v x y : G} (hxy : x ≠ y) :
    ({u, v} : Finset G) = {x, y} ↔ (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
  constructor
  · intro h
    have hu : u ∈ ({x, y} : Finset G) := h ▸ by simp
    have hv : v ∈ ({x, y} : Finset G) := h ▸ by simp
    have hx : x ∈ ({u, v} : Finset G) := h ▸ by simp
    have hy : y ∈ ({u, v} : Finset G) := h ▸ by simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv hx hy
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp_all
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Finset.pair_comm _ _

/-- Horizontal ordered count. -/
theorem card_horiz (a b : Fin (Fintype.card G) ≃ G) (x y g : G) (hg : x⁻¹ * y = g) :
    (Finset.univ.filter fun p : Fin (Fintype.card G) × Fin (Fintype.card G) =>
        ∃ h : (p.2 : ℕ) + 1 < Fintype.card G,
          a p.1 * b p.2 = x ∧ a p.1 * b ⟨p.2 + 1, h⟩ = y).card = diffCount b g := by
  unfold diffCount
  refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨h, h1, h2⟩ := hp
    refine ⟨h, ?_⟩
    have e1 : b p.2 = (a p.1)⁻¹ * x := eq_inv_mul_of_mul_eq h1
    have e2 : b ⟨p.2 + 1, h⟩ = (a p.1)⁻¹ * y := eq_inv_mul_of_mul_eq h2
    rw [e1, e2, ← hg]; group
  · intro p hp q hq hpq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    obtain ⟨_, h1, _⟩ := hp
    obtain ⟨_, h1', _⟩ := hq
    have : a p.1 = a q.1 := by
      have e : b p.2 = b q.2 := by rw [hpq]
      have := h1.trans h1'.symm
      rwa [e, mul_left_inj] at this
    exact Prod.ext (a.injective this) hpq
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨h, hj⟩ := hj
    refine ⟨(a.symm (x * (b j)⁻¹), j), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨h, by simp, ?_⟩
    simp only [Equiv.apply_symm_apply]
    have e : b ⟨j + 1, h⟩ = b j * g := by rw [← hj]; group
    rw [e, ← hg]; group

/-- Vertical ordered count, for the list `a⁻¹`. -/
theorem card_vert (a b : Fin (Fintype.card G) ≃ G) (x y g : G) (hg : x * y⁻¹ = g) :
    (Finset.univ.filter fun p : Fin (Fintype.card G) × Fin (Fintype.card G) =>
        ∃ h : (p.1 : ℕ) + 1 < Fintype.card G,
          a p.1 * b p.2 = x ∧ a ⟨p.1 + 1, h⟩ * b p.2 = y).card
      = diffCount (a.trans (Equiv.inv G)) g := by
  unfold diffCount
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.trans_apply,
      Equiv.inv_apply] at hp ⊢
    obtain ⟨h, h1, h2⟩ := hp
    refine ⟨h, ?_⟩
    have e1 : a p.1 = x * (b p.2)⁻¹ := eq_mul_inv_of_mul_eq h1
    have e2 : a ⟨p.1 + 1, h⟩ = y * (b p.2)⁻¹ := eq_mul_inv_of_mul_eq h2
    rw [e1, e2, ← hg]; group
  · intro p hp q hq hpq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    obtain ⟨_, h1, _⟩ := hp
    obtain ⟨_, h1', _⟩ := hq
    have e : a p.1 = a q.1 := by rw [hpq]
    have := h1.trans h1'.symm
    rw [e, mul_right_inj] at this
    exact Prod.ext hpq (b.injective this)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.trans_apply,
      Equiv.inv_apply] at hi
    obtain ⟨h, hi⟩ := hi
    refine ⟨(i, b.symm ((a i)⁻¹ * x)), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨h, by simp, ?_⟩
    simp only [Equiv.apply_symm_apply]
    have hi' : a i * (a ⟨i + 1, h⟩)⁻¹ = g := by simpa using hi
    have e2 : a ⟨i + 1, h⟩ = g⁻¹ * a i := by
      rw [← hi']; group
    rw [e2, ← hg]; group

theorem horiz_count (a b : Fin (Fintype.card G) ≃ G) {x y : G} (hxy : x ≠ y) :
    (Finset.univ.filter fun p : Fin (Fintype.card G) × Fin (Fintype.card G) =>
        ∃ h : (p.2 : ℕ) + 1 < Fintype.card G,
          ({a p.1 * b p.2, a p.1 * b ⟨p.2 + 1, h⟩} : Finset G) = {x, y}).card
      = diffCount b (x⁻¹ * y) + diffCount b (y⁻¹ * x) := by
  rw [← card_horiz a b x y _ rfl, ← card_horiz a b y x _ rfl,
    ← Finset.card_union_of_disjoint]
  · congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨h, hp⟩
      rcases (pair_iff hxy).1 hp with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
    · rintro (⟨h, hp⟩ | ⟨h, hp⟩)
      · exact ⟨h, (pair_iff hxy).2 (Or.inl hp)⟩
      · exact ⟨h, (pair_iff hxy).2 (Or.inr hp)⟩
  · rw [Finset.disjoint_left]
    intro p hp hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    obtain ⟨h, h1, _⟩ := hp
    obtain ⟨h', h3, _⟩ := hq
    exact hxy (h1.symm.trans h3)

theorem vert_count (a b : Fin (Fintype.card G) ≃ G) {x y : G} (hxy : x ≠ y) :
    (Finset.univ.filter fun p : Fin (Fintype.card G) × Fin (Fintype.card G) =>
        ∃ h : (p.1 : ℕ) + 1 < Fintype.card G,
          ({a p.1 * b p.2, a ⟨p.1 + 1, h⟩ * b p.2} : Finset G) = {x, y}).card
      = diffCount (a.trans (Equiv.inv G)) (x * y⁻¹)
        + diffCount (a.trans (Equiv.inv G)) (y * x⁻¹) := by
  rw [← card_vert a b x y _ rfl, ← card_vert a b y x _ rfl,
    ← Finset.card_union_of_disjoint]
  · congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨h, hp⟩
      rcases (pair_iff hxy).1 hp with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
    · rintro (⟨h, hp⟩ | ⟨h, hp⟩)
      · exact ⟨h, (pair_iff hxy).2 (Or.inl hp)⟩
      · exact ⟨h, (pair_iff hxy).2 (Or.inr hp)⟩
  · rw [Finset.disjoint_left]
    intro p hp hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    obtain ⟨h, h1, _⟩ := hp
    obtain ⟨h', h3, _⟩ := hq
    exact hxy (h1.symm.trans h3)

theorem quasiComplete_iff (a b : Fin (Fintype.card G) ≃ G) :
    IsQuasiComplete (fun i j => a i * b j) ↔ IsTerrace (a.trans (Equiv.inv G)) ∧ IsTerrace b := by
  constructor
  · intro hq
    constructor
    · intro g hg
      have hne : g ≠ 1 := hg
      have h := (hq g 1 hne).2
      rw [vert_count a b hne] at h
      simpa using h
    · intro g hg
      have h := (hq 1 g (Ne.symm hg)).1
      rw [horiz_count a b (Ne.symm hg)] at h
      simpa using h
  · rintro ⟨ha, hb⟩ x y hxy
    refine ⟨?_, ?_⟩
    · rw [horiz_count a b hxy]
      have := hb (x⁻¹ * y) (by simpa [inv_mul_eq_one] using hxy)
      simpa using this
    · rw [vert_count a b hxy]
      have := ha (x * y⁻¹) (by simpa [mul_inv_eq_one] using hxy)
      simpa using this

end Bailey


end
