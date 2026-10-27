/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum

/-!
# A tripartite Turán theorem

If three vertex sets `A, B, C` of a graph have pairwise edge densities `α = d(A, B)`, `β = d(B, C)`,
`γ = d(A, C)` with `αβ + γ > 1`, `βγ + α > 1` and `γα + β > 1`, the graph contains a triangle with
one vertex in each set (Bondy–Shen–Thomassé–Thomassen, 2006); in particular this holds when all
three densities exceed `1/φ`, since `(1/φ)² + 1/φ = 1`, and `1/φ` is optimal. The sets need not be
disjoint. Following the paper, a minimal weighted counterexample is reduced, by a Pareto argument on
the neighbourhoods, to parts with at most two strictly incomparable vertices; the remaining
configurations are closed by explicit inequalities (the final matching case is closed directly by
linear arithmetic here rather than as in the paper).

## Main results

* `TripartiteTuran.exists_triangle_of_mul_add`: densities with alpha*beta + gamma > 1 (and cyclic) force a triangle
* `TripartiteTuran.exists_triangle`: all three densities above 1/phi force a triangle

## References

* J. A. Bondy, J. Shen, S. Thomassé and C. Thomassen, *Density conditions for triangles in multipartite graphs*, Combinatorica 26 (2006), 121–131 (Theorem 3).
-/

@[expose] public section

open Finset

namespace TripartiteTuran

variable {V : Type*}

/-- Weight of the neighbourhood of `x` inside `Y` for the weight function `q`. -/
noncomputable def nbw (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) (Y : Finset V) (q : V → ℝ) : ℝ :=
  ∑ y ∈ Y, if G.Adj x y then q y else 0

/-- Weighted edge density between `X` (weights `p`) and `Y` (weights `q`). -/
noncomputable def dd (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) (p q : V → ℝ) : ℝ :=
  ∑ x ∈ X, p x * nbw G x Y q

/-- A cyclic triple of densities. -/
def Cyc (α β γ : ℝ) : Prop := 1 < α * β + γ ∧ 1 < β * γ + α ∧ 1 < γ * α + β

/-- No triangle with one vertex in each of `A`, `B`, `C`. -/
def NoTri (G : SimpleGraph V) (A B C : Finset V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ C, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj a c)

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem dd_comm (X Y : Finset V) (p q : V → ℝ) : dd G X Y p q = dd G Y X q p := by
  unfold dd nbw
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  by_cases h : G.Adj x y
  · simp [h, G.adj_comm y x, mul_comm]
  · simp [h, G.adj_comm y x]

theorem nbw_nonneg (x : V) (Y : Finset V) (q : V → ℝ) (hq : ∀ y ∈ Y, 0 ≤ q y) : 0 ≤ nbw G x Y q := by
  unfold nbw
  exact Finset.sum_nonneg fun y hy => by split_ifs <;> simp [hq y hy]

theorem dd_nonneg (X Y : Finset V) (p q : V → ℝ) (hp : ∀ x ∈ X, 0 ≤ p x) (hq : ∀ y ∈ Y, 0 ≤ q y) :
    0 ≤ dd G X Y p q :=
  Finset.sum_nonneg fun x hx => mul_nonneg (hp x hx) (nbw_nonneg G x Y q hq)

theorem Cyc.rot {α β γ : ℝ} (h : Cyc α β γ) : Cyc β γ α := ⟨h.2.1, h.2.2, h.1⟩

theorem Cyc.swap {α β γ : ℝ} (h : Cyc α β γ) : Cyc α γ β :=
  ⟨by linarith [h.2.2], by linarith [h.2.1], by linarith [h.1]⟩

theorem Cyc.mono {α β γ α' γ' : ℝ} (h : Cyc α β γ) (hβ : 0 ≤ β) (h0α : 0 ≤ α) (h0γ : 0 ≤ γ)
    (hα : α ≤ α') (hγ : γ ≤ γ') : Cyc α' β γ' := by
  obtain ⟨h1, h2, h3⟩ := h
  have e1 := mul_le_mul_of_nonneg_right hα hβ
  have e2 := mul_le_mul_of_nonneg_left hγ hβ
  have e3 := mul_le_mul hγ hα h0α (le_trans h0γ hγ)
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- Any real `2 × 2` matrix has a nonzero vector `(a, b)` with nonnegative image. -/
theorem exists_kernel (u v u' v' : ℝ) :
    ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ 0 ≤ a * u + b * v ∧ 0 ≤ a * u' + b * v' := by
  by_cases hD : u * v' - v * u' = 0
  · by_cases h1 : v ≠ 0 ∨ u ≠ 0
    · refine ⟨v, -u, ?_, ?_, ?_⟩
      · rcases h1 with h | h
        · exact Or.inl h
        · exact Or.inr (neg_ne_zero.mpr h)
      · exact le_of_eq (by ring)
      · linarith [hD]
    · push Not at h1
      obtain ⟨hv, hu⟩ := h1
      by_cases h2 : v' ≠ 0 ∨ u' ≠ 0
      · refine ⟨v', -u', ?_, ?_, ?_⟩
        · rcases h2 with h | h
          · exact Or.inl h
          · exact Or.inr (neg_ne_zero.mpr h)
        · subst hv; subst hu; simp
        · exact le_of_eq (by ring)
      · push Not at h2
        obtain ⟨hv', hu'⟩ := h2
        refine ⟨1, 0, Or.inl one_ne_zero, ?_, ?_⟩
        · subst hu; simp
        · subst hu'; simp
  · have hD : u * v' - v * u' ≠ 0 := hD
    have e1 : (v' - v) / (u * v' - v * u') * u + (u - u') / (u * v' - v * u') * v = 1 := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_one_iff_eq hD]; ring
    have e2 : (v' - v) / (u * v' - v * u') * u' + (u - u') / (u * v' - v * u') * v' = 1 := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_one_iff_eq hD]; ring
    refine ⟨(v' - v) / (u * v' - v * u'), (u - u') / (u * v' - v * u'), ?_, ?_, ?_⟩
    · by_contra hcon
      push Not at hcon
      obtain ⟨h1, h2⟩ := hcon
      rw [h1, h2] at e1
      simp at e1
    · rw [e1]; norm_num
    · rw [e2]; norm_num

section Reduce

variable [DecidableEq V]

theorem pareto3 (s : Finset V) (p f g : V → ℝ) (hp : ∀ i ∈ s, 0 ≤ p i) (hs : ∑ i ∈ s, p i = 1)
    (h3 : 3 ≤ s.card) :
    ∃ i ∈ s, ∃ p' : V → ℝ, (∀ x ∈ s.erase i, 0 ≤ p' x) ∧ ∑ x ∈ s.erase i, p' x = 1 ∧
      ∑ x ∈ s, p x * f x ≤ ∑ x ∈ s.erase i, p' x * f x ∧
      ∑ x ∈ s, p x * g x ≤ ∑ x ∈ s.erase i, p' x * g x := by
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.mp (by omega : 2 < s.card)
  obtain ⟨a, b, hab, h1, h2⟩ := exists_kernel (f x - f z) (f y - f z) (g x - g z) (g y - g z)
  let c : ℝ := -a - b
  let μ : V → ℝ := fun w => (if w = x then a else 0) + (if w = y then b else 0) + (if w = z then c else 0)
  have hμ : ∀ h : V → ℝ, ∑ w ∈ s, μ w * h w = a * h x + b * h y + c * h z := by
    intro h
    simp only [μ, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
    simp [Finset.sum_ite_eq', hx, hy, hz]
  have hμ1 : ∑ w ∈ s, μ w = 0 := by
    have := hμ (fun _ => 1)
    simp only [mul_one] at this
    rw [this]; simp only [c]; ring
  have hμf : 0 ≤ ∑ w ∈ s, μ w * f w := by
    rw [hμ]; simp only [c]; nlinarith [h1]
  have hμg : 0 ≤ ∑ w ∈ s, μ w * g w := by
    rw [hμ]; simp only [c]; nlinarith [h2]
  have hneg : ∃ w ∈ s, μ w < 0 := by
    by_contra hcon
    push Not at hcon
    have hz0 := (Finset.sum_eq_zero_iff_of_nonneg hcon).mp hμ1
    have e1 : μ x = 0 := hz0 x hx
    have e2 : μ y = 0 := hz0 y hy
    have : μ x = a := by simp [μ, hxy, hxz]
    have : μ y = b := by simp [μ, hxy.symm, hyz]
    rcases hab with h | h <;> simp_all
  obtain ⟨w0, hw0s, hw0⟩ := hneg
  have hN : (s.filter (fun w => μ w < 0)).Nonempty := ⟨w0, by simp [hw0s, hw0]⟩
  obtain ⟨i0, hi0N, hmin⟩ := Finset.exists_min_image _ (fun w => p w / (-μ w)) hN
  rw [Finset.mem_filter] at hi0N
  obtain ⟨hi0s, hi0neg⟩ := hi0N
  set t : ℝ := p i0 / (-μ i0) with ht
  have ht0 : 0 ≤ t := div_nonneg (hp i0 hi0s) (by linarith)
  have ht1 : t * (-μ i0) = p i0 := by rw [ht]; exact div_mul_cancel₀ _ (by linarith)
  refine ⟨i0, hi0s, fun w => p w + t * μ w, ?_, ?_, ?_, ?_⟩
  · intro w hw
    have hws := Finset.mem_of_mem_erase hw
    by_cases hm : 0 ≤ μ w
    · exact add_nonneg (hp w hws) (mul_nonneg ht0 hm)
    · push Not at hm
      have := hmin w (by rw [Finset.mem_filter]; exact ⟨hws, hm⟩)
      have h' : t * (-μ w) ≤ p w := by
        have := (le_div_iff₀ (by linarith : 0 < -μ w)).mp this
        exact this
      linarith
  · have hlin : ∑ w ∈ s, (p w + t * μ w) = ∑ w ∈ s, p w + t * ∑ w ∈ s, μ w := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_erase_eq_sub hi0s, hlin, hμ1, hs]
    nlinarith [ht1]
  · have hlin : ∑ w ∈ s, (p w + t * μ w) * f w = ∑ w ∈ s, p w * f w + t * ∑ w ∈ s, μ w * f w := by
      simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [Finset.sum_erase_eq_sub hi0s, hlin]
    have h0 : p i0 + t * μ i0 = 0 := by linarith [ht1]
    show _ ≤ _ - (p i0 + t * μ i0) * f i0
    rw [h0, zero_mul]
    nlinarith [mul_nonneg ht0 hμf]
  · have hlin : ∑ w ∈ s, (p w + t * μ w) * g w = ∑ w ∈ s, p w * g w + t * ∑ w ∈ s, μ w * g w := by
      simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [Finset.sum_erase_eq_sub hi0s, hlin]
    have h0 : p i0 + t * μ i0 = 0 := by linarith [ht1]
    show _ ≤ _ - (p i0 + t * μ i0) * g i0
    rw [h0, zero_mul]
    nlinarith [mul_nonneg ht0 hμg]

theorem dom_reduce (s : Finset V) (p f g : V → ℝ) (hp : ∀ i ∈ s, 0 ≤ p i) (hs : ∑ i ∈ s, p i = 1)
    (i j : V) (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    (h1 : p i * f i ≤ p i * f j) (h2 : p i * g i ≤ p i * g j) :
    ∃ p' : V → ℝ, (∀ x ∈ s.erase i, 0 ≤ p' x) ∧ ∑ x ∈ s.erase i, p' x = 1 ∧
      ∑ x ∈ s, p x * f x ≤ ∑ x ∈ s.erase i, p' x * f x ∧
      ∑ x ∈ s, p x * g x ≤ ∑ x ∈ s.erase i, p' x * g x := by
  have hjs : j ∈ s.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
  have key : ∀ h : V → ℝ, ∑ x ∈ s.erase i, (if x = j then p j + p i else p x) * h x
      = ∑ x ∈ s, p x * h x - p i * h i + p i * h j := by
    intro h
    have e : ∀ x, (if x = j then p j + p i else p x) * h x
        = p x * h x + (if x = j then p i * h j else 0) := by
      intro x
      by_cases hx : x = j
      · subst hx; simp; ring
      · simp [hx]
    simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', hjs]
    rw [Finset.sum_erase_eq_sub hi]
    simp
  refine ⟨fun x => if x = j then p j + p i else p x, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxs := Finset.mem_of_mem_erase hx
    by_cases hxj : x = j
    · simp only [hxj, ite_true]; exact add_nonneg (hp j hj) (hp i hi)
    · simp only [hxj, ite_false]; exact hp x hxs
  · have := key (fun _ => 1)
    simp only [mul_one] at this
    rw [this, hs]; ring
  · rw [key f]; linarith
  · rw [key g]; linarith

theorem reduce_sum (s : Finset V) (p f g : V → ℝ) (hp : ∀ i ∈ s, 0 ≤ p i) (hs : ∑ i ∈ s, p i = 1)
    (hred : 3 ≤ s.card ∨ ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ p i * f i ≤ p i * f j ∧ p i * g i ≤ p i * g j) :
    ∃ i ∈ s, ∃ p' : V → ℝ, (∀ x ∈ s.erase i, 0 ≤ p' x) ∧ ∑ x ∈ s.erase i, p' x = 1 ∧
      ∑ x ∈ s, p x * f x ≤ ∑ x ∈ s.erase i, p' x * f x ∧
      ∑ x ∈ s, p x * g x ≤ ∑ x ∈ s.erase i, p' x * g x := by
  rcases hred with h | ⟨i, hi, j, hj, hij, h1, h2⟩
  · exact pareto3 s p f g hp hs h
  · obtain ⟨p', hp', hs', hf, hg⟩ := dom_reduce s p f g hp hs i j hi hj hij h1 h2
    exact ⟨i, hi, p', hp', hs', hf, hg⟩

end Reduce

/-- A weighted tripartite configuration: triangle-free and cyclic. -/
structure Good (A B C : Finset V) (p q r : V → ℝ) : Prop where
  neA : A.Nonempty
  neB : B.Nonempty
  neC : C.Nonempty
  pA : ∀ a ∈ A, 0 ≤ p a
  qB : ∀ b ∈ B, 0 ≤ q b
  rC : ∀ c ∈ C, 0 ≤ r c
  sA : ∑ a ∈ A, p a = 1
  sB : ∑ b ∈ B, q b = 1
  sC : ∑ c ∈ C, r c = 1
  nt : NoTri G A B C
  cyc : Cyc (dd G A B p q) (dd G B C q r) (dd G A C p r)

variable {G}

/-- The part `s` (weights `p`, other parts `Y`, `Z`) can be shrunk: it has `≥ 3` vertices, or some vertex
`i` is dominated by another one `j` (weighted by `p i`). -/
def Red (s : Finset V) (p : V → ℝ) (Y : Finset V) (q : V → ℝ) (Z : Finset V) (r : V → ℝ) : Prop :=
  3 ≤ s.card ∨ ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ p i * nbw G i Y q ≤ p i * nbw G j Y q ∧
    p i * nbw G i Z r ≤ p i * nbw G j Z r

theorem Good.reduce [DecidableEq V] {A B C : Finset V} {p q r : V → ℝ} (h : Good G A B C p q r)
    (hr : Red (G := G) A p B q C r) :
    ∃ (A' : Finset V) (p' : V → ℝ), A'.card < A.card ∧ Good G A' B C p' q r := by
  obtain ⟨i, hi, p', hp', hs', hf, hg⟩ := reduce_sum A p (fun a => nbw G a B q) (fun a => nbw G a C r)
    h.pA h.sA hr
  have hne : (A.erase i).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    rw [hcon] at hs'
    simp at hs'
  refine ⟨A.erase i, p', Finset.card_erase_lt_of_mem hi, ?_⟩
  exact
    { neA := hne
      neB := h.neB
      neC := h.neC
      pA := hp'
      qB := h.qB
      rC := h.rC
      sA := hs'
      sB := h.sB
      sC := h.sC
      nt := fun a ha => h.nt a (Finset.mem_of_mem_erase ha)
      cyc := Cyc.mono h.cyc (dd_nonneg G B C q r h.qB h.rC) (dd_nonneg G A B p q h.pA h.qB)
        (dd_nonneg G A C p r h.pA h.rC) hf hg }

theorem Good.rot {A B C : Finset V} {p q r : V → ℝ} (h : Good G A B C p q r) :
    Good G B C A q r p where
  neA := h.neB
  neB := h.neC
  neC := h.neA
  pA := h.qB
  qB := h.rC
  rC := h.pA
  sA := h.sB
  sB := h.sC
  sC := h.sA
  nt := fun b hb c hc a ha ⟨h1, h2, h3⟩ => h.nt a ha b hb c hc ⟨h3.symm, h1, h2.symm⟩
  cyc := by
    have := h.cyc.rot
    rwa [dd_comm G A C p r, dd_comm G A B p q] at this

theorem Good.swap {A B C : Finset V} {p q r : V → ℝ} (h : Good G A B C p q r) :
    Good G B A C q p r where
  neA := h.neB
  neB := h.neA
  neC := h.neC
  pA := h.qB
  qB := h.pA
  rC := h.rC
  sA := h.sB
  sB := h.sA
  sC := h.sC
  nt := fun b hb a ha c hc ⟨h1, h2, h3⟩ => h.nt a ha b hb c hc ⟨h1.symm, h3, h2⟩
  cyc := by
    have := h.cyc.swap
    rwa [dd_comm G A B p q] at this

theorem nbw_le_sum (x : V) (Y : Finset V) (q : V → ℝ) (hq : ∀ y ∈ Y, 0 ≤ q y) :
    nbw G x Y q ≤ ∑ y ∈ Y, q y :=
  Finset.sum_le_sum fun y hy => by
    split_ifs
    · exact le_rfl
    · exact hq y hy

theorem nbw_add_le {a b : V} (hab : G.Adj a b) (C : Finset V) (r : V → ℝ) (hr : ∀ c ∈ C, 0 ≤ r c)
    (hnt : ∀ c ∈ C, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj a c)) :
    nbw G a C r + nbw G b C r ≤ ∑ c ∈ C, r c := by
  unfold nbw
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun c hc => ?_
  by_cases h1 : G.Adj a c
  · by_cases h2 : G.Adj b c
    · exact absurd ⟨hab, h2, h1⟩ (hnt c hc)
    · simp [h1, h2]
  · by_cases h2 : G.Adj b c
    · simp [h1, h2]
    · simp [h1, h2, hr c hc]

/-- Algebra of case 2 of BSTT: a vertex `b₂` of `B = {b₁, b₂}` without neighbours in `C`. -/
theorem case2_alg (α β γ b a c : ℝ) (hb0 : 0 < b) (hb1 : b < 1) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hβ : β = b * c) (hα : α ≤ b * a + (1 - b)) (hγ : γ ≤ 1 - a * c)
    (h1 : 1 < α * β + γ) (h2 : 1 < β * γ + α) : False := by
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have hX : β * γ + α - 1 ≤ b * c * (1 - a * c) + (b * a + (1 - b)) - 1 := by
    have := mul_le_mul_of_nonneg_left hγ hβ0
    rw [hβ] at this ⊢
    nlinarith
  have hY : α * β + γ - 1 ≤ b * c * (b * a + (1 - b)) + (1 - a * c) - 1 := by
    have := mul_le_mul_of_nonneg_right hα hβ0
    rw [hβ] at this ⊢
    nlinarith
  have k1 : 0 ≤ c * (1 - b) := mul_nonneg hc0 (by linarith)
  have k2 : 0 ≤ b * (1 - c) := mul_nonneg hb0.le (by linarith)
  have hE : c * (1 - b) * (β * γ + α - 1) + b * (1 - c) * (α * β + γ - 1)
      ≤ b * c * (1 - b) * (1 - c) * ((a - 1) * (1 - b) - a * (1 - c)) := by
    have e := mul_le_mul_of_nonneg_left hX k1
    have e' := mul_le_mul_of_nonneg_left hY k2
    nlinarith
  have hneg : b * c * (1 - b) * (1 - c) * ((a - 1) * (1 - b) - a * (1 - c)) ≤ 0 := by
    have : (a - 1) * (1 - b) - a * (1 - c) ≤ 0 := by nlinarith
    have h0 : 0 ≤ b * c * (1 - b) * (1 - c) := by
      have : 0 ≤ 1 - b := by linarith
      have : 0 ≤ 1 - c := by linarith
      positivity
    exact mul_nonpos_of_nonneg_of_nonpos h0 this
  have hpos : 0 < c * (1 - b) * (β * γ + α - 1) + b * (1 - c) * (α * β + γ - 1) := by
    by_cases hc : c = 1
    · have : 0 < c * (1 - b) := by rw [hc]; linarith
      have : 0 < β * γ + α - 1 := by linarith
      have : 0 ≤ b * (1 - c) * (α * β + γ - 1) := mul_nonneg k2 (by linarith)
      nlinarith [mul_pos ‹0 < c * (1 - b)› ‹0 < β * γ + α - 1›]
    · have hc' : c < 1 := lt_of_le_of_ne hc1 hc
      have : 0 < b * (1 - c) := mul_pos hb0 (by linarith)
      have : 0 < α * β + γ - 1 := by linarith
      have : 0 ≤ c * (1 - b) * (β * γ + α - 1) := mul_nonneg k1 (by linarith)
      nlinarith [mul_pos ‹0 < b * (1 - c)› ‹0 < α * β + γ - 1›]
  linarith

theorem Good.no_missing {A B C : Finset V} {p q r : V → ℝ} [DecidableEq V] (h : Good G A B C p q r)
    (b1 b2 : V) (hB : B = {b1, b2}) (hne : b1 ≠ b2) (hq1 : 0 < q b1) (hq2 : 0 < q b2)
    (hn : ∀ c ∈ C, ¬ G.Adj b2 c) : False := by
  subst hB
  have hsB : q b1 + q b2 = 1 := by
    have := h.sB
    rwa [Finset.sum_pair hne] at this
  have hb1 : q b1 < 1 := by linarith
  have hcN0 : 0 ≤ nbw G b1 C r := nbw_nonneg G b1 C r h.rC
  have hcN1 : nbw G b1 C r ≤ 1 := h.sC ▸ nbw_le_sum b1 C r h.rC
  have haN0 : 0 ≤ nbw G b1 A p := nbw_nonneg G b1 A p h.pA
  have haN1 : nbw G b1 A p ≤ 1 := h.sA ▸ nbw_le_sum b1 A p h.pA
  have hn0 : nbw G b2 C r = 0 := Finset.sum_eq_zero fun c hc => by simp [hn c hc]
  have hβ : dd G {b1, b2} C q r = q b1 * nbw G b1 C r := by
    unfold dd
    rw [Finset.sum_pair hne, hn0]; ring
  have hα : dd G A {b1, b2} p q ≤ nbw G b1 A p * q b1 + (1 - q b1) := by
    rw [dd_comm G A _ p q]
    unfold dd
    rw [Finset.sum_pair hne]
    have h2 : nbw G b2 A p ≤ 1 := h.sA ▸ nbw_le_sum b2 A p h.pA
    nlinarith
  have hγ : dd G A C p r ≤ 1 - nbw G b1 A p * nbw G b1 C r := by
    have hterm : ∀ a ∈ A, p a * nbw G a C r ≤ p a - (if G.Adj b1 a then p a else 0) * nbw G b1 C r := by
      intro a ha
      have hpa := h.pA a ha
      have hle : nbw G a C r ≤ 1 := h.sC ▸ nbw_le_sum a C r h.rC
      by_cases hadj : G.Adj b1 a
      · have := nbw_add_le (G := G) hadj.symm C r h.rC (fun c hc hh =>
          h.nt a ha b1 (Finset.mem_insert_self _ _) c hc ⟨hh.1, hh.2.1, hh.2.2⟩)
        rw [h.sC] at this
        simp only [hadj, ite_true]
        nlinarith [mul_nonneg hpa (by linarith : 0 ≤ 1 - nbw G a C r - nbw G b1 C r)]
      · simp only [hadj, ite_false]
        nlinarith
    have hsum := Finset.sum_le_sum hterm
    have e : ∑ a ∈ A, (p a - (if G.Adj b1 a then p a else 0) * nbw G b1 C r)
        = 1 - nbw G b1 A p * nbw G b1 C r := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, h.sA]
      rfl
    unfold dd
    linarith
  exact case2_alg (dd G A {b1, b2} p q) (dd G {b1, b2} C q r) (dd G A C p r) (q b1) (nbw G b1 A p)
    (nbw G b1 C r) hq1 hb1 haN0 haN1 hcN0 hcN1 hβ (by linarith) hγ
    h.cyc.1 h.cyc.2.1

/-- A part consisting of one vertex cannot occur. -/
theorem Good.card_C_ne_one {A B C : Finset V} {p q r : V → ℝ} (h : Good G A B C p q r) :
    C.card ≠ 1 := by
  intro hc
  obtain ⟨c, rfl⟩ := Finset.card_eq_one.mp hc
  have hrc : r c = 1 := by simpa using h.sC
  have hβ : dd G B {c} q r = ∑ b ∈ B, (if G.Adj b c then q b else 0) := by
    unfold dd nbw
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [hrc]
  have hγ : dd G A {c} p r = ∑ a ∈ A, (if G.Adj a c then p a else 0) := by
    unfold dd nbw
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [hrc]
  have hα : dd G A B p q ≤ 1 - (∑ a ∈ A, (if G.Adj a c then p a else 0)) *
      (∑ b ∈ B, (if G.Adj b c then q b else 0)) := by
    have hterm : ∀ a ∈ A, ∀ b ∈ B, p a * (if G.Adj a b then q b else 0)
        ≤ p a * q b - (if G.Adj a c then p a else 0) * (if G.Adj b c then q b else 0) := by
      intro a ha b hb
      have hpa := h.pA a ha
      have hqb := h.qB b hb
      by_cases h1 : G.Adj a b
      · by_cases h2 : G.Adj a c
        · by_cases h3 : G.Adj b c
          · exact absurd ⟨h1, h3, h2⟩ (h.nt a ha b hb c (Finset.mem_singleton_self c))
          · simp [h1, h2, h3]
        · simp [h1, h2]
      · by_cases h2 : G.Adj a c
        · by_cases h3 : G.Adj b c
          · simp [h1, h2, h3]
          · simp [h1, h2, h3, mul_nonneg hpa hqb]
        · simp [h1, h2, mul_nonneg hpa hqb]
    have hs : ∑ a ∈ A, ∑ b ∈ B, p a * (if G.Adj a b then q b else 0)
        ≤ ∑ a ∈ A, ∑ b ∈ B, (p a * q b - (if G.Adj a c then p a else 0) * (if G.Adj b c then q b else 0)) :=
      Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hterm a ha b hb
    have e : ∑ a ∈ A, ∑ b ∈ B, (p a * q b - (if G.Adj a c then p a else 0) * (if G.Adj b c then q b else 0))
        = 1 - (∑ a ∈ A, (if G.Adj a c then p a else 0)) * (∑ b ∈ B, (if G.Adj b c then q b else 0)) := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, h.sA, h.sB]
      ring
    have e2 : dd G A B p q = ∑ a ∈ A, ∑ b ∈ B, p a * (if G.Adj a b then q b else 0) := by
      unfold dd nbw
      simp only [Finset.mul_sum]
    linarith
  have := h.cyc.2.1
  rw [hβ, hγ] at this
  nlinarith [hα]

theorem Red_comm {s : Finset V} {p : V → ℝ} {Y Z : Finset V} {q r : V → ℝ} :
    Red (G := G) s p Y q Z r ↔ Red (G := G) s p Z r Y q := by
  unfold Red
  constructor <;> rintro (h | ⟨i, hi, j, hj, hij, h1, h2⟩)
  · exact Or.inl h
  · exact Or.inr ⟨i, hi, j, hj, hij, h2, h1⟩
  · exact Or.inl h
  · exact Or.inr ⟨i, hi, j, hj, hij, h2, h1⟩

theorem incomp (pi pj fi fj gi gj : ℝ) (hpi : 0 ≤ pi) (hpj : 0 ≤ pj)
    (h1 : ¬(pi * fi ≤ pi * fj ∧ pi * gi ≤ pi * gj)) (h2 : ¬(pj * fj ≤ pj * fi ∧ pj * gj ≤ pj * gi)) :
    0 < pi ∧ 0 < pj ∧ ((fi < fj ∧ gj < gi) ∨ (fj < fi ∧ gi < gj)) := by
  have hpi' : 0 < pi := by
    rcases hpi.lt_or_eq with h | h
    · exact h
    · exfalso; apply h1; rw [← h]; simp
  have hpj' : 0 < pj := by
    rcases hpj.lt_or_eq with h | h
    · exact h
    · exfalso; apply h2; rw [← h]; simp
  refine ⟨hpi', hpj', ?_⟩
  have e1 : fj < fi ∨ gj < gi := by
    by_contra hc
    push Not at hc
    exact h1 ⟨mul_le_mul_of_nonneg_left hc.1 hpi, mul_le_mul_of_nonneg_left hc.2 hpi⟩
  have e2 : fi < fj ∨ gi < gj := by
    by_contra hc
    push Not at hc
    exact h2 ⟨mul_le_mul_of_nonneg_left hc.1 hpj, mul_le_mul_of_nonneg_left hc.2 hpj⟩
  rcases e1 with a | a <;> rcases e2 with b | b
  · exact absurd (lt_trans a b) (lt_irrefl _)
  · exact Or.inr ⟨a, b⟩
  · exact Or.inl ⟨b, a⟩
  · exact absurd (lt_trans a b) (lt_irrefl _)

theorem irred_pair {s : Finset V} {p : V → ℝ} {Y Z : Finset V} {q r : V → ℝ}
    (hnr : ¬ Red (G := G) s p Y q Z r) (hp : ∀ i ∈ s, 0 ≤ p i) {x y : V} (hx : x ∈ s) (hy : y ∈ s)
    (hxy : x ≠ y) :
    0 < p x ∧ 0 < p y ∧ ((nbw G x Y q < nbw G y Y q ∧ nbw G y Z r < nbw G x Z r) ∨
      (nbw G y Y q < nbw G x Y q ∧ nbw G x Z r < nbw G y Z r)) :=
  incomp _ _ _ _ _ _ (hp x hx) (hp y hy)
    (fun hd => hnr (Or.inr ⟨x, hx, y, hy, hxy, hd.1, hd.2⟩))
    (fun hd => hnr (Or.inr ⟨y, hy, x, hx, hxy.symm, hd.1, hd.2⟩))

theorem Good.has_nbr [DecidableEq V] {A B C : Finset V} {p q r : V → ℝ} (h : Good G A B C p q r)
    (hnr : ¬ Red (G := G) B q C r A p) (hB2 : B.card = 2) : ∀ b ∈ B, ∃ c ∈ C, G.Adj b c := by
  intro b hb
  by_contra hcon
  push Not at hcon
  obtain ⟨x, y, hxy, hBxy⟩ := Finset.card_eq_two.mp hB2
  have hxB : x ∈ B := by rw [hBxy]; simp
  have hyB : y ∈ B := by rw [hBxy]; simp
  obtain ⟨hpx, hpy, -⟩ := irred_pair hnr h.qB hxB hyB hxy
  rw [hBxy] at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with hb | hb
  · rw [hb] at hcon
    exact h.no_missing y x (by rw [hBxy, Finset.pair_comm]) hxy.symm hpy hpx hcon
  · rw [hb] at hcon
    exact h.no_missing x y hBxy hxy hpx hpy hcon

theorem Good.no_full_core [DecidableEq V] {A B C : Finset V} {p q r : V → ℝ} (h : Good G A B C p q r)
    {a b1 b2 c0 : V} (ha : a ∈ A) (hb1 : b1 ∈ B) (hb2 : b2 ∈ B) (hC2 : C.card = 2) (hc0 : c0 ∈ C)
    (hac0 : G.Adj a c0) (hf1 : G.Adj a b1) (hf2 : G.Adj a b2) (hn1 : ∃ c ∈ C, G.Adj b1 c)
    (hn2 : ∃ c ∈ C, G.Adj b2 c)
    (hrig1 : ¬(q b1 * nbw G b1 C r ≤ q b1 * nbw G b2 C r ∧ q b1 * nbw G b1 A p ≤ q b1 * nbw G b2 A p))
    (hrig2 : ¬(q b2 * nbw G b2 C r ≤ q b2 * nbw G b1 C r ∧ q b2 * nbw G b2 A p ≤ q b2 * nbw G b1 A p)) :
    False := by
  have hnb1 : ¬ G.Adj b1 c0 := fun hbc => h.nt a ha b1 hb1 c0 hc0 ⟨hf1, hbc, hac0⟩
  have hnb2 : ¬ G.Adj b2 c0 := fun hbc => h.nt a ha b2 hb2 c0 hc0 ⟨hf2, hbc, hac0⟩
  have hC1 : (C.erase c0).card = 1 := by rw [Finset.card_erase_of_mem hc0, hC2]
  have hone := Finset.card_le_one.mp hC1.le
  have hEq : nbw G b1 C r = nbw G b2 C r := by
    unfold nbw
    refine Finset.sum_congr rfl fun c hc => ?_
    by_cases hcc : c = c0
    · subst hcc; simp [hnb1, hnb2]
    · obtain ⟨c1, hc1, hbc1⟩ := hn1
      obtain ⟨c2, hc2, hbc2⟩ := hn2
      have hc1' : c1 ∈ C.erase c0 := Finset.mem_erase.mpr ⟨fun e => hnb1 (e ▸ hbc1), hc1⟩
      have hc2' : c2 ∈ C.erase c0 := Finset.mem_erase.mpr ⟨fun e => hnb2 (e ▸ hbc2), hc2⟩
      have hcm : c ∈ C.erase c0 := Finset.mem_erase.mpr ⟨hcc, hc⟩
      have e1 := hone c1 hc1' c hcm
      have e2 := hone c2 hc2' c hcm
      subst e1; subst e2
      simp [hbc1, hbc2]
  have k1 : ¬ (q b1 * nbw G b1 A p ≤ q b1 * nbw G b2 A p) := fun hle =>
    hrig1 ⟨by rw [hEq], hle⟩
  have k2 : ¬ (q b2 * nbw G b2 A p ≤ q b2 * nbw G b1 A p) := fun hle =>
    hrig2 ⟨by rw [hEq], hle⟩
  have l1 : nbw G b2 A p < nbw G b1 A p := by
    by_contra hc
    push Not at hc
    exact k1 (mul_le_mul_of_nonneg_left hc (h.qB b1 hb1))
  have l2 : nbw G b1 A p < nbw G b2 A p := by
    by_contra hc
    push Not at hc
    exact k2 (mul_le_mul_of_nonneg_left hc (h.qB b2 hb2))
  linarith

theorem Good.no_full [DecidableEq V] {A B C : Finset V} {p q r : V → ℝ} (h : Good G A B C p q r)
    (hnr : ¬ Red (G := G) B q C r A p) (hB2 : B.card = 2) (hC2 : C.card = 2)
    (hbc : ∀ b ∈ B, ∃ c ∈ C, G.Adj b c) (hac : ∀ a ∈ A, ∃ c ∈ C, G.Adj a c) :
    ∀ a ∈ A, ∃ b ∈ B, ¬ G.Adj a b := by
  intro a ha
  by_contra hcon
  push Not at hcon
  obtain ⟨x, y, hxy, hBxy⟩ := Finset.card_eq_two.mp hB2
  have hxB : x ∈ B := by rw [hBxy]; simp
  have hyB : y ∈ B := by rw [hBxy]; simp
  obtain ⟨c0, hc0, hac0⟩ := hac a ha
  exact h.no_full_core ha hxB hyB hC2 hc0 hac0 (hcon x hxB) (hcon y hyB) (hbc x hxB) (hbc y hyB)
    (fun hd => hnr (Or.inr ⟨x, hxB, y, hyB, hxy, hd.1, hd.2⟩))
    (fun hd => hnr (Or.inr ⟨y, hyB, x, hxB, hxy.symm, hd.1, hd.2⟩))

omit [DecidableRel G.Adj] in
theorem pair_fact [DecidableEq V] {Y : Finset V} {y1 y2 x : V} (hY : Y = {y1, y2})
    (hex : ∃ y ∈ Y, G.Adj x y) (hnf : ∃ y ∈ Y, ¬ G.Adj x y) :
    (G.Adj x y1 ∧ ¬ G.Adj x y2) ∨ (¬ G.Adj x y1 ∧ G.Adj x y2) := by
  subst hY
  obtain ⟨y, hy, h1⟩ := hex
  obtain ⟨z, hz, h2⟩ := hnf
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy hz
  rcases hy with rfl | rfl <;> rcases hz with rfl | rfl
  · exact absurd h1 h2
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h2, h1⟩
  · exact absurd h1 h2

theorem matching4 (p11 p12 p21 p22 : Prop) (fA1 : (p11 ∧ ¬ p12) ∨ (¬ p11 ∧ p12))
    (fA2 : (p21 ∧ ¬ p22) ∨ (¬ p21 ∧ p22)) (fB1 : (p11 ∧ ¬ p21) ∨ (¬ p11 ∧ p21))
    (fB2 : (p12 ∧ ¬ p22) ∨ (¬ p12 ∧ p22)) :
    (p11 ∧ p22 ∧ ¬ p12 ∧ ¬ p21) ∨ (p12 ∧ p21 ∧ ¬ p11 ∧ ¬ p22) := by tauto

theorem Good.final [DecidableEq V] {A B C : Finset V} {p q r : V → ℝ} (h : Good G A B C p q r)
    (hA : ¬ Red (G := G) A p B q C r) (hB : ¬ Red (G := G) B q C r A p)
    (hC : ¬ Red (G := G) C r A p B q) (hA2 : A.card = 2) (hB2 : B.card = 2) (hC2 : C.card = 2) :
    False := by
  have hA' : ¬ Red (G := G) A p C r B q := fun hh => hA (Red_comm.mp hh)
  have hB' : ¬ Red (G := G) B q A p C r := fun hh => hB (Red_comm.mp hh)
  have hC' : ¬ Red (G := G) C r B q A p := fun hh => hC (Red_comm.mp hh)
  have hBC := h.has_nbr hB hB2
  have hCA := h.rot.has_nbr hC hC2
  have hAB := h.rot.rot.has_nbr hA hA2
  have hAC := h.swap.has_nbr hA' hA2
  have hBA := h.rot.swap.has_nbr hB' hB2
  have hCB := h.rot.rot.swap.has_nbr hC' hC2
  have nfAB := h.no_full hB hB2 hC2 hBC hAC
  have nfBC := h.rot.no_full hC hC2 hA2 hCA hBA
  have nfCA := h.rot.rot.no_full hA hA2 hB2 hAB hCB
  have nfBA := h.swap.no_full hA' hA2 hC2 hAC hBC
  have nfCB := h.rot.swap.no_full hB' hB2 hA2 hBA hCA
  have nfAC := h.rot.rot.swap.no_full hC' hC2 hB2 hCB hAB
  obtain ⟨a1, a2, ha12, hAeq⟩ := Finset.card_eq_two.mp hA2
  obtain ⟨b1, b2, hb12, hBeq⟩ := Finset.card_eq_two.mp hB2
  obtain ⟨c1, c2, hc12, hCeq⟩ := Finset.card_eq_two.mp hC2
  have ha1 : a1 ∈ A := by rw [hAeq]; simp
  have ha2 : a2 ∈ A := by rw [hAeq]; simp
  have hb1 : b1 ∈ B := by rw [hBeq]; simp
  have hb2 : b2 ∈ B := by rw [hBeq]; simp
  have hc1 : c1 ∈ C := by rw [hCeq]; simp
  have hc2 : c2 ∈ C := by rw [hCeq]; simp
  have iA := irred_pair hA h.pA ha1 ha2 ha12
  have iB := irred_pair hB h.qB hb1 hb2 hb12
  have iC := irred_pair hC h.rC hc1 hc2 hc12
  have fA1 := pair_fact hBeq (hAB a1 ha1) (nfAB a1 ha1)
  have fA2 := pair_fact hBeq (hAB a2 ha2) (nfAB a2 ha2)
  have fB1 := pair_fact hAeq (hBA b1 hb1) (nfBA b1 hb1)
  have fB2 := pair_fact hAeq (hBA b2 hb2) (nfBA b2 hb2)
  have gB1 := pair_fact hCeq (hBC b1 hb1) (nfBC b1 hb1)
  have gB2 := pair_fact hCeq (hBC b2 hb2) (nfBC b2 hb2)
  have gC1 := pair_fact hBeq (hCB c1 hc1) (nfCB c1 hc1)
  have gC2 := pair_fact hBeq (hCB c2 hc2) (nfCB c2 hc2)
  have kC1 := pair_fact hAeq (hCA c1 hc1) (nfCA c1 hc1)
  have kC2 := pair_fact hAeq (hCA c2 hc2) (nfCA c2 hc2)
  have kA1 := pair_fact hCeq (hAC a1 ha1) (nfAC a1 ha1)
  have kA2 := pair_fact hCeq (hAC a2 ha2) (nfAC a2 ha2)
  subst hAeq hBeq hCeq
  simp only [G.adj_comm b1 a1, G.adj_comm b1 a2, G.adj_comm b2 a1, G.adj_comm b2 a2,
    G.adj_comm c1 b1, G.adj_comm c1 b2, G.adj_comm c2 b1, G.adj_comm c2 b2,
    G.adj_comm a1 c1, G.adj_comm a1 c2, G.adj_comm a2 c1, G.adj_comm a2 c2] at fB1 fB2 gC1 gC2 kA1 kA2
  have mAB := matching4 _ _ _ _ fA1 fA2 fB1 fB2
  have mBC := matching4 _ _ _ _ gB1 gB2 gC1 gC2
  have mCA := matching4 _ _ _ _ kC1 kC2 kA1 kA2
  obtain ⟨-, -, iA'⟩ := iA
  obtain ⟨-, -, iB'⟩ := iB
  obtain ⟨-, -, iC'⟩ := iC
  rcases mAB with ⟨x1, x2, x3, x4⟩ | ⟨x1, x2, x3, x4⟩ <;>
  rcases mBC with ⟨y1, y2, y3, y4⟩ | ⟨y1, y2, y3, y4⟩ <;>
  rcases mCA with ⟨z1, z2, z3, z4⟩ | ⟨z1, z2, z3, z4⟩ <;>
  · simp only [nbw, Finset.sum_pair ha12, Finset.sum_pair hb12, Finset.sum_pair hc12,
      G.adj_comm b1 a1, G.adj_comm b1 a2, G.adj_comm b2 a1, G.adj_comm b2 a2,
      G.adj_comm c1 b1, G.adj_comm c1 b2, G.adj_comm c2 b1, G.adj_comm c2 b2,
      G.adj_comm a1 c1, G.adj_comm a1 c2, G.adj_comm a2 c1, G.adj_comm a2 c2,
      x1, x2, x3, x4, y1, y2, y3, y4, z1, z2, z3, z4, ite_true, ite_false, add_zero, zero_add]
      at iA' iB' iC'
    rcases iA' with ⟨u1, u2⟩ | ⟨u1, u2⟩ <;> rcases iB' with ⟨v1, v2⟩ | ⟨v1, v2⟩ <;>
      rcases iC' with ⟨w1, w2⟩ | ⟨w1, w2⟩ <;> linarith

/-- Main induction: no weighted cyclic triangle-free configuration exists. -/
theorem Good.false [DecidableEq V] : ∀ n : ℕ, ∀ {A B C : Finset V} {p q r : V → ℝ},
    A.card + B.card + C.card ≤ n → Good G A B C p q r → False := by
  intro n
  induction n with
  | zero =>
    intro A B C p q r hn h
    have := h.neA.card_pos
    omega
  | succ n ih =>
    intro A B C p q r hn h
    by_cases hA : Red (G := G) A p B q C r
    · obtain ⟨A', p', hlt, h'⟩ := h.reduce hA
      exact ih (by omega) h'
    by_cases hB : Red (G := G) B q C r A p
    · obtain ⟨B', q', hlt, h'⟩ := h.rot.reduce hB
      exact ih (by omega) h'.rot.rot
    by_cases hC : Red (G := G) C r A p B q
    · obtain ⟨C', r', hlt, h'⟩ := h.rot.rot.reduce hC
      exact ih (by omega) h'.rot
    have a3 : ¬ 3 ≤ A.card := fun hh => hA (Or.inl hh)
    have b3 : ¬ 3 ≤ B.card := fun hh => hB (Or.inl hh)
    have c3 : ¬ 3 ≤ C.card := fun hh => hC (Or.inl hh)
    have a1 := h.rot.card_C_ne_one
    have b1 := h.rot.rot.card_C_ne_one
    have c1 := h.card_C_ne_one
    have a0 := h.neA.card_pos
    have b0 := h.neB.card_pos
    have c0 := h.neC.card_pos
    exact h.final hA hB hC (by omega) (by omega) (by omega)

/-- Edge density between `A` and `B`. -/
noncomputable def dens (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) : ℝ :=
  (((A ×ˢ B).filter fun p => G.Adj p.1 p.2).card : ℝ) / (A.card * B.card)

theorem dd_const [DecidableEq V] (A B : Finset V) (hA : A.Nonempty) (hB : B.Nonempty) :
    dd G A B (fun _ => 1 / (A.card : ℝ)) (fun _ => 1 / (B.card : ℝ)) = dens G A B := by
  have hA0 : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_pos.ne'
  have hB0 : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
  have hc : (((A ×ˢ B).filter fun p => G.Adj p.1 p.2).card : ℝ)
      = ∑ a ∈ A, ∑ b ∈ B, if G.Adj a b then (1 : ℝ) else 0 := by
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_product]
    simp
  unfold dens
  rw [hc]
  unfold dd nbw
  rw [eq_div_iff (mul_ne_zero hA0 hB0), Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  show 1 / (A.card : ℝ) * (∑ y ∈ B, if G.Adj a y then 1 / (B.card : ℝ) else 0) *
    ((A.card : ℝ) * B.card) = _
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs
  · field_simp
  · simp

theorem sum_const_div (A : Finset V) (hA : A.Nonempty) : ∑ _a ∈ A, 1 / (A.card : ℝ) = 1 := by
  have hA0 : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_pos.ne'
  simp [Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- **Tripartite Turán, strong form.** If `αβ + γ > 1`, `βγ + α > 1` and `γα + β > 1` for the edge
densities `α, β, γ` between `A, B`, `B, C`, `A, C`, there is a triangle with one vertex in each part. -/
theorem exists_triangle_of_mul_add [DecidableEq V] (A B C : Finset V) (hA : A.Nonempty)
    (hB : B.Nonempty) (hC : C.Nonempty)
    (h1 : 1 < dens G A B * dens G B C + dens G A C) (h2 : 1 < dens G B C * dens G A C + dens G A B)
    (h3 : 1 < dens G A C * dens G A B + dens G B C) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, G.Adj a b ∧ G.Adj b c ∧ G.Adj a c := by
  by_contra hcon
  have nt : NoTri G A B C := fun a ha b hb c hc h => hcon ⟨a, ha, b, hb, c, hc, h⟩
  have hG : Good G A B C (fun _ => 1 / (A.card : ℝ)) (fun _ => 1 / (B.card : ℝ))
      (fun _ => 1 / (C.card : ℝ)) :=
    { neA := hA, neB := hB, neC := hC
      pA := fun _ _ => by positivity
      qB := fun _ _ => by positivity
      rC := fun _ _ => by positivity
      sA := sum_const_div A hA
      sB := sum_const_div B hB
      sC := sum_const_div C hC
      nt := nt
      cyc := by
        rw [dd_const A B hA hB, dd_const B C hB hC, dd_const A C hA hC]
        exact ⟨h1, h2, h3⟩ }
  exact hG.false _ le_rfl

/-- **A tripartite Turán theorem (Bondy–Shen–Thomassé–Thomassen 2006).** If the three edge densities
between `A, B, C` all exceed `1/φ`, there is a triangle with one vertex in each part. -/
theorem exists_triangle [DecidableEq V] (A B C : Finset V) (hA : A.Nonempty) (hB : B.Nonempty)
    (hC : C.Nonempty)
    (dAB : 1 / Real.goldenRatio < (((A ×ˢ B).filter fun p => G.Adj p.1 p.2).card : ℝ) / (A.card * B.card))
    (dBC : 1 / Real.goldenRatio < (((B ×ˢ C).filter fun p => G.Adj p.1 p.2).card : ℝ) / (B.card * C.card))
    (dAC : 1 / Real.goldenRatio < (((A ×ˢ C).filter fun p => G.Adj p.1 p.2).card : ℝ) / (A.card * C.card)) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, G.Adj a b ∧ G.Adj b c ∧ G.Adj a c := by
  have hφ := Real.goldenRatio_pos
  have hsq := Real.goldenRatio_sq
  set t : ℝ := 1 / Real.goldenRatio with ht
  have ht0 : 0 < t := by positivity
  have key : ∀ g : ℝ, 0 < g → g ^ 2 = g + 1 → 1 / g * (1 / g) + 1 / g = 1 := by
    intro g hg hs
    field_simp
    nlinarith
  have htt : t * t + t = 1 := by
    rw [ht]; exact key _ hφ hsq
  have dAB' : t < dens G A B := dAB
  have dBC' : t < dens G B C := dBC
  have dAC' : t < dens G A C := dAC
  have m1 : t * t < dens G A B * dens G B C := mul_lt_mul'' dAB' dBC' ht0.le ht0.le
  have m2 : t * t < dens G B C * dens G A C := mul_lt_mul'' dBC' dAC' ht0.le ht0.le
  have m3 : t * t < dens G A C * dens G A B := mul_lt_mul'' dAC' dAB' ht0.le ht0.le
  exact exists_triangle_of_mul_add A B C hA hB hC (by linarith) (by linarith) (by linarith)

end TripartiteTuran
