/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The limited augmented Zarankiewicz number in three columns

Qi, Cui and Xu define the limited augmented Zarankiewicz number z_L(m, n): start from a C4-free set
of z(m, n) cells of the m × n grid and add disjoint pairs of cells subject to two forbidden patterns
on the final occupied set. We prove z_L(m, 3) = m + 3 + ⌊(m − 2)/2⌋ for every m ≥ 3, answering Open
Problem 1 of arXiv:2608.06050.

## Main results

* `ZL.z_three`: z(m, 3) = m + 3 for m ≥ 3
* `ZL.zL_three`: z_L(m, 3) = m + 3 + ⌊(m − 2)/2⌋ for m ≥ 3

## References

* L. Qi, C. Cui, Y. Xu, arXiv:2604.04111v5 (2026), Def. 2.1.
* L. Qi, J. Löfberg, H. Chen, arXiv:2608.06050v3 (2026), §9 Open Problem 1.
-/

@[expose] public section

namespace ZL

variable {m n : ℕ}

/-- A cell of the `m × n` grid. -/
abbrev Cell (m n : ℕ) := Fin m × Fin n

/-- `E` contains no all-occupied rectangle (`C₄`). -/
def C4Free (E : Finset (Cell m n)) : Prop :=
  ∀ i p : Fin m, ∀ j q : Fin n, i ≠ p → j ≠ q →
    ¬ ((i, j) ∈ E ∧ (i, q) ∈ E ∧ (p, j) ∈ E ∧ (p, q) ∈ E)

/-- The Zarankiewicz number `z(m, n)`: the largest size of a `C₄`-free set of cells. -/
noncomputable def z (m n : ℕ) : ℕ :=
  sSup {t | ∃ E : Finset (Cell m n), C4Free E ∧ E.card = t}

/-- The occupied set: the fixed cells and both halves of every selected pair. -/
def occ (E₁ : Finset (Cell m n)) (E₂ : Finset (Cell m n × Cell m n)) : Finset (Cell m n) :=
  E₁ ∪ E₂.image Prod.fst ∪ E₂.image Prod.snd

/-- Admissibility of a family of 2-edges over a base `E₁` (Definition 2.1, conditions (S), C2, C3;
C3 is imposed on every pair, degenerate or not). -/
def Admissible (E₁ : Finset (Cell m n)) (E₂ : Finset (Cell m n × Cell m n)) : Prop :=
  -- (S) halves are distinct cells outside `E₁`, and distinct pairs share no cell
  (∀ e ∈ E₂, e.1 ≠ e.2 ∧ e.1 ∉ E₁ ∧ e.2 ∉ E₁) ∧
  (∀ e ∈ E₂, ∀ e' ∈ E₂, e ≠ e' →
    e.1 ≠ e'.1 ∧ e.1 ≠ e'.2 ∧ e.2 ≠ e'.1 ∧ e.2 ≠ e'.2) ∧
  -- (C2)
  (∀ e ∈ E₂, e.1.1 ≠ e.2.1 → e.1.2 ≠ e.2.2 →
    ¬ ((e.1.1, e.2.2) ∈ occ E₁ E₂ ∧ (e.2.1, e.1.2) ∈ occ E₁ E₂)) ∧
  -- (C3)
  (∀ e ∈ E₂, ∀ k : Fin m, ∀ l : Fin n, k ≠ e.1.1 → k ≠ e.2.1 → l ≠ e.1.2 → l ≠ e.2.2 →
    ¬ ((k, l) ∈ occ E₁ E₂ ∧ (k, e.1.2) ∈ occ E₁ E₂ ∧ (k, e.2.2) ∈ occ E₁ E₂ ∧
       (e.1.1, l) ∈ occ E₁ E₂ ∧ (e.2.1, l) ∈ occ E₁ E₂))

/-- The limited augmented Zarankiewicz number `z_L(m, n)`. -/
noncomputable def zL (m n : ℕ) : ℕ :=
  sSup {t | ∃ (E₁ : Finset (Cell m n)) (E₂ : Finset (Cell m n × Cell m n)),
    C4Free E₁ ∧ E₁.card = z m n ∧ Admissible E₁ E₂ ∧ E₁.card + E₂.card = t}

/-! ### Rows -/

/-- The columns occupied in row `i`. -/
def rowset (E : Finset (Cell m 3)) (i : Fin m) : Finset (Fin 3) :=
  Finset.univ.filter (fun j => (i, j) ∈ E)

theorem mem_rowset {E : Finset (Cell m 3)} {i : Fin m} {j : Fin 3} :
    j ∈ rowset E i ↔ (i, j) ∈ E := by simp [rowset]

theorem card_eq_sum_rowset (E : Finset (Cell m 3)) : E.card = ∑ i, (rowset E i).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.card_nbij' (fun c => c.2) (fun j => (i, j)) ?_ ?_ ?_ ?_
  · intro c hc
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hc
    obtain ⟨hc1, hc2⟩ := hc
    simp only [Finset.mem_coe, mem_rowset]
    rw [← hc2]; exact hc1
  · intro j hj
    simp only [Finset.mem_coe, mem_rowset] at hj
    simp [hj]
  · intro c hc
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hc
    obtain ⟨_, hc2⟩ := hc
    ext <;> simp [hc2]
  · intro j _; rfl

/-- Column pairs `j < q` both occupied in the row `R`. -/
def prs (R : Finset (Fin 3)) : Finset (Fin 3 × Fin 3) :=
  Finset.univ.filter (fun x => x.1 < x.2 ∧ x.1 ∈ R ∧ x.2 ∈ R)

/-- All column pairs `j < q`. -/
def lt3 : Finset (Fin 3 × Fin 3) := Finset.univ.filter (fun x => x.1 < x.2)

theorem lt3_card : lt3.card = 3 := by decide

theorem row_le : ∀ R : Finset (Fin 3), R.card ≤ 1 + (prs R).card := by decide

theorem row_eq : ∀ R : Finset (Fin 3), R.card = 1 + (prs R).card → R.card = 1 ∨ R.card = 2 := by
  decide

theorem lt3_or : ∀ j l : Fin 3, j ≠ l → (j, l) ∈ lt3 ∨ (l, j) ∈ lt3 := by decide

theorem third_col : ∀ j q : Fin 3, ∃ t, t ≠ j ∧ t ≠ q := by decide

theorem prs_disjoint {E : Finset (Cell m 3)} (h : C4Free E) (i p : Fin m) (hip : i ≠ p) :
    Disjoint (prs (rowset E i)) (prs (rowset E p)) := by
  rw [Finset.disjoint_left]
  rintro ⟨j, q⟩ h1 h2
  simp only [prs, Finset.mem_filter, Finset.mem_univ, true_and, mem_rowset] at h1 h2
  exact h i p j q hip (ne_of_lt h1.1) ⟨h1.2.1, h1.2.2, h2.2.1, h2.2.2⟩

theorem sum_prs {E : Finset (Cell m 3)} (h : C4Free E) :
    ∑ i, (prs (rowset E i)).card = (Finset.univ.biUnion fun i => prs (rowset E i)).card := by
  rw [Finset.card_biUnion]
  intro i _ p _ hip
  exact prs_disjoint h i p hip

theorem biUnion_sub (E : Finset (Cell m 3)) :
    (Finset.univ.biUnion fun i => prs (rowset E i)) ⊆ lt3 := by
  intro x hx
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
  obtain ⟨i, hi⟩ := hx
  simp only [prs, lt3, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.1

theorem sum_prs_le {E : Finset (Cell m 3)} (h : C4Free E) :
    ∑ i, (prs (rowset E i)).card ≤ 3 := by
  rw [sum_prs h]
  calc _ ≤ lt3.card := Finset.card_le_card (biUnion_sub E)
    _ = 3 := lt3_card

theorem sum_one_add (E : Finset (Cell m 3)) :
    ∑ i : Fin m, (1 + (prs (rowset E i)).card) = m + ∑ i, (prs (rowset E i)).card := by
  rw [Finset.sum_add_distrib]; simp

/-- (a) -/
theorem card_le_of_c4free (E : Finset (Cell m 3)) (h : C4Free E) : E.card ≤ m + 3 := by
  rw [card_eq_sum_rowset]
  calc ∑ i, (rowset E i).card
      ≤ ∑ i : Fin m, (1 + (prs (rowset E i)).card) :=
        Finset.sum_le_sum fun i _ => row_le _
    _ = m + ∑ i, (prs (rowset E i)).card := sum_one_add E
    _ ≤ m + 3 := by have := sum_prs_le h; omega

/-- (c) -/
theorem row_structure {E : Finset (Cell m 3)} (h : C4Free E) (hc : E.card = m + 3) :
    (∀ i, (rowset E i).card = 1 ∨ (rowset E i).card = 2) ∧
    ∀ j l : Fin 3, j ≠ l → ∃ k, (k, j) ∈ E ∧ (k, l) ∈ E := by
  have hsum : ∑ i, (rowset E i).card = m + 3 := by rw [← card_eq_sum_rowset]; exact hc
  have hle : ∑ i, (rowset E i).card ≤ ∑ i : Fin m, (1 + (prs (rowset E i)).card) :=
    Finset.sum_le_sum fun i _ => row_le _
  have hrhs := sum_one_add E
  have h3 := sum_prs_le h
  have heq : ∑ i, (rowset E i).card = ∑ i : Fin m, (1 + (prs (rowset E i)).card) := by omega
  have hpt := (Finset.sum_eq_sum_iff_of_le (fun i _ => row_le (rowset E i))).1 heq
  have hP : ∑ i, (prs (rowset E i)).card = 3 := by omega
  refine ⟨fun i => row_eq _ (hpt i (Finset.mem_univ _)), ?_⟩
  have hU : (Finset.univ.biUnion fun i => prs (rowset E i)) = lt3 :=
    Finset.eq_of_subset_of_card_le (biUnion_sub E) (by rw [lt3_card, ← sum_prs h, hP])
  intro j l hjl
  rcases lt3_or j l hjl with hj | hj
  · rw [← hU] at hj
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hj
    obtain ⟨k, hk⟩ := hj
    simp only [prs, Finset.mem_filter, Finset.mem_univ, true_and, mem_rowset] at hk
    exact ⟨k, hk.2.1, hk.2.2⟩
  · rw [← hU] at hj
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hj
    obtain ⟨k, hk⟩ := hj
    simp only [prs, Finset.mem_filter, Finset.mem_univ, true_and, mem_rowset] at hk
    exact ⟨k, hk.2.2, hk.2.1⟩

/-! ### Construction -/

/-- Row pattern of the extremal base. -/
def Rrow : ℕ → Finset (Fin 3)
  | 0 => {0, 1}
  | 1 => {0, 2}
  | 2 => {1, 2}
  | _ => {0}

/-- The extremal `C₄`-free base. -/
def Ebase (m : ℕ) : Finset (Cell m 3) := Finset.univ.filter fun c => c.2 ∈ Rrow c.1.val

theorem rowset_Ebase (i : Fin m) : rowset (Ebase m) i = Rrow i.val := by
  ext j; simp [mem_rowset, Ebase]

theorem Rrow_inj : ∀ (a b : ℕ) (j q : Fin 3), a ≠ b → j ≠ q →
    j ∈ Rrow a → q ∈ Rrow a → j ∈ Rrow b → q ∈ Rrow b → False := by
  intro a b j q hab hjq
  obtain _ | _ | _ | a := a <;> obtain _ | _ | _ | b := b <;>
    fin_cases j <;> fin_cases q <;> simp_all [Rrow]

theorem Ebase_c4 : C4Free (Ebase m) := by
  intro i p j q hip hjq ⟨h1, h2, h3, h4⟩
  simp only [Ebase, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2 h3 h4
  exact Rrow_inj i.val p.val j q (fun h => hip (Fin.ext h)) hjq h1 h2 h3 h4

theorem sum_Rrow (k : ℕ) : ∑ n ∈ Finset.range (k + 3), (Rrow n).card = k + 6 := by
  induction k with
  | zero => simp [Finset.sum_range_succ, Rrow]
  | succ k ih =>
    rw [show k + 1 + 3 = (k + 3) + 1 by ring, Finset.sum_range_succ, ih]
    simp [Rrow]

theorem card_Ebase (hm : 3 ≤ m) : (Ebase m).card = m + 3 := by
  rw [card_eq_sum_rowset]
  simp only [rowset_Ebase]
  rw [Fin.sum_univ_eq_sum_range (fun n => (Rrow n).card) m]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  rw [sum_Rrow]

/-- (b) -/
theorem z_three (hm : 3 ≤ m) : z m 3 = m + 3 := by
  unfold z
  apply IsGreatest.csSup_eq
  refine ⟨⟨Ebase m, Ebase_c4, card_Ebase hm⟩, ?_⟩
  rintro t ⟨E, hE, rfl⟩
  exact card_le_of_c4free E hE

/-! ### The 2-edges -/

theorem subset_occ (E₁ : Finset (Cell m 3)) (E₂ : Finset (Cell m 3 × Cell m 3)) :
    E₁ ⊆ occ E₁ E₂ := by
  intro x hx; simp [occ, hx]

theorem pair_props {E₁ : Finset (Cell m 3)} {E₂ : Finset (Cell m 3 × Cell m 3)}
    (ha : Admissible E₁ E₂) {e : Cell m 3 × Cell m 3} (he : e ∈ E₂)
    {x y : Cell m 3} (hxy : (x = e.1 ∧ y = e.2) ∨ (x = e.2 ∧ y = e.1)) :
    x ≠ y ∧ x ∉ E₁ ∧ y ∉ E₁ ∧
    (x.1 ≠ y.1 → x.2 ≠ y.2 → ¬ ((x.1, y.2) ∈ occ E₁ E₂ ∧ (y.1, x.2) ∈ occ E₁ E₂)) ∧
    (∀ k l, k ≠ x.1 → k ≠ y.1 → l ≠ x.2 → l ≠ y.2 →
      ¬ ((k, l) ∈ occ E₁ E₂ ∧ (k, x.2) ∈ occ E₁ E₂ ∧ (k, y.2) ∈ occ E₁ E₂ ∧
         (x.1, l) ∈ occ E₁ E₂ ∧ (y.1, l) ∈ occ E₁ E₂)) := by
  obtain ⟨hS, -, hC2, hC3⟩ := ha
  obtain ⟨h1, h2, h3⟩ := hS e he
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨h1, h2, h3, hC2 e he, hC3 e he⟩
  · refine ⟨h1.symm, h3, h2, fun a b hh => ?_, fun k l a b c d hh => ?_⟩
    · exact hC2 e he (Ne.symm a) (Ne.symm b) ⟨hh.2, hh.1⟩
    · exact hC3 e he k l b a d c ⟨hh.1, hh.2.2.1, hh.2.1, hh.2.2.2.2, hh.2.2.2.1⟩

theorem exists_partner {E₁ : Finset (Cell m 3)} {E₂ : Finset (Cell m 3 × Cell m 3)}
    (ha : Admissible E₁ E₂) {F : Fin m} {j : Fin 3}
    (hO : (F, j) ∈ occ E₁ E₂) (hn : (F, j) ∉ E₁) :
    ∃ y : Cell m 3, (F, j) ≠ y ∧ y ∉ E₁ ∧
    (F ≠ y.1 → j ≠ y.2 → ¬ ((F, y.2) ∈ occ E₁ E₂ ∧ (y.1, j) ∈ occ E₁ E₂)) ∧
    (∀ k l, k ≠ F → k ≠ y.1 → l ≠ j → l ≠ y.2 →
      ¬ ((k, l) ∈ occ E₁ E₂ ∧ (k, j) ∈ occ E₁ E₂ ∧ (k, y.2) ∈ occ E₁ E₂ ∧
         (F, l) ∈ occ E₁ E₂ ∧ (y.1, l) ∈ occ E₁ E₂)) := by
  have key : ∃ e ∈ E₂, (F, j) = e.1 ∨ (F, j) = e.2 := by
    simp only [occ, Finset.mem_union, Finset.mem_image] at hO
    rcases hO with (h | ⟨e, he, h⟩) | ⟨e, he, h⟩
    · exact absurd h hn
    · exact ⟨e, he, Or.inl h.symm⟩
    · exact ⟨e, he, Or.inr h.symm⟩
  obtain ⟨e, he, h | h⟩ := key
  · obtain ⟨a, -, c, d, f⟩ := pair_props ha he (x := (F, j)) (y := e.2) (Or.inl ⟨h, rfl⟩)
    exact ⟨e.2, a, c, d, f⟩
  · obtain ⟨a, -, c, d, f⟩ := pair_props ha he (x := (F, j)) (y := e.1) (Or.inr ⟨h, rfl⟩)
    exact ⟨e.1, a, c, d, f⟩

/-- Lemma F: at most one full row. -/
theorem no_two_full {E₁ : Finset (Cell m 3)} {E₂ : Finset (Cell m 3 × Cell m 3)}
    (hrow : ∀ i, 1 ≤ (rowset E₁ i).card ∧ (rowset E₁ i).card ≤ 2)
    (hcov : ∀ j l : Fin 3, j ≠ l → ∃ k, (k, j) ∈ E₁ ∧ (k, l) ∈ E₁)
    (ha : Admissible E₁ E₂) {F G : Fin m} (hFG : F ≠ G)
    (hF : ∀ c, (F, c) ∈ occ E₁ E₂) (hG : ∀ c, (G, c) ∈ occ E₁ E₂) : False := by
  have hex : ∃ j, (F, j) ∉ E₁ := by
    by_contra hh
    push Not at hh
    have h0 : rowset E₁ F = Finset.univ :=
      Finset.eq_univ_of_forall fun c => mem_rowset.2 (hh c)
    have h2 := (hrow F).2
    rw [h0] at h2
    simp at h2
  obtain ⟨j, hj⟩ := hex
  obtain ⟨⟨P, q⟩, hne, hy, hC2, hC3⟩ := exists_partner ha (hF j) hj
  have hsub := subset_occ E₁ E₂
  have hnonempty : ∀ P, ∃ a, (P, a) ∈ E₁ := fun P => by
    obtain ⟨a, ha'⟩ := Finset.card_pos.1 (hrow P).1
    exact ⟨a, mem_rowset.1 ha'⟩
  by_cases hP : P = F
  · have hqj : j ≠ q := fun h => hne (by rw [h, hP])
    obtain ⟨t, ht1, ht2⟩ := third_col j q
    have hGP : G ≠ P := fun h => hFG (hP ▸ h).symm
    exact hC3 G t (Ne.symm hFG) hGP ht1 ht2 ⟨hG t, hG j, hG q, hF t, hP ▸ hF t⟩
  · by_cases hq : q = j
    · obtain ⟨a, haE⟩ := hnonempty P
      have haj : a ≠ j := fun h => hy (by rw [hq, ← h]; exact haE)
      obtain ⟨S, hS1, hS2⟩ := hcov j a (Ne.symm haj)
      have hSF : S ≠ F := fun h => hj (by rw [← h]; exact hS1)
      have hSP : S ≠ P := fun h => hy (by rw [hq, ← h]; exact hS1)
      have haq : a ≠ q := fun h => haj (h.trans hq)
      have hSq : (S, q) ∈ occ E₁ E₂ := by rw [hq]; exact hsub hS1
      exact hC3 S a hSF hSP haj haq ⟨hsub hS2, hsub hS1, hSq, hF a, hsub haE⟩
    · have hPj : (P, j) ∉ occ E₁ E₂ := fun h =>
        hC2 (fun h' => hP h'.symm) (Ne.symm hq) ⟨hF q, h⟩
      obtain ⟨a, haE⟩ := hnonempty P
      have haj : a ≠ j := fun h => hPj (by rw [← h]; exact hsub haE)
      have haq : a ≠ q := fun h => hy (by rw [← h]; exact haE)
      have hGP : G ≠ P := fun h => hPj (by rw [← h]; exact hG j)
      exact hC3 G a (Ne.symm hFG) hGP haj haq ⟨hG a, hG j, hG q, hF a, hsub haE⟩

theorem card_occ {E₁ : Finset (Cell m 3)} {E₂ : Finset (Cell m 3 × Cell m 3)}
    (ha : Admissible E₁ E₂) : (occ E₁ E₂).card = E₁.card + 2 * E₂.card := by
  obtain ⟨hS, hD, -, -⟩ := ha
  have hA : (E₂.image Prod.fst).card = E₂.card := by
    apply Finset.card_image_of_injOn
    intro e he e' he' h
    by_contra hne
    exact (hD e he e' he' hne).1 h
  have hB : (E₂.image Prod.snd).card = E₂.card := by
    apply Finset.card_image_of_injOn
    intro e he e' he' h
    by_contra hne
    exact (hD e he e' he' hne).2.2.2 h
  have hdAB : Disjoint (E₂.image Prod.fst) (E₂.image Prod.snd) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_image] at hx hx'
    obtain ⟨e, he, rfl⟩ := hx
    obtain ⟨e', he', h⟩ := hx'
    by_cases hee : e = e'
    · subst hee; exact (hS e he).1 h.symm
    · exact (hD e he e' he' hee).2.1 h.symm
  have hdE : Disjoint E₁ (E₂.image Prod.fst) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_image] at hx'
    obtain ⟨e, he, rfl⟩ := hx'
    exact (hS e he).2.1 hx
  have hdE' : Disjoint (E₁ ∪ E₂.image Prod.fst) (E₂.image Prod.snd) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_image] at hx'
    obtain ⟨e, he, rfl⟩ := hx'
    rcases Finset.mem_union.1 hx with h | h
    · exact (hS e he).2.2 h
    · simp only [Finset.mem_image] at h
      obtain ⟨e', he', h'⟩ := h
      by_cases hee : e' = e
      · subst hee; exact (hS e' he').1 h'
      · exact (hD e' he' e he hee).2.1 h'
  unfold occ
  rw [Finset.card_union_of_disjoint hdE', Finset.card_union_of_disjoint hdE, hA, hB]
  ring

/-- (d) -/
theorem card_E2_le (hm : 3 ≤ m) (E₁ : Finset (Cell m 3)) (E₂ : Finset (Cell m 3 × Cell m 3))
    (h1 : C4Free E₁) (hc : E₁.card = m + 3) (ha : Admissible E₁ E₂) :
    2 * E₂.card ≤ m - 2 := by
  obtain ⟨hrow, hcov⟩ := row_structure h1 hc
  have hrow' : ∀ i, 1 ≤ (rowset E₁ i).card ∧ (rowset E₁ i).card ≤ 2 := fun i => by
    rcases hrow i with h | h <;> omega
  have hcardO := card_occ ha
  have hsum := card_eq_sum_rowset (occ E₁ E₂)
  have hle3 : ∀ i, (rowset (occ E₁ E₂) i).card ≤ 3 := fun i => by
    simpa using Finset.card_le_univ (rowset (occ E₁ E₂) i)
  have hfull : ∀ i, (rowset (occ E₁ E₂) i).card = 3 → ∀ c, (i, c) ∈ occ E₁ E₂ := by
    intro i hi c
    have : rowset (occ E₁ E₂) i = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [hi]; simp)
    exact mem_rowset.1 (by rw [this]; exact Finset.mem_univ _)
  have hone : ∀ i p, (rowset (occ E₁ E₂) i).card = 3 → (rowset (occ E₁ E₂) p).card = 3 →
      i = p := by
    intro i p hi hp
    by_contra hne
    exact no_two_full hrow' hcov ha hne (hfull i hi) (hfull p hp)
  have hbound : ∑ i, (rowset (occ E₁ E₂) i).card ≤ 2 * m + 1 := by
    by_cases hex : ∃ F, (rowset (occ E₁ E₂) F).card = 3
    · obtain ⟨F, hF⟩ := hex
      calc ∑ i, (rowset (occ E₁ E₂) i).card
          ≤ ∑ i : Fin m, (2 + if i = F then 1 else 0) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have := hle3 i
            by_cases hi : i = F
            · simp [hi]; omega
            · have h3 : (rowset (occ E₁ E₂) i).card ≠ 3 := fun h => hi (hone i F h hF)
              simp [hi]; omega
        _ = 2 * m + 1 := by simp [Finset.sum_add_distrib]; omega
    · push Not at hex
      calc ∑ i, (rowset (occ E₁ E₂) i).card ≤ ∑ _i : Fin m, 2 :=
            Finset.sum_le_sum fun i _ => by have := hle3 i; have := hex i; omega
        _ = 2 * m := by simp; ring
        _ ≤ 2 * m + 1 := by omega
  omega

/-- (e) -/
theorem zL_le (hm : 3 ≤ m) : zL m 3 ≤ m + 3 + (m - 2) / 2 := by
  unfold zL
  apply csSup_le'
  rintro t ⟨E₁, E₂, h1, hc, ha, rfl⟩
  have := card_E2_le hm E₁ E₂ h1 (hc.trans (z_three hm)) ha
  rw [hc, z_three hm]
  omega


/-! ### Lower bound: explicit constructions -/

theorem sumRows (n : ℕ) (hn : 3 ≤ n) :
    ∑ i ∈ Finset.range n, (if i < 3 then 2 else 1) = n + 3 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show k + 1 + 3 = (k + 3) + 1 by ring, Finset.sum_range_succ, ih (by omega)]
    simp only [show ¬ (k + 3 < 3) by omega, ite_false]

/-! ### Odd `m = 2N + 3` -/

/-- Membership predicate of the odd base. -/
def PO (i j : ℕ) : Prop :=
  (i = 0 ∧ j ≤ 1) ∨ (i = 1 ∧ j ≠ 1) ∨ (i = 2 ∧ 1 ≤ j) ∨ (3 ≤ i ∧ j = 0)

instance (i j : ℕ) : Decidable (PO i j) := by unfold PO; infer_instance

/-- The odd base. -/
def baseO (N : ℕ) : Finset (Cell (2 * N + 3) 3) :=
  Finset.univ.filter fun c => PO c.1.val c.2.val

/-- The odd pairs. -/
def pairsO (N : ℕ) : Finset (Cell (2 * N + 3) 3 × Cell (2 * N + 3) 3) :=
  (Finset.univ : Finset (Fin N)).image fun t =>
    ((⟨3 + 2 * t.val, by have := t.isLt; omega⟩, ⟨1, by omega⟩),
     (⟨4 + 2 * t.val, by have := t.isLt; omega⟩, ⟨2, by omega⟩))

theorem mem_baseO (N : ℕ) (c : Cell (2 * N + 3) 3) : c ∈ baseO N ↔ PO c.1.val c.2.val := by
  simp [baseO]

theorem mem_occO (N : ℕ) (c : Cell (2 * N + 3) 3) :
    c ∈ occ (baseO N) (pairsO N) ↔ PO c.1.val c.2.val ∨
      (3 ≤ c.1.val ∧ c.1.val % 2 = 1 ∧ c.2.val = 1) ∨
      (4 ≤ c.1.val ∧ c.1.val % 2 = 0 ∧ c.2.val = 2) := by
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := c
  simp only [occ, pairsO, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    mem_baseO]
  constructor
  · rintro ((h | ⟨a, ⟨t, rfl⟩, h⟩) | ⟨a, ⟨t, rfl⟩, h⟩)
    · exact Or.inl h
    · simp only [Prod.ext_iff, Fin.ext_iff] at h
      right; left; omega
    · simp only [Prod.ext_iff, Fin.ext_iff] at h
      right; right; omega
  · rintro (h | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl (Or.inl h)
    · refine Or.inl (Or.inr ⟨_, ⟨⟨(i - 3) / 2, by omega⟩, rfl⟩, ?_⟩)
      simp only [Prod.ext_iff, Fin.ext_iff]; omega
    · refine Or.inr ⟨_, ⟨⟨(i - 4) / 2, by omega⟩, rfl⟩, ?_⟩
      simp only [Prod.ext_iff, Fin.ext_iff]; omega

theorem card_baseO (N : ℕ) : (baseO N).card = 2 * N + 3 + 3 := by
  have h : ∀ i : Fin (2 * N + 3),
      ∑ j : Fin 3, (if PO i.val j.val then 1 else 0) = if i.val < 3 then 2 else 1 := by
    intro i
    have e0 : ((0 : Fin 3) : ℕ) = 0 := rfl
    have e1 : ((1 : Fin 3) : ℕ) = 1 := rfl
    have e2 : ((2 : Fin 3) : ℕ) = 2 := rfl
    rw [Fin.sum_univ_three]
    by_cases h3 : i.val < 3
    · have hh : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
      rcases hh with hh | hh | hh <;> simp [PO, hh]
    · have a0 : i.val ≠ 0 := by omega
      have a1 : i.val ≠ 1 := by omega
      have a2 : i.val ≠ 2 := by omega
      have a3 : 3 ≤ i.val := by omega
      simp [PO, a0, a1, a2, a3, h3]
  rw [baseO, Finset.card_filter, Fintype.sum_prod_type]
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < 3 then 2 else 1) (2 * N + 3),
    sumRows _ (by omega)]

theorem c4O (N : ℕ) : C4Free (baseO N) := by
  intro i p j q hip hjq h
  simp only [mem_baseO] at h
  have h1 : i.val ≠ p.val := fun e => hip (Fin.ext e)
  have h2 : j.val ≠ q.val := fun e => hjq (Fin.ext e)
  simp only [PO] at h
  omega

theorem admO (N : ℕ) : Admissible (baseO N) (pairsO N) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he
    simp only [pairsO, Finset.mem_image, Finset.mem_univ, true_and] at he
    obtain ⟨t, rfl⟩ := he
    simp only [mem_baseO, PO, ne_eq, Prod.ext_iff, Fin.ext_iff]
    omega
  · intro e he e' he' hne
    simp only [pairsO, Finset.mem_image, Finset.mem_univ, true_and] at he he'
    obtain ⟨t, rfl⟩ := he
    obtain ⟨t', rfl⟩ := he'
    have : t.val ≠ t'.val := fun e => hne (by rw [Fin.ext e])
    simp only [ne_eq, Prod.ext_iff, Fin.ext_iff]
    omega
  · intro e he h1 h2
    simp only [pairsO, Finset.mem_image, Finset.mem_univ, true_and] at he
    obtain ⟨t, rfl⟩ := he
    simp only [mem_occO, PO]
    omega
  · intro e he k l hk1 hk2 hl1 hl2
    simp only [pairsO, Finset.mem_image, Finset.mem_univ, true_and] at he
    obtain ⟨t, rfl⟩ := he
    have a1 : k.val ≠ 3 + 2 * t.val := fun e => hk1 (Fin.ext e)
    have a2 : k.val ≠ 4 + 2 * t.val := fun e => hk2 (Fin.ext e)
    have a3 : l.val ≠ 1 := fun e => hl1 (Fin.ext e)
    have a4 : l.val ≠ 2 := fun e => hl2 (Fin.ext e)
    have := k.isLt
    simp only [mem_occO, PO]
    omega

theorem card_pairsO (N : ℕ) : (pairsO N).card = N := by
  rw [pairsO, Finset.card_image_of_injective]
  · simp
  · intro a b h
    simp only [Prod.ext_iff, Fin.ext_iff] at h
    exact Fin.ext (by omega)

theorem exists_odd (N : ℕ) : ∃ (E₁ : Finset (Cell (2 * N + 3) 3))
    (E₂ : Finset (Cell (2 * N + 3) 3 × Cell (2 * N + 3) 3)),
    C4Free E₁ ∧ E₁.card = (2 * N + 3) + 3 ∧ Admissible E₁ E₂ ∧ E₂.card = (2 * N + 3 - 2) / 2 :=
  ⟨baseO N, pairsO N, c4O N, card_baseO N, admO N, by rw [card_pairsO]; omega⟩

/-! ### Even `m = 2q + 4` -/

/-- Membership predicate of the even base. -/
def PE (q i j : ℕ) : Prop :=
  (i = 0 ∧ j ≤ 1) ∨ (i = 1 ∧ j ≠ 1) ∨ (i = 2 ∧ 1 ≤ j) ∨ (3 ≤ i ∧ i ≤ q + 2 ∧ j = 0) ∨
    (q + 3 ≤ i ∧ j = 1)

instance (q i j : ℕ) : Decidable (PE q i j) := by unfold PE; infer_instance

/-- The even base. -/
def baseE (q : ℕ) : Finset (Cell (2 * q + 4) 3) :=
  Finset.univ.filter fun c => PE q c.1.val c.2.val

/-- The vertical pairs. -/
def vertE (q : ℕ) : Finset (Cell (2 * q + 4) 3 × Cell (2 * q + 4) 3) :=
  (Finset.univ : Finset (Fin q)).image fun t =>
    ((⟨3 + t.val, by have := t.isLt; omega⟩, ⟨2, by omega⟩),
     (⟨q + 3 + t.val, by have := t.isLt; omega⟩, ⟨2, by omega⟩))

/-- The special pair. -/
def specE (q : ℕ) : Cell (2 * q + 4) 3 × Cell (2 * q + 4) 3 :=
  ((⟨2, by omega⟩, ⟨0, by omega⟩), (⟨2 * q + 3, by omega⟩, ⟨2, by omega⟩))

/-- The even pairs. -/
def pairsE (q : ℕ) : Finset (Cell (2 * q + 4) 3 × Cell (2 * q + 4) 3) :=
  insert (specE q) (vertE q)

theorem mem_baseE (q : ℕ) (c : Cell (2 * q + 4) 3) : c ∈ baseE q ↔ PE q c.1.val c.2.val := by
  simp [baseE]

theorem mem_occE (q : ℕ) (c : Cell (2 * q + 4) 3) :
    c ∈ occ (baseE q) (pairsE q) ↔ PE q c.1.val c.2.val ∨
      (3 ≤ c.1.val ∧ c.2.val = 2) ∨ (c.1.val = 2 ∧ c.2.val = 0) := by
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := c
  simp only [occ, pairsE, vertE, Finset.mem_union, Finset.mem_insert, Finset.mem_image,
    Finset.mem_univ, true_and, mem_baseE]
  constructor
  · rintro ((h | ⟨a, (rfl | ⟨t, rfl⟩), h⟩) | ⟨a, (rfl | ⟨t, rfl⟩), h⟩)
    · exact Or.inl h
    · simp only [specE, Prod.ext_iff, Fin.ext_iff] at h
      right; right; omega
    · simp only [Prod.ext_iff, Fin.ext_iff] at h
      have := t.isLt
      right; left; omega
    · simp only [specE, Prod.ext_iff, Fin.ext_iff] at h
      right; left; omega
    · simp only [Prod.ext_iff, Fin.ext_iff] at h
      have := t.isLt
      right; left; omega
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl (Or.inl h)
    · by_cases hA : i ≤ q + 2
      · refine Or.inl (Or.inr ⟨_, Or.inr ⟨⟨i - 3, by omega⟩, rfl⟩, ?_⟩)
        simp only [Prod.ext_iff, Fin.ext_iff]; omega
      · by_cases hB : i ≤ 2 * q + 2
        · refine Or.inr ⟨_, Or.inr ⟨⟨i - q - 3, by omega⟩, rfl⟩, ?_⟩
          simp only [Prod.ext_iff, Fin.ext_iff]; omega
        · refine Or.inr ⟨_, Or.inl rfl, ?_⟩
          simp only [specE, Prod.ext_iff, Fin.ext_iff]; omega
    · refine Or.inl (Or.inr ⟨_, Or.inl rfl, ?_⟩)
      simp only [specE, Prod.ext_iff, Fin.ext_iff]; omega

theorem card_baseE (q : ℕ) : (baseE q).card = 2 * q + 4 + 3 := by
  have h : ∀ i : Fin (2 * q + 4),
      ∑ j : Fin 3, (if PE q i.val j.val then 1 else 0) = if i.val < 3 then 2 else 1 := by
    intro i
    have e0 : ((0 : Fin 3) : ℕ) = 0 := rfl
    have e1 : ((1 : Fin 3) : ℕ) = 1 := rfl
    have e2 : ((2 : Fin 3) : ℕ) = 2 := rfl
    rw [Fin.sum_univ_three]
    by_cases h3 : i.val < 3
    · have hh : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
      rcases hh with hh | hh | hh <;> simp [PE, hh]
    · have a0 : i.val ≠ 0 := by omega
      have a1 : i.val ≠ 1 := by omega
      have a2 : i.val ≠ 2 := by omega
      have a3 : 3 ≤ i.val := by omega
      by_cases hq : i.val ≤ q + 2
      · have a5 : i.val < q + 3 := by omega
        simp [PE, a0, a1, a2, a3, h3, hq, a5]
      · have a4 : q + 3 ≤ i.val := by omega
        simp [PE, a0, a1, a2, a3, h3, hq, a4]
  rw [baseE, Finset.card_filter, Fintype.sum_prod_type]
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < 3 then 2 else 1) (2 * q + 4),
    sumRows _ (by omega)]

theorem c4E (q : ℕ) : C4Free (baseE q) := by
  intro i p j q' hip hjq h
  simp only [mem_baseE] at h
  have h1 : i.val ≠ p.val := fun e => hip (Fin.ext e)
  have h2 : j.val ≠ q'.val := fun e => hjq (Fin.ext e)
  simp only [PE] at h
  omega

theorem admE (q : ℕ) : Admissible (baseE q) (pairsE q) := by
  have hspec : specE q ∈ pairsE q := Finset.mem_insert_self _ _
  have hvert : ∀ t : Fin q, ((⟨3 + t.val, by have := t.isLt; omega⟩, ⟨2, by omega⟩),
      (⟨q + 3 + t.val, by have := t.isLt; omega⟩, ⟨2, by omega⟩)) ∈ pairsE q := by
    intro t
    exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨t, Finset.mem_univ _, rfl⟩)
  have hcases : ∀ e ∈ pairsE q, e = specE q ∨ ∃ t : Fin q, e = ((⟨3 + t.val, by have := t.isLt; omega⟩, ⟨2, by omega⟩),
      (⟨q + 3 + t.val, by have := t.isLt; omega⟩, ⟨2, by omega⟩)) := by
    intro e he
    simp only [pairsE, vertE, Finset.mem_insert, Finset.mem_image, Finset.mem_univ,
      true_and] at he
    rcases he with h | ⟨t, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨t, h.symm⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he
    rcases hcases e he with rfl | ⟨t, rfl⟩
    · simp only [specE, mem_baseE, PE, ne_eq, Prod.ext_iff, Fin.ext_iff]
      omega
    · have := t.isLt
      simp only [mem_baseE, PE, ne_eq, Prod.ext_iff, Fin.ext_iff]
      omega
  · intro e he e' he' hne
    rcases hcases e he with rfl | ⟨t, rfl⟩ <;> rcases hcases e' he' with rfl | ⟨t', rfl⟩
    · exact absurd rfl hne
    · have := t'.isLt
      simp only [specE, ne_eq, Prod.ext_iff, Fin.ext_iff]
      omega
    · have := t.isLt
      simp only [specE, ne_eq, Prod.ext_iff, Fin.ext_iff]
      omega
    · have : t.val ≠ t'.val := fun e => hne (by rw [Fin.ext e])
      simp only [ne_eq, Prod.ext_iff, Fin.ext_iff]
      omega
  · intro e he h1 h2
    rcases hcases e he with rfl | ⟨t, rfl⟩
    · simp only [specE, mem_occE, PE]
      omega
    · exact absurd rfl h2
  · intro e he k l hk1 hk2 hl1 hl2
    have := k.isLt
    rcases hcases e he with rfl | ⟨t, rfl⟩
    · have a1 : k.val ≠ 2 := fun e => hk1 (Fin.ext e)
      have a2 : k.val ≠ 2 * q + 3 := fun e => hk2 (Fin.ext e)
      have a3 : l.val ≠ 0 := fun e => hl1 (Fin.ext e)
      have a4 : l.val ≠ 2 := fun e => hl2 (Fin.ext e)
      simp only [specE, mem_occE, PE]
      omega
    · have := t.isLt
      have a1 : k.val ≠ 3 + t.val := fun e => hk1 (Fin.ext e)
      have a2 : k.val ≠ q + 3 + t.val := fun e => hk2 (Fin.ext e)
      have a3 : l.val ≠ 2 := fun e => hl1 (Fin.ext e)
      have a4 : l.val ≠ 2 := fun e => hl2 (Fin.ext e)
      simp only [mem_occE, PE]
      omega

theorem card_pairsE (q : ℕ) : (pairsE q).card = q + 1 := by
  have hn : specE q ∉ vertE q := by
    simp only [vertE, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro t h
    have := t.isLt
    simp only [specE, Prod.ext_iff, Fin.ext_iff] at h
    omega
  rw [pairsE, Finset.card_insert_of_notMem hn, vertE, Finset.card_image_of_injective]
  · simp
  · intro a b h
    simp only [Prod.ext_iff, Fin.ext_iff] at h
    exact Fin.ext (by omega)

theorem exists_even (q : ℕ) : ∃ (E₁ : Finset (Cell (2 * q + 4) 3))
    (E₂ : Finset (Cell (2 * q + 4) 3 × Cell (2 * q + 4) 3)),
    C4Free E₁ ∧ E₁.card = (2 * q + 4) + 3 ∧ Admissible E₁ E₂ ∧
      E₂.card = (2 * q + 4 - 2) / 2 :=
  ⟨baseE q, pairsE q, c4E q, card_baseE q, admE q, by rw [card_pairsE]; omega⟩

/-- Lower-bound construction for every `m ≥ 3`. -/
theorem exists_good (hm : 3 ≤ m) :
    ∃ (E₁ : Finset (Cell m 3)) (E₂ : Finset (Cell m 3 × Cell m 3)),
      C4Free E₁ ∧ E₁.card = m + 3 ∧ Admissible E₁ E₂ ∧ E₂.card = (m - 2) / 2 := by
  rcases Nat.even_or_odd' m with ⟨a, ha | ha⟩
  · obtain ⟨q, hq⟩ : ∃ q, m = 2 * q + 4 := ⟨a - 2, by omega⟩
    subst hq
    exact exists_even q
  · obtain ⟨N, hN⟩ : ∃ N, m = 2 * N + 3 := ⟨a - 1, by omega⟩
    subst hN
    exact exists_odd N


/-- **Main theorem.** `z_L(m, 3) = m + 3 + ⌊(m - 2) / 2⌋` for every `m ≥ 3`. -/
theorem zL_three (hm : 3 ≤ m) : zL m 3 = m + 3 + (m - 2) / 2 := by
  apply le_antisymm (zL_le hm)
  obtain ⟨E₁, E₂, h1, hc, ha, h2⟩ := exists_good hm
  apply le_csSup
  · refine ⟨m + 3 + (m - 2) / 2, ?_⟩
    rintro t ⟨E₁', E₂', h1', hc', ha', rfl⟩
    have := card_E2_le hm E₁' E₂' h1' (hc'.trans (z_three hm)) ha'
    have hz := z_three (m := m) hm
    omega
  · exact ⟨E₁, E₂, h1, hc.trans (z_three hm).symm, ha, by omega⟩

end ZL
