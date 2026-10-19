/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# The step-gap energy and balanced gap configurations

A gap configuration of `k` parts of `n` is `g : Fin k → ℕ` with `1 ≤ g i` and `∑ g i = n`; it is
balanced when its maximum and minimum differ by at most one. For a strictly convex potential `V`
on `[0, ∞)`, the gap energy `∑ V (g i)` is minimized exactly by the balanced configurations.
This energy depends only on the multiset of gaps, so being balanced is necessary but not
sufficient for maximal evenness; the all-pairs energy of `AllPairsEvenness` singles out the
maximally even sets.

## Main results

* `swap_lt`, `exists_improve`: an unbalanced configuration can be improved.
* `balanced_energy_eq`: balanced configurations have equal energy.
* `isMinimizer_iff_balanced`: global minimizer iff balanced.
* `diatonic_balanced`: the diatonic gap word `(2, 2, 1, 2, 2, 2, 1)` is balanced.

## References

* P. Bak, R. Bruinsma, *One-dimensional Ising model and the complete devil's staircase*, Phys.
  Rev. Lett. 49 (1982).
* J. Clough, J. Douthett, *Maximally even sets*, J. Music Theory 35 (1991).
* J. Douthett, R. Krantz, *Maximally even sets and configurations: common threads in mathematics,
  physics, and music*, J. Comb. Optim. 14 (2007).
* C. Marín, *One transform and one duality: a machine-checked core of music theory in Lean 4*,
  Zenodo (2026), doi:10.5281/zenodo.20953767.
-/

@[expose] public section

namespace MusicTheory

namespace MaximalEvenness

open Finset

/-! ### Definitions -/

/-- A gap configuration is `Balanced` when `max − min ≤ 1`: every gap differs from every other by at
    most one. This is exactly the maximally-even structure (all gaps `⌊n/k⌋` or `⌈n/k⌉`). -/
def Balanced {k : ℕ} (g : Fin k → ℕ) : Prop := ∀ i j, g i ≤ g j + 1

/-- The energy of a configuration for a potential `V`, casting gaps to `ℝ`. -/
noncomputable def energy {k : ℕ} (V : ℝ → ℝ) (g : Fin k → ℕ) : ℝ := ∑ i, V ((g i : ℝ))

/-! ### Part 1 — the swap lemma (strict convexity) -/

/-- **Swap lemma.** For `V` strictly convex on `s` and endpoints `a, b ∈ s` with `b + 2 ≤ a`, pulling the
    two gaps one step together strictly lowers the pair energy:  `V (a-1) + V (b+1) < V a + V b`.
    Proof: write `a-1` and `b+1` as strict convex combinations of the endpoints `a, b`, apply binary
    strict Jensen to each, and add — the endpoint coefficients each total `1`. -/
theorem swap_lt {V : ℝ → ℝ} {s : Set ℝ} (hV : StrictConvexOn ℝ s V)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) (hab : b + 2 ≤ a) :
    V (a - 1) + V (b + 1) < V a + V b := by
  have hd : (0 : ℝ) < a - b := by linarith
  have hne_ab : a - b ≠ 0 := ne_of_gt hd
  have hxy : a ≠ b := ne_of_gt (by linarith)
  -- coefficients for `a - 1`:  α₁ = (a-1-b)/(a-b) on `a`,  β₁ = 1/(a-b) on `b`
  have hα1 : (0 : ℝ) < (a - 1 - b) / (a - b) := div_pos (by linarith) hd
  have hβ1 : (0 : ℝ) < 1 / (a - b) := div_pos one_pos hd
  have hs1 : (a - 1 - b) / (a - b) + 1 / (a - b) = 1 := by
    field_simp; ring
  -- coefficients for `b + 1`:  α₂ = 1/(a-b) on `a`,  β₂ = (a-b-1)/(a-b) on `b`
  have hα2 : (0 : ℝ) < 1 / (a - b) := div_pos one_pos hd
  have hβ2 : (0 : ℝ) < (a - b - 1) / (a - b) := div_pos (by linarith) hd
  have hs2 : 1 / (a - b) + (a - b - 1) / (a - b) = 1 := by
    field_simp; ring
  have h1 := hV.2 ha hb hxy hα1 hβ1 hs1
  have h2 := hV.2 ha hb hxy hα2 hβ2 hs2
  simp only [smul_eq_mul] at h1 h2
  have e1 : (a - 1 - b) / (a - b) * a + 1 / (a - b) * b = a - 1 := by
    field_simp; ring
  have e2 : 1 / (a - b) * a + (a - b - 1) / (a - b) * b = b + 1 := by
    field_simp; ring
  rw [e1] at h1
  rw [e2] at h2
  have key : (a - 1 - b) / (a - b) * V a + 1 / (a - b) * V b
      + (1 / (a - b) * V a + (a - b - 1) / (a - b) * V b) = V a + V b := by
    field_simp; ring
  linarith [h1, h2, key]

/-! ### Part 2 — minimality (the payoff) -/

/-- A two-index split of a `Finset.univ` sum: pull out the values at two distinct indices `i, j`. -/
theorem sum_split_two {k : ℕ} {M : Type*} [AddCommMonoid M] (F : Fin k → M) {i j : Fin k}
    (hij : i ≠ j) :
    ∑ x, F x = F i + F j + ∑ x ∈ (univ.erase i).erase j, F x := by
  rw [← Finset.add_sum_erase univ F (mem_univ i),
      ← Finset.add_sum_erase (univ.erase i) F (mem_erase.mpr ⟨Ne.symm hij, mem_univ j⟩),
      add_assoc]

/-- **Improvement step.** If a valid configuration is not Balanced, one swap of an unbalanced pair gives
    another valid configuration with the same sum and strictly smaller energy. -/
theorem exists_improve {k n : ℕ} {V : ℝ → ℝ} (hV : StrictConvexOn ℝ (Set.Ici (0 : ℝ)) V)
    (g : Fin k → ℕ) (hpos : ∀ i, 1 ≤ g i) (hsum : ∑ i, g i = n) (hnb : ¬ Balanced g) :
    ∃ g' : Fin k → ℕ, (∀ i, 1 ≤ g' i) ∧ (∑ i, g' i = n) ∧ energy V g' < energy V g := by
  -- extract an unbalanced pair `g j + 1 < g i`
  simp only [Balanced, not_forall, not_le] at hnb
  obtain ⟨i, j, hlt⟩ := hnb
  have hij : i ≠ j := by rintro rfl; omega
  have hge : g j + 2 ≤ g i := by omega
  -- the swapped configuration
  classical
  set g' : Fin k → ℕ := fun x => if x = i then g i - 1 else if x = j then g j + 1 else g x with hg'
  have hg'i : g' i = g i - 1 := by simp [hg']
  have hg'j : g' j = g j + 1 := by simp [hg', hij.symm]
  have hg'rest : ∀ x ∈ (univ.erase i).erase j, g' x = g x := by
    intro x hx
    rw [mem_erase] at hx
    obtain ⟨hxj, hx'⟩ := hx
    rw [mem_erase] at hx'
    obtain ⟨hxi, -⟩ := hx'
    simp [hg', hxi, hxj]
  refine ⟨g', ?_, ?_, ?_⟩
  · -- positivity
    intro x
    by_cases hxi : x = i
    · subst hxi; rw [hg'i]; omega
    · by_cases hxj : x = j
      · subst hxj; rw [hg'j]; omega
      · simp [hg', hxi, hxj]; exact hpos x
  · -- sum preserved
    have h1 : ∑ x, g' x
        = (g i - 1) + (g j + 1) + ∑ x ∈ (univ.erase i).erase j, g x := by
      rw [sum_split_two g' hij, hg'i, hg'j]
      congr 1
      exact Finset.sum_congr rfl hg'rest
    rw [h1, ← hsum, sum_split_two g hij]
    omega
  · -- energy strictly drops
    have hci : ((g' i : ℝ)) = (g i : ℝ) - 1 := by
      rw [hg'i, Nat.cast_sub (by omega), Nat.cast_one]
    have hcj : ((g' j : ℝ)) = (g j : ℝ) + 1 := by
      rw [hg'j]; push_cast; ring
    have hE_g' : energy V g' = V ((g i : ℝ) - 1) + V ((g j : ℝ) + 1)
        + ∑ x ∈ (univ.erase i).erase j, V ((g x : ℝ)) := by
      rw [energy, sum_split_two (fun x => V ((g' x : ℝ))) hij, hci, hcj]
      congr 1
      exact Finset.sum_congr rfl (fun x hx => by rw [hg'rest x hx])
    have hE_g : energy V g = V ((g i : ℝ)) + V ((g j : ℝ))
        + ∑ x ∈ (univ.erase i).erase j, V ((g x : ℝ)) := by
      rw [energy, sum_split_two (fun x => V ((g x : ℝ))) hij]
    rw [hE_g', hE_g]
    have hmem_a : (g i : ℝ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (by positivity)
    have hmem_b : (g j : ℝ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (by positivity)
    have hsw := swap_lt hV hmem_a hmem_b (by exact_mod_cast hge)
    linarith [hsw]

/-- **ME characterization.** Any configuration that minimizes the (strictly convex) energy over all valid
    configurations of the same sum is `Balanced` — i.e. maximally even. -/
theorem minimizer_balanced {k n : ℕ} {V : ℝ → ℝ} (hV : StrictConvexOn ℝ (Set.Ici (0 : ℝ)) V)
    (g : Fin k → ℕ) (hpos : ∀ i, 1 ≤ g i) (hsum : ∑ i, g i = n)
    (hmin : ∀ g' : Fin k → ℕ, (∀ i, 1 ≤ g' i) → (∑ i, g' i = n) → energy V g ≤ energy V g') :
    Balanced g := by
  by_contra hnb
  obtain ⟨g', hg'pos, hg'sum, hg'lt⟩ := exists_improve hV g hpos hsum hnb
  exact absurd (hmin g' hg'pos hg'sum) (not_le.mpr hg'lt)

/-! ### Part 3 — the converse: every Balanced config is a global energy minimizer -/

/-- Closed form of the energy of ANY balanced valid config: it depends only on `(k, n, V)`.
    Writing `m = ⌊n/k⌋` and `r = n % k`, exactly `r` gaps equal `m+1` and `k − r` equal `m`, so
    `energy V g = r · V(m+1) + (k−r) · V(m)`. (Counting identity; no convexity needed.) -/
theorem balanced_energy_closed {k n : ℕ} (V : ℝ → ℝ) (g : Fin k → ℕ)
    (hpos : ∀ i, 1 ≤ g i) (hsum : ∑ i, g i = n) (hbal : Balanced g) :
    energy V g = ((n % k : ℕ) : ℝ) * V (((n / k : ℕ) : ℝ) + 1)
               + ((k - n % k : ℕ) : ℝ) * V ((n / k : ℕ) : ℝ) := by
  classical
  set m := n / k with hm
  set r := n % k with hr
  have hdm : k * m + r = n := by
    have h := Nat.div_add_mod n k; rw [← hm, ← hr] at h; exact h
  -- every gap is `m` or `m+1`
  have hmem : ∀ i, g i = m ∨ g i = m + 1 := by
    intro i
    have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; exact i.elim0)
    have hrk : r < k := by rw [hr]; exact Nat.mod_lt n hk
    have hub : g i ≤ m + 1 := by
      by_contra hgt
      have hall : ∀ j ∈ (univ : Finset (Fin k)), m + 1 ≤ g j := by
        intro j _; have hb := hbal i j; omega
      have hle := Finset.card_nsmul_le_sum univ g (m + 1) hall
      rw [hsum, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] at hle
      have hexp : k * (m + 1) = k * m + k := by ring
      rw [hexp] at hle; omega
    have hlb : m ≤ g i := by
      by_contra hlt
      have hlt' : g i < m := not_le.mp hlt
      have hall : ∀ j ∈ (univ : Finset (Fin k)), g j ≤ m := by
        intro j _; have hb := hbal j i; omega
      have hlt2 := Finset.sum_lt_sum hall ⟨i, mem_univ i, hlt'⟩
      rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] at hlt2
      omega
    omega
  -- counts of the two gap values
  set c := (univ.filter (fun i => g i = m + 1)).card with hc
  set d := (univ.filter (fun i => ¬ g i = m + 1)).card with hd
  have hcardP : c + d = k := by
    rw [hc, hd, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have hval2 : ∀ i ∈ univ.filter (fun i => ¬ g i = m + 1), g i = m := by
    intro i hi; rw [Finset.mem_filter] at hi
    rcases hmem i with h | h
    · exact h
    · exact absurd h hi.2
  -- ℕ split of the sum to pin `c = r`
  have key : (∑ i ∈ univ.filter (fun i => g i = m + 1), g i)
           + (∑ i ∈ univ.filter (fun i => ¬ g i = m + 1), g i) = ∑ i, g i :=
    Finset.sum_filter_add_sum_filter_not univ _ g
  have e1 : (∑ i ∈ univ.filter (fun i => g i = m + 1), g i) = c * (m + 1) := by
    rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2),
        Finset.sum_const, nsmul_eq_mul, Nat.cast_id, ← hc]
  have e2 : (∑ i ∈ univ.filter (fun i => ¬ g i = m + 1), g i) = d * m := by
    rw [Finset.sum_congr rfl hval2, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, ← hd]
  have hcount : k * m + c = n := by
    have h := key; rw [e1, e2, hsum] at h
    have hrw : c * (m + 1) + d * m = k * m + c := by
      have e : c * (m + 1) + d * m = (c + d) * m + c := by ring
      rw [e, hcardP]
    rw [hrw] at h; exact h
  have hc_eq : c = r := by omega
  have hd_eq : d = k - r := by omega
  -- ℝ split of the energy into the two value classes
  have hPval : ∀ i ∈ univ.filter (fun i => g i = m + 1), V ((g i : ℝ)) = V ((m : ℝ) + 1) := by
    intro i hi; rw [Finset.mem_filter] at hi
    have hcast : (g i : ℝ) = (m : ℝ) + 1 := by rw [hi.2]; push_cast; ring
    rw [hcast]
  have hNval : ∀ i ∈ univ.filter (fun i => ¬ g i = m + 1), V ((g i : ℝ)) = V ((m : ℝ)) := by
    intro i hi; rw [hval2 i hi]
  have keyE : (∑ i ∈ univ.filter (fun i => g i = m + 1), V ((g i : ℝ)))
            + (∑ i ∈ univ.filter (fun i => ¬ g i = m + 1), V ((g i : ℝ))) = energy V g := by
    rw [energy]; exact Finset.sum_filter_add_sum_filter_not univ _ (fun i => V ((g i : ℝ)))
  have hEP : (∑ i ∈ univ.filter (fun i => g i = m + 1), V ((g i : ℝ))) = (c : ℝ) * V ((m : ℝ) + 1) := by
    rw [Finset.sum_congr rfl hPval, Finset.sum_const, nsmul_eq_mul, ← hc]
  have hEN : (∑ i ∈ univ.filter (fun i => ¬ g i = m + 1), V ((g i : ℝ))) = (d : ℝ) * V ((m : ℝ)) := by
    rw [Finset.sum_congr rfl hNval, Finset.sum_const, nsmul_eq_mul, ← hd]
  rw [← keyE, hEP, hEN, hc_eq, hd_eq]

/-- **Balanced configs all have the same energy.** Any two balanced valid configs of the same `(k, n)`
    have equal energy for any `V` (they are permutations of each other). -/
theorem balanced_energy_eq {k n : ℕ} (V : ℝ → ℝ) (g g' : Fin k → ℕ)
    (hpos : ∀ i, 1 ≤ g i) (hsum : ∑ i, g i = n) (hbal : Balanced g)
    (hpos' : ∀ i, 1 ≤ g' i) (hsum' : ∑ i, g' i = n) (hbal' : Balanced g') :
    energy V g = energy V g' := by
  rw [balanced_energy_closed V g hpos hsum hbal, balanced_energy_closed V g' hpos' hsum' hbal']

/-- Termination measure for the swap descent: `Φ g = ∑ (g i)²`, a strictly-decreasing ℕ-valued
    well-founded measure under any balancing swap (independent of `V`). -/
def phi {k : ℕ} (g : Fin k → ℕ) : ℕ := ∑ i, (g i) ^ 2

/-- **Improvement step with the `Φ` measure.** Same single swap as `exists_improve`, additionally
    certifying that the termination measure `Φ` strictly drops (`Δ = 2(b−a)+2 ≤ −2`). -/
theorem exists_improve_phi {k n : ℕ} {V : ℝ → ℝ} (hV : StrictConvexOn ℝ (Set.Ici (0 : ℝ)) V)
    (g : Fin k → ℕ) (hpos : ∀ i, 1 ≤ g i) (hsum : ∑ i, g i = n) (hnb : ¬ Balanced g) :
    ∃ g' : Fin k → ℕ, (∀ i, 1 ≤ g' i) ∧ (∑ i, g' i = n)
      ∧ energy V g' < energy V g ∧ phi g' < phi g := by
  simp only [Balanced, not_forall, not_le] at hnb
  obtain ⟨i, j, hlt⟩ := hnb
  have hij : i ≠ j := by rintro rfl; omega
  have hge : g j + 2 ≤ g i := by omega
  classical
  set g' : Fin k → ℕ := fun x => if x = i then g i - 1 else if x = j then g j + 1 else g x with hg'
  have hg'i : g' i = g i - 1 := by simp [hg']
  have hg'j : g' j = g j + 1 := by simp [hg', hij.symm]
  have hg'rest : ∀ x ∈ (univ.erase i).erase j, g' x = g x := by
    intro x hx
    rw [mem_erase] at hx
    obtain ⟨hxj, hx'⟩ := hx
    rw [mem_erase] at hx'
    obtain ⟨hxi, -⟩ := hx'
    simp [hg', hxi, hxj]
  refine ⟨g', ?_, ?_, ?_, ?_⟩
  · intro x
    by_cases hxi : x = i
    · subst hxi; rw [hg'i]; omega
    · by_cases hxj : x = j
      · subst hxj; rw [hg'j]; omega
      · simp [hg', hxi, hxj]; exact hpos x
  · have h1 : ∑ x, g' x
        = (g i - 1) + (g j + 1) + ∑ x ∈ (univ.erase i).erase j, g x := by
      rw [sum_split_two g' hij, hg'i, hg'j]
      congr 1
      exact Finset.sum_congr rfl hg'rest
    rw [h1, ← hsum, sum_split_two g hij]
    omega
  · have hci : ((g' i : ℝ)) = (g i : ℝ) - 1 := by
      rw [hg'i, Nat.cast_sub (by omega), Nat.cast_one]
    have hcj : ((g' j : ℝ)) = (g j : ℝ) + 1 := by
      rw [hg'j]; push_cast; ring
    have hE_g' : energy V g' = V ((g i : ℝ) - 1) + V ((g j : ℝ) + 1)
        + ∑ x ∈ (univ.erase i).erase j, V ((g x : ℝ)) := by
      rw [energy, sum_split_two (fun x => V ((g' x : ℝ))) hij, hci, hcj]
      congr 1
      exact Finset.sum_congr rfl (fun x hx => by rw [hg'rest x hx])
    have hE_g : energy V g = V ((g i : ℝ)) + V ((g j : ℝ))
        + ∑ x ∈ (univ.erase i).erase j, V ((g x : ℝ)) := by
      rw [energy, sum_split_two (fun x => V ((g x : ℝ))) hij]
    rw [hE_g', hE_g]
    have hmem_a : (g i : ℝ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (by positivity)
    have hmem_b : (g j : ℝ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (by positivity)
    have hsw := swap_lt hV hmem_a hmem_b (by exact_mod_cast hge)
    linarith [hsw]
  · -- the same swap strictly decreases `Φ = ∑ (g i)²`
    have hPhi_g' : phi g' = (g i - 1) ^ 2 + (g j + 1) ^ 2
        + ∑ x ∈ (univ.erase i).erase j, (g x) ^ 2 := by
      rw [phi, sum_split_two (fun x => (g' x) ^ 2) hij, hg'i, hg'j]
      congr 1
      exact Finset.sum_congr rfl (fun x hx => by rw [hg'rest x hx])
    have hPhi_g : phi g = (g i) ^ 2 + (g j) ^ 2
        + ∑ x ∈ (univ.erase i).erase j, (g x) ^ 2 := by
      rw [phi, sum_split_two (fun x => (g x) ^ 2) hij]
    rw [hPhi_g', hPhi_g]
    apply Nat.add_lt_add_right
    obtain ⟨t, ht⟩ := Nat.le.dest hge
    have hi1 : g i - 1 = g j + 1 + t := by omega
    rw [hi1, ← ht]
    have expand : (g j + 2 + t) ^ 2 + (g j) ^ 2
        = (g j + 1 + t) ^ 2 + (g j + 1) ^ 2 + (2 * t + 2) := by ring
    rw [expand]; omega

/-- **The converse (target).** For strictly convex `V`, any `Balanced` valid config is a GLOBAL energy
    minimizer over all valid configs of the same sum. Proof: well-founded descent on `Φ = ∑ (g i)²` —
    a non-balanced config strictly improves (lower energy AND lower `Φ`) via `exists_improve_phi`, and a
    balanced config matches `g`'s energy via `balanced_energy_eq`. -/
theorem balanced_isMinimizer {k n : ℕ} {V : ℝ → ℝ} (hV : StrictConvexOn ℝ (Set.Ici (0 : ℝ)) V)
    (g : Fin k → ℕ) (hgpos : ∀ i, 1 ≤ g i) (hgsum : ∑ i, g i = n) (hgbal : Balanced g) :
    ∀ g' : Fin k → ℕ, (∀ i, 1 ≤ g' i) → (∑ i, g' i = n) → energy V g ≤ energy V g' := by
  suffices H : ∀ N : ℕ, ∀ g' : Fin k → ℕ, phi g' ≤ N → (∀ i, 1 ≤ g' i) → (∑ i, g' i = n) →
      energy V g ≤ energy V g' by
    intro g' hpos hsum; exact H (phi g') g' le_rfl hpos hsum
  intro N
  induction N with
  | zero =>
      intro g' hphi hpos hsum
      by_cases hbal : Balanced g'
      · exact le_of_eq (balanced_energy_eq V g g' hgpos hgsum hgbal hpos hsum hbal)
      · obtain ⟨g'', _, _, _, hPhilt⟩ := exists_improve_phi hV g' hpos hsum hbal
        exfalso; omega
  | succ N IH =>
      intro g' hphi hpos hsum
      by_cases hbal : Balanced g'
      · exact le_of_eq (balanced_energy_eq V g g' hgpos hgsum hgbal hpos hsum hbal)
      · obtain ⟨g'', hpos'', hsum'', hElt, hPhilt⟩ := exists_improve_phi hV g' hpos hsum hbal
        have hle'' : phi g'' ≤ N := by omega
        have hrec := IH g'' hle'' hpos'' hsum''
        linarith

/-- **Ground-state characterization of maximal evenness (full iff).** For strictly convex `V`, a valid
    config `g` is a global energy minimizer over all valid configs of the same sum **iff** it is
    `Balanced` (maximally even). Combines `minimizer_balanced` (⇒) and `balanced_isMinimizer` (⇐). -/
theorem isMinimizer_iff_balanced {k n : ℕ} {V : ℝ → ℝ} (hV : StrictConvexOn ℝ (Set.Ici (0 : ℝ)) V)
    (g : Fin k → ℕ) (hpos : ∀ i, 1 ≤ g i) (hsum : ∑ i, g i = n) :
    (∀ g' : Fin k → ℕ, (∀ i, 1 ≤ g' i) → (∑ i, g' i = n) → energy V g ≤ energy V g') ↔ Balanced g := by
  constructor
  · intro hmin; exact minimizer_balanced hV g hpos hsum hmin
  · intro hbal; exact balanced_isMinimizer hV g hpos hsum hbal

/-! ### Part 4 — concrete music instance: the diatonic scale -/

/-- The circular gap word of the diatonic scale `{0,2,4,5,7,9,11} ⊂ ℤ/12`: `(2,2,1,2,2,2,1)`
    (`k = 7` gaps summing to `n = 12`). -/
def diatonicGaps : Fin 7 → ℕ := ![2, 2, 1, 2, 2, 2, 1]

/-- Every diatonic gap is positive. -/
theorem diatonic_pos : ∀ i, 1 ≤ diatonicGaps i := by decide

/-- The diatonic gaps sum to the octave, `n = 12`. -/
theorem diatonic_sum : ∑ i, diatonicGaps i = 12 := by decide

/-- **The diatonic scale is maximally even**: its gap word `(2,2,1,2,2,2,1)` is `Balanced`
    (`max − min = 2 − 1 = 1`). -/
theorem diatonic_balanced : Balanced diatonicGaps := by unfold Balanced; decide

/-- Strict convexity of `x ↦ x²` on `[0,∞)` (the canonical repulsive potential). -/
theorem strictConvexOn_sq : StrictConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => x ^ 2) :=
  strictConvexOn_pow (by norm_num)

/-- **Concrete corollary.** For the quadratic energy `E g = ∑ (g i)²`, any minimizer over valid configs
    of a fixed sum is `Balanced` (maximally even). Specializing the convex `minimizer_balanced`. -/
theorem sq_minimizer_balanced {k n : ℕ} (g : Fin k → ℕ) (hpos : ∀ i, 1 ≤ g i)
    (hsum : ∑ i, g i = n)
    (hmin : ∀ g' : Fin k → ℕ, (∀ i, 1 ≤ g' i) → (∑ i, g' i = n) →
      energy (fun x => x ^ 2) g ≤ energy (fun x => x ^ 2) g') :
    Balanced g :=
  minimizer_balanced strictConvexOn_sq g hpos hsum hmin

/-- **The diatonic gap word is a global minimizer of `∑ gaps²`.** Concrete instance of the converse:
    the diatonic `(2,2,1,2,2,2,1)` minimizes the quadratic energy over every valid `7`-gap config
    summing to `12` — the full ground-state statement of its maximal evenness. -/
theorem diatonic_sq_isMinimizer :
    ∀ g' : Fin 7 → ℕ, (∀ i, 1 ≤ g' i) → (∑ i, g' i = 12) →
      energy (fun x => x ^ 2) diatonicGaps ≤ energy (fun x => x ^ 2) g' :=
  balanced_isMinimizer strictConvexOn_sq diatonicGaps diatonic_pos diatonic_sum diatonic_balanced

/-- **Full iff at the diatonic.** Specializing the ground-state characterization to `V = x²`, `7`-of-`12`. -/
theorem diatonic_sq_iff :
    (∀ g' : Fin 7 → ℕ, (∀ i, 1 ≤ g' i) → (∑ i, g' i = 12) →
      energy (fun x => x ^ 2) diatonicGaps ≤ energy (fun x => x ^ 2) g') ↔ Balanced diatonicGaps :=
  isMinimizer_iff_balanced strictConvexOn_sq diatonicGaps diatonic_pos diatonic_sum

end MaximalEvenness

end MusicTheory
