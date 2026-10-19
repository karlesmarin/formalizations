/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.List.Basic

/-!
# The arithmetic of the moments `A₄`, `D`, `W` in `SU(7)` gauge-Higgs unification

The one-loop Wilson-line potential of the six-dimensional `SU(7)` model of Komori and Maru has
moments `A₄`, `D`, `W` that are sums over the bulk multiplets plus a gauge-sector contribution.
The gauge-sector contribution is read from eq. (68) of Komori–Maru and is a physical input, not
a logical step; two values ("seeds") are considered: the one printed (`gaugePublished`) and a
candidate with the ghost subtraction (`gaugeCandidate`). This file proves the statements that do
not depend on the seed, and states the one that does with its hypothesis explicit.

The coordinates are `(2 A₄, 8 D, 2 W)`: with the candidate seed `A₄` is a half-integer, so `2 A₄`
is the integer coordinate, and the proof of the mod-`6` law only uses the combination
`8 D − 2 A₄`.

## Main results

* `matter_key_mod6`, `matter_w2_even`, `matter_d_even`: the eight bulk multiplets
  (`7`, `28`, `48`, `84`, each with two parities) have `8D − 2A₄ ≡ 0 (mod 6)`, `2W` even and
  `8D` even.
* `key_seed_independent`: both seeds give `8D − 2A₄ = 9`.
* `mod6_law`: for every content with natural multiplicities, `8D ≡ 2A₄ + 3 (mod 6)`.
* `twoW_odd`: `2W` is odd for every content.
* `oddEighths`: if the gauge contribution to `8D` is odd, then `8D` is odd for every content
  (so `D ≠ 0`); `oddEighths_published`: the hypothesis holds for the printed seed;
  `candidate_hypothesis_fails`: it fails for the candidate seed.

## References

* Y. Komori, N. Maru, *`SU(7)` grand gauge-Higgs unification*, arXiv:2503.04090, eq. (68).
-/

@[expose] public section

namespace GaugeHiggsUnification.OddEighths

/-- The eight bulk multiplets in coordinates `(2 A₄, 8 D, 2 W)`. `A₄` is an integer for matter,
so the first coordinate is its double. -/
def matter : List (ℤ × ℤ × ℤ) :=
  [ (0,   -6,   2),      -- 7(+,+)
    (2,    8,  -2),      -- 7(+,-)
    (34,  16,   6),      -- 28(+,+)
    (8,    2,  -6),      -- 28(+,-)
    (36,   0,  12),      -- 48(+,+)
    (16,  28, -12),      -- 48(+,-)
    (136, 10,  18),      -- 84(+,+)
    (218, 80, -18) ]     -- 84(+,-)

/-- The gauge sector as printed in eq. (68). -/
def gaugePublished : ℤ × ℤ × ℤ := (-36, -27, -3)

/-- The gauge sector with the ghost subtraction. -/
def gaugeCandidate : ℤ × ℤ × ℤ := (-27, -18, -3)

/-- The combination `8 D − 2 A₄`. -/
def key (v : ℤ × ℤ × ℤ) : ℤ := v.2.1 - v.1

/-- The third coordinate, `2 W`. -/
def w2 (v : ℤ × ℤ × ℤ) : ℤ := v.2.2

/-! ### The matter multiplets -/

/-- Every matter multiplet has `8 D − 2 A₄ ≡ 0 (mod 6)`. -/
theorem matter_key_mod6 : ∀ v ∈ matter, (6 : ℤ) ∣ key v := by decide

/-- Every matter multiplet has `2 W` even. -/
theorem matter_w2_even : ∀ v ∈ matter, (2 : ℤ) ∣ w2 v := by decide

/-! ### The gauge base point: the same `9` for both seeds -/

/-- The printed seed gives `8 D − 2 A₄ = 9`. -/
theorem key_published : key gaugePublished = 9 := by decide

/-- The candidate seed gives the same `9`. -/
theorem key_candidate : key gaugeCandidate = 9 := by decide

/-- The two seeds agree on `8 D − 2 A₄`. -/
theorem key_seed_independent : key gaugePublished = key gaugeCandidate := by decide

/-- Both seeds have `2 W` odd. -/
theorem gauge_w2_odd : ¬ (2 : ℤ) ∣ w2 gaugePublished ∧ ¬ (2 : ℤ) ∣ w2 gaugeCandidate := by decide

/-! ### Linearity: arbitrary content -/

/-- A content is a list of natural multiplicities against the generators; `combo ns xs` is the
weighted sum of one coordinate. -/
def combo (ns : List ℕ) (xs : List ℤ) : ℤ :=
  (List.zipWith (fun (k : ℕ) (x : ℤ) => (k : ℤ) * x) ns xs).sum

/-- If `d` divides every generator, it divides every combination with natural multiplicities. -/
theorem dvd_combo {d : ℤ} (ns : List ℕ) (xs : List ℤ) (h : ∀ x ∈ xs, d ∣ x) :
    d ∣ combo ns xs := by
  unfold combo
  induction ns generalizing xs with
  | nil => simp
  | cons k ks ih =>
    cases xs with
    | nil => simp
    | cons x xs =>
      simp only [List.zipWith_cons_cons, List.sum_cons]
      obtain ⟨c, hc⟩ := h x (by simp)
      obtain ⟨e, he⟩ := ih xs (fun y hy => h y (by simp [hy]))
      exact ⟨(k : ℤ) * c + e, by rw [hc, he]; ring⟩

/-! ### The three statements -/

/-- **The mod-`6` law, independent of the seed.** For every gauge base point with
`8 D − 2 A₄ = 9` (both seeds, by `key_published` and `key_candidate`) and every content,
`8 D − 2 A₄ ≡ 3 (mod 6)`. -/
theorem mod6_law (g : ℤ × ℤ × ℤ) (hg : key g = 9) (ns : List ℕ) :
    (key g + combo ns (matter.map key)) % 6 = 3 := by
  have hc : (6 : ℤ) ∣ combo ns (matter.map key) := by
    refine dvd_combo ns _ ?_
    intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
    exact matter_key_mod6 v hv
  obtain ⟨t, ht⟩ := hc
  rw [hg, ht]
  omega

/-- **`2 W` is odd, independently of the seed.** The gauge sector contributes `−3` with both
seeds and matter contributes an even number. -/
theorem twoW_odd (g : ℤ × ℤ × ℤ) (hg : w2 g = -3) (ns : List ℕ) :
    ¬ (2 : ℤ) ∣ (w2 g + combo ns (matter.map w2)) := by
  have hc : (2 : ℤ) ∣ combo ns (matter.map w2) := by
    refine dvd_combo ns _ ?_
    intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
    exact matter_w2_even v hv
  obtain ⟨t, ht⟩ := hc
  rw [hg, ht]
  omega

/-- **Odd eighths, conditional.** If the gauge contribution to `8 D` is odd and the matter
contribution is even, then `8 D` is odd, hence non-zero. The hypothesis on the gauge sector is
an input from eq. (68). -/
theorem oddEighths (dGauge : ℤ) (hodd : ¬ (2 : ℤ) ∣ dGauge) (ns : List ℕ)
    (hmatter : (2 : ℤ) ∣ combo ns (matter.map (fun v => v.2.1))) :
    ¬ (2 : ℤ) ∣ (dGauge + combo ns (matter.map (fun v => v.2.1))) := by
  obtain ⟨t, ht⟩ := hmatter
  rw [ht]
  omega

/-- Every matter multiplet contributes an even `8 D`: the matter hypothesis of `oddEighths`. -/
theorem matter_d_even : ∀ v ∈ matter, (2 : ℤ) ∣ v.2.1 := by decide

/-- For the printed seed (`8 D = −27`, odd), `8 D` is odd for every content. -/
theorem oddEighths_published (ns : List ℕ) :
    ¬ (2 : ℤ) ∣ ((-27 : ℤ) + combo ns (matter.map (fun v => v.2.1))) := by
  refine oddEighths (-27) (by decide) ns ?_
  refine dvd_combo ns _ ?_
  intro x hx
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
  exact matter_d_even v hv

/-- For the candidate seed the hypothesis of `oddEighths` fails: its `8 D` is `−18`, even. -/
theorem candidate_hypothesis_fails : (2 : ℤ) ∣ (gaugeCandidate.2.1) := by decide

end GaugeHiggsUnification.OddEighths
