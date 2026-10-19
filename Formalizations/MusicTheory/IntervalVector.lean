/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Tactic.Ring

/-!
# The interval vector of a pitch-class set

For a pitch-class set `A ⊆ ℤ/12`, `IVraw A k` counts the ordered pairs `(a, b) ∈ A × A` whose
interval class `min (a - b).val (b - a).val` is `k`; the textbook interval vector is
`IVraw A k / 2`. The interval class is written so that invariance under negation is `min_comm`;
invariance is proved once for every embedding of `ℤ/12` preserving differences up to sign, and
transposition and inversion are special cases.

## Main results

* `IVraw_map`: invariance under a difference-class-preserving embedding.
* `IVraw_tpose`, `IVraw_invert`: the interval vector is invariant under transposition and inversion.

## References

* C. Marín, *One transform and one duality: a machine-checked core of music theory in Lean 4*,
  Zenodo (2026), doi:10.5281/zenodo.20953767.
-/

@[expose] public section

namespace MusicTheory

open Finset

namespace IntervalVector

/-- Interval class of a pitch-class difference: `min(d, 12−d)`, value in `0..6`.
    Written as `min d.val (-d).val` so that neg-invariance is just `min_comm`. -/
def ivc (d : ZMod 12) : ℕ := min d.val (-d).val

@[simp] lemma ivc_neg (d : ZMod 12) : ivc (-d) = ivc d := by
  unfold ivc; rw [neg_neg, min_comm]

/-- Raw interval vector: number of ORDERED pairs `(a,b) ∈ A×A` with interval class `k`.
    The textbook interval vector is `IVraw A k / 2` for `k = 1..6` (each unordered pair twice). -/
def IVraw (A : Finset (ZMod 12)) (k : ℕ) : ℕ :=
  ∑ a ∈ A, ∑ b ∈ A, if ivc (a - b) = k then 1 else 0

/-- C major triad `{0,4,7}`: ordered counts are 2 at k=3,4,5 and 0 elsewhere, i.e. the textbook
    interval vector ⟨0 0 1 1 1 0⟩. -/
example : IVraw {0, 4, 7} 4 = 2 := by decide
example : IVraw {0, 4, 7} 5 = 2 := by decide
example : IVraw {0, 4, 7} 1 = 0 := by decide

/-- Invariance under any embedding of ℤ/12 that preserves the interval class of differences. -/
lemma IVraw_map (e : ZMod 12 ↪ ZMod 12)
    (he : ∀ a b : ZMod 12, ivc (e a - e b) = ivc (a - b)) (A : Finset (ZMod 12)) (k : ℕ) :
    IVraw (A.map e) k = IVraw A k := by
  simp only [IVraw, Finset.sum_map]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by rw [he a b]

/-- Transposition `Tₙ : a ↦ a + n`. -/
def tpose (n : ZMod 12) (A : Finset (ZMod 12)) : Finset (ZMod 12) :=
  A.map ⟨(· + n), add_left_injective n⟩
/-- Inversion `I : a ↦ −a`. -/
def invert (A : Finset (ZMod 12)) : Finset (ZMod 12) :=
  A.map ⟨(-·), neg_injective⟩

/-- **The interval vector is invariant under transposition.** -/
theorem IVraw_tpose (n : ZMod 12) (A : Finset (ZMod 12)) (k : ℕ) :
    IVraw (tpose n A) k = IVraw A k :=
  IVraw_map _ (fun a b => by
    simp only [Function.Embedding.coeFn_mk]
    rw [show a + n - (b + n) = a - b from by ring]) A k

/-- **The interval vector is invariant under inversion.** -/
theorem IVraw_invert (A : Finset (ZMod 12)) (k : ℕ) :
    IVraw (invert A) k = IVraw A k :=
  IVraw_map _ (fun a b => by
    simp only [Function.Embedding.coeFn_mk]
    rw [show -a - -b = -(a - b) from by ring, ivc_neg]) A k

end IntervalVector

end MusicTheory
