/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.SetTheory.Ordinal.Notation

/-!
# Choice-free well-foundedness of ordinal notations below `ε₀`

Mathlib proves that its normal ordinal notations are well founded (`NONote.lt_wf`), but its
order `<` and normal form `ONote.NF` on `ONote` are defined through `ONote.repr : ONote → Ordinal`,
so that proof depends on `Classical.choice` (through `Ordinal.lt_wf`).

This file defines a syntactic strict order `slt` (lexicographic comparison by `ONote.cmp`) and a
syntactic Cantor normal form `SNF` on Mathlib's `ONote`, neither of which mentions `Ordinal` or
`repr`, and proves directly that `slt` is well founded on syntactic normal forms, by a nested
induction (exponent, coefficient, tail) in the style of Gentzen and Schütte. The core results
depend only on `propext`.

A bridge section proves that `slt` and `SNF` agree with Mathlib's `<` and `NF`; the bridge does
use `Classical.choice`.

## Main results

* `slt`, `SNF`: the syntactic order and normal form;
* `eq_of_cmp_eq'`: a choice-free version of `ONote.eq_of_cmp_eq`;
* `acc_slt`: every syntactic normal form is accessible for `slt` restricted to `SNF`;
* `wf_slt`: `slt` is well founded on `{a // SNF a}`;
* `ti_syntactic`: transfinite induction below `ε₀` on syntactic normal forms;
* `slt_iff_lt`, `SNF_iff_NF`: the bridge to Mathlib's `<` and `ONote.NF`.

## References

* B. Bryce, R. Goré, arXiv:2603.00487 (2026): Gentzen's consistency proof for PA in Coq.
-/

@[expose] public section

namespace Gentzen.Acc

open ONote

/-! ## Syntactic order and normal form (no `Ordinal`, no `repr`) -/

/-- Syntactic strict order on notations: lexicographic comparison by `ONote.cmp`. -/
def slt (a b : ONote) : Prop := ONote.cmp a b = Ordering.lt

instance (a b : ONote) : Decidable (slt a b) :=
  inferInstanceAs (Decidable (ONote.cmp a b = Ordering.lt))

/-- `topBelow a e`: the leading exponent of `a` (if any) is `slt`-below `e`. -/
def topBelow : ONote → ONote → Prop
  | ONote.zero, _ => True
  | ONote.oadd e' _ _, e => slt e' e

/-- Syntactic Cantor normal form: exponents strictly decreasing (w.r.t. `slt`), recursively. -/
def SNF : ONote → Prop
  | ONote.zero => True
  | ONote.oadd e _ a => SNF e ∧ SNF a ∧ topBelow a e

instance decTopBelow : ∀ a e, Decidable (topBelow a e)
  | ONote.zero, _ => isTrue trivial
  | ONote.oadd e' _ _, e => inferInstanceAs (Decidable (slt e' e))

instance decSNF : ∀ a, Decidable (SNF a)
  | ONote.zero => isTrue trivial
  | ONote.oadd e _ a =>
    @instDecidableAnd _ _ (decSNF e) (@instDecidableAnd _ _ (decSNF a) (decTopBelow a e))

/-! ## Constructive facts about `Ordering.then` and `cmp` -/

theorem then_eq_lt {o p : Ordering} (h : o.then p = Ordering.lt) :
    o = Ordering.lt ∨ (o = Ordering.eq ∧ p = Ordering.lt) := by
  cases o with
  | lt => exact Or.inl rfl
  | eq => exact Or.inr ⟨rfl, h⟩
  | gt => exact Ordering.noConfusion h

theorem then_eq_eq {o p : Ordering} (h : o.then p = Ordering.eq) :
    o = Ordering.eq ∧ p = Ordering.eq := by
  cases o with
  | lt => exact Ordering.noConfusion h
  | eq => exact ⟨rfl, h⟩
  | gt => exact Ordering.noConfusion h

theorem natCmp_lt {m n : ℕ} (h : _root_.cmp m n = Ordering.lt) : m < n := by
  unfold _root_.cmp cmpUsing at h
  cases Nat.decLt m n with
  | isTrue h1 => exact h1
  | isFalse h1 =>
    rw [ite_eq_right h1] at h
    cases Nat.decLt n m with
    | isTrue h2 => rw [ite_eq_left h2] at h; exact Ordering.noConfusion h
    | isFalse h2 => rw [ite_eq_right h2] at h; exact Ordering.noConfusion h

theorem natCmp_eq {m n : ℕ} (h : _root_.cmp m n = Ordering.eq) : m = n := by
  unfold _root_.cmp cmpUsing at h
  cases Nat.decLt m n with
  | isTrue h1 => rw [ite_eq_left h1] at h; exact Ordering.noConfusion h
  | isFalse h1 =>
    rw [ite_eq_right h1] at h
    cases Nat.decLt n m with
    | isTrue h2 => rw [ite_eq_left h2] at h; exact Ordering.noConfusion h
    | isFalse h2 => exact Nat.le_antisymm (Nat.ge_of_not_lt h2) (Nat.ge_of_not_lt h1)

/-- Constructive version of `ONote.eq_of_cmp_eq`. -/
theorem eq_of_cmp_eq' : ∀ {a b : ONote}, ONote.cmp a b = Ordering.eq → a = b
  | ONote.zero, ONote.zero, _ => rfl
  | ONote.zero, ONote.oadd _ _ _, h => Ordering.noConfusion h
  | ONote.oadd _ _ _, ONote.zero, h => Ordering.noConfusion h
  | ONote.oadd e n a, ONote.oadd e' n' a', h => by
    have h' : (ONote.cmp e e').then ((_root_.cmp (n : ℕ) n').then (ONote.cmp a a')) =
        Ordering.eq := h
    obtain ⟨h1, h2⟩ := then_eq_eq h'
    obtain ⟨h2, h3⟩ := then_eq_eq h2
    rw [eq_of_cmp_eq' h1, PNat.eq (natCmp_eq h2), eq_of_cmp_eq' h3]

theorem not_slt_zero : ∀ a, ¬ slt a ONote.zero
  | ONote.zero, h => Ordering.noConfusion h
  | ONote.oadd _ _ _, h => Ordering.noConfusion h

theorem slt_oadd_cases {e n a e' n' a'} (h : slt (ONote.oadd e' n' a') (ONote.oadd e n a)) :
    slt e' e ∨ (e' = e ∧ (n' : ℕ) < n) ∨ (e' = e ∧ n' = n ∧ slt a' a) := by
  have h' : (ONote.cmp e' e).then ((_root_.cmp (n' : ℕ) n).then (ONote.cmp a' a)) =
      Ordering.lt := h
  rcases then_eq_lt h' with h1 | ⟨h1, h2⟩
  · exact Or.inl h1
  · rcases then_eq_lt h2 with h3 | ⟨h3, h4⟩
    · exact Or.inr (Or.inl ⟨eq_of_cmp_eq' h1, natCmp_lt h3⟩)
    · exact Or.inr (Or.inr ⟨eq_of_cmp_eq' h1, PNat.eq (natCmp_eq h3), h4⟩)

/-! ## Accessibility -/

/-- The relation whose accessibility we prove: `slt` restricted to syntactic normal forms. -/
def R (x y : ONote) : Prop := SNF x ∧ slt x y

theorem acc_zero : Acc R ONote.zero :=
  Acc.intro _ fun x hx => absurd hx.2 (not_slt_zero x)

/-- `H e`: every normal notation below `ω ^ e` is accessible. -/
def H (e : ONote) : Prop := ∀ x, SNF x → topBelow x e → Acc R x

/-- Coefficient/tail step: if everything below `ω^e` is accessible, so is `ω^e·n + a`
for accessible `a` (induction on the coefficient bound `k`, then on `Acc a`). -/
theorem acc_oadd_of_H {e : ONote} (hH : H e) :
    ∀ k : ℕ, ∀ n : ℕ+, (n : ℕ) ≤ k → ∀ a, Acc R a → SNF (ONote.oadd e n a) →
      Acc R (ONote.oadd e n a) := by
  intro k
  induction k with
  | zero => intro n hn; exact absurd hn (Nat.not_le_of_gt n.2)
  | succ k ihk =>
    intro n hn a ha
    induction ha with
    | intro a _ iha =>
      intro hs
      refine Acc.intro _ fun x hx => ?_
      cases x with
      | zero => exact acc_zero
      | oadd e' n' a' =>
        have hxs : SNF (ONote.oadd e' n' a') := hx.1
        rcases slt_oadd_cases hx.2 with h1 | ⟨rfl, h2⟩ | ⟨rfl, rfl, h3⟩
        · exact hH _ hxs h1
        · exact ihk n' (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le h2 hn)) a'
            (hH a' hxs.2.1 hxs.2.2) hxs
        · exact iha a' ⟨hxs.2.1, h3⟩ hxs

/-- Exponent step (the "accessibility of `ω^x`" lemma): induction on `Acc e`. -/
theorem H_of_acc : ∀ e, Acc R e → H e := by
  intro e he
  induction he with
  | intro e _ ih =>
    intro x hx htop
    cases x with
    | zero => exact acc_zero
    | oadd e' n' a' =>
      have hH' : H e' := ih e' ⟨hx.1, htop⟩
      exact acc_oadd_of_H hH' n' n' (Nat.le_refl _) a' (hH' a' hx.2.1 hx.2.2) hx

/-- Main theorem: every syntactic normal form is accessible for `slt` restricted to `SNF`. -/
theorem acc_slt : ∀ a, SNF a → Acc (fun x y => SNF x ∧ slt x y) a
  | ONote.zero, _ => acc_zero
  | ONote.oadd e n a, h =>
    have He : H e := H_of_acc e (acc_slt e h.1)
    acc_oadd_of_H He n n (Nat.le_refl _) a (He a h.2.1 h.2.2) h

/-- Well-foundedness of `slt` on the subtype of syntactic normal forms. -/
theorem wf_slt : WellFounded (fun x y : {a // SNF a} => slt x.1 y.1) := by
  refine ⟨fun ⟨a, ha⟩ => ?_⟩
  have key : ∀ a, Acc R a → ∀ ha : SNF a,
      Acc (fun x y : {a // SNF a} => slt x.1 y.1) ⟨a, ha⟩ := by
    intro a hacc
    induction hacc with
    | intro a _ ih =>
      intro ha
      exact Acc.intro _ fun ⟨y, hy⟩ hlt => ih y ⟨hy, hlt⟩ hy
  exact key a (acc_slt a ha) ha

/-- Transfinite induction below `ε₀` on syntactic normal forms (choice-free). -/
theorem ti_syntactic {P : ONote → Prop}
    (h : ∀ a, SNF a → (∀ b, SNF b → slt b a → P b) → P a) : ∀ a, SNF a → P a := by
  have key : ∀ a, Acc R a → SNF a → P a := by
    intro a hacc
    induction hacc with
    | intro a _ ih => exact fun ha => h a ha fun b hb hlt => ih b ⟨hb, hlt⟩ hb
  exact fun a ha => key a (acc_slt a ha) ha

/-! ## Bridge to Mathlib's `<` and `NF` (uses choice) -/

theorem slt_iff_lt (a b : ONote) [ONote.NF a] [ONote.NF b] : slt a b ↔ a < b := by
  have hc := ONote.cmp_compares a b
  unfold slt
  cases h : ONote.cmp a b with
  | lt => rw [h] at hc; exact ⟨fun _ => hc, fun _ => rfl⟩
  | eq =>
    rw [h] at hc
    exact ⟨fun h' => Ordering.noConfusion h', fun h' => absurd (hc ▸ h') (lt_irrefl _)⟩
  | gt =>
    rw [h] at hc
    exact ⟨fun h' => Ordering.noConfusion h', fun h' => absurd h' (lt_asymm hc)⟩

theorem topBelow_iff (a e : ONote) : topBelow a e ↔ ONote.TopBelow e a := by
  cases a <;> exact Iff.rfl

theorem SNF_iff_NF : ∀ a : ONote, SNF a ↔ ONote.NF a
  | ONote.zero => ⟨fun _ => ONote.NF.zero, fun _ => trivial⟩
  | ONote.oadd e n a => by
    constructor
    · intro ⟨he, ha, ht⟩
      have : ONote.NF e := (SNF_iff_NF e).1 he
      have : ONote.NF a := (SNF_iff_NF a).1 ha
      exact ONote.NF.oadd ‹_› n (ONote.nfBelow_iff_topBelow.2 ⟨‹ONote.NF a›, (topBelow_iff a e).1 ht⟩)
    · intro h
      have he : ONote.NF e := h.fst
      have hb := (@ONote.nfBelow_iff_topBelow e he a).1 h.snd'
      exact ⟨(SNF_iff_NF e).2 he, (SNF_iff_NF a).2 hb.1, (topBelow_iff a e).2 hb.2⟩

/-! ## Checks on samples (by `decide`) -/

/-- Samples, in increasing order: `0, 1, 2, ω, ω+1, ω·2, ω^ω`. -/
def samples : List ONote :=
  [0, 1, ONote.ofNat 2, ONote.oadd 1 1 0, ONote.oadd 1 1 1, ONote.oadd 1 2 0,
    ONote.oadd (ONote.oadd 1 1 0) 1 0]

/-- All samples are syntactic normal forms. -/
example : samples.all (fun a => decide (SNF a)) = true := by decide

/-- On the samples, `slt` is the order in which they are listed. -/
example : ((List.range 7).all fun i => (List.range 7).all fun j =>
    decide (slt (samples.getD i 0) (samples.getD j 0)) == decide (i < j)) = true := by decide

example : SNF (ONote.oadd (ONote.oadd 1 1 0) 1 (ONote.oadd 1 2 1)) := by decide
example : ¬ SNF (ONote.oadd 1 1 (ONote.oadd 1 1 0)) := by decide

end Gentzen.Acc
