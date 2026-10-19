/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.SetTheory.Ordinal.Gentzen.Acc

/-!
# Choice-free `2 ^ α` and the cut-elimination inequalities below `ε₀`

The height-doubling map `twoPow'` (`2 ^ α`) and the inequalities L1–L5 of Gentzen's cut
elimination on Mathlib's `ONote`, stated with the syntactic order `slt` / `sle` and the syntactic
normal form `SNF` of `Formalizations.SetTheory.Ordinal.Gentzen.Acc`, without `Ordinal` or `repr`.
Writing `α = ω·γ + m`, `twoPow' α = ω ^ γ · 2 ^ m`. Syntactic addition `sadd` is Mathlib's
`ONote.add` (as data), and `ssucc` is the syntactic successor.

All results before the bridge section depend only on `propext`. (Mathlib's `ONote.opow` and the
core lemma `Nat.pow_lt_pow_right` depend on `Classical.choice`; they are not used.) The bridge
section, which does use choice, proves that `twoPow'`, `sadd` and `ssucc` denote `2 ^ α`, `α + β`
and `α + 1`, and that `twoPow'` agrees with Mathlib's `ONote.opow`, hence with
`Gentzen.Ordinals.twoPow`.

## Main results

* `twoPow'`, `ssucc`, `sadd`, `smax` and their closure under `SNF`
  (`SNF_twoPow'`, `SNF_ssucc`, `SNF_sadd`, `SNF_smax`);
* `twoPow'_slt`, `twoPow'_sle` (L3), `twoPow'_smax` (L4);
* `L1`, `L2`, `L5` and the counterexamples `L1_fails_at_zero`, `L2_fails_at_one`;
* `twoPow'_add_le`: `2^a + 2^b ≤ 2^(max a b + 1)` (two-premise cut);
* bridge: `repr_sadd`, `repr_ssucc`, `repr_twoPow'`, `twoPow'_eq_opow`, `ssucc_eq_add_one`.

## References

* B. Bryce, R. Goré, arXiv:2603.00487 (2026): Gentzen's consistency proof for PA in Coq.
-/

@[expose] public section

namespace Gentzen.TwoPow

open ONote Gentzen.Acc

/-! ## Constructive facts about `cmp` -/

theorem natCmp_of_lt {m n : ℕ} (h : m < n) : _root_.cmp m n = Ordering.lt := by
  unfold _root_.cmp cmpUsing; rw [ite_eq_left h]

theorem natCmp_self (n : ℕ) : _root_.cmp n n = Ordering.eq := by
  unfold _root_.cmp cmpUsing
  rw [ite_eq_right (Nat.lt_irrefl n), ite_eq_right (Nat.lt_irrefl n)]

/-- `2^i < 2^j` for `i < j` (own proof; `Nat.pow_lt_pow_right` pulls `Classical.choice`). -/
theorem two_pow_lt {i j : ℕ} (h : i < j) : 2 ^ i < 2 ^ j :=
  Nat.lt_of_lt_of_le
    (by rw [Nat.pow_succ, Nat.mul_two]; exact Nat.lt_add_of_pos_right (Nat.two_pow_pos i))
    (Nat.pow_le_pow_right (by decide) h)

theorem cmp_self : ∀ a : ONote, ONote.cmp a a = Ordering.eq
  | ONote.zero => rfl
  | ONote.oadd e n a => by
    show (ONote.cmp e e).then ((_root_.cmp (n : ℕ) n).then (ONote.cmp a a)) = Ordering.eq
    rw [cmp_self e, natCmp_self, cmp_self a]; rfl

theorem cmp_swap' : ∀ a b : ONote, (ONote.cmp a b).swap = ONote.cmp b a
  | ONote.zero, ONote.zero => rfl
  | ONote.zero, ONote.oadd _ _ _ => rfl
  | ONote.oadd _ _ _, ONote.zero => rfl
  | ONote.oadd e n a, ONote.oadd e' n' a' => by
    show ((ONote.cmp e e').then ((_root_.cmp (n : ℕ) n').then (ONote.cmp a a'))).swap =
      (ONote.cmp e' e).then ((_root_.cmp (n' : ℕ) n).then (ONote.cmp a' a))
    rw [Ordering.swap_then, Ordering.swap_then, cmp_swap' e e', _root_.cmp_swap, cmp_swap' a a']

theorem slt_irrefl (a : ONote) : ¬ slt a a := fun h => by
  have h' : ONote.cmp a a = Ordering.lt := h
  rw [cmp_self] at h'; exact Ordering.noConfusion h'

theorem cmp_gt_of_slt {a b : ONote} (h : slt a b) : ONote.cmp b a = Ordering.gt := by
  rw [← cmp_swap' a b, show ONote.cmp a b = Ordering.lt from h]; rfl

theorem slt_of_cmp_gt {a b : ONote} (h : ONote.cmp a b = Ordering.gt) : slt b a := by
  show ONote.cmp b a = Ordering.lt
  rw [← cmp_swap' a b, h]; rfl

theorem zero_slt_oadd (e : ONote) (n : ℕ+) (a : ONote) : slt ONote.zero (oadd e n a) := rfl

theorem exp_slt {γ γ' x y : ONote} {c d : ℕ+} (h : slt γ γ') : slt (oadd γ c x) (oadd γ' d y) := by
  show (ONote.cmp γ γ').then ((_root_.cmp (c : ℕ) d).then (ONote.cmp x y)) = Ordering.lt
  rw [show ONote.cmp γ γ' = Ordering.lt from h]; rfl

theorem coef_slt {γ x y : ONote} {c d : ℕ+} (h : (c : ℕ) < d) : slt (oadd γ c x) (oadd γ d y) := by
  show (ONote.cmp γ γ).then ((_root_.cmp (c : ℕ) d).then (ONote.cmp x y)) = Ordering.lt
  rw [cmp_self, natCmp_of_lt h]; rfl

/-! ## Syntactic order `sle`, max, numerals -/

/-- Weak syntactic order. -/
def sle (a b : ONote) : Prop := slt a b ∨ a = b

/-- Max via `cmp`. -/
def smax (a b : ONote) : ONote :=
  match ONote.cmp a b with
  | Ordering.lt => b
  | _ => a

theorem smax_of_lt {a b : ONote} (h : ONote.cmp a b = Ordering.lt) : smax a b = b := by
  unfold smax; rw [h]

theorem smax_of_eq {a b : ONote} (h : ONote.cmp a b = Ordering.eq) : smax a b = a := by
  unfold smax; rw [h]

theorem smax_of_gt {a b : ONote} (h : ONote.cmp a b = Ordering.gt) : smax a b = a := by
  unfold smax; rw [h]

theorem coef_sle {γ : ONote} {c d : ℕ+} (h : (c : ℕ) ≤ d) :
    sle (oadd γ c ONote.zero) (oadd γ d ONote.zero) := by
  rcases Nat.lt_or_eq_of_le h with h | h
  · exact Or.inl (coef_slt h)
  · exact Or.inr (by rw [PNat.eq h])

/-- The notation `1`. -/
def one' : ONote := oadd ONote.zero 1 ONote.zero
/-- The notation `2`. -/
def two' : ONote := oadd ONote.zero 2 ONote.zero

/-- Finite numerals. -/
def num : ℕ → ONote
  | 0 => ONote.zero
  | k + 1 => oadd ONote.zero k.succPNat ONote.zero

theorem num_slt : ∀ {i j : ℕ}, i < j → slt (num i) (num j)
  | 0, 0, h => absurd h (Nat.lt_irrefl 0)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | i + 1, j + 1, h => by
    show (ONote.cmp ONote.zero ONote.zero).then
      ((_root_.cmp (i + 1) (j + 1)).then (ONote.cmp ONote.zero ONote.zero)) = Ordering.lt
    rw [natCmp_of_lt h]; rfl

theorem SNF_num : ∀ k, SNF (num k)
  | 0 => trivial
  | _ + 1 => ⟨trivial, trivial, trivial⟩

/-! ## Syntactic addition, successor, and 2^α -/

/-- Syntactic addition: Mathlib's `ONote.add` (data only; choice-free as a definition). -/
def sadd (a b : ONote) : ONote := ONote.add a b

/-- Syntactic successor. -/
def ssucc : ONote → ONote
  | ONote.zero => one'
  | ONote.oadd ONote.zero n a => oadd ONote.zero (n + 1) a
  | ONote.oadd e n a => oadd e n (ssucc a)

/-- "Left predecessor" of a nonzero exponent: `1 + dec e = e`. -/
def dec : ONote → ONote
  | ONote.oadd ONote.zero n _ => num ((n : ℕ) - 1)
  | e => e

/-- Split `α = ω·γ + m` (γ, m) on Cantor normal forms. -/
def ssplit : ONote → ONote × ℕ
  | ONote.zero => (ONote.zero, 0)
  | ONote.oadd ONote.zero n _ => (ONote.zero, n)
  | ONote.oadd e n a => (oadd (dec e) n (ssplit a).1, (ssplit a).2)

/-- `2 ^ m` as a positive natural. -/
def pow2 (m : ℕ) : ℕ+ := ⟨2 ^ m, Nat.two_pow_pos m⟩

/-- `2 ^ α = ω ^ γ · 2 ^ m` where `α = ω·γ + m`. -/
def twoPow' (a : ONote) : ONote := oadd (ssplit a).1 (pow2 (ssplit a).2) ONote.zero

theorem ssplit_fin (n : ℕ+) (x : ONote) : ssplit (oadd ONote.zero n x) = (ONote.zero, (n : ℕ)) := rfl

theorem ssplit_inf (g z x : ONote) (m n : ℕ+) :
    ssplit (oadd (oadd g m z) n x) = (oadd (dec (oadd g m z)) n (ssplit x).1, (ssplit x).2) := rfl

theorem ssplit_ssucc : ∀ a, ssplit (ssucc a) = ((ssplit a).1, (ssplit a).2 + 1)
  | ONote.zero => rfl
  | ONote.oadd ONote.zero n a => by
    show (ONote.zero, ((n + 1 : ℕ+) : ℕ)) = (ONote.zero, (n : ℕ) + 1)
    rw [PNat.add_coe]; rfl
  | ONote.oadd (ONote.oadd g m z) n a => by
    show ssplit (oadd (oadd g m z) n (ssucc a)) = _
    rw [ssplit_inf, ssplit_inf, ssplit_ssucc a]

/-! ## SNF closure -/

theorem snf_tail_zero {n : ℕ+} {x : ONote} (h : SNF (oadd ONote.zero n x)) : x = ONote.zero := by
  cases x with
  | zero => rfl
  | oadd e' _ _ => exact absurd h.2.2 (not_slt_zero e')

theorem dec_slt : ∀ {e e' : ONote}, SNF e → SNF e' → e ≠ ONote.zero → slt e e' →
    slt (dec e) (dec e')
  | ONote.zero, _, _, _, hne, _ => absurd rfl hne
  | ONote.oadd _ _ _, ONote.zero, _, _, _, h => absurd h (not_slt_zero _)
  | ONote.oadd ONote.zero n1 x1, ONote.oadd ONote.zero n2 x2, h1, h2, _, h => by
    have hx1 := snf_tail_zero h1
    have hx2 := snf_tail_zero h2
    subst hx1; subst hx2
    rcases slt_oadd_cases h with h' | ⟨_, h'⟩ | ⟨_, _, h'⟩
    · exact absurd h' (not_slt_zero _)
    · exact num_slt (Nat.sub_lt_sub_right n1.2 h')
    · exact absurd h' (not_slt_zero _)
  | ONote.oadd ONote.zero n1 x1, ONote.oadd (ONote.oadd g m y) n2 x2, _, _, _, _ => by
    show slt (num ((n1 : ℕ) - 1)) (oadd (oadd g m y) n2 x2)
    generalize (n1 : ℕ) - 1 = k
    cases k <;> rfl
  | ONote.oadd (ONote.oadd g m y) n1 x1, ONote.oadd ONote.zero n2 x2, _, _, _, h => by
    rcases slt_oadd_cases h with h' | ⟨h', _⟩ | ⟨h', _, _⟩
    · exact absurd h' (not_slt_zero _)
    · exact ONote.noConfusion h'
    · exact ONote.noConfusion h'
  | ONote.oadd (ONote.oadd _ _ _) _ _, ONote.oadd (ONote.oadd _ _ _) _ _, _, _, _, h => h

theorem SNF_dec : ∀ {e : ONote}, SNF e → SNF (dec e)
  | ONote.zero, _ => trivial
  | ONote.oadd ONote.zero _ _, _ => SNF_num _
  | ONote.oadd (ONote.oadd _ _ _) _ _, h => h

theorem topBelow_ssplit {g z x : ONote} {m n : ℕ+} (h : SNF (oadd (oadd g m z) n x)) :
    topBelow (ssplit x).1 (dec (oadd g m z)) := by
  cases x with
  | zero => trivial
  | oadd e' n' x' =>
    cases e' with
    | zero => trivial
    | oadd g' m' z' =>
      exact dec_slt h.2.1.1 h.1 (fun h' => ONote.noConfusion h') h.2.2

theorem SNF_ssplit : ∀ a, SNF a → SNF (ssplit a).1
  | ONote.zero, _ => trivial
  | ONote.oadd ONote.zero _ _, _ => trivial
  | ONote.oadd (ONote.oadd g m z) n x, h => by
    rw [ssplit_inf]
    exact ⟨SNF_dec h.1, SNF_ssplit x h.2.1, topBelow_ssplit h⟩

theorem SNF_twoPow' {a : ONote} (h : SNF a) : SNF (twoPow' a) :=
  ⟨SNF_ssplit a h, trivial, trivial⟩

theorem topBelow_ssucc {e : ONote} (he : slt ONote.zero e) :
    ∀ {a : ONote}, topBelow a e → topBelow (ssucc a) e
  | ONote.zero, _ => he
  | ONote.oadd ONote.zero _ _, h => h
  | ONote.oadd (ONote.oadd _ _ _) _ _, h => h

theorem SNF_ssucc : ∀ {a : ONote}, SNF a → SNF (ssucc a)
  | ONote.zero, _ => ⟨trivial, trivial, trivial⟩
  | ONote.oadd ONote.zero n x, h => by
    have hx := snf_tail_zero h; subst hx
    exact ⟨trivial, trivial, trivial⟩
  | ONote.oadd (ONote.oadd g m z) n x, h =>
    ⟨h.1, SNF_ssucc h.2.1, topBelow_ssucc (zero_slt_oadd g m z) h.2.2⟩

theorem SNF_addAux {e : ONote} (n : ℕ+) (he : SNF e) :
    ∀ {o : ONote}, SNF o → SNF (ONote.addAux e n o)
  | ONote.zero, _ => ⟨he, trivial, trivial⟩
  | ONote.oadd e' n' a', ho => by
    cases h : ONote.cmp e e' with
    | lt => simp only [ONote.addAux, h]; exact ho
    | eq =>
      have hee := eq_of_cmp_eq' h; subst hee
      simp only [ONote.addAux, h]; exact ⟨he, ho.2.1, ho.2.2⟩
    | gt =>
      simp only [ONote.addAux, h]
      exact ⟨he, ho, slt_of_cmp_gt h⟩

theorem SNF_sadd : ∀ {a b : ONote}, SNF a → SNF b → SNF (sadd a b)
  | ONote.zero, _, _, hb => hb
  | ONote.oadd _ n _, b, ha, hb => SNF_addAux n ha.1 (SNF_sadd (b := b) ha.2.1 hb)

theorem SNF_smax {a b : ONote} (ha : SNF a) (hb : SNF b) : SNF (smax a b) := by
  unfold smax; cases ONote.cmp a b <;> assumption

/-! ## L3: monotonicity -/

/-- The split `(γ, m)` is lexicographically monotone. -/
theorem ssplit_mono : ∀ a b, SNF a → SNF b → slt a b →
    slt (ssplit a).1 (ssplit b).1 ∨ ((ssplit a).1 = (ssplit b).1 ∧ (ssplit a).2 < (ssplit b).2)
  | ONote.zero, ONote.zero, _, _, h => absurd h (not_slt_zero _)
  | ONote.zero, ONote.oadd ONote.zero n _, _, _, _ => Or.inr ⟨rfl, n.2⟩
  | ONote.zero, ONote.oadd (ONote.oadd _ _ _) _ _, _, _, _ => Or.inl rfl
  | ONote.oadd _ _ _, ONote.zero, _, _, h => absurd h (not_slt_zero _)
  | ONote.oadd e n x, ONote.oadd e' n' y, ha, hb, h => by
    rcases slt_oadd_cases h with h1 | ⟨rfl, h2⟩ | ⟨rfl, rfl, h3⟩
    · cases e with
      | zero =>
        cases e' with
        | zero => exact absurd h1 (not_slt_zero _)
        | oadd _ _ _ => exact Or.inl rfl
      | oadd g m z =>
        cases e' with
        | zero => exact absurd h1 (not_slt_zero _)
        | oadd g' m' z' =>
          rw [ssplit_inf, ssplit_inf]
          exact Or.inl (exp_slt (dec_slt ha.1 hb.1 (fun h' => ONote.noConfusion h') h1))
    · cases e with
      | zero => exact Or.inr ⟨rfl, h2⟩
      | oadd g m z =>
        rw [ssplit_inf, ssplit_inf]
        exact Or.inl (coef_slt h2)
    · cases e with
      | zero =>
        have hx := snf_tail_zero ha; have hy := snf_tail_zero hb
        subst hx; subst hy
        exact absurd h3 (not_slt_zero _)
      | oadd g m z =>
        rw [ssplit_inf, ssplit_inf]
        rcases ssplit_mono x y ha.2.1 hb.2.1 h3 with h4 | ⟨h4, h5⟩
        · refine Or.inl ?_
          show (ONote.cmp (dec (oadd g m z)) (dec (oadd g m z))).then
            ((_root_.cmp (n : ℕ) n).then (ONote.cmp (ssplit x).1 (ssplit y).1)) = Ordering.lt
          rw [cmp_self, natCmp_self, show ONote.cmp (ssplit x).1 (ssplit y).1 = Ordering.lt from h4]
          rfl
        · exact Or.inr ⟨by rw [h4], h5⟩

/-- L3 (strict). -/
theorem twoPow'_slt {a b : ONote} (ha : SNF a) (hb : SNF b) (h : slt a b) :
    slt (twoPow' a) (twoPow' b) := by
  rcases ssplit_mono a b ha hb h with h1 | ⟨h1, h2⟩
  · exact exp_slt h1
  · unfold twoPow'; rw [h1]
    exact coef_slt (two_pow_lt h2)

/-- L3 (weak). -/
theorem twoPow'_sle {a b : ONote} (ha : SNF a) (hb : SNF b) (h : sle a b) :
    sle (twoPow' a) (twoPow' b) := by
  rcases h with h | h
  · exact Or.inl (twoPow'_slt ha hb h)
  · exact Or.inr (by rw [h])

/-! ## L4: commutes with `smax` -/

theorem twoPow'_smax {a b : ONote} (ha : SNF a) (hb : SNF b) :
    twoPow' (smax a b) = smax (twoPow' a) (twoPow' b) := by
  cases h : ONote.cmp a b with
  | lt =>
    rw [smax_of_lt h, smax_of_lt (twoPow'_slt ha hb h)]
  | eq =>
    have hab := eq_of_cmp_eq' h; subst hab
    rw [smax_of_eq h, smax_of_eq (cmp_self _)]
  | gt =>
    rw [smax_of_gt h, smax_of_gt (cmp_gt_of_slt (twoPow'_slt hb ha (slt_of_cmp_gt h)))]

/-! ## Addition of the special shapes -/

theorem sadd_lt {γa γb x : ONote} {ca cb : ℕ+} (h : ONote.cmp γa γb = Ordering.lt) :
    sadd (oadd γa ca ONote.zero) (oadd γb cb x) = oadd γb cb x := by
  simp only [sadd, ONote.add, ONote.addAux, h]

theorem sadd_eq {γa γb x : ONote} {ca cb : ℕ+} (h : ONote.cmp γa γb = Ordering.eq) :
    sadd (oadd γa ca ONote.zero) (oadd γb cb x) = oadd γa (ca + cb) x := by
  simp only [sadd, ONote.add, ONote.addAux, h]

theorem sadd_gt {γa γb x : ONote} {ca cb : ℕ+} (h : ONote.cmp γa γb = Ordering.gt) :
    sadd (oadd γa ca ONote.zero) (oadd γb cb x) = oadd γa ca (oadd γb cb x) := by
  simp only [sadd, ONote.add, ONote.addAux, h]

theorem twoPow'_ssucc (a : ONote) :
    twoPow' (ssucc a) = oadd (ssplit a).1 (pow2 ((ssplit a).2 + 1)) ONote.zero := by
  unfold twoPow'; rw [ssplit_ssucc]

theorem pow2_succ (m : ℕ) : ((pow2 (m + 1) : ℕ+) : ℕ) = 2 ^ m + 2 ^ m := by
  show 2 ^ (m + 1) = 2 ^ m + 2 ^ m
  rw [Nat.pow_succ, Nat.mul_two]

/-- If `a` is finite (`γ = 0`) and `j ≤ a`, then `j ≤ m`. -/
theorem le_fin_part {a : ONote} {j : ℕ+} (ha : SNF a) (hγ : (ssplit a).1 = ONote.zero)
    (h : sle (oadd ONote.zero j ONote.zero) a) : (j : ℕ) ≤ (ssplit a).2 := by
  cases a with
  | zero =>
    rcases h with h | h
    · exact absurd h (not_slt_zero _)
    · exact ONote.noConfusion h
  | oadd e n x =>
    cases e with
    | zero =>
      have hx := snf_tail_zero ha; subst hx
      rw [ssplit_fin]
      rcases h with h | h
      · rcases slt_oadd_cases h with h' | ⟨_, h'⟩ | ⟨_, _, h'⟩
        · exact absurd h' (not_slt_zero _)
        · exact Nat.le_of_lt h'
        · exact absurd h' (not_slt_zero _)
      · cases h; exact Nat.le_refl _
    | oadd g m z =>
      rw [ssplit_inf] at hγ; exact ONote.noConfusion hγ

/-! ## L1, L2, L5 -/

/-- Generic form: `2^α + j < 2^(α+1)` when `j < 2^m` in the finite case. -/
theorem twoPow'_add_num_lt {a : ONote} {j : ℕ+}
    (hfin : (ssplit a).1 = ONote.zero → (j : ℕ) < 2 ^ (ssplit a).2) :
    slt (sadd (twoPow' a) (oadd ONote.zero j ONote.zero)) (twoPow' (ssucc a)) := by
  rw [twoPow'_ssucc]
  unfold twoPow'
  generalize hγ : (ssplit a).1 = γ at hfin ⊢
  generalize (ssplit a).2 = m at hfin ⊢
  cases γ with
  | zero =>
    rw [sadd_eq rfl]
    refine coef_slt ?_
    rw [PNat.add_coe, pow2_succ]
    exact Nat.add_lt_add_left (hfin rfl) _
  | oadd g k z =>
    rw [sadd_gt rfl]
    refine coef_slt ?_
    rw [pow2_succ]
    exact Nat.lt_add_of_pos_right (Nat.two_pow_pos m)

/-- L1. False at `a = 0` (2^0 + 1 = 2^1). -/
theorem L1 {a : ONote} (ha : SNF a) (h : sle one' a) :
    slt (sadd (twoPow' a) one') (twoPow' (ssucc a)) := by
  refine twoPow'_add_num_lt fun hγ => ?_
  have hm : 1 ≤ (ssplit a).2 := le_fin_part ha hγ h
  calc (((1 : ℕ+)) : ℕ) = 1 := rfl
    _ < 2 ^ 1 := by decide
    _ ≤ 2 ^ (ssplit a).2 := Nat.pow_le_pow_right (by decide) hm

/-- L2. False at `a = 1` (2^1 + 2 = 2^2). -/
theorem L2 {a : ONote} (ha : SNF a) (h : sle two' a) :
    slt (sadd (twoPow' a) two') (twoPow' (ssucc a)) := by
  refine twoPow'_add_num_lt fun hγ => ?_
  have hm : 2 ≤ (ssplit a).2 := le_fin_part ha hγ h
  calc (((2 : ℕ+)) : ℕ) = 2 := rfl
    _ < 2 ^ 2 := by decide
    _ ≤ 2 ^ (ssplit a).2 := Nat.pow_le_pow_right (by decide) hm

/-- L5. `2^α + 2 < 2^(α+2)` for every `α`. -/
theorem L5 (a : ONote) : slt (sadd (twoPow' a) two') (twoPow' (ssucc (ssucc a))) := by
  rw [twoPow'_ssucc, ssplit_ssucc]
  show slt (sadd (oadd (ssplit a).1 (pow2 (ssplit a).2) ONote.zero) (oadd ONote.zero 2 ONote.zero))
    (oadd (ssplit a).1 (pow2 ((ssplit a).2 + 1 + 1)) ONote.zero)
  generalize (ssplit a).1 = γ
  generalize (ssplit a).2 = m
  have h4 : ((pow2 (m + 1 + 1) : ℕ+) : ℕ) = 2 ^ m + 2 ^ m + (2 ^ m + 2 ^ m) := by
    show 2 ^ (m + 1 + 1) = _
    rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_two, Nat.mul_two]
  have hp := Nat.two_pow_pos m
  cases γ with
  | zero =>
    rw [sadd_eq rfl]
    refine coef_slt ?_
    rw [PNat.add_coe, h4]
    show 2 ^ m + 2 < 2 ^ m + 2 ^ m + (2 ^ m + 2 ^ m)
    rw [Nat.add_assoc]
    refine Nat.add_lt_add_left ?_ _
    calc 2 = 1 + 1 := rfl
      _ < 2 ^ m + 2 ^ m + 1 := Nat.lt_succ_of_le (Nat.add_le_add hp hp)
      _ ≤ 2 ^ m + (2 ^ m + 2 ^ m) := by
        rw [← Nat.add_assoc]; exact Nat.add_le_add_left hp _
  | oadd g k z =>
    rw [sadd_gt rfl]
    refine coef_slt ?_
    rw [h4]
    show 2 ^ m < 2 ^ m + 2 ^ m + (2 ^ m + 2 ^ m)
    rw [Nat.add_assoc]
    exact Nat.lt_add_of_pos_right (Nat.add_pos_left hp _)

/-! ## Two-premise cut bound -/

theorem sum_bound_right {γa γb : ONote} {ma mb : ℕ}
    (h : slt γa γb ∨ (γa = γb ∧ ma ≤ mb)) :
    sle (sadd (oadd γa (pow2 ma) ONote.zero) (oadd γb (pow2 mb) ONote.zero))
      (oadd γb (pow2 (mb + 1)) ONote.zero) := by
  rcases h with h | ⟨rfl, h⟩
  · rw [sadd_lt h]
    refine coef_sle ?_
    rw [pow2_succ]; exact Nat.le_add_right _ _
  · rw [sadd_eq (cmp_self _)]
    refine coef_sle ?_
    rw [PNat.add_coe, pow2_succ]
    exact Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) h) _

theorem sum_bound_left {γa γb : ONote} {ma mb : ℕ}
    (h : slt γb γa ∨ (γb = γa ∧ mb ≤ ma)) :
    sle (sadd (oadd γa (pow2 ma) ONote.zero) (oadd γb (pow2 mb) ONote.zero))
      (oadd γa (pow2 (ma + 1)) ONote.zero) := by
  rcases h with h | ⟨rfl, h⟩
  · rw [sadd_gt (cmp_gt_of_slt h)]
    refine Or.inl (coef_slt ?_)
    rw [pow2_succ]; exact Nat.lt_add_of_pos_right (Nat.two_pow_pos ma)
  · rw [sadd_eq (cmp_self _)]
    refine coef_sle ?_
    rw [PNat.add_coe, pow2_succ]
    exact Nat.add_le_add_left (Nat.pow_le_pow_right (by decide) h) _

/-- Cut with premises of heights `a, b`: `2^a + 2^b ≤ 2^(max a b + 1)`. -/
theorem twoPow'_add_le {a b : ONote} (ha : SNF a) (hb : SNF b) :
    sle (sadd (twoPow' a) (twoPow' b)) (twoPow' (ssucc (smax a b))) := by
  cases h : ONote.cmp a b with
  | lt =>
    rw [smax_of_lt h, twoPow'_ssucc]
    unfold twoPow'
    rcases ssplit_mono a b ha hb h with h1 | ⟨h1, h2⟩
    · exact sum_bound_right (Or.inl h1)
    · exact sum_bound_right (Or.inr ⟨h1, Nat.le_of_lt h2⟩)
  | eq =>
    have hab := eq_of_cmp_eq' h; subst hab
    rw [smax_of_eq h, twoPow'_ssucc]
    unfold twoPow'
    exact sum_bound_right (Or.inr ⟨rfl, Nat.le_refl _⟩)
  | gt =>
    rw [smax_of_gt h, twoPow'_ssucc]
    unfold twoPow'
    rcases ssplit_mono b a hb ha (slt_of_cmp_gt h) with h1 | ⟨h1, h2⟩
    · exact sum_bound_left (Or.inl h1)
    · exact sum_bound_left (Or.inr ⟨h1, Nat.le_of_lt h2⟩)


/-! ## Counterexamples at the excluded points (choice-free, by evaluation) -/

/-- L1 fails at `a = 0`: `2^0 + 1 = 2 = 2^1`. -/
theorem L1_fails_at_zero : ¬ slt (sadd (twoPow' ONote.zero) one') (twoPow' (ssucc ONote.zero)) := by
  decide

/-- L2 fails at `a = 1`: `2^1 + 2 = 4 = 2^2`. -/
theorem L2_fails_at_one : ¬ slt (sadd (twoPow' one') two') (twoPow' (ssucc one')) := by
  decide


/-! ## Bridge to `Ordinal` (uses choice): these are the right functions -/

section Bridge

open Ordinal

theorem nf_of_snf {a : ONote} (h : SNF a) : ONote.NF a := (SNF_iff_NF a).1 h
theorem snf_of_nf {a : ONote} (h : ONote.NF a) : SNF a := (SNF_iff_NF a).2 h

theorem repr_sadd (a b : ONote) [ONote.NF a] [ONote.NF b] :
    ONote.repr (sadd a b) = ONote.repr a + ONote.repr b :=
  ONote.repr_add a b

theorem repr_ssucc : ∀ (a : ONote), ONote.NF a → ONote.repr (ssucc a) = ONote.repr a + 1
  | ONote.zero, _ => by simp [ssucc, one']
  | ONote.oadd ONote.zero n x, h => by
    have hx := snf_tail_zero (snf_of_nf h); subst hx
    show ONote.repr (oadd ONote.zero (n + 1) ONote.zero) = _
    simp [PNat.add_coe]
  | ONote.oadd (ONote.oadd g m z) n x, h => by
    show ONote.repr (oadd (oadd g m z) n (ssucc x)) = _
    simp only [ONote.repr]
    rw [repr_ssucc x h.snd, add_assoc]

theorem repr_num (k : ℕ) : ONote.repr (num k) = k := by
  cases k with
  | zero => simp [num]
  | succ k => simp [num]

theorem one_add_repr_dec : ∀ {e : ONote}, ONote.NF e → e ≠ ONote.zero →
    1 + ONote.repr (dec e) = ONote.repr e
  | ONote.zero, _, hne => absurd rfl hne
  | ONote.oadd ONote.zero n x, h, _ => by
    have hx := snf_tail_zero (snf_of_nf h); subst hx
    show 1 + ONote.repr (num ((n : ℕ) - 1)) = _
    have hk : 1 + ((n : ℕ) - 1) = n := Nat.add_sub_cancel' n.2
    rw [repr_num]
    simp only [ONote.repr, opow_zero, one_mul, add_zero]
    exact_mod_cast hk
  | ONote.oadd (ONote.oadd g m z) n x, _, _ => by
    show 1 + ONote.repr (oadd (oadd g m z) n x) = _
    refine one_add_of_omega0_le ?_
    have hr : (0 : Ordinal) < ONote.repr (oadd g m z) := ONote.oadd_pos g m z
    have hn : (0 : Ordinal) < ((n : ℕ) : Ordinal) := by exact_mod_cast n.2
    simp only [ONote.repr]
    calc ω ≤ ω ^ ONote.repr (oadd g m z) := left_le_opow ω hr
      _ ≤ ω ^ ONote.repr (oadd g m z) * ((n : ℕ) : Ordinal) := le_mul_left _ hn
      _ ≤ _ := le_self_add

theorem repr_ssplit : ∀ (a : ONote), ONote.NF a →
    ONote.repr a = ω * ONote.repr (ssplit a).1 + ((ssplit a).2 : Ordinal)
  | ONote.zero, _ => by simp [ssplit]
  | ONote.oadd ONote.zero n x, h => by
    have hx := snf_tail_zero (snf_of_nf h); subst hx
    rw [ssplit_fin]; simp
  | ONote.oadd (ONote.oadd g m z) n x, h => by
    rw [ssplit_inf]
    have he : 1 + ONote.repr (dec (oadd g m z)) = ONote.repr (oadd g m z) :=
      one_add_repr_dec h.fst (fun h' => ONote.noConfusion h')
    show ONote.repr (oadd (oadd g m z) n x) =
      ω * ONote.repr (oadd (dec (oadd g m z)) n (ssplit x).1) + ((ssplit x).2 : Ordinal)
    show ω ^ ONote.repr (oadd g m z) * ((n : ℕ) : Ordinal) + ONote.repr x =
      ω * (ω ^ ONote.repr (dec (oadd g m z)) * ((n : ℕ) : Ordinal) + ONote.repr (ssplit x).1) +
        ((ssplit x).2 : Ordinal)
    rw [repr_ssplit x h.snd, mul_add, ← mul_assoc, ← opow_one_add, he, add_assoc]

/-- `twoPow'` denotes `2 ^ α`. -/
theorem repr_twoPow' (a : ONote) (h : ONote.NF a) : ONote.repr (twoPow' a) = 2 ^ ONote.repr a := by
  rw [repr_ssplit a h, opow_add, opow_mul,
    opow_omega0 one_lt_two (by exact_mod_cast natCast_lt_omega0 2)]
  show ω ^ ONote.repr (ssplit a).1 * (((2 ^ (ssplit a).2 : ℕ)) : Ordinal) + 0 = _
  rw [add_zero, Ordinal.natCast_pow, Nat.cast_ofNat, ← opow_natCast]

/-- `twoPow'` agrees with Mathlib's `ONote.opow` (hence with `Gentzen.Ordinals.twoPow`,
whose underlying notation is `ONote.ofNat 2 ^ a`). -/
theorem twoPow'_eq_opow (a : ONote) [h : ONote.NF a] : twoPow' a = ONote.ofNat 2 ^ a := by
  have : ONote.NF (twoPow' a) := nf_of_snf (SNF_twoPow' (snf_of_nf h))
  refine ONote.repr_inj.1 ?_
  rw [repr_twoPow' a h, ONote.repr_opow, ONote.repr_ofNat, Nat.cast_ofNat]

theorem ssucc_eq_add_one (a : ONote) [h : ONote.NF a] : ssucc a = a + 1 := by
  have : ONote.NF (ssucc a) := nf_of_snf (SNF_ssucc (snf_of_nf h))
  refine ONote.repr_inj.1 ?_
  rw [repr_ssucc a h, ONote.repr_add, ONote.repr_one, Nat.cast_one]


end Bridge

/-! ## Checks on samples (by `decide`) -/

/-- Samples: `0, 1, 2, ω, ω+1, ω·2, ω^ω`. -/
def samples : List ONote :=
  [0, 1, ONote.ofNat 2, oadd 1 1 0, oadd 1 1 1, oadd 1 2 0, oadd (oadd 1 1 0) 1 0]

/-- `twoPow'` on the samples: `1, 2, 4, ω, ω·2, ω^2, ω^(ω^ω)`. -/
example : samples.map twoPow' =
    [oadd 0 1 0, oadd 0 2 0, oadd 0 4 0, oadd (oadd 0 1 0) 1 0, oadd (oadd 0 1 0) 2 0,
      oadd (oadd 0 2 0) 1 0, oadd (oadd (oadd (oadd 0 1 0) 1 0) 1 0) 1 0] := by decide

/-- L1 on the samples: false only at `0`. -/
example : samples.map (fun a => decide (slt (sadd (twoPow' a) one') (twoPow' (ssucc a)))) =
    [false, true, true, true, true, true, true] := by decide

/-- L2 on the samples: false at `0` and `1`. -/
example : samples.map (fun a => decide (slt (sadd (twoPow' a) two') (twoPow' (ssucc a)))) =
    [false, false, true, true, true, true, true] := by decide

/-- L5 on the samples. -/
example : samples.all
    (fun a => decide (slt (sadd (twoPow' a) two') (twoPow' (ssucc (ssucc a))))) = true := by
  decide

end Gentzen.TwoPow
