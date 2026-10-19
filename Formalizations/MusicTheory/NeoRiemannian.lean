/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Perm.Subgroup
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Ring

/-!
# The neo-Riemannian `PLR` group and the `T/I` group on the 24 triads

The 24 major and minor triads `Triad = ZMod 12 × Bool` carry the transposition/inversion action
of `DihedralGroup 12`, which is simply transitive. The neo-Riemannian involutions `P`, `L`, `R`
commute with it, and the group they generate is the full centralizer of the `T/I` action in
`Equiv.Perm Triad`: the two groups are dual in the sense of Crans, Fiore and Satyendra. The key
step is that in a faithful transitive action a centralizing permutation with a fixed point is the
identity, so the centralizer has at most 24 elements.

## Main results

* `Duality.centralizing_fixedPoint_eq_one`: a permutation commuting with a transitive action and
  fixing a point is the identity.
* `Duality.card_TIgrp`, `Duality.card_PLRgrp`: both groups have order 24.
* `Duality.centralizer_eq_PLR`: the centralizer of the `T/I` group is the `PLR` group.
* `VoiceLeading.P_size_one`, `L_size_one`, `R_size_two`, `P_holds_two`: voice-leading sizes and
  common tones of `P`, `L`, `R`.

## References

* A. S. Crans, T. M. Fiore, R. Satyendra, *Musical actions of dihedral groups*, Amer. Math.
  Monthly 116 (2009) 479–495.
* L. Aniva, C. Wang, *Prismriver: formalization of music theory and algorithmic composition in
  Lean 4*, arXiv:2606.19936.
* C. Marín, *A tritone-centered self-duality: the set class 6-30 and its order-12
  neo-Riemannian dual*, Zenodo (2026), doi:10.5281/zenodo.20820961.
-/

@[expose] public section

namespace MusicTheory

open DihedralGroup

/-- A triad is a root pitch-class in `ZMod 12` with a quality bit (`true` = major,
    `false` = minor). There are exactly 24. -/
abbrev Triad := ZMod 12 × Bool

namespace Triad

/-- The root pitch class. -/
abbrev root (t : Triad) : ZMod 12 := t.1
/-- Quality: `true` = major, `false` = minor. -/
abbrev isMajor (t : Triad) : Bool := t.2

/-- Exactly 24 triads. -/
example : Fintype.card Triad = 24 := by decide

/-- Pitch-class content: major root r = {r, r+4, r+7}; minor root r = {r, r+3, r+7}. -/
def pcs (t : Triad) : Finset (ZMod 12) :=
  if t.2 then {t.1, t.1 + 4, t.1 + 7} else {t.1, t.1 + 3, t.1 + 7}

example : pcs (0, true)  = {0, 4, 7} := by decide
example : pcs (0, false) = {0, 3, 7} := by decide

end Triad

/-! ## The T/I (transposition/inversion) action of `D₁₂`

`r i` acts as transposition up by `i`; `sr j` acts as an inversion (flips quality, root ↦ −x−j−7).
The constants are forced by the pitch-class content; the reindex makes this a genuine *left*
action matching Mathlib's `DihedralGroup` multiplication. -/

namespace TI

/-- The T/I action on triads. -/
def smul : DihedralGroup 12 → Triad → Triad
  | r i,  (x, b) => (x + i, b)
  | sr j, (x, b) => (-x - j - 7, !b)

instance : SMul (DihedralGroup 12) Triad := ⟨smul⟩

@[simp] lemma smul_r  (i x : ZMod 12) (b : Bool) :
    (r i : DihedralGroup 12) • (x, b) = ((x + i : ZMod 12), b) := rfl
@[simp] lemma smul_sr (j x : ZMod 12) (b : Bool) :
    (sr j : DihedralGroup 12) • (x, b) = ((-x - j - 7 : ZMod 12), !b) := rfl

instance : MulAction (DihedralGroup 12) Triad where
  one_smul t := by
    obtain ⟨x, b⟩ := t
    show (r 0 : DihedralGroup 12) • (x, b) = (x, b)  -- (1 : D₁₂) = r 0 definitionally
    rw [smul_r, add_zero]
  mul_smul g h t := by
    obtain ⟨x, b⟩ := t
    cases g <;> cases h <;>
      simp only [r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr, smul_r, smul_sr, Prod.mk.injEq] <;>
      exact ⟨by ring, by simp⟩

/-- The T/I action is transitive: any triad maps to any other. -/
instance : MulAction.IsPretransitive (DihedralGroup 12) Triad where
  exists_smul_eq := by
    rintro ⟨x, b⟩ ⟨y, c⟩
    cases b <;> cases c
    · exact ⟨r (y - x),       by simp only [smul_r];  rw [Prod.mk.injEq]; exact ⟨by ring, rfl⟩⟩
    · exact ⟨sr (-x - y - 7),  by simp only [smul_sr]; rw [Prod.mk.injEq]; exact ⟨by ring, rfl⟩⟩
    · exact ⟨sr (-x - y - 7),  by simp only [smul_sr]; rw [Prod.mk.injEq]; exact ⟨by ring, rfl⟩⟩
    · exact ⟨r (y - x),       by simp only [smul_r];  rw [Prod.mk.injEq]; exact ⟨by ring, rfl⟩⟩

end TI

/-! ## The neo-Riemannian operations P, L, R

P (parallel): same root, flip quality.  L (leading-tone exchange).  R (relative).
Each is an involution. The crux of the duality is proved here at generator level:
**every one of P, L, R commutes with the entire T/I action** — i.e. P, L, R lie in the
centralizer of the T/I group inside `Equiv.Perm Triad`. -/

namespace PLR

/-- Parallel: C major ↔ C minor. -/
def Pf : Triad → Triad | (x, b) => (x, !b)
/-- Leading-tone exchange: C major ↔ E minor. -/
def Lf : Triad → Triad
  | (x, true)  => (x + 4, false)
  | (x, false) => (x - 4, true)
/-- Relative: C major ↔ A minor. -/
def Rf : Triad → Triad
  | (x, true)  => (x - 3, false)
  | (x, false) => (x + 3, true)

lemma Pf_invol : Function.Involutive Pf := by
  rintro ⟨x, b⟩; cases b <;> simp [Pf]
lemma Lf_invol : Function.Involutive Lf := by
  rintro ⟨x, b⟩
  cases b <;> (simp only [Lf]; rw [Prod.mk.injEq]; exact ⟨by ring, rfl⟩)
lemma Rf_invol : Function.Involutive Rf := by
  rintro ⟨x, b⟩
  cases b <;> (simp only [Rf]; rw [Prod.mk.injEq]; exact ⟨by ring, rfl⟩)

/-- The three operations as elements of `Equiv.Perm Triad` (involutions are their own inverse). -/
def P : Equiv.Perm Triad := Function.Involutive.toPerm Pf Pf_invol
def L : Equiv.Perm Triad := Function.Involutive.toPerm Lf Lf_invol
def R : Equiv.Perm Triad := Function.Involutive.toPerm Rf Rf_invol

/-- Sanity (the textbook examples): C major →ᴾ C minor, →ᴸ E minor, →ᴿ A minor. -/
example : Pf (0, true) = (0, false) := rfl   -- C → c
example : Lf (0, true) = (4, false) := rfl   -- C → e
example : Rf (0, true) = (9, false) := rfl   -- C → a

/-! ### The duality crux: P, L, R each commute with the whole T/I action. -/

lemma Pf_comm (g : DihedralGroup 12) (t : Triad) : Pf (g • t) = g • Pf t := by
  obtain ⟨x, b⟩ := t
  show Pf (TI.smul g (x, b)) = TI.smul g (Pf (x, b))
  cases g <;> simp [TI.smul, Pf]

lemma Lf_comm (g : DihedralGroup 12) (t : Triad) : Lf (g • t) = g • Lf t := by
  obtain ⟨x, b⟩ := t
  show Lf (TI.smul g (x, b)) = TI.smul g (Lf (x, b))
  cases g <;> cases b <;>
    (simp only [TI.smul, Lf, Bool.not_false, Bool.not_true]
     rw [Prod.mk.injEq]; exact ⟨by ring, rfl⟩)

lemma Rf_comm (g : DihedralGroup 12) (t : Triad) : Rf (g • t) = g • Rf t := by
  obtain ⟨x, b⟩ := t
  show Rf (TI.smul g (x, b)) = TI.smul g (Rf (x, b))
  cases g <;> cases b <;>
    (simp only [TI.smul, Rf, Bool.not_false, Bool.not_true]
     rw [Prod.mk.injEq]; exact ⟨by ring, rfl⟩)

end PLR

/-! ## The duality engine (centralizer of the regular T/I rep)

The headline. Two layers:

* **Abstract.** For *any* faithful transitive `MulAction G α`, the
  centralizer of the image of `G` in `Equiv.Perm α` is **semiregular**: a centralizing permutation
  with a fixed point is the identity (`centralizing_fixedPoint_eq_one`). Consequently, evaluation at
  any base point embeds the centralizer into `α`, so `|centralizer| ≤ |α|` (`card_Cgrp_le` for the
  triads). This is the regular-action case of **Wielandt's theorem** on centralizers of transitive
  permutation groups, which we did not find in Mathlib.

* **Concrete (CFS duality).** The T/I action is faithful (`decide`-level) and transitive,
  so it is the **left regular representation** on the 24 triads. The neo-Riemannian `P, L, R` all lie
  in its centralizer (the `_comm` lemmas, repackaged as `Subgroup.closure {P,L,R} ≤
  centralizer`), and the centralizer has at most 24 elements. PLR is thus exactly the centralizer
  iff `|⟨P,L,R⟩| = 24`, proved below. -/

/-- The T/I action is faithful (two test triads pin down the dihedral element). -/
instance : FaithfulSMul (DihedralGroup 12) Triad where
  eq_of_smul_eq_smul {g h} hyp := by
    have h1 := hyp (0, true); have h2 := hyp (0, false)
    cases g <;> cases h <;> simp_all

namespace Duality

open MulAction

/-- **Wielandt, regular case (abstract, reusable).** In a faithful *transitive* `G`-action, any
permutation `σ` commuting with the whole image of `G` and fixing one point is the identity — the
centralizer of a transitive group is semiregular. -/
theorem centralizing_fixedPoint_eq_one
    {G α : Type*} [Group G] [MulAction G α] [IsPretransitive G α]
    (σ : Equiv.Perm α) (hcomm : ∀ g : G, σ * toPerm g = toPerm g * σ)
    (a : α) (hfix : σ a = a) : σ = 1 := by
  ext x
  obtain ⟨g, rfl⟩ := exists_smul_eq G a x
  have := congrArg (fun p => p a) (hcomm g)
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, toPerm_apply] at this
  rw [hfix] at this
  simpa using this

/-- The image of the T/I group inside `Equiv.Perm Triad` — the left regular representation. -/
abbrev TIgrp : Subgroup (Equiv.Perm Triad) := (toPermHom (DihedralGroup 12) Triad).range

/-- Its centralizer in `Sym(Triad)` — the object we identify with PLR. -/
abbrev Cgrp : Subgroup (Equiv.Perm Triad) := Subgroup.centralizer (TIgrp : Set (Equiv.Perm Triad))

/-- A centralizer element commutes with every `toPerm g`. -/
theorem Cgrp_comm {σ : Equiv.Perm Triad} (hσ : σ ∈ Cgrp) (g : DihedralGroup 12) :
    σ * toPerm g = toPerm g * σ :=
  ((Subgroup.mem_centralizer_iff).1 hσ (toPerm g) ⟨g, rfl⟩).symm

/-- Evaluation at the base triad `(0, true)` injects the centralizer into `Triad` (semiregularity). -/
theorem eval_injective : Function.Injective (fun c : Cgrp => (c : Equiv.Perm Triad) (0, true)) := by
  rintro ⟨c, hc⟩ ⟨d, hd⟩ heq
  simp only at heq
  have hmem : d⁻¹ * c ∈ Cgrp := mul_mem (inv_mem hd) hc
  have hfix : (d⁻¹ * c) (0, true) = (0, true) := by
    show d⁻¹ (c (0, true)) = (0, true)
    rw [heq]; exact d.symm_apply_apply (0, true)
  have h1 : d⁻¹ * c = 1 :=
    centralizing_fixedPoint_eq_one (G := DihedralGroup 12) (d⁻¹ * c) (Cgrp_comm hmem) (0, true) hfix
  exact Subtype.ext (inv_mul_eq_one.1 h1).symm

/-- **Wielandt bound (concrete):** the centralizer of the T/I image has at most 24 elements. -/
theorem card_Cgrp_le : Nat.card Cgrp ≤ 24 := by
  have : Nat.card Cgrp ≤ Nat.card Triad := Nat.card_le_card_of_injective _ eval_injective
  simpa [Nat.card_eq_fintype_card, show Fintype.card Triad = 24 from by decide] using this

/-- A neo-Riemannian generator (as a permutation) commuting with the whole T/I image, packaged
from a pointwise commuting law `f (g • t) = g • f t`. -/
theorem mem_Cgrp_of_comm (σ : Equiv.Perm Triad)
    (h : ∀ (g : DihedralGroup 12) (t : Triad), σ (g • t) = g • σ t) : σ ∈ Cgrp := by
  refine (Subgroup.mem_centralizer_iff).2 ?_
  rintro _ ⟨g, rfl⟩
  refine Equiv.Perm.ext fun t => ?_
  show toPerm g (σ t) = σ (toPerm g t)
  simp only [toPerm_apply]
  exact (h g t).symm

/-- **PLR centralizes T/I.** The neo-Riemannian group sits inside the centralizer of the
regular T/I representation — the substantive direction of the CFS duality. -/
theorem PLR_le_centralizer :
    Subgroup.closure ({PLR.P, PLR.L, PLR.R} : Set (Equiv.Perm Triad)) ≤ Cgrp := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl | rfl)
  · exact mem_Cgrp_of_comm PLR.P PLR.Pf_comm
  · exact mem_Cgrp_of_comm PLR.L PLR.Lf_comm
  · exact mem_Cgrp_of_comm PLR.R PLR.Rf_comm

/-- The Cayley identification: T/I ≅ its image, of order 24 (left regular rep is faithful). -/
theorem card_TIgrp : Nat.card TIgrp = 24 := by
  have e := Equiv.Perm.subgroupOfMulAction (DihedralGroup 12) Triad
  rw [show TIgrp = (toPermHom (DihedralGroup 12) Triad).range from rfl, ← Nat.card_congr e.toEquiv,
    Nat.card_eq_fintype_card, DihedralGroup.card]

/-! ### `Cgrp = ⟨P, L, R⟩`

The remaining numeric obligation `|⟨P,L,R⟩| = 24` is discharged by orbit–stabilizer: the PLR
subgroup acts on the 24 triads **transitively** (P, L, R already reach everything: `L∘R` is the
root-translation by `−7`, a generator of `ℤ/12`, and `P` flips quality) and **semiregularly**
(it lies in the semiregular centralizer `Cgrp`). A transitive + semiregular action is regular, so
`|⟨P,L,R⟩| = |Triad| = 24`. Then `⟨P,L,R⟩ ≤ Cgrp`, `|Cgrp| ≤ 24 = |⟨P,L,R⟩|` force equality. -/

/-- Abbreviation for the neo-Riemannian subgroup of `Sym(Triad)`. -/
abbrev PLRgrp : Subgroup (Equiv.Perm Triad) :=
  Subgroup.closure ({PLR.P, PLR.L, PLR.R} : Set (Equiv.Perm Triad))

/-- The generators belong to `PLRgrp`. -/
theorem P_mem : PLR.P ∈ PLRgrp :=
  Subgroup.subset_closure (by simp)
theorem L_mem : PLR.L ∈ PLRgrp :=
  Subgroup.subset_closure (by simp)
theorem R_mem : PLR.R ∈ PLRgrp :=
  Subgroup.subset_closure (by simp)

/-- `L ∘ R` translates a major triad's root by `−7`; iterating reaches every major triad. -/
theorem LR_smul_major (x : ZMod 12) :
    ((PLR.L * PLR.R : Equiv.Perm Triad)) (x, true) = (x - 7, true) := by
  show PLR.Lf (PLR.Rf (x, true)) = (x - 7, true)
  simp only [PLR.Rf, PLR.Lf]
  rw [Prod.mk.injEq]; exact ⟨by ring, rfl⟩

/-- The subgroup element `(L*R)^k`, packaged in `PLRgrp`. -/
def wk (k : ℕ) : PLRgrp :=
  ⟨(PLR.L * PLR.R) ^ k, pow_mem (mul_mem L_mem R_mem) k⟩

/-- Acting by `(L*R)^k` on the base major triad lands on root `−7k`. -/
theorem wk_smul (k : ℕ) :
    (wk k) • ((0, true) : Triad) = ((-(7 * (k : ZMod 12)), true) : Triad) := by
  induction k with
  | zero => simp [wk, MulAction.subgroup_smul_def]
  | succ n ih =>
    have step : (wk (n + 1)) • ((0, true) : Triad)
        = (PLR.L * PLR.R : Equiv.Perm Triad) ((wk n) • ((0, true) : Triad)) := by
      show ((PLR.L * PLR.R) ^ (n + 1) : Equiv.Perm Triad) (0, true)
        = (PLR.L * PLR.R) (((PLR.L * PLR.R) ^ n) (0, true))
      rw [pow_succ', Equiv.Perm.mul_apply]
    rw [step, ih, LR_smul_major]
    rw [Prod.mk.injEq]
    refine ⟨?_, rfl⟩
    push_cast; ring

/-- Every major triad is reached from the base by some `(L*R)^k`. -/
theorem reach_major (m : ZMod 12) : ∃ g : PLRgrp, g • ((0, true) : Triad) = (m, true) := by
  -- solve `-(7 * k) = m` in `ZMod 12`: `7 * 7 = 49 ≡ 1`, so `k = -7 * m` works.
  obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective (-7 * m)
  refine ⟨wk n, ?_⟩
  rw [wk_smul, Prod.mk.injEq]
  refine ⟨?_, rfl⟩
  rw [hn]
  -- `-(7 * (-7 * m)) = m`, i.e. `49 * m = m`, true since `49 = 1` in ZMod 12
  have h49 : (49 : ZMod 12) = 1 := by decide
  calc -(7 * (-7 * m)) = (49 : ZMod 12) * m := by ring
    _ = m := by rw [h49, one_mul]

/-- Every minor triad is reached from the base (apply `P` after a major reach). -/
theorem reach_minor (m : ZMod 12) : ∃ g : PLRgrp, g • ((0, true) : Triad) = (m, false) := by
  obtain ⟨g, hg⟩ := reach_major m
  refine ⟨⟨PLR.P, P_mem⟩ * g, ?_⟩
  rw [mul_smul, hg]
  show PLR.Pf (m, true) = (m, false)
  simp [PLR.Pf]

/-- The PLR action on the 24 triads is **transitive**. -/
instance : MulAction.IsPretransitive PLRgrp Triad where
  exists_smul_eq := by
    -- enough to reach every triad from the base `(0, true)`, then compose via the group
    have base : ∀ t : Triad, ∃ g : PLRgrp, g • ((0, true) : Triad) = t := by
      rintro ⟨m, c⟩; cases c
      · exact reach_minor m
      · exact reach_major m
    rintro a b
    obtain ⟨ga, hga⟩ := base a
    obtain ⟨gb, hgb⟩ := base b
    exact ⟨gb * ga⁻¹, by rw [mul_smul, ← hga, inv_smul_smul, hgb]⟩

/-- The PLR action is **semiregular**: the stabilizer of any triad is trivial (it sits inside the
semiregular centralizer `Cgrp`). -/
theorem PLRgrp_stabilizer_eq_bot :
    MulAction.stabilizer PLRgrp ((0, true) : Triad) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro ⟨h, hh⟩ hstab
  rw [MulAction.mem_stabilizer_iff, MulAction.subgroup_smul_def] at hstab
  have hcent : h ∈ Cgrp := PLR_le_centralizer hh
  have : h = 1 := centralizing_fixedPoint_eq_one (G := DihedralGroup 12) h
    (Cgrp_comm hcent) (0, true) hstab
  exact Subtype.ext this

/-- **The numeric crux:** the neo-Riemannian group has exactly 24 elements (regular action). -/
theorem card_PLRgrp : Nat.card PLRgrp = 24 := by
  classical
  have key := MulAction.card_orbit_mul_card_stabilizer_eq_card_group PLRgrp ((0, true) : Triad)
  have horb : Nat.card (MulAction.orbit PLRgrp ((0, true) : Triad)) = 24 := by
    rw [MulAction.orbit_eq_univ, Nat.card_univ, Nat.card_eq_fintype_card]
    exact by decide
  have hstab : Nat.card (MulAction.stabilizer PLRgrp ((0, true) : Triad)) = 1 := by
    rw [PLRgrp_stabilizer_eq_bot, Subgroup.card_bot]
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      horb, hstab, mul_one] at key
  exact key.symm

/-- **Headline:** the centralizer of the regular T/I representation is *exactly* the
neo-Riemannian PLR group — the Crans–Fiore–Satyendra duality, deductively closed. -/
theorem centralizer_eq_PLR : Cgrp = PLRgrp := by
  refine (Subgroup.eq_of_le_of_card_ge PLR_le_centralizer ?_).symm
  rw [card_PLRgrp]
  exact card_Cgrp_le

end Duality

/-! ## M.3 — P, L, R as minimal voice-leadings (Cohn, JMT 41 (1997))

The neo-Riemannian moves are the *parsimonious* triad-to-triad voice-leadings: each holds two common
tones and shifts the remaining voice by a single step. The precise sizes (in the `L¹` voice-leading
metric, distances mod 12) are **P = 1, L = 1, R = 2** — NOT all equal: `R` moves its voice by a whole
tone. We verify both facts as finite checks over all 24 triads, decoupled from the orbifold (G.1/M.2).

A voice-leading is a bijection between the two triads' three voices; its size is the sum of the
(circular) semitone displacements; `vlDist` is the minimum over all 6 bijections. -/

namespace VoiceLeading

open Triad

/-- Circular semitone distance on the pitch-class circle: `min(d, 12−d)`. -/
def cdist (a b : ZMod 12) : ℕ := min (a - b).val (b - a).val

/-- The three voices of a triad in order (root, third, fifth). -/
def voices (t : Triad) : Fin 3 → ZMod 12 :=
  if t.2 then ![t.1, t.1 + 4, t.1 + 7] else ![t.1, t.1 + 3, t.1 + 7]

/-- The six bijections of three voices. -/
def perms3 : List (Fin 3 → Fin 3) :=
  [![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]]

/-- The size of the voice-leading `t → u` that matches voice `i` of `t` to voice `σ i` of `u`. -/
def cost (t u : Triad) (σ : Fin 3 → Fin 3) : ℕ :=
  cdist (voices t 0) (voices u (σ 0)) + cdist (voices t 1) (voices u (σ 1))
    + cdist (voices t 2) (voices u (σ 2))

/-- The voice-leading distance: minimal size over all bijective matchings of the voices. -/
def vlDist (t u : Triad) : ℕ := (perms3.map (cost t u)).foldr min 100

/-- Sanity (C major): →ᴾ C minor at size 1, →ᴸ E minor at size 1, →ᴿ A minor at size 2. -/
example : vlDist (0, true) (0, false) = 1 := by decide
example : vlDist (0, true) (4, false) = 1 := by decide
example : vlDist (0, true) (9, false) = 2 := by decide

/-- **P is a single-semitone voice-leading** (size 1), for every triad. -/
theorem P_size_one : ∀ t : Triad, vlDist t (PLR.Pf t) = 1 := by decide

/-- **L is a single-semitone voice-leading** (size 1), for every triad. -/
theorem L_size_one : ∀ t : Triad, vlDist t (PLR.Lf t) = 1 := by decide

/-- **R is a whole-tone voice-leading** (size 2 — NOT 1), for every triad: the honest correction to
    "P, L, R are all minimal/equal". -/
theorem R_size_two : ∀ t : Triad, vlDist t (PLR.Rf t) = 2 := by decide

/-- Each of P, L, R retains exactly **two common tones** (the parsimony that makes them minimal). -/
theorem P_holds_two : ∀ t : Triad, (pcs t ∩ pcs (PLR.Pf t)).card = 2 := by decide
theorem L_holds_two : ∀ t : Triad, (pcs t ∩ pcs (PLR.Lf t)).card = 2 := by decide
theorem R_holds_two : ∀ t : Triad, (pcs t ∩ pcs (PLR.Rf t)).card = 2 := by decide

end VoiceLeading

end MusicTheory
