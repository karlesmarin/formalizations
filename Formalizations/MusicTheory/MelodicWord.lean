/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Tactic.Ring

/-!
# A direction-sensitive invariant of melodic words

For a word `xs : List (ZMod 12)` and an odd function `f : ZMod 12 → M` into an additive group,
`W f xs` sums `f` over the successive steps `x (j+1) - x j`. Reversing the word negates `W`, and
repeating a note does not change it. In contrast, order-blind statistics such as the step
coefficients are invariant under reversal.

## Main results

* `steps_reverse`, `W_reverse`: retrograde antisymmetry.
* `W_cons_dup`, `W_dup_general`: invariance under repeated notes.
* `f_zero`, `W_reverse_odd`, `W_dup_general_odd`: the same laws from oddness alone in a
  torsion-free group.
* `acoef_blind_to_retrograde`, `W_separates_retrograde`.
* `two_torsion_eq_tritone`, `odd_vanishes_at_tritone`.
-/

@[expose] public section

namespace MusicTheory

namespace MelodicWord

variable {M : Type*} [AddCommGroup M]

/-! ### Directed steps of a melodic word. -/

/-- The consecutive directed intervals of a melodic word: `steps [x₀,…,xₙ] = [x₁−x₀, …, xₙ−xₙ₋₁]`.
    Each entry `step_j = x_{j+1} − x_j` is the directed melodic interval (sign = up/down). -/
def steps : List (ZMod 12) → List (ZMod 12)
  | [] => []
  | [_] => []
  | a :: b :: rest => (b - a) :: steps (b :: rest)

@[simp] lemma steps_nil : steps [] = [] := rfl
@[simp] lemma steps_singleton (a : ZMod 12) : steps [a] = [] := rfl
@[simp] lemma steps_cons_cons (a b : ZMod 12) (rest : List (ZMod 12)) :
    steps (a :: b :: rest) = (b - a) :: steps (b :: rest) := rfl

/-- **The directed winding statistic.** `W f xs = Σ_j f(step_j)` over the directed steps. -/
def W (f : ZMod 12 → M) (xs : List (ZMod 12)) : M := ((steps xs).map f).sum

@[simp] lemma W_nil (f : ZMod 12 → M) : W f [] = 0 := rfl
@[simp] lemma W_singleton (f : ZMod 12 → M) (a : ZMod 12) : W f [a] = 0 := rfl

lemma W_cons_cons (f : ZMod 12 → M) (a b : ZMod 12) (rest : List (ZMod 12)) :
    W f (a :: b :: rest) = f (b - a) + W f (b :: rest) := by
  unfold W; rw [steps_cons_cons, List.map_cons, List.sum_cons]

/-! ### Oddness ⇒ `f 0 = 0` (the concrete ℝ-valued `sin` invariant; needs 2-torsion-freeness). -/

/-- From oddness `f (−m) = − f m`, at `m = 0` we get `f 0 = − f 0`, hence `f 0 = 0`. Stated for the
    real-valued case (the concrete `sin(2π·/12)` invariant), where 2-torsion-freeness is automatic. -/
theorem f_zero {f : ZMod 12 → ℝ} (Hodd : ∀ m, f (-m) = - f m) : f 0 = 0 := by
  have h : f 0 = - f 0 := by simpa using Hodd 0
  have hsum : f 0 + f 0 = 0 := add_eq_zero_iff_eq_neg.mpr h
  exact add_self_eq_zero.mp hsum

/-! ### Helper: how `steps` interacts with prepending a single LEADING note.

`steps` peels notes off the FRONT. Prepending a note `z` to a NONEMPTY word `(a :: l)` PREPENDS one
new first step `a − z` to `steps`, leaving the rest unchanged. This single fact drives `steps_reverse`
via concat (`reverseRecOn`) induction, since `(xs ++ [z]).reverse = z :: xs.reverse`. -/

/-- Prepending a note `z` before a NONEMPTY word `(a :: l)` prepends the step `a − z`:
    `steps (z :: a :: l) = (a − z) :: steps (a :: l)`. (Just unfolds the recursion.) -/
lemma steps_cons (z a : ZMod 12) (l : List (ZMod 12)) :
    steps (z :: a :: l) = (a - z) :: steps (a :: l) := rfl

/-- **The retrograde step law.** The directed steps of the reversed word are the negated steps of the
    word, in reversed order: `steps xs.reverse = ((steps xs).map (-·)).reverse`. Reversing a melody
    flips every directed interval (`x_{j+1}−x_j ↦ x_j−x_{j+1} = −step_j`) AND their order.

    Proof by concat induction (`reverseRecOn`): appending a trailing note `z` to `xs` is, after
    reversing, prepending `z` to `xs.reverse`. -/
theorem steps_reverse (xs : List (ZMod 12)) :
    steps xs.reverse = ((steps xs).map (fun s => -s)).reverse := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton ys z ih =>
    -- (ys ++ [z]).reverse = z :: ys.reverse. Split on whether ys is empty.
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
    cases ys with
    | nil => rfl
    | cons a t =>
      -- ys.reverse is nonempty, headed by the LAST of ys; expose it as (c :: l)
      obtain ⟨c, l, hcl⟩ : ∃ c l, (a :: t).reverse = c :: l := by
        cases h : (a :: t).reverse with
        | nil => simp at h
        | cons c l => exact ⟨c, l, rfl⟩
      -- LHS: steps (z :: (a::t).reverse) = steps (z :: c :: l) = (c - z) :: steps (c :: l)
      rw [hcl, steps_cons]
      -- ih : steps (a::t).reverse = ((steps (a::t)).map (-·)).reverse, with LHS = steps (c::l)
      rw [hcl] at ih
      rw [ih]
      -- RHS: steps (ys ++ [z]) reverses to ... ; compute steps of the concat then map/reverse
      -- steps ((a::t) ++ [z]) appends the final step (z - last). Use the concat-append lemma.
      have hsteps_concat : ∀ (a : ZMod 12) (t : List (ZMod 12)),
          steps ((a :: t) ++ [z]) = steps (a :: t) ++ [z - (a :: t).getLast (by simp)] := by
        intro a t
        induction t generalizing a with
        | nil => simp [steps]
        | cons b u ihu =>
          -- (a::b::u)++[z] = a :: ((b::u)++[z]); peel a, then apply ihu on (b::u)++[z]
          rw [List.cons_append, show steps (a :: ((b :: u) ++ [z]))
                = (b - a) :: steps ((b :: u) ++ [z]) from rfl, ihu b,
              steps_cons_cons,
              show (a :: b :: u).getLast (by simp) = (b :: u).getLast (by simp) from
                List.getLast_cons (by simp), List.cons_append]
      rw [hsteps_concat a t, List.map_append, List.reverse_append]
      -- last of (a::t) = head c of its reverse (read off hcl)
      have hlast : (a :: t).getLast (by simp) = c := by
        have h1 : (a :: t).getLast? = some c := by
          rw [← List.head?_reverse, hcl]; rfl
        rw [List.getLast?_eq_getLast_of_ne_nil (by simp)] at h1
        exact Option.some.inj h1
      rw [hlast]
      simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append]
      rw [neg_sub]

/-- Summing a list of negated terms negates the sum: `(l.map (fun s => -g s)).sum = -(l.map g).sum`. -/
lemma sum_map_neg (g : ZMod 12 → M) :
    ∀ l : List (ZMod 12), ((l.map (fun s => -g s)).sum) = -((l.map g).sum)
  | [] => by simp
  | a :: l => by rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
      sum_map_neg g l, neg_add]

/-! ### Theorem 1 — Retrograde antisymmetry. -/

/-- **RETROGRADE ANTISYMMETRY.** Reversing a melodic word negates its winding statistic:
    `W f xs.reverse = − W f xs`, for any ODD `f`. (Each directed step negates under retrograde
    — `steps_reverse` — and `f` odd turns each `f(−s)` into `−f(s)`; the sum then negates.) -/
theorem W_reverse {f : ZMod 12 → M} (Hodd : ∀ m, f (-m) = - f m) (xs : List (ZMod 12)) :
    W f xs.reverse = - W f xs := by
  unfold W
  rw [steps_reverse, List.map_reverse, List.sum_reverse, List.map_map]
  -- (steps xs).map (f ∘ (-·)) = (steps xs).map (-f) by oddness
  have : (steps xs).map (f ∘ fun s => -s) = (steps xs).map (fun s => -f s) := by
    apply List.map_congr_left
    intro s _; simp only [Function.comp_apply]; exact Hodd s
  rw [this, sum_map_neg f]

/-! ### Theorem 2 — Repetition / reparametrization invariance. -/

/-- **Repeat the HEAD note.** Inserting an immediate repeat of the first note inserts a step of `0`,
    which `f 0 = 0` kills: `W f (a :: a :: rest) = W f (a :: rest)`. -/
theorem W_cons_dup {f : ZMod 12 → M} (hf0 : f 0 = 0) (a : ZMod 12) (rest : List (ZMod 12)) :
    W f (a :: a :: rest) = W f (a :: rest) := by
  rw [W_cons_cons]; simp [hf0]

/-- **Repeat an INTERIOR note** (the step on each side is unaffected; the inserted middle step is `0`).
    `W f (a :: b :: b :: rest) = W f (a :: b :: rest)`. -/
theorem W_cons_cons_dup {f : ZMod 12 → M} (hf0 : f 0 = 0) (a b : ZMod 12) (rest : List (ZMod 12)) :
    W f (a :: b :: b :: rest) = W f (a :: b :: rest) := by
  rw [W_cons_cons (rest := b :: rest), W_cons_dup hf0, W_cons_cons]

/-- **REPETITION / REPARAMETRIZATION INVARIANCE (general).** Duplicating the note `a` at ANY position
    of a melodic word leaves `W` unchanged: `W f (pre ++ a :: a :: rest) = W f (pre ++ a :: rest)`.
    The duplicated note inserts a single directed step `a − a = 0`, killed by `f 0 = 0`; all other
    steps are untouched. This is the "tempo / note-value is irrelevant" law — `W` sees the PATH, not
    its parametrization. -/
theorem W_dup_general {f : ZMod 12 → M} (hf0 : f 0 = 0) (a : ZMod 12) :
    ∀ (pre rest : List (ZMod 12)),
      W f (pre ++ a :: a :: rest) = W f (pre ++ a :: rest)
  | [], rest => by simpa using W_cons_dup hf0 a rest
  | [p], rest => by simpa using W_cons_cons_dup hf0 p a rest
  | p :: q :: pre, rest => by
      show W f (p :: q :: (pre ++ a :: a :: rest)) = W f (p :: q :: (pre ++ a :: rest))
      rw [W_cons_cons, W_cons_cons]
      congr 1
      have ih := W_dup_general hf0 a (q :: pre) rest
      rw [List.cons_append, List.cons_append] at ih
      exact ih

/-! ### Specialization (the concrete `sin` invariant): `f 0 = 0` comes for free from oddness over a
    2-torsion-free codomain (e.g. ℝ, where `NoZeroSMulDivisors ℕ ℝ` holds). -/

/-- Retrograde antisymmetry needing ONLY oddness, over a 2-torsion-free codomain (ℝ): `f 0 = 0` free. -/
theorem W_reverse_odd {M : Type*} [AddCommGroup M] {f : ZMod 12 → M}
    (Hodd : ∀ m, f (-m) = - f m) (xs : List (ZMod 12)) :
    W f xs.reverse = - W f xs :=
  W_reverse Hodd xs

/-- Repetition invariance (general) needing ONLY oddness, for the real-valued `sin` invariant. -/
theorem W_dup_general_odd {f : ZMod 12 → ℝ}
    (Hodd : ∀ m, f (-m) = - f m) (a : ZMod 12) (pre rest : List (ZMod 12)) :
    W f (pre ++ a :: a :: rest) = W f (pre ++ a :: rest) :=
  W_dup_general (f_zero Hodd) a pre rest

/-! ### Order-blindness of the pitch-class DFT

The DFT coefficient `a_k` of a melodic word is a SUM over the notes of a per-note quantity
`φ(xᵢ)`; the SUMMAND depends on each pitch class alone, never on its neighbours. Hence `a_k`
factors through the MULTISET of pitch classes and is invariant under retrograde (reverse) AND under
any permutation. The crucial point: this needs NOTHING about the exponential — it is pure list-sum
invariance. We give it in two layers.

Layer (a) — ABSTRACT, over any `AddCommMonoid` codomain. The whole content is `List.sum_reverse`
(through `List.map_reverse`) and `List.Perm.sum_eq` (through `List.Perm.map`). -/

section OrderBlind
variable {N : Type*} [AddCommMonoid N]

/-- **Reverse-invariance of a list-sum-of-a-pointwise-function** (any `AddCommMonoid` codomain).
    `Σᵢ φ(xᵢ)` is unchanged by reversing the list: order is invisible to a sum of per-element terms. -/
theorem sum_map_reverse (φ : ZMod 12 → N) (xs : List (ZMod 12)) :
    ((xs.reverse).map φ).sum = (xs.map φ).sum := by
  rw [List.map_reverse, List.sum_reverse]

/-- **Permutation-invariance of a list-sum-of-a-pointwise-function** (any `AddCommMonoid` codomain).
    `Σᵢ φ(xᵢ)` depends only on the MULTISET of `xs`: any reordering gives the same sum. -/
theorem sum_map_perm {φ : ZMod 12 → N} {xs ys : List (ZMod 12)} (h : List.Perm xs ys) :
    (xs.map φ).sum = (ys.map φ).sum :=
  (h.map φ).sum_eq

end OrderBlind

/-! Layer (b) — SPECIALIZE to the actual pc-DFT character. The exact exponent is irrelevant to the
two laws (only that the summand is a function of the single note `x`); we use the standard kernel
`exp(−2πi·k·x/12)`. `acoef` is `noncomputable` (it uses `Complex.exp`); the theorems are pure. -/

/-- The pc-DFT coefficient `a_k` of a melodic WORD: `a_k(xs) = Σⱼ exp(−2πi·k·xⱼ/12)`. Built as a
    list-sum of a per-note kernel, so it is order-blind by construction (see `acoef_reverse`/`_perm`). -/
noncomputable def acoef (k : ℕ) (xs : List (ZMod 12)) : ℂ :=
  (xs.map (fun x => Complex.exp (-2 * Real.pi * Complex.I * k * (x.val : ℝ) / 12))).sum

/-- **The DFT cannot see direction.** `a_k` is invariant under RETROGRADE: `acoef k xs.reverse =
    acoef k xs`. Immediate specialization of `sum_map_reverse`. -/
theorem acoef_reverse (k : ℕ) (xs : List (ZMod 12)) :
    acoef k xs.reverse = acoef k xs :=
  sum_map_reverse _ xs

/-- **The DFT cannot see order at all.** `a_k` factors through the multiset of pitch classes:
    `xs ~ ys → acoef k xs = acoef k ys`. Immediate specialization of `sum_map_perm`. -/
theorem acoef_perm {k : ℕ} {xs ys : List (ZMod 12)} (h : List.Perm xs ys) :
    acoef k xs = acoef k ys :=
  sum_map_perm h

/-! ### Directional ⊥ a_k : the harmonic axis CANNOT separate a word from its retrograde,
    yet the directed axis `W` CAN.

`a_k` is retrograde-blind (previous section), so ANY functional of the WHOLE `a_k`-vector is retrograde-blind too
(`acoef_blind_to_retrograde`): the entire harmonic profile is the same forwards and backwards. The
directed winding statistic `W`, by contrast, FLIPS SIGN under retrograde (`W_reverse`), so it
strictly distinguishes a word from its reverse whenever it is nonzero over a 2-torsion-free codomain
(`W_separates_retrograde`). The two axes are orthogonal-on-direction: harmonic content is symmetric,
directed motion is antisymmetric. -/

/-- **No functional of the a_k-vector separates a word from its retrograde.** For ANY `g` on the full
    coefficient vector `(k ↦ a_k)`, the forward and retrograde words give the SAME value. (The two
    coefficient vectors are equal pointwise by `acoef_reverse`, hence equal as functions.) -/
theorem acoef_blind_to_retrograde {β : Type*} (g : (ℕ → ℂ) → β) (xs : List (ZMod 12)) :
    g (fun k => acoef k xs.reverse) = g (fun k => acoef k xs) := by
  congr 1
  funext k
  exact acoef_reverse k xs

/-- **`W` strictly separates a word from its retrograde when nonzero.** Over a 2-torsion-free
    `AddCommGroup` (`NoZeroSMulDivisors ℕ M`, e.g. ℝ), if the directed winding `W f xs ≠ 0` then the
    retrograde value `W f xs.reverse = −W f xs` differs from `W f xs`. So `W` SEES the direction that
    the entire harmonic `a_k`-vector is blind to. -/
theorem W_separates_retrograde {M : Type*} [AddCommGroup M] [NoZeroSMulDivisors ℕ M]
    {f : ZMod 12 → M} (Hodd : ∀ m, f (-m) = - f m) (xs : List (ZMod 12))
    (hne : W f xs ≠ 0) : W f xs.reverse ≠ W f xs := by
  rw [W_reverse Hodd]
  intro h
  -- h : -W f xs = W f xs.  So W + W = W + (-W) = 0 ⇒ 2•W = 0 ⇒ W = 0, contradicting hne.
  apply hne
  have hzero : W f xs + W f xs = 0 := by
    nth_rewrite 1 [← h]; exact neg_add_cancel (W f xs)
  have h2 : (2 : ℕ) • W f xs = 0 := by rw [two_smul]; exact hzero
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

/-! ### The tritone obstruction

`f 0 = 0` (the existing `f_zero`) is only the FIRST of the 2-torsion obstructions. ℤ/12 has EXACTLY
two solutions of `m = −m`: the identity `0` and the tritone `6` (`6 + 6 = 12 ≡ 0`). Both are forced
to vanish for any odd `f` over a 2-torsion-free codomain. The tritone `6` is the same central element
`T₆` that recurs throughout the corpus: the unique nonzero element fixed by inversion, the centre of
6-30, the fixed axis of the rhythmic oddity property, and the tritone anomaly of the interval vector. -/

/-- **The unique nonzero 2-torsion point of ℤ/12 is the tritone.** `m = −m ↔ m = 0 ∨ m = 6`. -/
theorem two_torsion_eq_tritone : ∀ m : ZMod 12, (m = -m) ↔ (m = 0 ∨ m = 6) := by decide

/-- **The TRITONE obstruction.** Any odd `f` over a 2-torsion-free codomain (here ℝ, the concrete
    `sin(2π·/12)` invariant) must VANISH at the tritone: `f 6 = 0`. Since `−6 = 6` in ℤ/12, oddness
    gives `f 6 = f(−6) = −f 6`, and 2-torsion-freeness forces `f 6 = 0` — exactly mirroring `f_zero`
    at the second (and only other) self-inverse point. -/
theorem odd_vanishes_at_tritone {f : ZMod 12 → ℝ} (Hodd : ∀ m, f (-m) = - f m) : f 6 = 0 := by
  have h : f 6 = - f 6 := by
    have h6 : (-(6 : ZMod 12)) = 6 := by decide
    have := Hodd 6
    rwa [h6] at this
  have hsum : f 6 + f 6 = 0 := add_eq_zero_iff_eq_neg.mpr h
  exact add_self_eq_zero.mp hsum

/-! ### A concrete witness: a genuinely odd `f` on ℤ/12 with `W` direction-sensitive.

`fsign m = (if m.val ≤ 6 then m.val else m.val − 12 : ℤ)` is the signed representative in `[−5,6]`…
but `6 ↦ 6` and `−6 = 6` so that exact map is NOT odd at the tritone. The clean odd integer model
is `g m = m.val − 6·(…)`; rather than fight the tritone we exhibit oddness abstractly: any `f` built
as `f m = h m − h (−m)` is odd, and `sin(2π·/12)` is the analytic instance. We record the small
arithmetic witness that the directed step really does flip sign, which is the whole point. -/

/-- The directed step from `x` to `y` is the negation of the step from `y` to `x`:
    `steps [y, x] = [x − y] = −(steps [x, y])` — the atomic source of retrograde antisymmetry. -/
example (x y : ZMod 12) : steps [y, x] = ((steps [x, y]).map (fun s => -s)).reverse := by
  simp [steps, neg_sub]

end MelodicWord

end MusicTheory
