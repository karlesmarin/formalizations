/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.Analysis.Polynomial.RealRoots.RealRooted
public import Formalizations.Analysis.Polynomial.RealRoots.NewtonInequalities
public import Formalizations.Analysis.Polynomial.RealRoots.Sturm
public import Formalizations.Analysis.Polynomial.RealRoots.BudanFourier

/-!
# Reusable layer: real polynomials and their real roots

Stable names for results on real-rooted real polynomials and on counting real roots. Every
statement uses Mathlib concepts only: real-rootedness is `Polynomial.Splits` (the archive
predicate `MSS.RealRooted` is that by definition, `realRooted_iff_splits`), Sturm's chain is
Mathlib's `Polynomial.sturmSeq`, and sign variations are Mathlib's `List.signVariations`. Each
theorem is proved by the archive theorem it re-exposes (no proof is copied); where the archive
uses its own sign-variation counter, the re-exposition only rewrites it into Mathlib's by the
archive's bridge lemmas.

This module imports no paper of the archive: only the four general modules of
`Formalizations.Analysis.Polynomial.RealRoots` it re-exposes.

## Main results

* `Formalizations.Reusable.splits_of_alternating_sign`: alternating signs at `n + 1` points and
  degree at most `n` give `Splits` (archive: `MSS.realRooted_of_alternating`).
* `Formalizations.Reusable.card_roots_toFinset_ge_of_alternating_sign`: alternating signs at
  `n + 1` points give at least `n` distinct real roots (archive: `MSS.card_roots_ge_of_alternating`).
* `Formalizations.Reusable.splits_of_isRoot_mem_Ioo_of_gaps`: a root in each of the `n` gaps and
  degree at most `n` give `Splits` (archive: `MSS.realRooted_of_root_per_gap`).
* `Formalizations.Reusable.sturm_signVariations_sub_eq_card_roots`: Sturm's theorem with
  `Polynomial.sturmSeq p (derivative p)` (archive: `Sturm.sturm`).
* `Formalizations.Reusable.budan_fourier_card_roots_le`: the Budan–Fourier theorem with
  `List.signVariations` of the derivative tower (archive: `BudanFourier.budan_fourier`).
* `Formalizations.Reusable.newton_inequality_esymm_roots`: Newton's inequalities for the roots of a
  monic real-rooted polynomial (archive: `Newton.newton_inequality`).
-/

@[expose] public section

open Polynomial

namespace Formalizations.Reusable

/-- The archive predicate `MSS.RealRooted` is Mathlib's `Polynomial.Splits` over `ℝ`, by
definition. This is the bridge that lets the results of this module be stated with Mathlib
concepts only. -/
theorem realRooted_iff_splits (p : Polynomial ℝ) : MSS.RealRooted p ↔ p.Splits :=
  Iff.rfl

/-- **Real-rootedness from sign alternation.** A nonzero real polynomial `h` of degree at most `n`
that alternates sign at `n + 1` strictly increasing points `x 0 < x 1 < ⋯ < x n`
(`h (x i) · h (x (i+1)) < 0`) splits over `ℝ`: the intermediate value theorem gives a root in each
of the `n` gaps, and the degree bound leaves no room for non-real roots. This is the step in which
the method of interlacing polynomials (Marcus–Spielman–Srivastava) concludes real-rootedness.

* Archive: `MSS.realRooted_of_alternating`
  (`Formalizations.Analysis.Polynomial.RealRoots.RealRooted`, a tool for the Heilmann–Lieb theorem
  on matching polynomials in the same archive); restated with `Polynomial.Splits` through
  `realRooted_iff_splits`.
* Classical reference: S. Fisk, *Polynomials, roots, and interlacing*, arXiv:math/0612833;
  A. W. Marcus, D. A. Spielman, N. Srivastava, Ann. of Math. 182 (2015) 307–325.
* Example: for `h = X² − 1`, `n = 2` and the points `−2 < 0 < 2`, the signs are `+, −, +`, so
  `splits_of_alternating_sign` shows that `X² − 1` splits. -/
theorem splits_of_alternating_sign (h : Polynomial ℝ) (hh : h ≠ 0) (n : ℕ)
    (hdeg : h.natDegree ≤ n) (x : Fin (n + 1) → ℝ) (hmono : StrictMono x)
    (halt : ∀ i : Fin n, h.eval (x i.castSucc) * h.eval (x i.succ) < 0) :
    h.Splits :=
  (realRooted_iff_splits h).1 (MSS.realRooted_of_alternating h hh n hdeg x hmono halt)

/-- **Counting real roots by sign alternation.** If a nonzero real polynomial `h` takes strictly
alternating signs at `n + 1` strictly increasing points (`h (x i) · h (x (i+1)) < 0`), it has at
least `n` distinct real roots: the intermediate value theorem puts one in each open gap, and the
gaps are disjoint. No degree hypothesis is needed.

* Archive: `MSS.card_roots_ge_of_alternating`
  (`Formalizations.Analysis.Polynomial.RealRoots.RealRooted`, a tool for the Heilmann–Lieb theorem
  in the same archive); the module cites no paper DOI of ours.
* Classical reference: S. Fisk, *Polynomials, roots, and interlacing*, arXiv:math/0612833.
* Example: `X³ − X` has signs `−, +, −, +` at `−2, −1/2, 1/2, 2`, so
  `card_roots_toFinset_ge_of_alternating_sign` gives at least `3` distinct real roots. -/
theorem card_roots_toFinset_ge_of_alternating_sign (h : Polynomial ℝ) (hh : h ≠ 0) (n : ℕ)
    (x : Fin (n + 1) → ℝ) (hmono : StrictMono x)
    (halt : ∀ i : Fin n, h.eval (x i.castSucc) * h.eval (x i.succ) < 0) :
    n ≤ h.roots.toFinset.card :=
  MSS.card_roots_ge_of_alternating h hh n x hmono halt

/-- **Real-rootedness from one root per gap.** If a nonzero real polynomial `f` of degree at most
`n` has a root in each of the `n` open gaps `(x i, x (i+1))` between `n + 1` strictly increasing
points, then `f` splits over `ℝ`. This is the closing step of the interlacing proofs of
real-rootedness (orthogonal polynomials through their three-term recurrence; Cauchy interlacing of
characteristic polynomials).

* Archive: `MSS.realRooted_of_root_per_gap`
  (`Formalizations.Analysis.Polynomial.RealRoots.RealRooted`); restated with `Polynomial.Splits`
  through `realRooted_iff_splits`. The module cites no paper DOI of ours.
* Classical reference: S. Fisk, *Polynomials, roots, and interlacing*, arXiv:math/0612833.
* Example: `X² − 1` has degree `2` and roots in `(−2, 0)` and `(0, 2)`, so
  `splits_of_isRoot_mem_Ioo_of_gaps` shows that it splits. -/
theorem splits_of_isRoot_mem_Ioo_of_gaps (f : Polynomial ℝ) (hf : f ≠ 0) (n : ℕ)
    (hdeg : f.natDegree ≤ n) (x : Fin (n + 1) → ℝ) (hmono : StrictMono x)
    (hroot : ∀ i : Fin n, ∃ r, x i.castSucc < r ∧ r < x i.succ ∧ f.IsRoot r) :
    f.Splits :=
  (realRooted_iff_splits f).1 (MSS.realRooted_of_root_per_gap f hf n hdeg x hmono hroot)

/-- **Sturm's theorem.** For a squarefree real polynomial `p` and `a < b` with `p a ≠ 0` and
`p b ≠ 0`, the number of sign variations of Mathlib's Sturm chain
`Polynomial.sturmSeq p (derivative p)` evaluated at `a`, minus the number at `b`, is the number of
distinct real roots of `p` in `(a, b]`. Sign variations are Mathlib's `List.signVariations`
(zeros are skipped).

* Archive: `Sturm.sturm` (`Formalizations.Analysis.Polynomial.RealRoots.Sturm`), restated with
  Mathlib's chain and counter through the archive bridges `Sturm.sturmSeq_eq` and
  `Sturm.signVarAt_eq_signVariations`. Mathlib's `Polynomial.sturmSeq` contains only the algebraic
  properties of the chain; this is the theorem it is defined for.
* Classical reference: C. Sturm (1829); S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real
  Algebraic Geometry*, ch. 2.
* Example: for `p = X² − 2` on `[0, 2]`, the theorem counts the single root `√2`. -/
theorem sturm_signVariations_sub_eq_card_roots (p : Polynomial ℝ) (hp : Squarefree p) {a b : ℝ}
    (hab : a < b) (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((Polynomial.sturmSeq p (derivative p)).map (fun q => q.eval a)).signVariations -
        ((Polynomial.sturmSeq p (derivative p)).map (fun q => q.eval b)).signVariations =
      (p.roots.toFinset.filter (fun x => a < x ∧ x ≤ b)).card := by
  rw [← Sturm.sturmSeq_eq hp.ne_zero, ← Sturm.signVarAt_eq_signVariations,
    ← Sturm.signVarAt_eq_signVariations]
  exact Sturm.sturm p hp hab ha hb

/-- **The Budan–Fourier theorem.** For a nonzero real polynomial `p` and `a < b` with `p a ≠ 0`
and `p b ≠ 0`, let `V x` be the number of sign variations (Mathlib's `List.signVariations`, zeros
skipped) of the derivative tower `p, p', p'', …, p^{(deg p)}` evaluated at `x`. Then the number of
real roots of `p` in `(a, b]`, counted with multiplicity, is at most `V a − V b`, and the
difference is even. Descartes' rule of signs is the case `(0, ∞)`.

* Archive: `BudanFourier.budan_fourier`
  (`Formalizations.Analysis.Polynomial.RealRoots.BudanFourier`), restated with
  `List.signVariations` through the archive bridges `BudanFourier.fourierVar_eq_signVarAt` and
  `Sturm.signVarAt_eq_signVariations`.
* Classical reference: F. D. Budan (1807), J. Fourier (1820); S. Basu, R. Pollack, M.-F. Roy,
  *Algorithms in Real Algebraic Geometry*, ch. 2.
* Example: for `p = X² − 1` on `(0, 2]`, the theorem bounds the number of roots (one, at `1`) by
  the drop of sign variations of `(X² − 1, 2X, 2)` from `0` to `2`, which is `1`. -/
theorem budan_fourier_card_roots_le (p : Polynomial ℝ) (hp : p ≠ 0) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    (p.roots.filter (fun x => a < x ∧ x ≤ b)).card ≤
        ((List.range (p.natDegree + 1)).map (fun k => ((derivative^[k]) p).eval a)).signVariations -
          ((List.range (p.natDegree + 1)).map (fun k => ((derivative^[k]) p).eval b)).signVariations ∧
      Even (((List.range (p.natDegree + 1)).map
          (fun k => ((derivative^[k]) p).eval a)).signVariations -
        ((List.range (p.natDegree + 1)).map (fun k => ((derivative^[k]) p).eval b)).signVariations -
        (p.roots.filter (fun x => a < x ∧ x ≤ b)).card) := by
  have hV : ∀ x, BudanFourier.fourierVar p x =
      ((List.range (p.natDegree + 1)).map (fun k => ((derivative^[k]) p).eval x)).signVariations := by
    intro x
    rw [BudanFourier.fourierVar_eq_signVarAt, Sturm.signVarAt_eq_signVariations,
      BudanFourier.fourierSeq, List.map_map]
    rfl
  simpa only [hV] using BudanFourier.budan_fourier p hp hab ha hb

/-- **Newton's inequalities.** Let `p` be a monic real polynomial of degree `n` that splits over
`ℝ`, with roots (with multiplicity) `p.roots`, and let `e_j = p.roots.esymm j` be their elementary
symmetric functions. For `1 ≤ k ≤ n − 1`,
`e_k² · C(n, k−1) · C(n, k+1) ≥ e_{k−1} · e_{k+1} · C(n, k)²`; that is, the normalized
`E_k = e_k / C(n, k)` satisfy `E_k² ≥ E_{k−1} E_{k+1}`. The proof differentiates and reverses the
polynomial down to a real-rooted quadratic.

* Archive: `Newton.newton_inequality`
  (`Formalizations.Analysis.Polynomial.RealRoots.NewtonInequalities`), restated with
  `Polynomial.Splits` through `realRooted_iff_splits`; the module cites no paper DOI of ours.
* Classical reference: I. Newton, *Arithmetica universalis* (1707); G. H. Hardy, J. E. Littlewood,
  G. Pólya, *Inequalities*, 2nd ed. (1952), ch. II.
* Example: for `p = (X − 1)(X − 2)(X − 3)` and `k = 1`, it gives `e_1² · 1 · 3 ≥ e_0 e_2 · 9`,
  that is `36 · 3 ≥ 11 · 9`. -/
theorem newton_inequality_esymm_roots {p : Polynomial ℝ} (hp : p.Splits) (hmonic : p.Monic)
    {k : ℕ} (hk : 1 ≤ k) (hk2 : k + 1 ≤ p.natDegree) :
    (p.roots.esymm k) ^ 2 * ((p.natDegree.choose (k - 1) : ℝ) * (p.natDegree.choose (k + 1) : ℝ))
      ≥ (p.roots.esymm (k - 1)) * (p.roots.esymm (k + 1)) * ((p.natDegree.choose k : ℝ)) ^ 2 :=
  Newton.newton_inequality ((realRooted_iff_splits p).2 hp) hmonic hk hk2

end Formalizations.Reusable
