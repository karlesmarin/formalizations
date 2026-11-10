/-
Usage examples of the reusable layer, area Polynomial, with the minimal import of that area: the
same code a user pastes into a file of their own project (README, section "Reusable layer").
-/
import Formalizations.Reusable.Polynomial

open Formalizations.Reusable Polynomial

/-- `X² − 1` splits over `ℝ`: its signs at `−2, 0, 2` are `+, −, +`. -/
example : (X ^ 2 - 1 : Polynomial ℝ).Splits := by
  refine splits_of_alternating_sign _ ?_ 2 ?_ ![-2, 0, 2] ?_ ?_
  · intro h
    have := congrArg (eval 0) h
    simp at this
  · compute_degree!
  · refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i <;> norm_num
  · intro i
    fin_cases i <;> norm_num

/-- `X³ − X` has at least three distinct real roots: its signs at `−2, −1/2, 1/2, 2` alternate. -/
example : 3 ≤ (X ^ 3 - X : Polynomial ℝ).roots.toFinset.card := by
  refine card_roots_toFinset_ge_of_alternating_sign _ ?_ 3 ![-2, -1 / 2, 1 / 2, 2] ?_ ?_
  · intro h
    have := congrArg (eval 2) h
    norm_num at this
  · refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i <;> norm_num
  · intro i
    fin_cases i <;> norm_num

/-- `X² − 1` splits over `ℝ`: it has degree `2` and a root in each gap of `−2 < 0 < 2`. -/
example : (X ^ 2 - 1 : Polynomial ℝ).Splits := by
  refine splits_of_isRoot_mem_Ioo_of_gaps _ ?_ 2 ?_ ![-2, 0, 2] ?_ ?_
  · intro h
    have := congrArg (eval 0) h
    simp at this
  · compute_degree!
  · refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i <;> norm_num
  · intro i
    fin_cases i
    · exact ⟨-1, by norm_num, by norm_num, by norm_num [IsRoot.def]⟩
    · exact ⟨1, by norm_num, by norm_num, by norm_num [IsRoot.def]⟩

/-- Sturm: if the Sturm chain of a squarefree `p` does not lose sign variations from `a` to `b`,
then `p` has no root in `(a, b]`. -/
example (p : Polynomial ℝ) (hp : Squarefree p) {a b : ℝ} (hab : a < b) (ha : p.eval a ≠ 0)
    (hb : p.eval b ≠ 0)
    (h : ((sturmSeq p (derivative p)).map (fun q => q.eval a)).signVariations ≤
      ((sturmSeq p (derivative p)).map (fun q => q.eval b)).signVariations) :
    ∀ x ∈ Set.Ioc a b, ¬ p.IsRoot x := by
  intro x hx hroot
  have hcount := sturm_signVariations_sub_eq_card_roots p hp hab ha hb
  have hmem : x ∈ p.roots.toFinset.filter (fun x => a < x ∧ x ≤ b) := by
    rw [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hp.ne_zero]
    exact ⟨hroot, hx.1, hx.2⟩
  have hpos := Finset.card_pos.2 ⟨x, hmem⟩
  omega

/-- Budan–Fourier: if the derivative tower loses exactly one sign variation from `a` to `b`, then
`p` has a root in `(a, b]` (the parity forbids zero roots). -/
example (p : Polynomial ℝ) (hp : p ≠ 0) {a b : ℝ} (hab : a < b) (ha : p.eval a ≠ 0)
    (hb : p.eval b ≠ 0)
    (h1 : ((List.range (p.natDegree + 1)).map (fun k => ((derivative^[k]) p).eval a)).signVariations -
        ((List.range (p.natDegree + 1)).map (fun k => ((derivative^[k]) p).eval b)).signVariations = 1) :
    ∃ x ∈ Set.Ioc a b, p.IsRoot x := by
  obtain ⟨-, hev⟩ := budan_fourier_card_roots_le p hp hab ha hb
  rw [h1] at hev
  have hne : (p.roots.filter (fun x => a < x ∧ x ≤ b)).card ≠ 0 := by
    intro h0
    rw [h0] at hev
    simp at hev
  obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.1 (Nat.pos_of_ne_zero hne)
  rw [Multiset.mem_filter] at hx
  exact ⟨x, ⟨hx.2.1, hx.2.2⟩, (mem_roots hp).1 hx.1⟩

/-- Newton's inequality for a monic real-rooted cubic and `k = 1`: `3 e₂ ≤ e₁²`. -/
example (p : Polynomial ℝ) (hp : p.Splits) (hm : p.Monic) (h3 : p.natDegree = 3) :
    3 * p.roots.esymm 2 ≤ p.roots.esymm 1 ^ 2 := by
  have h := newton_inequality_esymm_roots hp hm (k := 1) le_rfl (by omega)
  rw [h3] at h
  norm_num [Nat.choose] at h
  linarith

/-- Every higher derivative of a real-rooted polynomial is real-rooted (the step behind the
real roots of the Legendre polynomials, `dⁿ/dxⁿ (x² − 1)ⁿ`). -/
example (p : Polynomial ℝ) (hp : p.Splits) (k : ℕ) : ((derivative^[k]) p).Splits := by
  induction k with
  | zero => exact hp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact splits_derivative ih

/-- The reverse of a real-rooted polynomial has as many real roots, with multiplicity, as its
degree. -/
example (p : Polynomial ℝ) (hp : p.Splits) : p.reverse.roots.card = p.reverse.natDegree :=
  splits_iff_card_roots.1 (splits_reverse hp)
