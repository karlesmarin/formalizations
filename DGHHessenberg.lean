/-
Author: Carles Marín (with Claude as AI assistant).

DGHHessenberg: Jakobs' order on finite multisets of ordinals (F. Jakobs, thesis 2019,
Thm 1.1.3; Dubrovin–Gräter–Hanke Prop 2.1) read as the order of ordinals through the
Hessenberg (natural) sum `h s = ♯_{x ∈ s} ω ^ x`.

The installed Mathlib (rev 701fb6e9, May 2026) no longer ships `NatOrdinal` / `Ordinal.nadd`
(no `NaturalOps.lean`, no occurrence of `nadd`), so the natural sum is defined here in the
classical way, through Cantor normal form coefficients:
`a ♯ b = CNF.eval ω (CNF.coeff ω a + CNF.coeff ω b)`.

Proved:
(1) `hval_add`        : h (s + t) = h s ♯ h t.
(2) `jakobsLT_iff_hval_lt` : jakobsLT s t ↔ h s < h t; hence `hval_injective`.
(3) `image_hval`      : {h s | ∀ x ∈ s, x ≤ Λ} = Set.Iio (ω ^ (Λ + 1)).
Corollary `omega0_opow_add_one_lt_epsilon_zero` : Λ < ε₀ → ω ^ (Λ + 1) < ε₀.
-/
import DGHLex
import Mathlib.SetTheory.Ordinal.CantorNormalForm
import Mathlib.SetTheory.Ordinal.Veblen
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.Data.Finsupp.Multiset

universe u

namespace DGH

open Ordinal Multiset Finsupp

noncomputable section

/-! ### Natural (Hessenberg) sum via CNF coefficients -/

lemma coeff_omega0_lt (o : Ordinal.{u}) (e : Ordinal.{u}) : CNF.coeff ω o e < ω := by
  by_cases he : e ∈ (CNF ω o).map Prod.fst
  · rw [List.mem_map] at he
    obtain ⟨⟨e', c⟩, hm, rfl⟩ := he
    rw [CNF.coeff_of_mem_CNF hm]
    exact CNF.snd_lt one_lt_omega0 hm
  · rw [CNF.coeff_of_notMem_CNF he]
    exact omega0_pos

/-- Natural (Hessenberg) sum: add Cantor-normal-form coefficients base `ω`. -/
def nadd (a b : Ordinal.{u}) : Ordinal.{u} :=
  CNF.eval ω (CNF.coeff ω a + CNF.coeff ω b)

@[inherit_doc] scoped infixl:65 " ♯ " => nadd

lemma coeff_nadd (a b : Ordinal.{u}) :
    CNF.coeff ω (a ♯ b) = CNF.coeff ω a + CNF.coeff ω b :=
  CNF.coeff_eval one_lt_omega0 fun e =>
    isPrincipal_add_omega0 (coeff_omega0_lt a e) (coeff_omega0_lt b e)

/-- Ordinal `+` is commutative below `ω` (natural numbers). -/
lemma add_comm_of_lt_omega0 {x y : Ordinal.{u}} (hx : x < ω) (hy : y < ω) : x + y = y + x := by
  obtain ⟨n, rfl⟩ := lt_omega0.1 hx
  obtain ⟨m, rfl⟩ := lt_omega0.1 hy
  rw [← Nat.cast_add, ← Nat.cast_add, Nat.add_comm]

theorem nadd_comm (a b : Ordinal.{u}) : a ♯ b = b ♯ a := by
  unfold nadd
  congr 1
  ext e
  rw [Finsupp.add_apply, Finsupp.add_apply]
  exact add_comm_of_lt_omega0 (coeff_omega0_lt a e) (coeff_omega0_lt b e)

theorem nadd_assoc (a b c : Ordinal.{u}) : a ♯ b ♯ c = a ♯ (b ♯ c) := by
  show CNF.eval ω (CNF.coeff ω (a ♯ b) + CNF.coeff ω c)
    = CNF.eval ω (CNF.coeff ω a + CNF.coeff ω (b ♯ c))
  rw [coeff_nadd, coeff_nadd, add_assoc]

@[simp] theorem nadd_zero (a : Ordinal.{u}) : a ♯ 0 = a := by
  rw [nadd, CNF.coeff_zero_right, add_zero, CNF.eval_coeff]

/-! ### Multisets of ordinals as CNF coefficient functions -/

/-- `cf s x = count x s`, as a finitely supported `Ordinal`-valued function. -/
def cf (s : Multiset Ordinal.{u}) : Ordinal.{u} →₀ Ordinal.{u} :=
  Finsupp.mapRange (fun n : ℕ => (n : Ordinal.{u})) Nat.cast_zero (Multiset.toFinsupp s)

@[simp] lemma cf_apply (s : Multiset Ordinal.{u}) (x : Ordinal.{u}) :
    cf s x = (count x s : Ordinal) := by
  simp [cf, Multiset.toFinsupp_apply]

lemma mem_support_cf {s : Multiset Ordinal.{u}} {x : Ordinal.{u}} :
    x ∈ (cf s).support ↔ x ∈ s := by
  rw [Finsupp.mem_support_iff, cf_apply, Ne, Nat.cast_eq_zero, count_eq_zero, not_not]

lemma cf_add (s t : Multiset Ordinal.{u}) : cf (s + t) = cf s + cf t := by
  ext x; simp [count_add]

@[simp] lemma cf_zero : cf (0 : Multiset Ordinal.{u}) = 0 := by
  ext x; simp

lemma cf_replicate (n : ℕ) (x : Ordinal.{u}) : cf (replicate n x) = Finsupp.single x (n : Ordinal) := by
  ext y
  rw [cf_apply, count_replicate, Finsupp.single_apply]
  split_ifs <;> simp

lemma cf_lt (s : Multiset Ordinal.{u}) (x : Ordinal.{u}) : cf s x < ω := by
  rw [cf_apply]; exact natCast_lt_omega0 _

/-- `h s = ♯_{x ∈ s} ω ^ x` (the Hessenberg sum of the `ω ^ x`). -/
def hval (s : Multiset Ordinal.{u}) : Ordinal.{u} := CNF.eval ω (cf s)

/-- (1) `h` is a monoid homomorphism `(Multiset Ordinal, +) → (Ordinal, ♯)`. -/
theorem hval_add (s t : Multiset Ordinal.{u}) : hval (s + t) = hval s ♯ hval t := by
  rw [hval, hval, hval, nadd, CNF.coeff_eval one_lt_omega0 (cf_lt s),
    CNF.coeff_eval one_lt_omega0 (cf_lt t), cf_add]

@[simp] theorem hval_zero : hval (0 : Multiset Ordinal.{u}) = 0 := by
  simp [hval]

theorem hval_replicate (n : ℕ) (x : Ordinal.{u}) : hval (replicate n x) = ω ^ x * n := by
  rw [hval, cf_replicate, CNF.eval_single]

theorem hval_singleton (x : Ordinal.{u}) : hval {x} = ω ^ x := by
  simpa using hval_replicate 1 x

/-- When every element of `t` is `≤` every element of `s`, `♯` is ordinary `+`. -/
lemma hval_add_of_le {s t : Multiset Ordinal.{u}} (hst : ∀ a ∈ s, ∀ b ∈ t, b ≤ a) :
    hval (s + t) = hval s + hval t := by
  rw [hval, cf_add]
  exact CNF.eval_add _ fun e₁ h₁ e₂ h₂ => hst _ (mem_support_cf.1 h₁) _ (mem_support_cf.1 h₂)

lemma hval_lt {s : Multiset Ordinal.{u}} {x : Ordinal.{u}} (hs : ∀ a ∈ s, a < x) :
    hval s < ω ^ x :=
  CNF.eval_lt (cf_lt s) fun e he => hs e (mem_support_cf.1 he)

lemma decomp (s : Multiset Ordinal.{u}) (x : Ordinal.{u}) :
    s = s.filter (x < ·) + (s.filter (· = x) + s.filter (· < x)) := by
  ext a
  simp only [count_add, count_filter]
  rcases lt_trichotomy x a with h | rfl | h
  · simp [h, h.ne', not_lt.2 h.le]
  · simp
  · simp [h, h.ne, not_lt.2 h.le]

lemma hval_split (s : Multiset Ordinal.{u}) (x : Ordinal.{u}) :
    hval s = hval (s.filter (x < ·)) + (ω ^ x * (count x s : Ordinal)
      + hval (s.filter (· < x))) := by
  conv_lhs => rw [decomp s x]
  rw [hval_add_of_le, hval_add_of_le, Multiset.filter_eq',hval_replicate]
  · intro a ha b hb
    rw [mem_filter] at ha hb
    exact (hb.2.trans_eq ha.2.symm).le
  · intro a ha b hb
    rw [mem_filter] at ha
    rw [mem_add, mem_filter, mem_filter] at hb
    rcases hb with hb | hb
    · exact (hb.2.trans_lt ha.2).le
    · exact (hb.2.trans ha.2).le

/-! ### (2) Jakobs' order is the ordinal order through `h` -/

theorem hval_lt_of_jakobsLT {s t : Multiset Ordinal.{u}} (h : jakobsLT s t) :
    hval s < hval t := by
  obtain ⟨x, hx, hgt⟩ := h
  have hhi : s.filter (x < ·) = t.filter (x < ·) := by
    ext a
    simp only [count_filter]
    split_ifs with ha
    · exact hgt a ha
    · rfl
  rw [hval_split s x, hval_split t x, hhi]
  apply (add_lt_add_iff_left _).2
  calc ω ^ x * (count x s : Ordinal) + hval (s.filter (· < x))
      < ω ^ x * (count x s : Ordinal) + ω ^ x :=
        (add_lt_add_iff_left _).2 (hval_lt fun a ha => (mem_filter.1 ha).2)
    _ = ω ^ x * ((count x s + 1 : ℕ) : Ordinal) := by
        rw [Nat.cast_add, Nat.cast_one, mul_add_one]
    _ ≤ ω ^ x * (count x t : Ordinal) := by
        gcongr
        exact_mod_cast hx
    _ ≤ ω ^ x * (count x t : Ordinal) + hval (t.filter (· < x)) := le_self_add

/-- (2) `s <_J t ↔ h s < h t`. -/
theorem jakobsLT_iff_hval_lt {s t : Multiset Ordinal.{u}} :
    jakobsLT s t ↔ hval s < hval t := by
  refine ⟨hval_lt_of_jakobsLT, fun H => ?_⟩
  by_cases he : s = t
  · subst he; exact absurd H (lt_irrefl _)
  rcases jakobsLT_total he with h | h
  · exact h
  · exact absurd H (not_lt.2 (hval_lt_of_jakobsLT h).le)

theorem hval_injective : Function.Injective (hval : Multiset Ordinal.{u} → Ordinal.{u}) := by
  intro s t hst
  by_contra he
  rcases jakobsLT_total he with h | h
  · exact (hval_lt_of_jakobsLT h).ne hst
  · exact (hval_lt_of_jakobsLT h).ne hst.symm

/-! ### (3) Image of `N(Λ)` -/

lemma exists_cf (f : Ordinal.{u} →₀ Ordinal.{u}) (hf : ∀ e, f e < ω) : ∃ s, cf s = f := by
  induction f using Finsupp.induction with
  | zero => exact ⟨0, cf_zero⟩
  | single_add a b f ha hb ih =>
    have hfa : f a = 0 := Finsupp.notMem_support_iff.1 ha
    obtain ⟨s, hs⟩ := ih fun e => by
      by_cases he : e = a
      · subst he; rw [hfa]; exact omega0_pos
      · have := hf e
        rwa [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm he), zero_add] at this
    obtain ⟨n, hn⟩ := lt_omega0.1 (by simpa [hfa] using hf a)
    exact ⟨replicate n a + s, by rw [cf_add, cf_replicate, hs, hn]⟩

/-- (3) `{h s | all x ∈ s are ≤ Λ} = [0, ω ^ (Λ + 1))`. -/
theorem image_hval (Λ : Ordinal.{u}) :
    {β | ∃ s : Multiset Ordinal.{u}, (∀ x ∈ s, x ≤ Λ) ∧ hval s = β} = Set.Iio (ω ^ (Λ + 1)) := by
  ext β
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact hval_lt fun a ha => Order.lt_add_one_iff.2 (hs a ha)
  · intro hβ
    obtain ⟨s, hs⟩ := exists_cf (CNF.coeff ω β) (coeff_omega0_lt β)
    refine ⟨s, fun x hx => ?_, by rw [hval, hs, CNF.eval_coeff]⟩
    have hx' : x ∈ (CNF.coeff ω β).support := by rw [← hs]; exact mem_support_cf.2 hx
    rw [CNF.support_coeff, List.mem_toFinset, List.mem_map] at hx'
    obtain ⟨p, hp, rfl⟩ := hx'
    have hβ0 : β ≠ 0 := by rintro rfl; simp [CNF.zero_right] at hp
    have h2 := (lt_opow_iff_log_lt one_lt_omega0 hβ0).1 hβ
    exact Order.lt_add_one_iff.1 ((CNF.fst_le_log hp).trans_lt h2)

/-- (2)+(3) packaged: `N(Λ)` with Jakobs' order is order-isomorphic to `ω ^ (Λ + 1)`. -/
theorem exists_equiv_jakobs (Λ : Ordinal.{u}) :
    ∃ e : {s : Multiset Ordinal.{u} // ∀ x ∈ s, x ≤ Λ} ≃ Set.Iio (ω ^ (Λ + 1)),
      ∀ s t, jakobsLT s.1 t.1 ↔ (e s : Ordinal.{u}) < e t := by
  have hmem : ∀ s : {s : Multiset Ordinal.{u} // ∀ x ∈ s, x ≤ Λ},
      hval s.1 ∈ Set.Iio (ω ^ (Λ + 1)) := fun s => by
    rw [← image_hval]; exact ⟨s.1, s.2, rfl⟩
  refine ⟨Equiv.ofBijective (fun s => ⟨hval s.1, hmem s⟩) ⟨fun s t hst => ?_, fun β => ?_⟩,
    fun s t => jakobsLT_iff_hval_lt⟩
  · exact Subtype.ext (hval_injective (congrArg Subtype.val hst))
  · have hβ : (β : Ordinal.{u}) ∈ {β | ∃ s : Multiset Ordinal.{u}, (∀ x ∈ s, x ≤ Λ) ∧
        hval s = β} := (image_hval Λ).symm ▸ β.2
    obtain ⟨s, hs, hsβ⟩ := hβ
    exact ⟨⟨s, hs⟩, Subtype.ext hsβ⟩

/-- Corollary: for `Λ < ε₀`, the order type `ω ^ (Λ + 1)` of `N(Λ)` stays below `ε₀`. -/
theorem omega0_opow_add_one_lt_epsilon_zero {Λ : Ordinal.{u}} (h : Λ < ε₀) :
    ω ^ (Λ + 1) < ε₀ := by
  obtain ⟨n, hn⟩ := lt_epsilon_zero.1 h
  calc ω ^ (Λ + 1) ≤ ω ^ ((fun a => ω ^ a)^[n] 0) :=
        opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hn)
    _ = (fun a => ω ^ a)^[n + 1] 0 := by rw [Function.iterate_succ_apply']
    _ < ε₀ := iterate_omega0_opow_lt_epsilon_zero _

end

end DGH

#print axioms DGH.hval_add
#print axioms DGH.jakobsLT_iff_hval_lt
#print axioms DGH.hval_injective
#print axioms DGH.image_hval
#print axioms DGH.exists_equiv_jakobs
#print axioms DGH.omega0_opow_add_one_lt_epsilon_zero
#print axioms DGH.nadd_assoc
