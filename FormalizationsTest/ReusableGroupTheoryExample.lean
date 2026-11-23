/-
Usage example of the reusable layer, area GroupTheory, with the minimal import of that area: the
same code a user pastes into a file of their own project (README, section "Reusable layer").
-/
import Formalizations.Reusable.GroupTheory

open Formalizations.Reusable

open Classical in
/-- Counting colourings up to symmetry (all weights `1`): `|G| · #orbits` is the sum over `g` of
`|C|` to the number of cycles of `g` on `α`, fixed points included. -/
example {G α C : Type*} [Group G] [Fintype G] [MulAction G α] [Fintype α] [Fintype C] :
    letI := arrowAction (G := G) (A := α) (B := C)
    Fintype.card G * Fintype.card (MulAction.orbitRel.Quotient G (α → C)) =
      ∑ g : G, (Fintype.card C) ^
        (Fintype.card (Function.fixedPoints (MulAction.toPerm g : Equiv.Perm α)) +
          (MulAction.toPerm g : Equiv.Perm α).cycleType.card) := by
  let _ := arrowAction (G := G) (A := α) (B := C)
  have h := polya_redfield_card_mul_sum_orbit_weight (G := G) (α := α) (C := C) (R := ℤ)
    (fun _ => 1)
  simp only [Finset.prod_const_one, Finset.sum_const, Finset.card_univ, one_pow, nsmul_eq_mul,
    mul_one, Multiset.map_const', Multiset.prod_replicate] at h
  rw [← Nat.cast_inj (R := ℤ)]
  push_cast
  rw [h]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [pow_add]

/-- Separation: some permutation of `Fin 4` sends `0` outside `{1}` (`1 · 1 < 4`). -/
example : ∃ g : Equiv.Perm (Fin 4), ∀ a ∈ ({0} : Finset (Fin 4)), g • a ∉ ({1} : Finset (Fin 4)) :=
  separation_lemma_of_pretransitive (Equiv.Perm (Fin 4)) (by simp)

/-- Praeger with `m = 1`: if every point moves and no set of two or more points is moved off itself,
there is at most one orbit. -/
example {G Ω : Type*} [Group G] [MulAction G Ω] (hfix : ∀ x : Ω, ∃ g : G, g • x ≠ x)
    (hmove : ∀ (Γ : Finset Ω) (g : G), (∀ x ∈ Γ, g • x ∉ Γ) → Γ.card ≤ 1) :
    Nat.card (MulAction.orbitRel.Quotient G Ω) ≤ 1 :=
  (praeger_bounded_movement 1 le_rfl hfix hmove).2.1
