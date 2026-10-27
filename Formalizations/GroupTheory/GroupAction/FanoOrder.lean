/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.GroupTheory.GroupAction.DistinguishingNumber
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# The order of the Fano collineation group

The collineation group `TotD.fanoGroup` of the Fano plane (the stabilizer of its seven lines in
`Equiv.Perm (Fin 7)`) has order `168`. The map `g ↦ (g 0, g 1, g 3)` is a bijection onto the triples
of non-collinear points. It is injective because a collineation fixing three non-collinear points
fixes every point (each remaining point is the third point of a line through two fixed ones). It is
surjective because, reading the points as the nonzero vectors of `F₂³`, the linear map sending
`e₁, e₂, e₃` to a given triple maps lines to lines; this is checked by `decide` over the 168
triples, never over all of `Equiv.Perm (Fin 7)`.

## Main results

* `TotD.fanoGroup_card`: Nat.card fanoGroup = 168

## References

* C. Marín, *When Separation Fails, a Canon Appears: One counting identity behind separation,
  synchronization, and symmetry-breaking in permutation groups, formalized in Lean 4 (Part I)*,
  Zenodo (2026), doi:10.5281/zenodo.21419285, `fano-order`.
-/

@[expose] public section

set_option maxRecDepth 10000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 200000

open MulAction Pointwise

namespace TotD

/-- Triples `(a,b,c)` of distinct points with `c` not on the line `ab` (point `i` is the vector `i+1`). -/
private def Tset : Finset (Fin 7 × Fin 7 × Fin 7) :=
  Finset.univ.filter fun t =>
    t.1 ≠ t.2.1 ∧ t.2.2 ≠ t.1 ∧ t.2.2 ≠ t.2.1 ∧ (t.1.val + 1) ^^^ (t.2.1.val + 1) ≠ t.2.2.val + 1

private theorem Tset_card : Tset.card = 168 := by decide +kernel

private theorem mem_Tset {t : Fin 7 × Fin 7 × Fin 7} : t ∈ Tset ↔
    (t.1 ≠ t.2.1 ∧ t.2.2 ≠ t.1 ∧ t.2.2 ≠ t.2.1 ∧
      (t.1.val + 1) ^^^ (t.2.1.val + 1) ≠ t.2.2.val + 1) := by
  simp [Tset]

/-- The linear map of `F₂³` sending `e₁,e₂,e₃` (points 0,1,3) to the triple. -/
private def phi (t : Fin 7 × Fin 7 × Fin 7) (i : Fin 7) : Fin 7 :=
  ⟨(((if (i.val + 1) &&& 1 ≠ 0 then t.1.val + 1 else 0) ^^^
     (if (i.val + 1) &&& 2 ≠ 0 then t.2.1.val + 1 else 0) ^^^
     (if (i.val + 1) &&& 4 ≠ 0 then t.2.2.val + 1 else 0)) + 6) % 7, Nat.mod_lt _ (by decide)⟩

private theorem phi_spec : ∀ t ∈ Tset, Function.Injective (phi t) ∧
    fanoLines.image (fun L => L.image (phi t)) = fanoLines ∧
    phi t 0 = t.1 ∧ phi t 1 = t.2.1 ∧ phi t 3 = t.2.2 := by decide +kernel

private theorem line_unique : ∀ L ∈ fanoLines, ∀ M ∈ fanoLines, ∀ x y : Fin 7, x ≠ y →
    x ∈ L → y ∈ L → x ∈ M → y ∈ M → L = M := by decide +kernel

private theorem third : ∀ L ∈ fanoLines, ∀ a b z : Fin 7, a ∈ L → b ∈ L → z ∈ L → a ≠ b →
    z ≠ a → z ≠ b → (a.val + 1) ^^^ (b.val + 1) = z.val + 1 := by decide +kernel

private theorem fill : ∀ L ∈ fanoLines, ∀ x y z w : Fin 7, x ≠ y → x ≠ z → y ≠ z →
    x ∈ L → y ∈ L → z ∈ L → w ∈ L → w ≠ x → w ≠ y → w = z := by decide +kernel

private theorem hline {g : Equiv.Perm (Fin 7)} (hg : g ∈ fanoGroup) (L : Finset (Fin 7))
    (hL : L ∈ fanoLines) : g • L ∈ fanoLines := by
  have hstab : g • fanoLines = fanoLines := MulAction.mem_stabilizer_iff.mp hg
  rw [← hstab]; exact Finset.smul_mem_smul_finset hL

private theorem happ (g : Equiv.Perm (Fin 7)) (L : Finset (Fin 7)) (y : Fin 7) (hy : y ∈ L) :
    g y ∈ g • L := by
  have := Finset.smul_mem_smul_finset (a := g) hy
  rwa [Equiv.Perm.smul_def] at this

private theorem pin {g : Equiv.Perm (Fin 7)} (hg : g ∈ fanoGroup) {L : Finset (Fin 7)}
    (hL : L ∈ fanoLines) {x y z : Fin 7} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : x ∈ L) (hy : y ∈ L) (hz : z ∈ L) (gx : g x = x) (gy : g y = y) : g z = z := by
  have hgL : g • L ∈ fanoLines := hline hg L hL
  have mx : x ∈ g • L := by have h := happ g L x hx; rwa [gx] at h
  have my : y ∈ g • L := by have h := happ g L y hy; rwa [gy] at h
  have heq : g • L = L := line_unique _ hgL L hL x y hxy mx my hx hy
  have mz : g z ∈ L := by have h := happ g L z hz; rwa [heq] at h
  have h1 : g z ≠ x := fun h => hxz (g.injective (h.trans gx.symm)).symm
  have h2 : g z ≠ y := fun h => hyz (g.injective (h.trans gy.symm)).symm
  exact fill L hL x y z (g z) hxy hxz hyz hx hy hz mz h1 h2

private theorem dec7' (y : Fin 7) :
    y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 := by
  revert y; decide

private theorem eq_one_of_fix3 {k : Equiv.Perm (Fin 7)} (hk : k ∈ fanoGroup)
    (h0 : k 0 = 0) (h1 : k 1 = 1) (h3 : k 3 = 3) : k = 1 := by
  have h2 : k 2 = 2 := pin hk (L := {0, 1, 2}) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) h0 h1
  have h4 : k 4 = 4 := pin hk (L := {0, 3, 4}) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) h0 h3
  have h5 : k 5 = 5 := pin hk (L := {1, 3, 5}) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) h1 h3
  have h6 : k 6 = 6 := pin hk (L := {0, 5, 6}) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) h0 h5
  refine Equiv.ext fun x => ?_
  rcases dec7' x with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4, h5, h6]

private theorem eval_mem {p : Equiv.Perm (Fin 7)} (hp : p ∈ fanoGroup) :
    (p 0, p 1, p 3) ∈ Tset := by
  rw [mem_Tset]
  have hL : p • ({0, 1, 2} : Finset (Fin 7)) ∈ fanoLines := hline hp _ (by decide)
  have m0 : p 0 ∈ p • ({0, 1, 2} : Finset (Fin 7)) := happ p _ 0 (by decide)
  have m1 : p 1 ∈ p • ({0, 1, 2} : Finset (Fin 7)) := happ p _ 1 (by decide)
  have m2 : p 2 ∈ p • ({0, 1, 2} : Finset (Fin 7)) := happ p _ 2 (by decide)
  have a01 : p 0 ≠ p 1 := fun h => absurd (p.injective h) (by decide)
  have a20 : p 2 ≠ p 0 := fun h => absurd (p.injective h) (by decide)
  have a21 : p 2 ≠ p 1 := fun h => absurd (p.injective h) (by decide)
  have a30 : p 3 ≠ p 0 := fun h => absurd (p.injective h) (by decide)
  have a31 : p 3 ≠ p 1 := fun h => absurd (p.injective h) (by decide)
  have a32 : p 3 ≠ p 2 := fun h => absurd (p.injective h) (by decide)
  have h3 := third _ hL (p 0) (p 1) (p 2) m0 m1 m2 a01 a20 a21
  refine ⟨a01, a30, a31, fun h => a32 (Fin.ext ?_)⟩
  have := h3.symm.trans h
  simp only at this
  omega

private def evalT (g : fanoGroup) : Tset :=
  ⟨((g : Equiv.Perm (Fin 7)) 0, (g : Equiv.Perm (Fin 7)) 1, (g : Equiv.Perm (Fin 7)) 3),
    eval_mem g.2⟩

private theorem evalT_inj : Function.Injective evalT := by
  intro g h hgh
  have e := congrArg Subtype.val hgh
  simp only [evalT, Prod.mk.injEq] at e
  obtain ⟨e0, e1, e3⟩ := e
  have hk : (g : Equiv.Perm (Fin 7))⁻¹ * h ∈ fanoGroup :=
    fanoGroup.mul_mem (fanoGroup.inv_mem g.2) h.2
  have := eq_one_of_fix3 hk
    (by rw [Equiv.Perm.mul_apply, ← e0]; simp)
    (by rw [Equiv.Perm.mul_apply, ← e1]; simp)
    (by rw [Equiv.Perm.mul_apply, ← e3]; simp)
  exact Subtype.ext (inv_mul_eq_one.mp this)

private theorem evalT_surj : Function.Surjective evalT := by
  rintro ⟨t, ht⟩
  obtain ⟨hinj, himg, p0, p1, p3⟩ := phi_spec t ht
  let g : Equiv.Perm (Fin 7) := Equiv.ofBijective (phi t) (Finite.injective_iff_bijective.mp hinj)
  have hgc : ∀ i, g i = phi t i := fun i => rfl
  have hmem : g ∈ fanoGroup := by
    rw [fanoGroup, MulAction.mem_stabilizer_iff, Finset.smul_finset_def]
    have : (fun L : Finset (Fin 7) => g • L) = fun L => L.image (phi t) := by
      funext L
      rw [Finset.smul_finset_def]
      simp only [Equiv.Perm.smul_def, hgc]
    rw [this]
    exact himg
  refine ⟨⟨g, hmem⟩, Subtype.ext ?_⟩
  simp only [evalT]
  rw [hgc, hgc, hgc, p0, p1, p3]

/-- The collineation group of the Fano plane has order `168`: `g ↦ (g 0, g 1, g 3)` is a bijection
onto the triples of non-collinear points (`7 · 6 · 4`). -/
theorem fanoGroup_card : Nat.card fanoGroup = 168 := by
  have e : fanoGroup ≃ ↥Tset := Equiv.ofBijective evalT ⟨evalT_inj, evalT_surj⟩
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  exact Tset_card

end TotD
