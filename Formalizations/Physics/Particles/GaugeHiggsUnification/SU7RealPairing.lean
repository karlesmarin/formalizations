/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Order.Units

/-!
# Under diagonal `±1` parities the adjoint of `SU(n)` furnishes no chiral state

Orbifold parities `P₅, P₅'` act diagonally on the indices of the fundamental. A component of a
bulk multiplet survives in the multiplet of parities `(η, η')` iff `P₅ P₅' = η η'`, and then
carries `4`D chirality `−η P₅` (Komori–Maru, eqs. (37)–(40)). The component `(i, j̄)` of
`n ⊗ n̄` carries the parity `p i * (p j)⁻¹`; for its conjugate `(j, ī)` this is `p j * (p i)⁻¹`.
When every `p i` squares to `1` the two coincide, so `(i, j̄)` and `(j, ī)` survive together, with
the same chirality and opposite charges: the surviving spectrum of the adjoint is vector-like.

The hypothesis `p i * p i = 1` is exactly what is used: in a general commutative group the
conjugate index carries the inverse parity and the swap no longer preserves it. For the `ℤ₂`
parities of the model (`ℤˣ`-valued) it holds automatically (`Int.units_mul_self`).

The counts of the paper are checked by `decide` on its data
`P₅ = diag(+,+,+,+,+,−,−)`, `P₅' = diag(+,+,+,−,−,−,+)`, with the hypercharge and the extra
`U(1)` per index (in units of `1/2`). Off the Cartan (`42` components, as in the paper's
script), a `48^(+,+)` has `18` survivors and a `48^(+,−)` has `24`, all paired; the complex
controls `28 = Sym² 7` and `84 = Sym³ 7` leave `10` and `34` unpaired states at `(+,+)`.
"Paired" means: another survivor of the same chirality with opposite `(Y, extra)`.

## Main results

* `adjParity_swap`: with parities squaring to `1`, `(i, j̄)` and `(j, ī)` have the same parity.
* `survives_swap`, `chirality_swap`, `charge_swap`: the swap preserves survival and chirality and
  negates every additive charge.
* `adjoint_vectorLike`: every off-diagonal survivor of the adjoint has a distinct partner of the
  same chirality and opposite charges, for any `n`, any `ℤˣ` parities and any `(η, η')`.
* `adjoint_survivors_pp`, `adjoint_survivors_pm`: `18` and `24` survivors on the paper's data;
  `adjoint_unpaired_pp`, `adjoint_unpaired_pm`: none unpaired (derived from `adjoint_vectorLike`).
* `sym2_survivors`, `sym2_unpaired`, `sym3_survivors`, `sym3_unpaired`: the controls,
  `16` survivors with `10` unpaired, and `44` survivors with `34` unpaired.

## References

* C. Marín, *Proton Decay in `SU(7)` Grand Gauge-Higgs Unification: An Obstruction, Its Minimal
  Escapes, and the One Row of Their Table 1 That Can Pay for Them (Part VI)*, Zenodo,
  doi:10.5281/zenodo.22033303, Proposition (a real representation under diagonal `±1` parities
  furnishes no chiral generation).
* Y. Komori, N. Maru, *`SU(7)` grand gauge-Higgs unification*, arXiv:2503.04090, eqs. (37)–(41).
-/

@[expose] public section

namespace GaugeHiggsUnification.SU7RealPairing

section General

variable {G : Type*} [CommGroup G] {n : ℕ}

/-- The parity of the component `(i, j̄)` of `n ⊗ n̄`: the conjugate index carries the inverse. -/
def adjParity (p : Fin n → G) (i j : Fin n) : G := p i * (p j)⁻¹

/-- With parities squaring to `1`, the conjugate component `(j, ī)` has the parity of `(i, j̄)`. -/
theorem adjParity_swap (p : Fin n → G) (hp : ∀ i, p i * p i = 1) (i j : Fin n) :
    adjParity p j i = adjParity p i j := by
  have hinv : ∀ k, (p k)⁻¹ = p k := fun k => inv_eq_of_mul_eq_one_right (hp k)
  simp only [adjParity, hinv, mul_comm]

end General

variable {n : ℕ}

/-- The component `(i, j̄)` survives in the multiplet of parities `(η, η')` iff
`P₅ P₅' = η η'`. -/
def Survives (p5 p5' : Fin n → ℤˣ) (η η' : ℤˣ) (i j : Fin n) : Prop :=
  adjParity p5 i j * adjParity p5' i j = η * η'

/-- The `4`D chirality `−η P₅` of the component `(i, j̄)`. -/
def chirality (p5 : Fin n → ℤˣ) (η : ℤˣ) (i j : Fin n) : ℤˣ :=
  -(η * adjParity p5 i j)

/-- The additive charge `Q i − Q j` of the component `(i, j̄)`. -/
def charge {A : Type*} [AddCommGroup A] (Q : Fin n → A) (i j : Fin n) : A := Q i - Q j

theorem survives_swap (p5 p5' : Fin n → ℤˣ) (η η' : ℤˣ) (i j : Fin n) :
    Survives p5 p5' η η' j i ↔ Survives p5 p5' η η' i j := by
  simp only [Survives, adjParity_swap p5 fun _ => Int.units_mul_self _,
    adjParity_swap p5' fun _ => Int.units_mul_self _]

theorem chirality_swap (p5 : Fin n → ℤˣ) (η : ℤˣ) (i j : Fin n) :
    chirality p5 η j i = chirality p5 η i j := by
  simp only [chirality, adjParity_swap p5 fun _ => Int.units_mul_self _]

theorem charge_swap {A : Type*} [AddCommGroup A] (Q : Fin n → A) (i j : Fin n) :
    charge Q j i = -charge Q i j := by
  simp only [charge, neg_sub]

/-- **The adjoint is vector-like.** Every off-diagonal survivor `(i, j̄)` has a distinct partner
`(j, ī)` that survives, with the same chirality and opposite values of any two additive
charges. -/
theorem adjoint_vectorLike {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (p5 p5' : Fin n → ℤˣ) (η η' : ℤˣ) (Y : Fin n → A) (E : Fin n → B) (i j : Fin n)
    (hij : i ≠ j) (hs : Survives p5 p5' η η' i j) :
    (j, i) ≠ (i, j) ∧ Survives p5 p5' η η' j i ∧ chirality p5 η j i = chirality p5 η i j ∧
      charge Y j i = -charge Y i j ∧ charge E j i = -charge E i j :=
  ⟨fun h => hij (Prod.ext_iff.1 h).2, (survives_swap p5 p5' η η' i j).2 hs,
    chirality_swap p5 η i j, charge_swap Y i j, charge_swap E i j⟩

/-! ### The paper's data -/

/-- `P₅ = diag(+,+,+,+,+,−,−)`. -/
def P5 : Fin 7 → ℤˣ := ![1, 1, 1, 1, 1, -1, -1]

/-- `P₅' = diag(+,+,+,−,−,−,+)`. -/
def P5' : Fin 7 → ℤˣ := ![1, 1, 1, -1, -1, -1, 1]

/-- Twice the hypercharge per index: `Y = (0,0,0,½,½,−1,0)`. -/
def Y2 : Fin 7 → ℤ := ![0, 0, 0, 1, 1, -2, 0]

/-- Twice the extra `U(1)` charge per index: `extra = (0,0,0,0,0,½,−½)`. -/
def E2 : Fin 7 → ℤ := ![0, 0, 0, 0, 0, 1, -1]

/-- The quantum numbers of a component: `P₅`, `P₅'`, `2Y`, `2·extra`. -/
structure QN where
  /-- The parity `P₅`. -/
  p5 : ℤˣ
  /-- The parity `P₅'`. -/
  p5' : ℤˣ
  /-- Twice the hypercharge. -/
  y : ℤ
  /-- Twice the extra charge. -/
  e : ℤ

/-- Survivors of a list of components in the multiplet of parities `(η, η')`. -/
def survivors {α : Type*} (comps : Finset α) (qn : α → QN) (η η' : ℤˣ) : Finset α :=
  comps.filter fun c => (qn c).p5 * (qn c).p5' = η * η'

/-- A survivor is paired if another survivor has the same chirality and opposite `(Y, extra)`. -/
def Paired {α : Type*} (S : Finset α) (qn : α → QN) (η : ℤˣ) (c : α) : Prop :=
  ∃ d ∈ S, d ≠ c ∧ -(η * (qn d).p5) = -(η * (qn c).p5) ∧ (qn d).y = -(qn c).y ∧
    (qn d).e = -(qn c).e

instance {α : Type*} [DecidableEq α] (S : Finset α) (qn : α → QN) (η : ℤˣ) :
    DecidablePred (Paired S qn η) := fun _ => by unfold Paired; infer_instance

/-- The number of unpaired (chiral) survivors. -/
def unpaired {α : Type*} [DecidableEq α] (comps : Finset α) (qn : α → QN) (η η' : ℤˣ) : ℕ :=
  ((survivors comps qn η η').filter fun c => ¬ Paired (survivors comps qn η η') qn η c).card

/-- The off-diagonal components `(i, j̄)`, `i ≠ j`, of the adjoint (the Cartan left aside). -/
def adjComps : Finset (Fin 7 × Fin 7) := Finset.univ.filter fun c => c.1 ≠ c.2

/-- Quantum numbers of `(i, j̄)`. -/
def qnAdj (c : Fin 7 × Fin 7) : QN :=
  ⟨adjParity P5 c.1 c.2, adjParity P5' c.1 c.2, charge Y2 c.1 c.2, charge E2 c.1 c.2⟩

/-- The components `i ≤ j` of `Sym² 7`. -/
def sym2Comps : Finset (Fin 7 × Fin 7) := Finset.univ.filter fun c => c.1 ≤ c.2

/-- Quantum numbers of a component of `Sym² 7`. -/
def qnSym2 (c : Fin 7 × Fin 7) : QN :=
  ⟨P5 c.1 * P5 c.2, P5' c.1 * P5' c.2, Y2 c.1 + Y2 c.2, E2 c.1 + E2 c.2⟩

/-- The components `i ≤ j ≤ k` of `Sym³ 7`. -/
def sym3Comps : Finset (Fin 7 × Fin 7 × Fin 7) :=
  Finset.univ.filter fun c => c.1 ≤ c.2.1 ∧ c.2.1 ≤ c.2.2

/-- Quantum numbers of a component of `Sym³ 7`. -/
def qnSym3 (c : Fin 7 × Fin 7 × Fin 7) : QN :=
  ⟨P5 c.1 * P5 c.2.1 * P5 c.2.2, P5' c.1 * P5' c.2.1 * P5' c.2.2,
    Y2 c.1 + Y2 c.2.1 + Y2 c.2.2, E2 c.1 + E2 c.2.1 + E2 c.2.2⟩

theorem adjComps_card : adjComps.card = 42 := by decide

theorem sym2Comps_card : sym2Comps.card = 28 := by decide

theorem sym3Comps_card : sym3Comps.card = 84 := by decide

theorem adjoint_survivors_pp : (survivors adjComps qnAdj 1 1).card = 18 := by decide

theorem adjoint_survivors_pm : (survivors adjComps qnAdj 1 (-1)).card = 24 := by decide

/-- On the paper's data, no off-diagonal survivor of the adjoint is unpaired, at any `(η, η')`;
derived from `adjoint_vectorLike`, not by enumeration. -/
theorem adjoint_unpaired_eq_zero (η η' : ℤˣ) : unpaired adjComps qnAdj η η' = 0 := by
  unfold unpaired
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨i, j⟩ hc
  have hc' := hc
  simp only [survivors, adjComps, Finset.mem_filter, Finset.mem_univ, true_and] at hc'
  obtain ⟨hij, hs⟩ := hc'
  obtain ⟨hne, hs', hch, hy, he⟩ :=
    adjoint_vectorLike P5 P5' η η' Y2 E2 i j hij (by simpa [Survives, qnAdj] using hs)
  refine not_not.2 ⟨(j, i), ?_, hne, ?_, hy, he⟩
  · simp only [survivors, adjComps, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Ne.symm hij, by simpa [Survives, qnAdj] using hs'⟩
  · simpa [chirality, qnAdj] using hch

theorem adjoint_unpaired_pp : unpaired adjComps qnAdj 1 1 = 0 := adjoint_unpaired_eq_zero 1 1

theorem adjoint_unpaired_pm : unpaired adjComps qnAdj 1 (-1) = 0 :=
  adjoint_unpaired_eq_zero 1 (-1)

/-- Control: `Sym² 7` at `(+,+)` has `16` survivors. -/
theorem sym2_survivors : (survivors sym2Comps qnSym2 1 1).card = 16 := by decide

/-- Control: `Sym² 7` at `(+,+)` leaves `10` unpaired (chiral) states. -/
theorem sym2_unpaired : unpaired sym2Comps qnSym2 1 1 = 10 := by decide

/-- Control: `Sym³ 7` at `(+,+)` has `44` survivors. -/
theorem sym3_survivors : (survivors sym3Comps qnSym3 1 1).card = 44 := by decide

/-- Control: `Sym³ 7` at `(+,+)` leaves `34` unpaired (chiral) states. -/
theorem sym3_unpaired : unpaired sym3Comps qnSym3 1 1 = 34 := by decide

end GaugeHiggsUnification.SU7RealPairing
