/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Formalizations.Physics.Particles.GaugeHiggsUnification.OddEighths

/-!
# Charge channels of `SU(7)` representations and the moment generators

Finite identities, checked by `decide`, for the six-dimensional `SU(7)` gauge-Higgs unification
model. A weight records the Wilson-line charge `q` and two orbifold parities `p`, `b`; the
`7`, `Sym² 7 = 28`, `End 7 = 48 + 1` and `Sym³ 7 = 84` are built as lists of weights, and their
charge channels give the gauge-sector coefficients and the moment generators `(8D, 2A₄)` of the
eight bulk multiplets. This is conditional algebra; the Fourier and interval analysis of the
potential is not formalized.

`eight_generator_moments_eq_matter` identifies the computed generators with the data
`OddEighths.matter`, so the mod-`6` law and the odd-eighths statement of `OddEighths` apply to
them; they are not repeated here.

## Main results

* `symmetric2_dimension`, `symmetric3_dimension`, `adjoint_dimension`: `28`, `84`, `48`.
* `symmetric2_coefficients`, `adjoint_coefficients`, `symmetric3_coefficients`: the charge
  channels.
* `printed_gauge_coefficients`, `background_gauge_coefficients`: the gauge coefficients for
  `4` and `3` periodic degrees of freedom.
* `seed_shift_d8`, `seed_shift_a4`, `seed_shift_w`: in units of `1/4` the two seeds differ by
  `36` in `8D` and `18` in `A₄` (so `Δ(8D) = 9`, `ΔA₄ = 9/2`) and agree in `W`;
  `seed_shift_preserves_law_combination`: they agree in `8D − 2A₄`.
* `quartet_lower_weight_is_required`: the `SU(2)` quartet has weights `±1` and `±3`.
* `eight_generator_moments`, `eight_generator_moments_eq_matter`: the moments `(8D, 2A₄)` of the
  eight bulk multiplets.
* `candidate_seed_even`: with the candidate seed `8D` is even for every content.

## References

* Y. Komori, N. Maru, *`SU(7)` grand gauge-Higgs unification*, arXiv:2503.04090, eq. (68).
-/

@[expose] public section

namespace GaugeHiggsUnification.SU7WeightChannels

/-- A weight: Wilson-line charge `q` and the parities `p`, `b`. -/
structure Weight where
  /-- The Wilson-line charge. -/
  q : Int
  /-- The first parity. -/
  p : Int
  /-- The second parity. -/
  b : Int
deriving DecidableEq, Repr

/-- The weights of the fundamental `7`. -/
def fundamental : List Weight :=
  [⟨0,1,1⟩, ⟨0,1,1⟩, ⟨0,1,1⟩, ⟨0,-1,-1⟩,
   ⟨0,-1,1⟩, ⟨1,-1,-1⟩, ⟨-1,-1,-1⟩]

/-- The weight of a tensor product: charges add, parities multiply. -/
def tensor (a b : Weight) : Weight :=
  ⟨a.q+b.q, a.p*b.p, a.b*b.b⟩

/-- The conjugate weight. -/
def conjugate (a : Weight) : Weight := ⟨-a.q,a.p,a.b⟩

instance : Inhabited Weight := ⟨⟨0,1,1⟩⟩

/-- The `i`-th weight of the fundamental. -/
def w (i : Nat) : Weight := fundamental[i]!

/-- The weights of `Sym² 7`. -/
def symmetric2 : List Weight :=
  (List.range 7).flatMap fun i =>
    ((List.range 7).filter fun j => i ≤ j).map fun j => tensor (w i) (w j)

/-- The weights of `Sym³ 7`. -/
def symmetric3 : List Weight :=
  (List.range 7).flatMap fun i =>
    (List.range 7).flatMap fun j =>
      ((List.range 7).filter fun k => i ≤ j && j ≤ k).map fun k =>
        tensor (tensor (w i) (w j)) (w k)

/-- The weights of `End 7` (dimension `49`). Removing its neutral singlet gives the adjoint; the
singlet contributes to none of the nonzero-charge counts below. -/
def endomorphisms : List Weight :=
  fundamental.flatMap fun a => fundamental.map fun b => tensor a (conjugate b)

/-- The number of weights of charge `q` and parity `b`. -/
def channel (rep : List Weight) (q b : Int) : Nat :=
  (rep.filter fun a => a.q == q && a.b == b).length

/-- The number of weights of `End 7` of charge `q` and parities `p`, `b`. -/
def parityChannel (q p b : Int) : Nat :=
  (endomorphisms.filter fun a => a.q == q && a.p == p && a.b == b).length

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The fundamental has dimension `7`. -/
theorem fundamental_dimension : fundamental.length = 7 := by decide

/-- `Sym² 7` has dimension `28`. -/
theorem symmetric2_dimension : symmetric2.length = 28 := by decide

/-- `Sym³ 7` has dimension `84`. -/
theorem symmetric3_dimension : symmetric3.length = 84 := by decide

/-- The adjoint has dimension `48`. -/
theorem adjoint_dimension : endomorphisms.length - 1 = 48 := by decide

/-- The charge channels of the fundamental. -/
theorem fundamental_coefficients :
    channel fundamental 1 (-1) = 1 ∧ channel fundamental 1 1 = 0 := by decide

/-- The charge channels of `Sym² 7`. -/
theorem symmetric2_coefficients :
    channel symmetric2 2 1 = 1 ∧ channel symmetric2 2 (-1) = 0 ∧
    channel symmetric2 1 1 = 1 ∧ channel symmetric2 1 (-1) = 4 := by decide

/-- The charge channels of the adjoint. -/
theorem adjoint_coefficients :
    channel endomorphisms 2 1 = 1 ∧ channel endomorphisms 2 (-1) = 0 ∧
    channel endomorphisms 1 1 = 2 ∧ channel endomorphisms 1 (-1) = 8 := by decide

/-- The charge channels of `Sym³ 7`. -/
theorem symmetric3_coefficients :
    channel symmetric3 3 (-1) = 1 ∧ channel symmetric3 3 1 = 0 ∧
    channel symmetric3 2 (-1) = 1 ∧ channel symmetric3 2 1 = 4 ∧
    channel symmetric3 1 (-1) = 12 ∧ channel symmetric3 1 1 = 4 := by decide

/-- The adjoint channels resolved by both parities. -/
theorem adjoint_parity_resolution :
    parityChannel 2 1 1 = 1 ∧ parityChannel 1 1 1 = 2 ∧
    parityChannel 1 1 (-1) = 2 ∧ parityChannel 1 (-1) (-1) = 6 ∧
    parityChannel 2 (-1) 1 = 0 ∧ parityChannel 1 (-1) 1 = 0 := by decide

/-- The gauge-sector coefficient of charge `q` and parity `b`, with `periodicDof` periodic
degrees of freedom. -/
def gaugeFourM (periodicDof q b : Int) : Int :=
  -periodicDof * (parityChannel q 1 b : Int) - (parityChannel q (-1) b : Int)

/-- The gauge coefficients with `4` periodic degrees of freedom (the printed seed). -/
theorem printed_gauge_coefficients :
    gaugeFourM 4 2 1 = -4 ∧ gaugeFourM 4 1 1 = -8 ∧
    gaugeFourM 4 1 (-1) = -14 := by decide

/-- The gauge coefficients with `3` periodic degrees of freedom (the candidate seed). -/
theorem background_gauge_coefficients :
    gaugeFourM 3 2 1 = -3 ∧ gaugeFourM 3 1 1 = -6 ∧
    gaugeFourM 3 1 (-1) = -12 := by decide

/-- Four times the gauge contribution to `8D`. -/
def d8Four (n : Int) : Int :=
  32*gaugeFourM n 2 1 + 8*gaugeFourM n 1 1 - 6*gaugeFourM n 1 (-1)

/-- Four times the gauge contribution to `A₄`. -/
def a4Four (n : Int) : Int := 16*gaugeFourM n 2 1 + gaugeFourM n 1 1

/-- Four times the gauge contribution to `W`. -/
def wFour (n : Int) : Int := -gaugeFourM n 1 1 + gaugeFourM n 1 (-1)

/-- The seeds differ by `36 / 4 = 9` in `8D`. -/
theorem seed_shift_d8 : d8Four 3 - d8Four 4 = 36 := by decide

/-- The seeds differ by `18 / 4 = 9/2` in `A₄`. -/
theorem seed_shift_a4 : a4Four 3 - a4Four 4 = 18 := by decide

/-- The seeds agree in `W`. -/
theorem seed_shift_w : wFour 3 = wFour 4 := by decide

/-- The seeds agree in `8D − 2A₄`. -/
theorem seed_shift_preserves_law_combination :
    (d8Four 3-2*a4Four 3) = (d8Four 4-2*a4Four 4) := by decide

/-- The weights of the `SU(2)` doublet. -/
def doublet : List Weight := [⟨1,-1,-1⟩, ⟨-1,-1,-1⟩]

/-- The weights of the `SU(2)` quartet `Sym³ 2`. -/
def quartet : List Weight :=
  (List.range 2).flatMap fun i => (List.range 2).flatMap fun j =>
    ((List.range 2).filter fun k => i ≤ j && j ≤ k).map fun k =>
      tensor (tensor doublet[i]! doublet[j]!) doublet[k]!

/-- The quartet has weights of charge `1` and `3`, each once: its lower weight cannot be
discarded. -/
theorem quartet_lower_weight_is_required :
    channel quartet 1 (-1) = 1 ∧ channel quartet 3 (-1) = 1 := by decide

/-- The same matter content preserves the shift in `8D`. -/
theorem same_matter_preserves_d8_shift (matter : Int) :
    (d8Four 3 + matter) - (d8Four 4 + matter) = 36 := by
  have h := seed_shift_d8
  omega

/-- The same matter content preserves the shift in `A₄`. -/
theorem same_matter_preserves_a4_shift (matter : Int) :
    (a4Four 3 + matter) - (a4Four 4 + matter) = 18 := by
  have h := seed_shift_a4
  omega

/-- The same matter content preserves `W`. -/
theorem same_matter_preserves_w (matter : Int) :
    wFour 3 + matter = wFour 4 + matter := by
  rw [seed_shift_w]

/-- The Dirac chirality trace cancels the parity. -/
theorem dirac_chirality_trace_cancels_parity (z : Int) :
    2*(1+z) + 2*(1+z) + 2*(1-z) + 2*(1-z) = 8 := by omega

/-- The moment `8D` of a representation with parity `eta`. -/
def representationD8 (rep : List Weight) (eta : Int) : Int :=
  (rep.filter fun a => a.q > 0).foldl
    (fun total a => total + (if eta*a.b == 1 then 8 else -6)*a.q^2) 0

/-- The moment `2A₄` of a representation with parity `eta`. -/
def representation2A4 (rep : List Weight) (eta : Int) : Int :=
  (rep.filter fun a => a.q > 0).foldl
    (fun total a => total + (if eta*a.b == 1 then 2*a.q^4 else 0)) 0

/-- The pair `(8D, 2A₄)`. -/
def representationMoments (rep : List Weight) (eta : Int) : Int × Int :=
  (representationD8 rep eta, representation2A4 rep eta)

/-- The moments `(8D, 2A₄)` of the eight bulk multiplets. -/
theorem eight_generator_moments :
    [representationMoments fundamental 1, representationMoments fundamental (-1),
     representationMoments symmetric2 1, representationMoments symmetric2 (-1),
     representationMoments endomorphisms 1, representationMoments endomorphisms (-1),
     representationMoments symmetric3 1, representationMoments symmetric3 (-1)] =
    [(-6,0),(8,2),(16,34),(2,8),(0,36),(28,16),(10,136),(80,218)] := by decide

/-- The computed moments are the data `OddEighths.matter` (coordinates `(2A₄, 8D, 2W)`). -/
theorem eight_generator_moments_eq_matter :
    [representationMoments fundamental 1, representationMoments fundamental (-1),
     representationMoments symmetric2 1, representationMoments symmetric2 (-1),
     representationMoments endomorphisms 1, representationMoments endomorphisms (-1),
     representationMoments symmetric3 1, representationMoments symmetric3 (-1)] =
    OddEighths.matter.map (fun v => (v.2.1, v.1)) := by
  rw [eight_generator_moments]
  decide

/-- The moment `8D` of a content with integer multiplicities. -/
def bulkD8 (a b c d e f g h : Int) : Int :=
  -6*a+8*b+16*c+2*d+0*e+28*f+10*g+80*h

/-- With the candidate seed (`8D = −18`), `8D` is even for every content. -/
theorem candidate_seed_even (a b c d e f g h : Int) :
    (-18 + bulkD8 a b c d e f g h) % 2 = 0 := by
  unfold bulkD8
  omega

end GaugeHiggsUnification.SU7WeightChannels
