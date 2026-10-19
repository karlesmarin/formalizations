/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Tactic.Ring

/-!
# Weight moments of two `13`-dimensional `USp(4)` contents

Finite weight and coefficient certificates, checked by `decide`, for two contents of dimension
`13` written with the weights of the `USp(4)` representations `1`, `4`, `5`: the original
`5 + 4 + 4` and the alternative `1 + 1 + 1 + 5 + 5`. Their weight moments agree up to degree
three and first differ in degree four. The `USp(4)` interpretation of the weight lists is an
input, not a formalized classification; no anomaly cancellation or continuum spectrum is stated.

## Main results

* `same_degree_zero` … `same_degree_three`: the moment polynomials agree in degrees `0`–`3`.
* `degree_four_difference`: in degree four they differ by `(0, 0, 24, 0, 0)`.
* `character_factor_coefficients`: the difference of multiplicities factors as
  `z(w₁) z(w₂)` with `z = (−1, 2, −1)` on `{−1, 0, 1}`.
* `fourth_moment_resolves_kernel`: dimension, second and fourth moments determine the
  multiplicities `(a, b, c)` of `(1, 5, 4)`.
* `two_nonnegative_solutions`: the only nonnegative contents with dimension `13` and second
  moment `8` are `(0, 1, 2)` and `(3, 2, 0)`.
-/

@[expose] public section

namespace GaugeHiggsUnification.USp4WeightMoments

/-- A weight of rank two. -/
abbrev Weight := Int × Int

/-- The weights of the trivial representation. -/
def one : List Weight := [(0,0)]

/-- The weights of the `5`. -/
def five : List Weight := [(0,0),(1,1),(1,-1),(-1,1),(-1,-1)]

/-- The weights of the `4`. -/
def four : List Weight := [(1,0),(-1,0),(0,1),(0,-1)]

/-- The original content `5 + 4 + 4`. -/
def original : List Weight := five ++ four ++ four

/-- The alternative content `1 + 1 + 1 + 5 + 5`. -/
def alternative : List Weight := one ++ one ++ one ++ five ++ five

/-- The mixed moment `Σ w₁^p w₂^q`. -/
def mixed (ws : List Weight) (p q : Nat) : Int :=
  (ws.map fun w => w.1 ^ p * w.2 ^ q).foldl (· + ·) 0

/-- Binomial coefficients by Pascal's recursion. -/
def binomial : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _+1 => 0
  | _+1, 0 => 1
  | n+1, k+1 => binomial n k + binomial n (k+1)

/-- The coefficients of the moment polynomial `Σ (x w₁ + y w₂)^degree`. -/
def coefficients (ws : List Weight) (degree : Nat) : List Int :=
  (List.range (degree+1)).map fun p =>
    (binomial degree p : Int) * mixed ws p (degree-p)

/-- The multiplicity of a weight in a list. -/
def multiplicity (ws : List Weight) (w : Weight) : Int :=
  ((ws.filter (· == w)).length : Int)

/-- The difference of multiplicities, alternative minus original. -/
def delta (w : Weight) : Int := multiplicity alternative w - multiplicity original w

/-- The one-variable factor `(−1, 2, −1)` on `{−1, 0, 1}`. -/
def zcoeff (n : Int) : Int := if n == 0 then 2 else if n == 1 || n == -1 then -1 else 0

/-- The grid `{−1, 0, 1}²`. -/
def grid : List Weight := [-1,0,1].flatMap fun x => [-1,0,1].map fun y => (x,y)

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Both contents have dimension `13`. -/
theorem dimensions : original.length = 13 ∧ alternative.length = 13 := by decide

/-- Equal moments in degree `0`. -/
theorem same_degree_zero : coefficients original 0 = coefficients alternative 0 := by decide

/-- Equal moments in degree `1`. -/
theorem same_degree_one : coefficients original 1 = coefficients alternative 1 := by decide

/-- Equal moments in degree `2`. -/
theorem same_degree_two : coefficients original 2 = coefficients alternative 2 := by decide

/-- Equal moments in degree `3`. -/
theorem same_degree_three : coefficients original 3 = coefficients alternative 3 := by decide

/-- In degree `4` the moments differ by `(0, 0, 24, 0, 0)`. -/
theorem degree_four_difference :
    (List.range 5).map (fun i => (coefficients alternative 4)[i]! - (coefficients original 4)[i]!)
    = [0,0,24,0,0] := by decide

/-- The difference of multiplicities factors on the grid. -/
theorem character_factor_coefficients :
    grid.map delta = grid.map (fun w => zcoeff w.1 * zcoeff w.2) := by decide

/-- All weights of both contents lie on the grid. -/
theorem character_support :
    (original ++ alternative).all (fun w => grid.contains w) = true := by decide

/-- The two contents are different. -/
theorem representations_differ : delta (1,1) = 1 := by decide

/-- The common kernel of dimension and second moment. -/
theorem observation_kernel (a b c : Int)
    (h0 : a + 5*b + 4*c = 0) (h2 : 4*b + 2*c = 0) :
    a = 3*b ∧ c = -2*b := by omega

/-- Adding the fourth moment, the kernel is trivial. -/
theorem fourth_moment_resolves_kernel (a b c : Int)
    (h0 : a + 5*b + 4*c = 0) (h2 : 4*b + 2*c = 0)
    (h4 : 24*b = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by omega

/-- The augmented determinant. -/
theorem augmented_determinant : (1 : Int)*(4*0-2*24) = -48 := by decide

/-- The two nonnegative solutions with dimension `13` and second moment `8`. -/
theorem two_nonnegative_solutions (a b c : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h0 : a+5*b+4*c=13) (h2 : 4*b+2*c=8) :
    (a=0 ∧ b=1 ∧ c=2) ∨ (a=3 ∧ b=2 ∧ c=0) := by omega

/-- The pairing capacities of the alternative content. -/
theorem alternative_pairing_capacity :
    (min (2 : Nat) 0 = 0) ∧ (min (1 : Nat) 2 = 1) ∧ (min (3 : Nat) 3 = 3) := by decide

end GaugeHiggsUnification.USp4WeightMoments
