/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# Runge–Kutta order conditions over rooted trees

A Runge–Kutta method with tableau `(A, b)` has order `p` when the elementary weight `Φ(t)(A, b)`
equals `1/γ(t)` for every rooted tree `t` with at most `p` nodes, where `γ` is the density
(Butcher). This file builds a computable engine over planar rooted trees (order `|t|`, density
`γ(t)`, elementary weight `Φ(t)(A, b)`), states the order conditions in the division-free form
`γ(t) · Φ(t) = 1`, reduces "order `p`" to a finite catalogue check, and certifies concrete methods.

## Main results

* `Butcher.satisfiesOrderConditions_iff`: "order `p`" holds iff the condition holds on the finite
  catalogue of trees with at most `p` nodes (sound and complete).
* `Butcher.euler_ord1`, `Butcher.heun_ord2`, `Butcher.heun_not_ord3`: Euler has order 1, Heun
  order 2 and not 3.
* `Butcher.rk4_order4`, `Butcher.rk4_not_ord5`: the classical RK4 has order 4 and not 5.
* `Butcher.dp_order5`: Dormand–Prince (DOPRI5) has order 5.
* `Butcher.gauss_order4`: Gauss–Legendre with 3 stages has order 4, coefficients in `ℚ(√15)`.
* `Butcher.gauss_order6`: the Gauss–Legendre tableau with 3 stages, cleared of denominators by
  `D = 360` into `ℤ[√15]`, satisfies `γ(t) · Φ(D·A, D·b, t) = D^{|t|}` for every tree with at most
  6 nodes (by `decide`). The equivalence with the unscaled conditions (homogeneity of `Φ`) is not
  formalized.
* `Butcher.orderCond_node_perm`: `Φ` and `γ` are invariant under permuting a node's children, so
  the conditions on planar trees subsume those on abstract trees.

## Implementation notes

Only the algebraic order conditions are certified, not Butcher's theorem that they are equivalent
to a local error `O(h^{p+1})`. Trees are planar (ordered children), with their own inductive type
`Butcher.RTree`, of the same shape as `ConnesKreimer.RTree`; Mathlib's order-theoretic `RootedTree`
is not used (see `Formalizations.RingTheory.HopfAlgebra.ConnesKreimer.Coproduct`).
`Butcher.Q15` and `Butcher.Z15` are computable models of `ℚ(√15)` and `ℤ[√15]` as pairs. Mathlib
has `Zsqrtd 15` and `QuadraticAlgebra`; the concrete pairs are kept because the certificates
unfold them with `simp` and `decide`. Over `ℚ` the kernel cannot reduce the `Nat.gcd` inside
`Rat` normalization, so the `ℚ` conditions are closed by `norm_num` and the order-6 certificate
works over integers.

## References

* J. C. Butcher, *Coefficients for the study of Runge–Kutta integration processes*,
  J. Austral. Math. Soc. 3 (1963) 185–201.
* E. Hairer, C. Lubich, G. Wanner, *Geometric Numerical Integration*, Springer (2006).
* L. Foissy, *Les algèbres de Hopf des arbres enracinés décorés, I*, Bull. Sci. Math. 126 (2002)
  193–239.
* C. Marín, *What Order a Method Knows: certified Runge–Kutta order conditions over rooted trees,
  machine-checked in Lean 4* (2026), doi:10.5281/zenodo.20787666. Ported from `ButcherOrder.lean`
  of [karlesmarin/runge-kutta-order-conditions-lean](https://github.com/karlesmarin/runge-kutta-order-conditions-lean)
  (Lean v4.30.0-rc2).
-/

@[expose] public section

namespace Butcher

/-- ℚ(√15) as a computable `CommRing`: `⟨a, b⟩` means `a + b·√15`; the relation √15²=15 is baked
    into `mul`.  Coefficient ring for the Gauss–Legendre s=3 tableau (`gauss_order4`).  Working in
    this concrete pair ring keeps the order-condition checks a pure ℚ component computation closed by
    `norm_num` — no algebraic-number tactic needed. -/
structure Q15 where
  re : ℚ
  im : ℚ
deriving DecidableEq, Repr

namespace Q15
@[ext] theorem ext' {x y : Q15} (hr : x.re = y.re) (hi : x.im = y.im) : x = y := by
  cases x; cases y; simp_all
instance : Zero Q15 := ⟨0, 0⟩
instance : One Q15  := ⟨1, 0⟩
instance : Add Q15  := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance : Neg Q15  := ⟨fun x => ⟨-x.re, -x.im⟩⟩
instance : Sub Q15  := ⟨fun x y => ⟨x.re - y.re, x.im - y.im⟩⟩
instance : Mul Q15  := ⟨fun x y => ⟨x.re * y.re + 15 * x.im * y.im, x.re * y.im + x.im * y.re⟩⟩
@[simp] theorem zero_re : (0 : Q15).re = 0 := rfl
@[simp] theorem zero_im : (0 : Q15).im = 0 := rfl
@[simp] theorem one_re : (1 : Q15).re = 1 := rfl
@[simp] theorem one_im : (1 : Q15).im = 0 := rfl
@[simp] theorem add_re (x y : Q15) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_im (x y : Q15) : (x + y).im = x.im + y.im := rfl
@[simp] theorem neg_re (x : Q15) : (-x).re = -x.re := rfl
@[simp] theorem neg_im (x : Q15) : (-x).im = -x.im := rfl
@[simp] theorem sub_re (x y : Q15) : (x - y).re = x.re - y.re := rfl
@[simp] theorem sub_im (x y : Q15) : (x - y).im = x.im - y.im := rfl
@[simp] theorem mul_re (x y : Q15) : (x * y).re = x.re * y.re + 15 * x.im * y.im := rfl
@[simp] theorem mul_im (x y : Q15) : (x * y).im = x.re * y.im + x.im * y.re := rfl
instance : CommRing Q15 where
  add_assoc a b c := by ext <;> simp <;> ring
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_comm a b := by ext <;> simp <;> ring
  neg_add_cancel a := by ext <;> simp
  mul_assoc a b c := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  left_distrib a b c := by ext <;> simp <;> ring
  right_distrib a b c := by ext <;> simp <;> ring
  mul_comm a b := by ext <;> simp <;> ring
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp
  sub_eq_add_neg a b := by ext <;> simp <;> ring
  nsmul := nsmulRec
  zsmul := zsmulRec
@[simp] theorem natCast_eq (n : ℕ) : ((n : ℕ) : Q15) = ⟨(n : ℚ), 0⟩ := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.cast_succ, ih]; ext <;> simp [Nat.cast_succ]
end Q15

/-- ℤ[√15] as a computable `CommRing`: `⟨a,b⟩` means `a + b·√15` with `a,b : ℤ`.  Identical in shape to
    `Q15` but over the INTEGERS, so equality is decided by the kernel's GMP `Int` arithmetic with no
    rational `Nat.gcd` normalization.  Used in `gauss_order6` to certify Gauss order 6 by `decide` after the
    tableau is cleared of denominators (scaled by `D=360`). -/
structure Z15 where
  re : Int
  im : Int
deriving DecidableEq, Repr

namespace Z15
@[ext] theorem ext' {x y : Z15} (hr : x.re = y.re) (hi : x.im = y.im) : x = y := by
  cases x; cases y; simp_all
instance : Zero Z15 := ⟨0, 0⟩
instance : One Z15  := ⟨1, 0⟩
instance : Add Z15  := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance : Neg Z15  := ⟨fun x => ⟨-x.re, -x.im⟩⟩
instance : Sub Z15  := ⟨fun x y => ⟨x.re - y.re, x.im - y.im⟩⟩
instance : Mul Z15  := ⟨fun x y => ⟨x.re * y.re + 15 * x.im * y.im, x.re * y.im + x.im * y.re⟩⟩
@[simp] theorem zero_re : (0 : Z15).re = 0 := rfl
@[simp] theorem zero_im : (0 : Z15).im = 0 := rfl
@[simp] theorem one_re : (1 : Z15).re = 1 := rfl
@[simp] theorem one_im : (1 : Z15).im = 0 := rfl
@[simp] theorem add_re (x y : Z15) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_im (x y : Z15) : (x + y).im = x.im + y.im := rfl
@[simp] theorem neg_re (x : Z15) : (-x).re = -x.re := rfl
@[simp] theorem neg_im (x : Z15) : (-x).im = -x.im := rfl
@[simp] theorem sub_re (x y : Z15) : (x - y).re = x.re - y.re := rfl
@[simp] theorem sub_im (x y : Z15) : (x - y).im = x.im - y.im := rfl
@[simp] theorem mul_re (x y : Z15) : (x * y).re = x.re * y.re + 15 * x.im * y.im := rfl
@[simp] theorem mul_im (x y : Z15) : (x * y).im = x.re * y.im + x.im * y.re := rfl
instance : CommRing Z15 where
  add_assoc a b c := by ext <;> simp <;> ring
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_comm a b := by ext <;> simp <;> ring
  neg_add_cancel a := by ext <;> simp
  mul_assoc a b c := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  left_distrib a b c := by ext <;> simp <;> ring
  right_distrib a b c := by ext <;> simp <;> ring
  mul_comm a b := by ext <;> simp <;> ring
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp
  sub_eq_add_neg a b := by ext <;> simp <;> ring
  nsmul := nsmulRec
  zsmul := zsmulRec
end Z15

inductive RTree where
  | node : List RTree → RTree
deriving Repr, Inhabited

abbrev Forest := List RTree

-- the building blocks: • and grafting
def leaf : RTree := .node []
def graft (F : Forest) : RTree := .node F

/-! ### order and density (γ) -/

mutual
  def order : RTree → Nat | .node F => 1 + orderF F
  def orderF : Forest → Nat | [] => 0 | t :: ts => order t + orderF ts
end

mutual
  /-- density γ(t) = |t| · ∏_children γ.  γ(•)=1, γ(•–•)=2, γ(cherry)=3, γ(ladder₃)=6. -/
  def gamma : RTree → Nat | .node F => order (.node F) * gammaF F
  def gammaF : Forest → Nat | [] => 1 | t :: ts => gamma t * gammaF ts
end

/-! ### the Butcher elementary weight Φ(t)(A,b)

    A method is a tableau: `A` the stage matrix (rows), `b` the weights; #stages s = A.length.
    Internal weight vector  g(t)ᵢ = ∏_children (A·g(child))ᵢ ,  leaf ↦ 𝟙.
    Elementary weight  Φ(t) = bᵀ g(t).  Order conditions:  Φ(t) = 1/γ(t)  for all |t| ≤ p. -/

-- The engine is generic over a commutative coefficient ring `K` (ℚ for the classical methods,
-- the ℚ(√15) ring `Q15` for Gauss–Legendre s=3).
variable {K : Type*} [CommRing K]

def dot (u v : List K) : K := (List.zipWith (· * ·) u v).sum
def pmul (u v : List K) : List K := List.zipWith (· * ·) u v
def mulMatVec (A : List (List K)) (v : List K) : List K := A.map (fun row => dot row v)

mutual
  def phiVec (A : List (List K)) : RTree → List K
    | .node F => phiForest A F
  /-- ∏ over children of (A · phiVec child), pointwise; empty forest ↦ all-ones (length s). -/
  def phiForest (A : List (List K)) : Forest → List K
    | []      => A.map (fun _ => 1)
    | t :: ts => pmul (mulMatVec A (phiVec A t)) (phiForest A ts)
end

/-- elementary weight Φ(t) = bᵀ·g(t). -/
def Phi (A : List (List K)) (b : List K) (t : RTree) : K := dot b (phiVec A t)

/-- the order condition at a single tree, in MULTIPLICATIVE form `γ(t)·Φ(t) = 1` (⟺ Φ(t)=1/γ(t)
    since γ(t) ≥ 1); stated this way it needs only a commutative ring, no division. -/
abbrev orderCond (A : List (List K)) (b : List K) (t : RTree) : Prop :=
  (gamma t : K) * Phi A b t = 1

/-! ### the classical methods (exact rationals) -/

-- named small trees
def t1 : RTree := leaf                                  -- •            |t|=1  γ=1
def t2 : RTree := .node [leaf]                          -- •–•          |t|=2  γ=2
def t31 : RTree := .node [leaf, leaf]                   -- cherry       |t|=3  γ=3
def t32 : RTree := .node [.node [leaf]]                 -- ladder₃      |t|=3  γ=6
-- order 4
def t41 : RTree := .node [leaf, leaf, leaf]             -- γ=4
def t42 : RTree := .node [leaf, .node [leaf]]           -- γ=8
def t43 : RTree := .node [.node [leaf, leaf]]           -- γ=12
def t44 : RTree := .node [.node [.node [leaf]]]         -- ladder₄  γ=24
-- one order-5 tree (to witness RK4 is NOT order 5)
def t5bushy : RTree := .node [leaf, leaf, leaf, leaf]   -- γ=5

def euler_A : List (List ℚ) := [[0]]
def euler_b : List ℚ := [1]

def heun_A : List (List ℚ) := [[0,0],[1,0]]
def heun_b : List ℚ := [1/2, 1/2]

def rk4_A : List (List ℚ) := [[0,0,0,0],[1/2,0,0,0],[0,1/2,0,0],[0,0,1,0]]
def rk4_b : List ℚ := [1/6, 1/3, 1/3, 1/6]

-- Dormand–Prince RK45 (DOPRI5): 7 stages (FSAL), the 5th-order solution weights.
def dp_A : List (List ℚ) :=
  [[0,0,0,0,0,0,0],
   [1/5,0,0,0,0,0,0],
   [3/40,9/40,0,0,0,0,0],
   [44/45,-56/15,32/9,0,0,0,0],
   [19372/6561,-25360/2187,64448/6561,-212/729,0,0,0],
   [9017/3168,-355/33,46732/5247,49/176,-5103/18656,0,0],
   [35/384,0,500/1113,125/192,-2187/6784,11/84,0]]
def dp_b : List ℚ := [35/384, 0, 500/1113, 125/192, -2187/6784, 11/84, 0]

-- Gauss–Legendre s=3 (order 6), fully implicit, coefficients in ℚ(√15): ⟨a,b⟩ = a + b·√15.
def gauss_A : List (List Q15) :=
  [[⟨5/36, 0⟩,     ⟨2/9, -1/15⟩, ⟨5/36, -1/30⟩],
   [⟨5/36, 1/24⟩,  ⟨2/9, 0⟩,     ⟨5/36, -1/24⟩],
   [⟨5/36, 1/30⟩,  ⟨2/9, 1/15⟩,  ⟨5/36, 0⟩]]
def gauss_b : List Q15 := [⟨5/18, 0⟩, ⟨4/9, 0⟩, ⟨5/18, 0⟩]

/-- discharge a Q15 order condition: unfold the engine + cast, split into ℚ components, `norm_num`. -/
macro "gauss_check" : tactic =>
  `(tactic| (simp only [orderCond, Phi, phiVec, phiForest, dot, pmul, mulMatVec, gamma, gammaF,
      order, orderF, leaf, gauss_A, gauss_b, t1, t2, t31, t32, t41, t42, t43, t44, t5bushy,
      Q15.natCast_eq, List.map_cons, List.map_nil, List.zipWith_cons_cons, List.zipWith_nil_right,
      List.zipWith_nil_left, List.sum_cons, List.sum_nil]; apply Q15.ext' <;>
      simp only [Q15.mul_re, Q15.mul_im, Q15.add_re, Q15.add_im, Q15.sub_re, Q15.sub_im,
        Q15.neg_re, Q15.neg_im, Q15.one_re, Q15.one_im, Q15.zero_re, Q15.zero_im] <;> norm_num))

/-! ### certificates — the order conditions, machine-checked (axiom-free)

    Each `orderCond` unfolds the computable engine on the concrete tree/tableau to a closed ℚ
    arithmetic goal, closed by `norm_num` (symbolic — sidesteps the kernel's stuck `Nat.gcd`
    reduction in `Rat` normalization that defeats `decide`). -/

/-- unfold the engine on a concrete instance to a closed ℚ goal, then `norm_num`. -/
macro "butcher_check" : tactic =>
  `(tactic| (simp only [orderCond, Phi, phiVec, phiForest, dot, pmul, mulMatVec, gamma, gammaF,
      order, orderF, leaf, t1, t2, t31, t32, t41, t42, t43, t44, t5bushy,
      euler_A, euler_b, heun_A, heun_b, rk4_A, rk4_b, dp_A, dp_b,
      List.map_cons, List.map_nil, List.zipWith_cons_cons, List.zipWith_nil_right,
      List.zipWith_nil_left, List.sum_cons, List.sum_nil]; norm_num))

-- Euler attains order 1:
theorem euler_ord1 : orderCond euler_A euler_b t1 := by butcher_check

-- Heun (explicit trapezoid) attains order 2:
theorem heun_ord1 : orderCond heun_A heun_b t1 := by butcher_check
theorem heun_ord2 : orderCond heun_A heun_b t2 := by butcher_check
-- and FAILS at order 3 (so it is exactly order 2):
theorem heun_not_ord3 : ¬ orderCond heun_A heun_b t31 := by butcher_check

-- classic RK4 satisfies every order condition through order 4:
theorem rk4_ord1 : orderCond rk4_A rk4_b t1  := by butcher_check
theorem rk4_ord2 : orderCond rk4_A rk4_b t2  := by butcher_check
theorem rk4_ord3a : orderCond rk4_A rk4_b t31 := by butcher_check
theorem rk4_ord3b : orderCond rk4_A rk4_b t32 := by butcher_check
theorem rk4_ord4a : orderCond rk4_A rk4_b t41 := by butcher_check
theorem rk4_ord4b : orderCond rk4_A rk4_b t42 := by butcher_check
theorem rk4_ord4c : orderCond rk4_A rk4_b t43 := by butcher_check
theorem rk4_ord4d : orderCond rk4_A rk4_b t44 := by butcher_check
-- ...but FAILS an order-5 condition (bushy 4-leaf tree: Φ=5/24 ≠ 1/5).  RK4 is EXACTLY order 4:
theorem rk4_not_ord5 : ¬ orderCond rk4_A rk4_b t5bushy := by butcher_check

/-! ### Completeness: "order p" is exactly a finite check (order-budget generator)

    A method satisfies the order-p conditions iff Φ(t)=1/γ(t) for the FINITE catalogue of trees
    with |t| ≤ p.  This turns the infinite quantifier (∀ rooted trees) into a decidable
    finite enumeration.  The generator `build` is bounded by an ORDER BUDGET (not by length), so the
    catalogue stays Catalan-small (|trees of order ≤ p| = 1,2,4,9,23,…) and `fin_cases` is feasible
    up to order 5+ (Dormand–Prince).  Structural on the budget → reduces in the kernel; completeness
    is mutual induction with measure (budget, structure). -/

theorem one_le_order (t : RTree) : 1 ≤ order t := by
  cases t with | node F => simp only [order]; omega

theorem order_le_orderF_of_mem : ∀ {c : RTree} {F : Forest}, c ∈ F → order c ≤ orderF F
  | _, _ :: ts, h => by
      rcases List.mem_cons.1 h with rfl | h'
      · simp only [orderF]; omega
      · have ih := order_le_orderF_of_mem h'; simp only [orderF]; omega

/-- ORDER-BUDGET generator (structural on the budget `n`; no length over-generation).
    `(build n).1` = all trees of order ≤ n; `(build n).2` = all forests of orderF ≤ n.  The filter
    bounds each forest by the remaining budget, keeping intermediate lists Catalan-small. -/
def build : Nat → List RTree × List Forest
  | 0     => ([], [[]])
  | n + 1 =>
      let fs := (build n).2
      let trees := fs.map RTree.node
      let forests := [] :: trees.flatMap (fun t =>
          (fs.filter (fun ts => decide (order t + orderF ts ≤ n + 1))).map (fun ts => t :: ts))
      (trees, forests)

def treesB (n : Nat) : List RTree := (build n).1

-- COMPLETENESS of the order-budget generator (mutual, measure = (budget, structure)).
mutual
theorem mem_build_trees : ∀ (n : Nat) (t : RTree), order t ≤ n → t ∈ (build n).1
  | n, RTree.node F, h => by
      cases n with
      | zero => simp only [order] at h; omega
      | succ m =>
          have hF : orderF F ≤ m := by simp only [order] at h; omega
          have hmemF : F ∈ (build m).2 := mem_build_forests m F hF
          show RTree.node F ∈ (build (m+1)).1
          simp only [build, List.mem_map]; exact ⟨F, hmemF, rfl⟩
  termination_by n t => (n, sizeOf t)
  decreasing_by simp_wf; omega

theorem mem_build_forests : ∀ (n : Nat) (F : Forest), orderF F ≤ n → F ∈ (build n).2
  | n, [], _ => by cases n <;> simp [build]
  | n, t :: ts, h => by
      have ht1 : 1 ≤ order t := one_le_order t
      cases n with
      | zero => simp only [orderF] at h; omega
      | succ m =>
          have hsum : order t + orderF ts ≤ m + 1 := by simpa only [orderF] using h
          have htm : order t ≤ m + 1 := by omega
          have htsm : orderF ts ≤ m := by omega
          have hmem_t : t ∈ (build (m+1)).1 := mem_build_trees (m+1) t htm
          have hmem_ts : ts ∈ (build m).2 := mem_build_forests m ts htsm
          have hfilt : ts ∈ ((build m).2).filter (fun ts => decide (order t + orderF ts ≤ m + 1)) :=
            List.mem_filter.2 ⟨hmem_ts, by simpa using hsum⟩
          show (t :: ts) ∈ (build (m+1)).2
          simp only [build, List.mem_cons, List.mem_flatMap, List.mem_map]
          refine Or.inr ⟨t, ?_, ts, hfilt, rfl⟩
          simpa only [build, List.mem_map] using hmem_t
  termination_by n F => (n, sizeOf F)
  decreasing_by
    · simp_wf; omega
    · simp_wf; omega
end

/-- the finite catalogue of all rooted trees with |t| ≤ p. -/
def catalog (p : Nat) : List RTree := (treesB p).filter (fun t => decide (order t ≤ p))

/-- a method `(A,b)` satisfies the order-p conditions: every order condition holds through order p. -/
def satisfiesOrderConditions (A : List (List K)) (b : List K) (p : Nat) : Prop :=
  ∀ t, order t ≤ p → orderCond A b t

/-- The order-p conditions ⟺ a finite check over the catalogue (sound and complete). -/
theorem satisfiesOrderConditions_iff (A : List (List K)) (b : List K) (p : Nat) :
    satisfiesOrderConditions A b p ↔ ∀ t ∈ catalog p, orderCond A b t := by
  constructor
  · intro h t ht
    exact h t (of_decide_eq_true (List.mem_filter.1 ht).2)
  · intro h t hle
    exact h t (List.mem_filter.2 ⟨mem_build_trees p t hle, decide_eq_true hle⟩)

/-- classic RK4 satisfies ALL order-≤4 conditions, certified, axiom-free. -/
theorem rk4_order4 : satisfiesOrderConditions rk4_A rk4_b 4 := by
  rw [satisfiesOrderConditions_iff]; intro t ht
  fin_cases ht <;> butcher_check

/-! ### The planar → abstract bridge: Φ is symmetric in a node's children

    Our trees are PLANAR (ordered children).  The numerical literature uses ABSTRACT rooted trees
    (multiset children); the abstract Connes–Kreimer algebra is the abelianization (Foissy 2002) of
    our noncommutative one.  Here we prove the order condition descends along that symmetrization:
    permuting the children of a node leaves Φ, γ and hence the order condition unchanged.  So
    certifying all PLANAR trees of order ≤ p genuinely subsumes the abstract order conditions —
    mirror planar trees (same abstract shape) share a single condition.  Engine of the bridge:
    `pmul` (pointwise ℚ-product of stage vectors) is commutative and associative UNconditionally. -/

theorem pmul_comm : ∀ u v : List ℚ, pmul u v = pmul v u
  | [],    []    => rfl
  | [],    _::_  => rfl
  | _::_,  []    => rfl
  | a::u,  b::v  => by simp only [pmul, List.zipWith_cons_cons, mul_comm a b]; rw [← pmul, ← pmul, pmul_comm u v]

theorem pmul_assoc : ∀ u v w : List ℚ, pmul (pmul u v) w = pmul u (pmul v w)
  | [],    _,     _     => by simp [pmul]
  | _::_,  [],    _     => by simp [pmul]
  | _::_,  _::_,  []    => by simp [pmul]
  | a::u,  b::v,  c::w  => by
      simp only [pmul, List.zipWith_cons_cons, mul_assoc]
      rw [← pmul, ← pmul, ← pmul, ← pmul, pmul_assoc u v w]

theorem phiForest_perm (A : List (List ℚ)) {F G : Forest} (h : F.Perm G) :
    phiForest A F = phiForest A G := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [phiForest]; rw [ih]
  | swap x y l =>
      simp only [phiForest]
      rw [← pmul_assoc, pmul_comm (mulMatVec A (phiVec A y)) (mulMatVec A (phiVec A x)), pmul_assoc]
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

theorem orderF_perm {F G : Forest} (h : F.Perm G) : orderF F = orderF G := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [orderF]; rw [ih]
  | swap x y l => simp only [orderF]; ring
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

theorem gammaF_perm {F G : Forest} (h : F.Perm G) : gammaF F = gammaF G := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [gammaF]; rw [ih]
  | swap x y l => simp only [gammaF]; ring
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

/-- Φ is invariant under permuting the children of the root. -/
theorem Phi_node_perm (A : List (List ℚ)) (b : List ℚ) {F G : Forest} (h : F.Perm G) :
    Phi A b (.node F) = Phi A b (.node G) := by
  simp only [Phi, phiVec]; rw [phiForest_perm A h]

/-- γ is invariant under permuting the children of the root. -/
theorem gamma_node_perm {F G : Forest} (h : F.Perm G) : gamma (.node F) = gamma (.node G) := by
  simp only [gamma, order]; rw [orderF_perm h, gammaF_perm h]

/-- The order condition depends only on the abstract tree: permuting children is invisible. -/
theorem orderCond_node_perm (A : List (List ℚ)) (b : List ℚ) {F G : Forest} (h : F.Perm G) :
    orderCond A b (.node F) ↔ orderCond A b (.node G) := by
  unfold orderCond; rw [Phi_node_perm A b h, gamma_node_perm h]

/-! ### A higher-order method: Dormand–Prince certified order 5

    The order-budget generator makes `catalog 5` (23 planar trees) small enough that `fin_cases`
    discharges every order-≤5 condition for the 7-stage DOPRI5 tableau (the default method of
    MATLAB `ode45` and SciPy `RK45`).  (Heartbeat bump: `fin_cases` whnf-reduces the 23-tree catalogue — a
    finite computation, just slow in the elaborator; no effect on the axiom set.) -/
set_option maxHeartbeats 4000000 in
theorem dp_order5 : satisfiesOrderConditions dp_A dp_b 5 := by
  rw [satisfiesOrderConditions_iff]; intro t ht
  fin_cases ht <;> butcher_check

/-! ### An implicit method with algebraic coefficients: Gauss–Legendre s=3

    Gauss–Legendre with 3 stages is fully implicit, with a tableau living in ℚ(√15).  Working in the
    computable pair ring `Q15` (where √15²=15 is baked into multiplication), every order condition
    collapses to a pair of ℚ identities that `gauss_check` closes by `norm_num` — no algebraic-number
    tactic.  This certifies the framework on implicit methods with irrational (algebraic) coefficients.

    We certify order 4 here by this route; by `fin_cases` over `catalog 6` (65 planar trees) with
    `norm_num` it does not complete in practical time. Order 6 is certified below over the integers. -/
set_option maxHeartbeats 2000000 in
theorem gauss_order4 : satisfiesOrderConditions gauss_A gauss_b 4 := by
  rw [satisfiesOrderConditions_iff]; intro t ht
  fin_cases ht <;> gauss_check

/-! ### Gauss–Legendre s=3 to order 6 (integer ℤ[√15] + `decide`)

    `gauss_order4` above unfolds the engine symbolically and closes the ℚ(√15) components by `norm_num`.
    At order 6 that route dies: the 65 per-tree `norm_num` calls exhaust memory,
    because ℚ's `Nat.gcd` normalization does not reduce in the kernel and the unfolded Q15 products are
    huge.  The fix is to clear all denominators.  Scaling the tableau by `D = 360` (the lcm of the denominators
    36,9,15,30,24,18) lands it in the INTEGER ring `Z15 = ℤ[√15]`.  The elementary weight is homogeneous,
    `Φ(D·A, D·b, t) = D^{|t|}·Φ(A,b,t)`, so the order condition `γ(t)·Φ = 1` becomes the integer identity
    `γ(t)·Φ(D·A,D·b,t) = D^{|t|}`.  Over `Z15` (a pair of `Int`) this closes by `decide`: the kernel's
    GMP `Int` arithmetic evaluates it directly — no rational normalization, negligible memory.  The whole
    certificate (all 65 planar trees of `catalog 6`) checks in about a second.

    Not formalized here: the homogeneity of `Φ`, and that `gaussI_A`, `gaussI_b` are `D` times
    `gauss_A`, `gauss_b` entrywise; together they make the integer conditions equivalent to the
    unscaled ones. `gauss_order6` is the statement about the scaled integer tableau.

    The scaled integer tableau: entry `a + b√15` with denominator cleared by 360 becomes `⟨360a, 360b⟩`.
    E.g. `2/9 - √15/15 ↦ ⟨80, -24⟩`, `5/18 ↦ ⟨100,0⟩`. -/

def gaussI_A : List (List Z15) :=
  [[⟨50, 0⟩,   ⟨80, -24⟩, ⟨50, -12⟩],
   [⟨50, 15⟩,  ⟨80, 0⟩,   ⟨50, -15⟩],
   [⟨50, 12⟩,  ⟨80, 24⟩,  ⟨50, 0⟩]]
def gaussI_b : List Z15 := [⟨100, 0⟩, ⟨160, 0⟩, ⟨100, 0⟩]
def Dscale : Int := 360

/-- the order condition with denominators cleared: `γ(t)·Φ(D·A,D·b,t) = D^{|t|}` in `Z15`.  Equivalent
    to `orderCond` on the unscaled ℚ(√15) tableau by homogeneity of `Φ`, but decidable by the kernel. -/
abbrev orderCondInt (A : List (List Z15)) (b : List Z15) (D : Int) (t : RTree) : Prop :=
  (⟨(gamma t : Int), 0⟩ : Z15) * Phi A b t = ⟨D ^ (order t), 0⟩

def satisfiesOrderConditionsInt (A : List (List Z15)) (b : List Z15) (D : Int) (p : Nat) : Prop :=
  ∀ t, order t ≤ p → orderCondInt A b D t

/-- Same reduction as `satisfiesOrderConditions_iff`, for the integer condition: the order-p conditions
    reduce to the finite catalogue check (reuses the generic `build`/`catalog` completeness). -/
theorem satisfiesOrderConditionsInt_iff (A : List (List Z15)) (b : List Z15) (D : Int) (p : Nat) :
    satisfiesOrderConditionsInt A b D p ↔ ∀ t ∈ catalog p, orderCondInt A b D t := by
  constructor
  · intro h t ht
    exact h t (of_decide_eq_true (List.mem_filter.1 ht).2)
  · intro h t hle
    exact h t (List.mem_filter.2 ⟨mem_build_trees p t hle, decide_eq_true hle⟩)

/-! Gauss–Legendre s=3 satisfies ALL order-≤6 conditions: the full order-6 certificate, axiom-free.
    `fin_cases` enumerates the 65-tree catalogue; each condition is closed by the kernel (`decide`)
    over `Z15` integer arithmetic.  (Heartbeat bump bounds only `fin_cases`' elaboration; the per-tree
    `decide` is cheap and has no effect on the axiom set.) -/
set_option maxHeartbeats 1000000 in
theorem gauss_order6 : satisfiesOrderConditionsInt gaussI_A gaussI_b Dscale 6 := by
  rw [satisfiesOrderConditionsInt_iff]; intro t ht
  fin_cases ht <;> decide

/-! ### Examples

Orders and densities of the small trees, and the sizes of the catalogues: the numbers of planar
rooted trees with at most `p` nodes (`1, 2, 4, 9, 23`, partial sums of Catalan numbers), not of
abstract rooted trees. -/

example : [order t1, order t2, order t31, order t32, order t41, order t44, order t5bushy]
    = [1, 2, 3, 3, 4, 4, 5] := by decide
example : [gamma t1, gamma t2, gamma t31, gamma t32, gamma t41, gamma t42, gamma t43, gamma t44,
    gamma t5bushy] = [1, 2, 3, 6, 4, 8, 12, 24, 5] := by decide
example : [(catalog 1).length, (catalog 2).length, (catalog 3).length, (catalog 4).length,
    (catalog 5).length] = [1, 2, 4, 9, 23] := by decide

end Butcher
