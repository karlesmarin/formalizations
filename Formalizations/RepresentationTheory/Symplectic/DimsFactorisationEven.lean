/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
-- encaje: Thm 10.1 (thm:dims) de characters_at_aP.tex: ocupaciones derivadas de N_q(ℓ) = N_q(ρ) (d impar) y caso d par con κ
module

public import Formalizations.RepresentationTheory.Symplectic.DimsFactorisation
public import Formalizations.RepresentationTheory.Symplectic.ResidueCapacity
public import Formalizations.RepresentationTheory.Symplectic.SurvivorCount

/-!
# Theorem 10.1 (`thm:dims`): occupancies from `N_q(ℓ) = N_q(ρ)`, and the case `d` even

* `dims_odd_occ`: `DimsFactorisation.dims_odd` with the class occupancies *derived* from
  `N_q ℓ = N_q ρ` (through `ResidueCapacity.conj_cap` and `ResidueCapacity.shape_odd`).
* the case `d = 2r + 2` even, with the constant `κ ∈ {1, 2}`.
-/

@[expose] public section

namespace RhoLine

open ResidueCapacity

/-! ### Bridge `List ℤ → List (ZMod (2h))`: class lengths are occupancies -/

lemma clsList_length_eq_occ (h : ℕ) (c₀ : ℤ) (L : List ℤ) :
    (clsList h c₀ L).length =
      occ (L.map (Int.castAddHom (ZMod (2 * h)))) (c₀ : ZMod (2 * h)) := by
  classical
  unfold clsList occ
  rw [List.countP_map, ← List.countP_eq_length_filter]
  refine List.countP_congr fun a _ => ?_
  simp

lemma two_nsmul_zero_half (h : ℕ) : 2 • ((h : ℤ) : ZMod (2 * h)) = 0 := by
  rw [two_nsmul, Int.cast_natCast, ← Nat.cast_add, ← two_mul, ZMod.natCast_self]

lemma two_nsmul_ne_zero_of {h : ℕ} (c₀ : ℤ) (h1 : 1 ≤ c₀) (h2 : c₀ ≤ (h : ℤ) - 1) :
    2 • (c₀ : ZMod (2 * h)) ≠ 0 := by
  have := two_c_ne_zero (h := h) c₀ h1 h2
  rwa [two_nsmul, ← two_mul]

/-- The shape hypothesis: `x` of length `m` over `ZMod (2h)`, `(2s+1)·2h = 2m+2`, `N_q x = N_q ρ`. -/
lemma o_shape_odd {h s m : ℕ} (hm : m + 1 = (2 * s + 1) * h) (l : List ℤ) (hlen : l.length = m)
    (hN : N (2 * h) l = N (2 * h) (rhoZ m)) (g : ZMod (2 * h)) :
    o (l.map (Int.castAddHom (ZMod (2 * h)))) g =
      ((2 * s + 1 : ℕ) : ℤ) - (if 2 • g = 0 then 1 else 0) := by
  have hh : 0 < h := hpos_of_hm hm
  have : NeZero (2 * h) := ⟨by omega⟩
  have hd : (2 * s + 1) * (2 * h) = 2 * m + 2 := by nlinarith
  have hx : (l.map (Int.castAddHom (ZMod (2 * h)))).length = m := by simpa using hlen
  have hNq : Nq (l.map (Int.castAddHom (ZMod (2 * h)))) = Nq (rho (2 * h) m) := by
    rw [← rhoZ_cast (2 * h) m, Nq_cast, Nq_cast]; exact hN
  have hc := (conj_cap hd _ hx).2.1 hNq
  rw [cap_iff] at hc
  exact shape_odd (2 * s + 1) _ (card_hyp hd _ hx) hc
    (by rw [Nat.not_even_iff_odd]; exact ⟨s, rfl⟩) (two_fixed ⟨h, by ring⟩) g

/-- **Occupancies for `d` odd.** -/
theorem occ_odd {h s m : ℕ} (hm : m + 1 = (2 * s + 1) * h) (l : List ℤ) (hlen : l.length = m)
    (hN : N (2 * h) l = N (2 * h) (rhoZ m)) :
    (clsList h 0 l).length = s ∧ (clsList h (h : ℤ) l).length = s ∧
      ∀ c < h - 1, (clsList h ((c + 1 : ℕ) : ℤ) l).length = 2 * s + 1 := by
  have hh : 0 < h := hpos_of_hm hm
  have key := o_shape_odd hm l hlen hN
  refine ⟨?_, ?_, ?_⟩
  · rw [clsList_length_eq_occ]
    have e := key 0
    rw [o_eq_occ] at e
    simp only [smul_zero, ite_true] at e
    push_cast at e ⊢
    omega
  · rw [clsList_length_eq_occ]
    have e := key ((h : ℤ) : ZMod (2 * h))
    rw [o_eq_occ] at e
    simp only [two_nsmul_zero_half, ite_true] at e
    push_cast at e ⊢
    omega
  · intro c hc
    rw [clsList_length_eq_occ]
    have h1 : 1 ≤ ((c + 1 : ℕ) : ℤ) := by omega
    have h2 : ((c + 1 : ℕ) : ℤ) ≤ (h : ℤ) - 1 := by omega
    have e := key (((c + 1 : ℕ) : ℤ) : ZMod (2 * h))
    rw [o_eq_occ] at e
    simp only [two_nsmul_ne_zero_of _ h1 h2, ite_false] at e
    push_cast at e ⊢
    omega

/-- **Theorem 10.1 (`thm:dims`), `d = 2s+1` odd, occupancies derived.**  As `dims_odd`, but the
three occupancy hypotheses are replaced by `N_q(ℓ) = N_q(ρ)` and `|ℓ| = m`. -/
theorem dims_odd_occ {h s m : ℕ} (hm : m + 1 = (2 * s + 1) * h) (l : List ℤ)
    (hlen : l.length = m) (hN : N (2 * h) l = N (2 * h) (rhoZ m))
    (L0 ν0 : ℕ → ℤ)
    (hL0 : ∀ i < s, (clsList h 0 l).getD i 0 = ((2 * h : ℕ) : ℤ) * L0 i)
    (hν0 : ∀ i < s, ν0 i = L0 i - ((s : ℤ) - i)) (νh : ℕ → ℚ)
    (hνh : ∀ i < s, νh i = ((clsList h (h : ℤ) l).getD i 0 : ℚ) / ((2 * h : ℕ) : ℚ) -
      (2 * ((s : ℚ) - i) - 1) / 2)
    (y ν : ℕ → ℕ → ℤ)
    (hy : ∀ c < h - 1, ∀ i < 2 * s + 1,
      orient (2 * h) (((c + 1 : ℕ) : ℤ) : ZMod (2 * h))
          ((clsList h ((c + 1 : ℕ) : ℤ) l).getD i 0) =
        ((c + 1 : ℕ) : ℤ) + ((2 * h : ℕ) : ℤ) * y c i)
    (hν : ∀ c < h - 1, ∀ i < 2 * s + 1,
      ν c i = y c i - y c (2 * s + 1 - 1) - (((2 * s + 1 : ℕ) : ℤ) - 1 - i)) :
    |prodDiv (2 * h) l / prodDiv (2 * h) (rhoZ m)| =
      |dimSp s ν0| * |dimSoOdd s νh| *
        ∏ c ∈ Finset.range (h - 1), |dimGl (2 * s + 1) (ν c)| := by
  obtain ⟨hl0, hlh, hlc⟩ := occ_odd hm l hlen hN
  exact dims_odd hm l hl0 L0 ν0 hL0 hν0 hlh νh hνh hlc y ν hy hν

/-! ## `d` even: the block constants

`V n = ∏_{j<n} j!` (`GL_n`), `WC n` and `WB n` the Weyl numerators at `ρ_C = (n,…,1)` and
`ρ_B = (n-½,…,½)`.  The recursions `WC (n+1) = (2n+1)! WC n`, `WB (n+1) = ((2n+1)!/2) WB n`,
`V (n+1) = n! V n` are the note's `C_s / C_{s-1} = 2 (2s-1)!`, `V_{2s}/V_{2s-1} = B_s/B_{s-1}
= (2s-1)!` (the `2` of `C_n` is the long-root factor `2 q` of `prodDiv_alldiv`). -/

/-- `V n = ∏_{j<n} j!`. -/
def Vc (n : ℕ) : ℚ := ∏ j ∈ Finset.range n, ((j.factorial : ℕ) : ℚ)

/-- Weyl numerator of type `C` at `ρ_C`. -/
def WC (n : ℕ) : ℚ := weylC n (fun i => (n : ℚ) - i)

/-- Weyl numerator of type `B` at `ρ_B`. -/
def WB (n : ℕ) : ℚ := weylC n (fun i => (2 * ((n : ℚ) - i) - 1) / 2)

lemma npairs_succ (n : ℕ) : npairs (n + 1) = npairs n + n := by
  unfold npairs
  rw [Finset.sum_range_succ]
  have : ∑ i ∈ Finset.range n, (n + 1 - (i + 1)) = ∑ i ∈ Finset.range n, ((n - (i + 1)) + 1) :=
    Finset.sum_congr rfl fun i hi => by have := Finset.mem_range.1 hi; omega
  rw [this, Finset.sum_add_distrib]
  simp

lemma Vc_succ (n : ℕ) : Vc (n + 1) = Vc n * ((n.factorial : ℕ) : ℚ) := by
  unfold Vc; rw [Finset.prod_range_succ]

lemma weylC_succ (n : ℕ) (l : ℕ → ℚ) :
    weylC (n + 1) l = (l 0 * ∏ j ∈ Finset.range n, ((l 0 - l (j + 1)) * (l 0 + l (j + 1)))) *
      weylC n (fun k => l (k + 1)) := by
  unfold weylC
  rw [Finset.prod_range_succ', mul_comm]
  congr 1
  · rw [Finset.range_eq_Ico, ← Finset.prod_Ico_add' (fun j => ((l 0 - l j) * (l 0 + l j))) 0 n 1]
  · refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    rw [← Finset.prod_Ico_add' (fun j => ((l (i + 1) - l j) * (l (i + 1) + l j))) (i + 1) n 1]

lemma prod_desc (n k : ℕ) (hk : k ≤ n) :
    (∏ j ∈ Finset.range k, ((n : ℚ) - j)) * (((n - k).factorial : ℕ) : ℚ) =
      ((n.factorial : ℕ) : ℚ) := by
  have h := Nat.factorial_mul_descFactorial hk
  rw [Nat.descFactorial_eq_prod_range] at h
  have h' : ((((n - k).factorial * ∏ j ∈ Finset.range k, (n - j) : ℕ)) : ℚ) = (n.factorial : ℕ) := by
    exact_mod_cast h
  rw [Nat.cast_mul, Nat.cast_prod] at h'
  rw [mul_comm, ← h']
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  have := Finset.mem_range.1 hj
  rw [Nat.cast_sub (by omega)]

lemma WC_succ (n : ℕ) : WC (n + 1) = (((2 * n + 1).factorial : ℕ) : ℚ) * WC n := by
  unfold WC
  rw [weylC_succ]
  have e1 : weylC n (fun k => (((n + 1 : ℕ) : ℚ) - ((k + 1 : ℕ) : ℚ))) =
      weylC n (fun i => (n : ℚ) - i) :=
    weylC_congr n _ _ fun i _ => by push_cast; ring
  rw [e1]
  have hd := prod_desc (2 * n + 1) n (by omega)
  rw [show 2 * n + 1 - n = n + 1 by omega, Nat.factorial_succ] at hd
  push_cast at hd
  have hf : ∏ j ∈ Finset.range n, ((j : ℚ) + 1) = ((n.factorial : ℕ) : ℚ) := by
    have := Finset.prod_range_add_one_eq_factorial n
    exact_mod_cast this
  have hp : ∏ j ∈ Finset.range n, ((((n + 1 : ℕ) : ℚ) - ((0 : ℕ) : ℚ) -
      (((n + 1 : ℕ) : ℚ) - ((j + 1 : ℕ) : ℚ))) *
      (((n + 1 : ℕ) : ℚ) - ((0 : ℕ) : ℚ) + (((n + 1 : ℕ) : ℚ) - ((j + 1 : ℕ) : ℚ)))) =
      (n.factorial : ℚ) * ∏ j ∈ Finset.range n, ((2 * (n : ℚ) + 1) - j) := by
    rw [← hf, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    push_cast; ring
  rw [hp, ← hd]
  push_cast
  ring

lemma WB_succ (n : ℕ) : WB (n + 1) = (((2 * n + 1).factorial : ℕ) : ℚ) / 2 * WB n := by
  unfold WB
  rw [weylC_succ]
  have e1 : weylC n (fun k => (2 * (((n + 1 : ℕ) : ℚ) - ((k + 1 : ℕ) : ℚ)) - 1) / 2) =
      weylC n (fun i => (2 * ((n : ℚ) - i) - 1) / 2) :=
    weylC_congr n _ _ fun i _ => by push_cast; ring
  rw [e1]
  have hd := prod_desc (2 * n) n (by omega)
  rw [show 2 * n - n = n by omega] at hd
  push_cast at hd
  have hf : ∏ j ∈ Finset.range n, ((j : ℚ) + 1) = ((n.factorial : ℕ) : ℚ) := by
    have := Finset.prod_range_add_one_eq_factorial n
    exact_mod_cast this
  have hp : ∏ j ∈ Finset.range n,
      (((2 * (((n + 1 : ℕ) : ℚ) - ((0 : ℕ) : ℚ)) - 1) / 2 -
        (2 * (((n + 1 : ℕ) : ℚ) - ((j + 1 : ℕ) : ℚ)) - 1) / 2) *
      ((2 * (((n + 1 : ℕ) : ℚ) - ((0 : ℕ) : ℚ)) - 1) / 2 +
        (2 * (((n + 1 : ℕ) : ℚ) - ((j + 1 : ℕ) : ℚ)) - 1) / 2)) =
      (((2 * n).factorial : ℕ) : ℚ) := by
    push_cast
    rw [← hd, ← hf, mul_comm, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    ring
  rw [hp, Nat.factorial_succ (2 * n)]
  push_cast
  ring

lemma WC_pos (n : ℕ) : 0 < WC n := by
  induction n with
  | zero => simp [WC, weylC]
  | succ n ih => rw [WC_succ]; exact mul_pos (by exact_mod_cast Nat.factorial_pos _) ih

lemma WB_pos (n : ℕ) : 0 < WB n := by
  induction n with
  | zero => simp [WB, weylC]
  | succ n ih => rw [WB_succ]; exact mul_pos (by have := Nat.factorial_pos (2 * n + 1); positivity) ih

lemma Vc_pos (n : ℕ) : 0 < Vc n :=
  Finset.prod_pos fun j _ => by exact_mod_cast Nat.factorial_pos j

/-! ## `d` even: values of the class blocks of `prodDiv` -/

lemma hpos_even {h r m : ℕ} (hm : m + 1 = (2 * r + 2) * h) : 0 < h :=
  Nat.pos_of_ne_zero (by rintro rfl; simp at hm)

/-- Non-fixed class with `n` rows: `|prodDiv| = q^{npairs n} V_n |dim_gl ν|`. -/
theorem abs_prodDiv_nf {q : ℕ} (hq : 0 < q) (c : ZMod q) (hc : 2 * c ≠ 0) (c₀ : ℤ) (n : ℕ)
    (L : List ℤ) (hLn : L.length = n)
    (hL : ∀ v ∈ L, (v : ZMod q) = c ∨ (v : ZMod q) = -c)
    (y ν : ℕ → ℤ) (hy : ∀ i < n, orient q c (L.getD i 0) = c₀ + q * y i)
    (hν : ∀ i < n, ν i = y i - y (n - 1) - ((n : ℤ) - 1 - i)) :
    |prodDiv q L| = (q : ℚ) ^ npairs n * Vc n * |dimGl n ν| := by
  have hpos : 0 < (q : ℚ) ^ npairs n * Vc n :=
    mul_pos (pow_pos (by exact_mod_cast hq) _) (Vc_pos n)
  have hb := block_ratio n q hq (fun i => orient q c (L.getD i 0)) y ν c₀ hy hν
  rw [abs_prodDiv_nonfixed L (fun v hv => two_ne_of_cls c hc v (hL v hv)),
    pairProdL_eq_abs_vdm c hc L hL, hLn]
  have hv : vdm n (fun i => ((orient q c (L.getD i 0) : ℤ) : ℚ)) =
      dimGl n ν * ((q : ℚ) ^ npairs n * Vc n) := (div_eq_iff hpos.ne').1 hb
  rw [hv, abs_mul, abs_of_pos hpos]; ring

/-- Class `0` with `n` rows `ℓ_i = q L'_i`: `prodDiv = (2q)^n (q²)^{npairs n} · dim_sp ν · WC n`. -/
theorem prodDiv_zero_eq {q : ℕ} (n : ℕ) (L : List ℤ) (hn : L.length = n)
    (L' ν : ℕ → ℤ) (hL : ∀ i < n, L.getD i 0 = (q : ℤ) * L' i)
    (hν : ∀ i < n, ν i = L' i - ((n : ℤ) - i)) :
    prodDiv q L = (2 * (q : ℚ)) ^ n * ((q : ℚ) ^ 2) ^ npairs n * (dimSp n ν * WC n) := by
  have A := prodDiv_alldiv q n L hn (fun i => (L' i : ℚ))
    (fun i hi => by rw [hL i hi]; push_cast; ring)
    (fun i hi => ⟨2 * L' i, by rw [hL i hi]; ring⟩)
    (fun i j hij hj => by
      rw [hL i (hij.trans hj), hL j hj]
      exact ⟨⟨L' i - L' j, by ring⟩, ⟨L' i + L' j, by ring⟩⟩)
  have hW : weylC n (fun i => (L' i : ℚ)) = dimSp n ν * WC n := by
    rw [dimSp_shift n ν L' hν]; exact (div_mul_cancel₀ _ (WC_pos n).ne').symm
  rw [A, hW]

/-- Class `q/2` with `n` rows: `prodDiv = (2q)^n (q²)^{npairs n} · dim_so ν · WB n`. -/
theorem prodDiv_half_eq {h : ℕ} (hh : 0 < h) (n : ℕ) (L : List ℤ) (hn : L.length = n)
    (hL : ∀ v ∈ L, (v : ZMod (2 * h)) = ((h : ℤ) : ZMod (2 * h))) (ν : ℕ → ℚ)
    (hν : ∀ i < n, ν i = (L.getD i 0 : ℚ) / ((2 * h : ℕ) : ℚ) - (2 * ((n : ℚ) - i) - 1) / 2) :
    prodDiv (2 * h) L = (2 * ((2 * h : ℕ) : ℚ)) ^ n * (((2 * h : ℕ) : ℚ) ^ 2) ^ npairs n *
      (dimSoOdd n ν * WB n) := by
  have hq : (0 : ℚ) < ((2 * h : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < 2 * h)
  have hqZ : ((2 * h : ℕ) : ℤ) = 2 * h := by push_cast; ring
  have P : ∀ i < n, ∃ u : ℤ, L.getD i 0 = h + ((2 * h : ℕ) : ℤ) * u := fun i hi =>
    half_param (hL _ (getD_mem_of_lt L i (by omega)))
  have A := prodDiv_alldiv (2 * h) n L hn (fun i => (L.getD i 0 : ℚ) / ((2 * h : ℕ) : ℚ))
    (fun i hi => by field_simp)
    (fun i hi => by
      obtain ⟨u, hu⟩ := P i hi
      exact ⟨1 + 2 * u, by rw [hu, hqZ]; ring⟩)
    (fun i j hij hj => by
      obtain ⟨u, hu⟩ := P i (hij.trans hj)
      obtain ⟨w, hw⟩ := P j hj
      rw [hu, hw, hqZ]
      exact ⟨⟨u - w, by ring⟩, ⟨1 + u + w, by ring⟩⟩)
  have hW : weylC n (fun i => (L.getD i 0 : ℚ) / ((2 * h : ℕ) : ℚ)) = dimSoOdd n ν * WB n := by
    rw [dimSoOdd_shift n ν _ hν]; exact (div_mul_cancel₀ _ (WB_pos n).ne').symm
  rw [A, hW]

/-- The `ρ`-rows of class `0` (`r` rows `q(r - i)`). -/
theorem prodDiv_zero_rho {q : ℕ} (r : ℕ) :
    prodDiv q ((List.range r).map fun i : ℕ => (q : ℤ) * ((r : ℤ) - i)) =
      (2 * (q : ℚ)) ^ r * ((q : ℚ) ^ 2) ^ npairs r * WC r := by
  have hE : ∀ i < r, ((List.range r).map fun i : ℕ => (q : ℤ) * ((r : ℤ) - i)).getD i 0 =
      (q : ℤ) * ((r : ℤ) - i) := by
    intro i hi
    simp [List.getD_eq_getElem?_getD, hi]
  exact prodDiv_alldiv q r _ (by simp) (fun i => (r : ℚ) - i)
    (fun i hi => by rw [hE i hi]; push_cast; ring)
    (fun i hi => ⟨2 * ((r : ℤ) - i), by rw [hE i hi]; ring⟩)
    (fun i j hij hj => by
      rw [hE i (hij.trans hj), hE j hj]
      exact ⟨⟨(j : ℤ) - i, by ring⟩, ⟨2 * r - i - j, by ring⟩⟩)

/-- The `ρ`-rows of class `q/2` (`s` rows `h (2(s - i) - 1)`). -/
theorem prodDiv_half_rho {h : ℕ} (s : ℕ) :
    prodDiv (2 * h) ((List.range s).map fun i : ℕ => (h : ℤ) * (2 * ((s : ℤ) - i) - 1)) =
      (2 * ((2 * h : ℕ) : ℚ)) ^ s * (((2 * h : ℕ) : ℚ) ^ 2) ^ npairs s * WB s := by
  have hqZ : ((2 * h : ℕ) : ℤ) = 2 * h := by push_cast; ring
  have hE : ∀ i < s, ((List.range s).map fun i : ℕ => (h : ℤ) * (2 * ((s : ℤ) - i) - 1)).getD i 0
      = (h : ℤ) * (2 * ((s : ℤ) - i) - 1) := by
    intro i hi
    simp [List.getD_eq_getElem?_getD, hi]
  exact prodDiv_alldiv (2 * h) s _ (by simp) (fun i => (2 * ((s : ℚ) - i) - 1) / 2)
    (fun i hi => by rw [hE i hi]; push_cast; ring)
    (fun i hi => ⟨(2 * ((s : ℤ) - i) - 1), by rw [hE i hi, hqZ]; ring⟩)
    (fun i j hij hj => by
      rw [hE i (hij.trans hj), hE j hj, hqZ]
      exact ⟨⟨(j : ℤ) - i, by ring⟩, ⟨2 * s - i - j - 1, by ring⟩⟩)

/-! ### The classes of `ρ_m`, `m + 1 = (2r+2) h` (`d = 2(r+1)` even, `q = 2h`) -/

/-- Rows of `ρ_m` divisible by `q = 2h`: `q (r - i)`, `i < r`. -/
lemma rho_filter_zero_even {h r m : ℕ} (hm : m + 1 = (2 * r + 2) * h) :
    (rhoZ m).filter (fun v : ℤ => decide ((v : ZMod (2 * h)) = 0)) =
      (List.range r).map fun i : ℕ => ((2 * h : ℕ) : ℤ) * ((r : ℤ) - i) := by
  have hmZ : (m : ℤ) + 1 = (2 * r + 2) * h := by exact_mod_cast hm
  have hh : 1 ≤ h := hpos_even hm
  have hqZ : ((2 * h : ℕ) : ℤ) = 2 * h := by push_cast; ring
  refine List.Pairwise.eq_of_mem_iff (r := (· > ·)) ((rhoZ_pairwise m).filter _) ?_ ?_
  · rw [List.pairwise_map]
    refine (List.pairwise_lt_range (n := r)).imp ?_
    intro a b hab
    have : (a : ℤ) < b := by exact_mod_cast hab
    rw [hqZ]; nlinarith
  · intro v
    simp only [List.mem_filter, List.mem_map, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨hv, hz⟩
      obtain ⟨hv1, hv2⟩ := mem_rhoZ hv
      have hd : ((2 * h : ℕ) : ℤ) ∣ v := by
        rw [dvd_iff_zmod]; exact hz
      obtain ⟨k, hk⟩ := hd
      rw [hqZ] at hk
      have hk0 : 1 ≤ k := by
        by_contra hn; push Not at hn
        nlinarith
      have hk1 : k ≤ r := by
        by_contra hn; push Not at hn
        nlinarith
      exact ⟨(r - k).toNat, by omega,
        by rw [hqZ, show (((r - k).toNat : ℕ) : ℤ) = r - k by omega, hk]; ring⟩
    · rintro ⟨i, hi, rfl⟩
      have hi' : (i : ℤ) + 1 ≤ r := by exact_mod_cast hi
      rw [hqZ]
      refine ⟨mem_rhoZ_of (by nlinarith) (by nlinarith), ?_⟩
      have : ((2 * h : ℕ) : ℤ) ∣ 2 * h * ((r : ℤ) - i) := by rw [hqZ]; exact Dvd.intro _ rfl
      have := (dvd_iff_zmod (2 * h) _).1 this
      simpa using this

/-- Rows of `ρ_m` in the class `q/2 = h`: `h (2(r+1-i) - 1)`, `i < r + 1`. -/
lemma rho_filter_half_even {h r m : ℕ} (hm : m + 1 = (2 * r + 2) * h) :
    (rhoZ m).filter (fun v : ℤ => decide ((v : ZMod (2 * h)) = ((h : ℤ) : ZMod (2 * h)))) =
      (List.range (r + 1)).map fun i : ℕ => (h : ℤ) * (2 * (((r + 1 : ℕ) : ℤ) - i) - 1) := by
  have hmZ : (m : ℤ) + 1 = (2 * r + 2) * h := by exact_mod_cast hm
  have hh : 1 ≤ h := hpos_even hm
  have hqZ : ((2 * h : ℕ) : ℤ) = 2 * h := by push_cast; ring
  refine List.Pairwise.eq_of_mem_iff (r := (· > ·)) ((rhoZ_pairwise m).filter _) ?_ ?_
  · rw [List.pairwise_map]
    refine (List.pairwise_lt_range (n := r + 1)).imp ?_
    intro a b hab
    have : (a : ℤ) < b := by exact_mod_cast hab
    push_cast
    nlinarith
  · intro v
    simp only [List.mem_filter, List.mem_map, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨hv, hz⟩
      obtain ⟨hv1, hv2⟩ := mem_rhoZ hv
      obtain ⟨k, hk⟩ := (cls_iff_c _ v h).1 hz
      rw [hqZ] at hk
      have hk0 : 0 ≤ k := by
        by_contra hn; push Not at hn
        nlinarith
      have hk1 : k ≤ r := by
        by_contra hn; push Not at hn
        nlinarith
      exact ⟨(r - k).toNat, by omega,
        by rw [show (((r - k).toNat : ℕ) : ℤ) = r - k by omega]; push_cast; linarith⟩
    · rintro ⟨i, hi, rfl⟩
      have hi' : (i : ℤ) ≤ r := by omega
      refine ⟨mem_rhoZ_of (by push_cast; nlinarith) (by push_cast; nlinarith), ?_⟩
      rw [cls_iff_c, hqZ]
      exact ⟨(r : ℤ) - i, by push_cast; ring⟩

/-- Oriented rows of `ρ_m` in the class of `c₀`: exactly `c₀ + q y`, `y ∈ [-(r+1), r]`. -/
theorem rho_orient_mem_even {h r m : ℕ} (hm : m + 1 = (2 * r + 2) * h) (c₀ : ℤ) (h1 : 1 ≤ c₀)
    (h2 : c₀ ≤ (h : ℤ) - 1) (a : ℤ) :
    (∃ v ∈ rhoZ m, ((v : ZMod (2 * h)) = (c₀ : ZMod (2 * h)) ∨
        (v : ZMod (2 * h)) = -(c₀ : ZMod (2 * h))) ∧
      orient (2 * h) (c₀ : ZMod (2 * h)) v = a) ↔
    ∃ t : ℕ, t < 2 * r + 2 ∧ a = c₀ + ((2 * h : ℕ) : ℤ) * ((t : ℤ) - ((r : ℤ) + 1)) := by
  have hmZ : (m : ℤ) + 1 = (2 * r + 2) * h := by exact_mod_cast hm
  have hh : (2 : ℤ) ≤ h := by
    have : 0 < h := hpos_even hm
    omega
  have hqZ : ((2 * h : ℕ) : ℤ) = 2 * h := by push_cast; ring
  have hneg := c_ne_neg_c (h := h) c₀ h1 h2
  constructor
  · rintro ⟨v, hv, hcl, rfl⟩
    obtain ⟨hv1, hv2⟩ := mem_rhoZ hv
    rcases hcl with hvc | hvn
    · have hor : orient (2 * h) (c₀ : ZMod (2 * h)) v = v := by simp [orient, hvc]
      rw [hor]
      obtain ⟨y, hy⟩ := (cls_iff_c _ v c₀).1 hvc
      rw [hqZ] at hy
      have hy0 : 0 ≤ y := by
        by_contra hn; push Not at hn
        nlinarith
      have hy1 : y ≤ r := by
        by_contra hn; push Not at hn
        nlinarith
      refine ⟨(y + r + 1).toNat, by omega, ?_⟩
      rw [hqZ, show (((y + r + 1).toNat : ℕ) : ℤ) = y + r + 1 by omega]
      linarith
    · have hne : ¬ (v : ZMod (2 * h)) = (c₀ : ZMod (2 * h)) := fun he => hneg (he.symm.trans hvn)
      have hor : orient (2 * h) (c₀ : ZMod (2 * h)) v = -v := by simp [orient, hne]
      rw [hor]
      obtain ⟨k, hk⟩ := (cls_iff_negc _ v c₀).1 hvn
      rw [hqZ] at hk
      have hk0 : 1 ≤ k := by
        by_contra hn; push Not at hn
        nlinarith
      have hk1 : k ≤ r + 1 := by
        by_contra hn; push Not at hn
        nlinarith
      refine ⟨(r + 1 - k).toNat, by omega, ?_⟩
      rw [hqZ, show (((r + 1 - k).toNat : ℕ) : ℤ) = r + 1 - k by omega]
      linarith
  · rintro ⟨t, ht, rfl⟩
    rw [hqZ]
    by_cases hts : r + 1 ≤ t
    · have hY0 : 0 ≤ (t : ℤ) - ((r : ℤ) + 1) := by omega
      have hY1 : (t : ℤ) - ((r : ℤ) + 1) ≤ r := by omega
      have e1 : 0 ≤ (h : ℤ) * ((t : ℤ) - ((r : ℤ) + 1)) := mul_nonneg (by omega) hY0
      have e2 : (h : ℤ) * ((t : ℤ) - ((r : ℤ) + 1)) ≤ h * r :=
        mul_le_mul_of_nonneg_left hY1 (by omega)
      have hmem : c₀ + 2 * h * ((t : ℤ) - ((r : ℤ) + 1)) ∈ rhoZ m :=
        mem_rhoZ_of (by nlinarith) (by nlinarith)
      have hcl : ((c₀ + 2 * h * ((t : ℤ) - ((r : ℤ) + 1)) : ℤ) : ZMod (2 * h)) =
          (c₀ : ZMod (2 * h)) := by
        rw [cls_iff_c, hqZ.symm]
        exact ⟨(t : ℤ) - ((r : ℤ) + 1), by push_cast; ring⟩
      exact ⟨_, hmem, Or.inl hcl, by simp [orient, hcl]⟩
    · push Not at hts
      have hk : 1 ≤ ((r : ℤ) + 1) - t := by omega
      have hk1 : ((r : ℤ) + 1) - t ≤ r + 1 := by omega
      have e1 : (h : ℤ) ≤ h * (((r : ℤ) + 1) - t) := by nlinarith
      have e2 : (h : ℤ) * (((r : ℤ) + 1) - t) ≤ h * (r + 1) :=
        mul_le_mul_of_nonneg_left hk1 (by omega)
      have hmem : -(c₀ + 2 * h * ((t : ℤ) - ((r : ℤ) + 1))) ∈ rhoZ m :=
        mem_rhoZ_of (by nlinarith) (by nlinarith)
      have hcl : ((-(c₀ + 2 * h * ((t : ℤ) - ((r : ℤ) + 1))) : ℤ) : ZMod (2 * h)) =
          -(c₀ : ZMod (2 * h)) := by
        rw [cls_iff_negc, hqZ.symm]
        exact ⟨((r : ℤ) + 1) - t, by push_cast; ring⟩
      have hne : ¬ ((-(c₀ + 2 * h * ((t : ℤ) - ((r : ℤ) + 1))) : ℤ) : ZMod (2 * h)) =
          (c₀ : ZMod (2 * h)) := fun he => hneg (he.symm.trans hcl)
      exact ⟨_, hmem, Or.inr hcl, by unfold orient; simp only [hne, ↓reduceIte]; ring⟩

/-- **`ρ`-block of a non-fixed class, `d` even.**  For `q = 2h`, `m + 1 = (2r+2) h` and
`0 < c₀ < h`, the block of `ρ_m` in the folded class of `c₀` has pair product
`q^{npairs (2r+2)} ∏_{j<2r+2} j!`. -/
theorem rho_block_prod_even {h r m : ℕ} (hm : m + 1 = (2 * r + 2) * h) (c₀ : ℤ) (h1 : 1 ≤ c₀)
    (h2 : c₀ ≤ (h : ℤ) - 1) :
    pairProdL (2 * h) ((rhoZ m).filter fun v : ℤ => decide ((v : ZMod (2 * h)) = (c₀ : ZMod (2 * h)) ∨
        (v : ZMod (2 * h)) = -(c₀ : ZMod (2 * h)))) =
      ((2 * h : ℕ) : ℚ) ^ npairs (2 * r + 2) * Vc (2 * r + 2) := by
  have hh : (1 : ℤ) ≤ h - 1 := le_trans h1 h2
  have hq0 : 0 < (2 * h : ℕ) := by omega
  have hneg := c_ne_neg_c (h := h) c₀ h1 h2
  have hc := two_c_ne_zero (h := h) c₀ h1 h2
  set L := (rhoZ m).filter fun v : ℤ => decide ((v : ZMod (2 * h)) = (c₀ : ZMod (2 * h)) ∨
        (v : ZMod (2 * h)) = -(c₀ : ZMod (2 * h))) with hL
  have hLc : ∀ v ∈ L, (v : ZMod (2 * h)) = (c₀ : ZMod (2 * h)) ∨
      (v : ZMod (2 * h)) = -(c₀ : ZMod (2 * h)) := fun v hv => by
    simpa using (List.mem_filter.1 hv).2
  rw [pairProdL_eq_avdmL (c₀ : ZMod (2 * h)) hc L hLc]
  have hperm : (L.map (orient (2 * h) (c₀ : ZMod (2 * h)))).Perm
      ((List.range (2 * r + 2)).map fun t : ℕ =>
        c₀ + ((2 * h : ℕ) : ℤ) * ((t : ℤ) - ((r : ℤ) + 1))) := by
    rw [List.perm_ext_iff_of_nodup]
    · intro a
      rw [List.mem_map, List.mem_map]
      have := rho_orient_mem_even hm c₀ h1 h2 a
      constructor
      · rintro ⟨v, hv, rfl⟩
        obtain ⟨hv1, hv2⟩ := List.mem_filter.1 hv
        obtain ⟨t, ht, e⟩ := this.1 ⟨v, hv1, by simpa using hv2, rfl⟩
        exact ⟨t, List.mem_range.2 ht, e.symm⟩
      · rintro ⟨t, ht, rfl⟩
        obtain ⟨v, hv, hcl, e⟩ := this.2 ⟨t, List.mem_range.1 ht, rfl⟩
        exact ⟨v, List.mem_filter.2 ⟨hv, by simpa using hcl⟩, e⟩
    · refine List.Nodup.map_on (fun v hv w hw hvw => ?_) ((rhoZ_nodup m).filter _)
      obtain ⟨hv1, hv2⟩ := List.mem_filter.1 hv
      obtain ⟨hw1, hw2⟩ := List.mem_filter.1 hw
      have hvp := (mem_rhoZ hv1).1
      have hwp := (mem_rhoZ hw1).1
      have hv3 : (v : ZMod (2 * h)) = c₀ ∨ (v : ZMod (2 * h)) = -(c₀ : ZMod (2 * h)) := by
        simpa using hv2
      have hw3 : (w : ZMod (2 * h)) = c₀ ∨ (w : ZMod (2 * h)) = -(c₀ : ZMod (2 * h)) := by
        simpa using hw2
      by_cases a1 : (v : ZMod (2 * h)) = c₀ <;> by_cases a2 : (w : ZMod (2 * h)) = c₀ <;>
        simp only [orient, a1, a2, ↓reduceIte] at hvw <;> omega
    · refine List.Nodup.map (fun t t' htt => ?_) (List.nodup_range)
      have h0 : ((2 * h : ℕ) : ℤ) * ((t : ℤ) - ((r : ℤ) + 1)) =
          ((2 * h : ℕ) : ℤ) * ((t' : ℤ) - ((r : ℤ) + 1)) := by
        linarith
      have := mul_left_cancel₀ (by exact_mod_cast hq0.ne' : ((2 * h : ℕ) : ℤ) ≠ 0) h0
      omega
  have e1 : L.map (fun v => ((orient (2 * h) (c₀ : ZMod (2 * h)) v : ℤ) : ℚ)) =
      (L.map (orient (2 * h) (c₀ : ZMod (2 * h)))).map (Int.cast : ℤ → ℚ) := by
    rw [List.map_map]; rfl
  rw [e1, avdmL_perm (hperm.map (Int.cast : ℤ → ℚ)), List.map_map, avdmL_idx, List.length_map,
    List.length_range]
  have e2 : avdm (2 * r + 2) (fun i => (List.map ((Int.cast : ℤ → ℚ) ∘ fun t : ℕ =>
      c₀ + ((2 * h : ℕ) : ℤ) * ((t : ℤ) - ((r : ℤ) + 1))) (List.range (2 * r + 2))).getD i 0) =
      avdm (2 * r + 2) (fun i => ((2 * h : ℕ) : ℚ) * (i : ℚ) +
        ((c₀ : ℚ) - ((2 * h : ℕ) : ℚ) * ((r : ℚ) + 1))) :=
    avdm_congr _ _ _ fun i hi => by
      simp [List.getD_eq_getElem?_getD, hi]
      ring
  rw [e2, avdm_shift (2 * r + 2) (fun i => ((2 * h : ℕ) : ℚ) * (i : ℚ)),
    avdm_scale (2 * r + 2) _ (fun i => (i : ℚ)), avdm_id, abs_of_nonneg (by positivity)]
  rfl

/-! ### Ratios of class blocks (`ℓ` against `ρ`) and the constant `κ` -/

/-- `P = q^{2r+1} (2r+1)!`: moving the free place from the class `0` costs `2P`; it gives back `P⁻¹`
in the class `q/2` or in a non-fixed class. -/
def Pq (q : ℚ) (r : ℕ) : ℚ := q ^ (2 * r + 1) * (((2 * r + 1).factorial : ℕ) : ℚ)

lemma Pq_pos {q : ℚ} (hq : 0 < q) (r : ℕ) : 0 < Pq q r :=
  mul_pos (pow_pos hq _) (by exact_mod_cast Nat.factorial_pos _)

lemma div_cancel_aux (K D W : ℚ) (hK : K ≠ 0) (hW : W ≠ 0) : K * (D * W) / (K * W) = D := by
  field_simp

lemma div_cancel_aux2 (K D : ℚ) (hK : K ≠ 0) : K * D / K = D := by
  field_simp

lemma ratio_zero_aux {q : ℚ} (hq : q ≠ 0) (r : ℕ) (D : ℚ) :
    (2 * q) ^ (r + 1) * (q ^ 2) ^ npairs (r + 1) * (D * WC (r + 1)) /
      ((2 * q) ^ r * (q ^ 2) ^ npairs r * WC r) = D * (2 * Pq q r) := by
  have h1 : WC r ≠ 0 := (WC_pos r).ne'
  rw [npairs_succ, WC_succ]
  unfold Pq
  field_simp
  ring

lemma ratio_half_aux {q : ℚ} (hq : q ≠ 0) (r : ℕ) (D : ℚ) :
    (2 * q) ^ r * (q ^ 2) ^ npairs r * (D * WB r) /
      ((2 * q) ^ (r + 1) * (q ^ 2) ^ npairs (r + 1) * WB (r + 1)) = D * (Pq q r)⁻¹ := by
  have h1 : WB r ≠ 0 := (WB_pos r).ne'
  rw [npairs_succ, WB_succ]
  unfold Pq
  field_simp
  ring

lemma ratio_nf_aux {q : ℚ} (hq : q ≠ 0) (r : ℕ) (D : ℚ) :
    q ^ npairs (2 * r + 1) * Vc (2 * r + 1) * D / (q ^ npairs (2 * r + 2) * Vc (2 * r + 2)) =
      D * (Pq q r)⁻¹ := by
  have e : npairs (2 * r + 2) = npairs (2 * r + 1) + (2 * r + 1) := npairs_succ _
  have e' : Vc (2 * r + 2) = Vc (2 * r + 1) * (((2 * r + 1).factorial : ℕ) : ℚ) := Vc_succ _
  have hV : Vc (2 * r + 1) ≠ 0 := (Vc_pos _).ne'
  have hf : (((2 * r + 1).factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [e, e']
  unfold Pq
  field_simp
  ring

/-- **Theorem 10.1 (`thm:dims`), `d = 2(r+1)` even, `q = 2h`, modulus form.**
`m + 1 = (2r+2) h`.  The free place is in the class `f ∈ [0, h]` (class representatives
`0, 1, …, h-1, h`): the class `f` has one row fewer than its capacity (`r` instead of `r+1` in a
fixed class, `2r+1` instead of `2r+2` in a non-fixed one) and every other class is full.  Then
`|∏_{q∣a} a / ∏_{q∣b} b| = κ · |D_0| · |D_{q/2}| · ∏_c |D_c|` with `κ = 1` if `f = 0` and `κ = 2`
otherwise. -/
theorem dims_even {h r m : ℕ} (hm : m + 1 = (2 * r + 2) * h) (l : List ℤ) (f : ℕ) (hf : f ≤ h)
    (hl0 : (clsList h 0 l).length = if f = 0 then r else r + 1)
    (L0 ν0 : ℕ → ℤ)
    (hL0 : ∀ i < (clsList h 0 l).length,
      (clsList h 0 l).getD i 0 = ((2 * h : ℕ) : ℤ) * L0 i)
    (hν0 : ∀ i < (clsList h 0 l).length,
      ν0 i = L0 i - (((clsList h 0 l).length : ℤ) - i))
    (hlh : (clsList h (h : ℤ) l).length = if f = h then r else r + 1)
    (νh : ℕ → ℚ)
    (hνh : ∀ i < (clsList h (h : ℤ) l).length, νh i =
      ((clsList h (h : ℤ) l).getD i 0 : ℚ) / ((2 * h : ℕ) : ℚ) -
        (2 * (((clsList h (h : ℤ) l).length : ℚ) - i) - 1) / 2)
    (hlc : ∀ c < h - 1, (clsList h ((c + 1 : ℕ) : ℤ) l).length =
      if f = c + 1 then 2 * r + 1 else 2 * r + 2)
    (y ν : ℕ → ℕ → ℤ)
    (hy : ∀ c < h - 1, ∀ i < (clsList h ((c + 1 : ℕ) : ℤ) l).length,
      orient (2 * h) (((c + 1 : ℕ) : ℤ) : ZMod (2 * h))
          ((clsList h ((c + 1 : ℕ) : ℤ) l).getD i 0) =
        ((c + 1 : ℕ) : ℤ) + ((2 * h : ℕ) : ℤ) * y c i)
    (hν : ∀ c < h - 1, ∀ i < (clsList h ((c + 1 : ℕ) : ℤ) l).length,
      ν c i = y c i - y c ((clsList h ((c + 1 : ℕ) : ℤ) l).length - 1) -
        ((((clsList h ((c + 1 : ℕ) : ℤ) l).length : ℕ) : ℤ) - 1 - i)) :
    |prodDiv (2 * h) l / prodDiv (2 * h) (rhoZ m)| =
      (if f = 0 then 1 else 2) * |dimSp (clsList h 0 l).length ν0| *
        |dimSoOdd (clsList h (h : ℤ) l).length νh| *
        ∏ c ∈ Finset.range (h - 1), |dimGl (clsList h ((c + 1 : ℕ) : ℤ) l).length (ν c)| := by
  have hh : 0 < h := hpos_even hm
  have hqpos : (0 : ℚ) < ((2 * h : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < 2 * h)
  have hq0 : ((2 * h : ℕ) : ℚ) ≠ 0 := hqpos.ne'
  have hP := Pq_pos hqpos r
  have hT : ∀ v : ℤ, fcl h v ∈ (Finset.range (h + 1)).image (fun c : ℕ => fcl h (c : ℤ)) :=
    fun v => fcl_mem_T h hh v
  rw [ratio_by_class h _ l (rhoZ m) (fun v _ => hT v) (fun v _ => hT v),
    Finset.prod_image (fun c hc c' hc' e => fcl_inj h hh c c'
      (by have := Finset.mem_range.1 (Finset.mem_coe.1 hc); omega)
      (by have := Finset.mem_range.1 (Finset.mem_coe.1 hc'); omega) e),
    range_split h hh]
  simp only [Nat.cast_zero, filter_fcl]
  have E0 : |prodDiv (2 * h) (clsList h 0 l) / prodDiv (2 * h) (clsList h 0 (rhoZ m))| =
      |dimSp (clsList h 0 l).length ν0| *
        (if f = 0 then 1 else 2 * Pq ((2 * h : ℕ) : ℚ) r) := by
    rw [prodDiv_zero_eq (q := 2 * h) (clsList h 0 l).length (clsList h 0 l) rfl L0 ν0 hL0 hν0,
      clsList_zero h (rhoZ m), rho_filter_zero_even hm, prodDiv_zero_rho r]
    by_cases hf0 : f = 0
    · have hn : (clsList h 0 l).length = r := by simp [hl0, hf0]
      rw [hn, div_cancel_aux _ _ _ (by positivity) (WC_pos r).ne']
      simp [hf0]
    · have hn : (clsList h 0 l).length = r + 1 := by simp [hl0, hf0]
      rw [hn, ratio_zero_aux hq0 r, abs_mul, abs_of_pos (mul_pos two_pos hP)]
      simp [hf0]
  have Eh : |prodDiv (2 * h) (clsList h (h : ℤ) l) /
      prodDiv (2 * h) (clsList h (h : ℤ) (rhoZ m))| =
      |dimSoOdd (clsList h (h : ℤ) l).length νh| *
        (if f = h then (Pq ((2 * h : ℕ) : ℚ) r)⁻¹ else 1) := by
    have hmem : ∀ v ∈ clsList h (h : ℤ) l, (v : ZMod (2 * h)) = ((h : ℤ) : ZMod (2 * h)) :=
      fun v hv => by
        have hv' := (List.mem_filter.1 hv).2
        simp only [decide_eq_true_eq] at hv'
        rcases hv' with e | e
        · exact e
        · rw [e, neg_half]
    rw [prodDiv_half_eq hh _ _ rfl hmem νh hνh, clsList_half h (rhoZ m),
      rho_filter_half_even hm, prodDiv_half_rho (r + 1)]
    by_cases hfh : f = h
    · have hn : (clsList h (h : ℤ) l).length = r := by simp [hlh, hfh]
      rw [hn, ratio_half_aux hq0 r, abs_mul, abs_of_pos (inv_pos.2 hP)]
      simp [hfh]
    · have hn : (clsList h (h : ℤ) l).length = r + 1 := by simp [hlh, hfh]
      rw [hn, div_cancel_aux _ _ _ (by positivity) (WB_pos (r + 1)).ne']
      simp [hfh]
  have Ec : ∀ c ∈ Finset.range (h - 1),
      |prodDiv (2 * h) (clsList h ((c + 1 : ℕ) : ℤ) l) /
        prodDiv (2 * h) (clsList h ((c + 1 : ℕ) : ℤ) (rhoZ m))| =
      |dimGl (clsList h ((c + 1 : ℕ) : ℤ) l).length (ν c)| *
        (if f = c + 1 then (Pq ((2 * h : ℕ) : ℚ) r)⁻¹ else 1) := by
    intro c hc
    have hc' : c < h - 1 := Finset.mem_range.1 hc
    have h1 : 1 ≤ ((c + 1 : ℕ) : ℤ) := by omega
    have h2 : ((c + 1 : ℕ) : ℤ) ≤ (h : ℤ) - 1 := by omega
    have hc2 := two_c_ne_zero (h := h) _ h1 h2
    have hnf : ∀ L : List ℤ, ∀ v ∈ clsList h ((c + 1 : ℕ) : ℤ) L, 2 * (v : ZMod (2 * h)) ≠ 0 :=
      fun L v hv => two_ne_of_cls _ hc2 v (by simpa [clsList] using (List.mem_filter.1 hv).2)
    have hA := abs_prodDiv_nf (q := 2 * h) (by omega) (((c + 1 : ℕ) : ℤ) : ZMod (2 * h)) hc2
      ((c + 1 : ℕ) : ℤ) (clsList h ((c + 1 : ℕ) : ℤ) l).length
      (clsList h ((c + 1 : ℕ) : ℤ) l) rfl
      (fun v hv => by simpa using (List.mem_filter.1 hv).2) (y c) (ν c) (hy c hc') (hν c hc')
    have hR : |prodDiv (2 * h) (clsList h ((c + 1 : ℕ) : ℤ) (rhoZ m))| =
        ((2 * h : ℕ) : ℚ) ^ npairs (2 * r + 2) * Vc (2 * r + 2) := by
      rw [abs_prodDiv_nonfixed _ (hnf (rhoZ m))]
      exact rho_block_prod_even hm _ h1 h2
    rw [abs_div, hA, hR]
    by_cases hfc : f = c + 1
    · have hn : (clsList h ((c + 1 : ℕ) : ℤ) l).length = 2 * r + 1 :=
        (hlc c hc').trans (by simp [hfc])
      rw [hn, ratio_nf_aux hq0 r]
      simp [hfc]
    · have hn : (clsList h ((c + 1 : ℕ) : ℤ) l).length = 2 * r + 2 :=
        (hlc c hc').trans (by simp [hfc])
      rw [hn, div_cancel_aux2 _ _ (mul_pos (pow_pos hqpos _) (Vc_pos _)).ne']
      simp [hfc]
  rw [E0, Eh, Finset.prod_congr rfl Ec, Finset.prod_mul_distrib]
  rcases (by omega : f = 0 ∨ f = h ∨ (1 ≤ f ∧ f ≤ h - 1)) with hf0 | hfh | ⟨hf1, hf2⟩
  · have hne : f ≠ h := by omega
    have eκ : (if f = 0 then (1 : ℚ) else 2) = 1 := by simp [hf0]
    have ea : (if f = 0 then (1 : ℚ) else 2 * Pq ((2 * h : ℕ) : ℚ) r) = 1 := by simp [hf0]
    have eh : (if f = h then (Pq ((2 * h : ℕ) : ℚ) r)⁻¹ else 1) = 1 := by simp [hne]
    have hb : ∏ c ∈ Finset.range (h - 1),
        (if f = c + 1 then (Pq ((2 * h : ℕ) : ℚ) r)⁻¹ else 1) = 1 :=
      Finset.prod_eq_one fun c hc => by simp [hf0]
    rw [eκ, ea, eh, hb]
    ring
  · have eκ : (if f = 0 then (1 : ℚ) else 2) = 2 := by simp [hfh]; omega
    have ea : (if f = 0 then (1 : ℚ) else 2 * Pq ((2 * h : ℕ) : ℚ) r) =
        2 * Pq ((2 * h : ℕ) : ℚ) r := by simp [hfh]; omega
    have eh : (if f = h then (Pq ((2 * h : ℕ) : ℚ) r)⁻¹ else 1) =
        (Pq ((2 * h : ℕ) : ℚ) r)⁻¹ := by simp [hfh]
    have hb : ∏ c ∈ Finset.range (h - 1),
        (if f = c + 1 then (Pq ((2 * h : ℕ) : ℚ) r)⁻¹ else 1) = 1 :=
      Finset.prod_eq_one fun c hc => by
        have := Finset.mem_range.1 hc
        simp [show f ≠ c + 1 by omega]
    rw [eκ, ea, eh, hb]
    field_simp
  · have hne : f ≠ h := by omega
    have hne0 : f ≠ 0 := by omega
    have eκ : (if f = 0 then (1 : ℚ) else 2) = 2 := by simp [hne0]
    have ea : (if f = 0 then (1 : ℚ) else 2 * Pq ((2 * h : ℕ) : ℚ) r) =
        2 * Pq ((2 * h : ℕ) : ℚ) r := by simp [hne0]
    have eh : (if f = h then (Pq ((2 * h : ℕ) : ℚ) r)⁻¹ else 1) = 1 := by simp [hne]
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have hb : ∏ c ∈ Finset.range (h - 1),
        (if f' + 1 = c + 1 then (Pq ((2 * h : ℕ) : ℚ) r)⁻¹ else 1) =
        (Pq ((2 * h : ℕ) : ℚ) r)⁻¹ := by
      simp only [Nat.add_right_cancel_iff]
      rw [Finset.prod_ite_eq]
      simp [Finset.mem_range]
      omega
    rw [eκ, ea, eh, hb]
    field_simp

/-! ### The free class from `N_q(ℓ) = N_q(ρ)` (`ResidueCapacity.shape_even`) -/

lemma bump_nat {h : ℕ} (hh : 0 < h) (f k : ℕ) (hf : f ≤ h) (hk : k ≤ h) :
    bump (f : ZMod (2 * h)) (k : ZMod (2 * h)) =
      (if f = k then 1 else 0) + (if (f = 0 ∧ k = 0) ∨ (f = h ∧ k = h) then 1 else 0) := by
  unfold bump
  have e1 : ((f : ZMod (2 * h)) = k) ↔ f = k := by
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have e2 : (-(f : ZMod (2 * h)) = k) ↔ ((f = 0 ∧ k = 0) ∨ (f = h ∧ k = h)) := by
    rw [neg_eq_iff_add_eq_zero, add_comm, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]
    constructor
    · rintro ⟨t, ht⟩
      have : t ≤ 1 := by
        by_contra hn; push Not at hn
        nlinarith
      interval_cases t <;> omega
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by ring⟩
  simp only [e1, e2]

/-- **Occupancies for `d = 2r+2` even**: exactly one folded class `f ∈ [0, h]` is one row short. -/
theorem occ_even {h r m : ℕ} (hm : m + 1 = (2 * r + 2) * h) (l : List ℤ) (hlen : l.length = m)
    (hN : N (2 * h) l = N (2 * h) (rhoZ m)) :
    ∃ f : ℕ, f ≤ h ∧ (clsList h 0 l).length = (if f = 0 then r else r + 1) ∧
      (clsList h (h : ℤ) l).length = (if f = h then r else r + 1) ∧
      ∀ c < h - 1, (clsList h ((c + 1 : ℕ) : ℤ) l).length =
        if f = c + 1 then 2 * r + 1 else 2 * r + 2 := by
  have hh : 0 < h := hpos_even hm
  have : NeZero (2 * h) := ⟨by omega⟩
  have hd : (2 * r + 2) * (2 * h) = 2 * m + 2 := by nlinarith
  have hx : (l.map (Int.castAddHom (ZMod (2 * h)))).length = m := by simpa using hlen
  have hNq : Nq (l.map (Int.castAddHom (ZMod (2 * h)))) = Nq (rho (2 * h) m) := by
    rw [← rhoZ_cast (2 * h) m, Nq_cast, Nq_cast]; exact hN
  have hc := (conj_cap hd _ hx).2.1 hNq
  rw [cap_iff] at hc
  obtain ⟨c, hcc⟩ := shape_even (2 * r + 2) _ (card_hyp hd _ hx) hc ⟨r + 1, by ring⟩
  have hcv : ∃ f : ℕ, f ≤ h ∧ (c = (f : ZMod (2 * h)) ∨ c = -(f : ZMod (2 * h))) := by
    have hr : ((c.val : ℕ) : ZMod (2 * h)) = c := ZMod.natCast_zmod_val c
    have hrl : c.val < 2 * h := ZMod.val_lt c
    by_cases hrh : c.val ≤ h
    · exact ⟨c.val, hrh, Or.inl hr.symm⟩
    · refine ⟨2 * h - c.val, by omega, Or.inr ?_⟩
      have h0 : ((2 * h : ℕ) : ZMod (2 * h)) = 0 := ZMod.natCast_self _
      rw [Nat.cast_sub (by omega), h0, zero_sub, neg_neg, hr]
  obtain ⟨f, hfh, hfc⟩ := hcv
  have hbump : ∀ g, bump c g = bump (f : ZMod (2 * h)) g := by
    intro g
    rcases hfc with h' | h'
    · rw [h']
    · rw [h']; unfold bump; rw [neg_neg, add_comm]
  have key : ∀ k : ℕ, k ≤ h → o (l.map (Int.castAddHom (ZMod (2 * h)))) (k : ZMod (2 * h)) =
      ((2 * r + 2 : ℕ) : ℤ) - ((if f = k then 1 else 0) +
        (if (f = 0 ∧ k = 0) ∨ (f = h ∧ k = h) then 1 else 0)) := fun k hk => by
    rw [hcc, hbump, bump_nat hh f k hfh hk]
  refine ⟨f, hfh, ?_, ?_, ?_⟩
  · rw [clsList_length_eq_occ, Int.cast_zero]
    have e := key 0 (Nat.zero_le _)
    rw [o_eq_occ] at e
    simp only [Nat.cast_zero, smul_zero, ite_true] at e
    by_cases hf0 : f = 0 <;> simp [hf0] at e ⊢ <;> omega
  · rw [clsList_length_eq_occ, Int.cast_natCast]
    have e := key h le_rfl
    rw [o_eq_occ] at e
    have h2 : 2 • ((h : ℕ) : ZMod (2 * h)) = 0 := by
      have := two_nsmul_zero_half h
      rwa [Int.cast_natCast] at this
    simp only [h2, ite_true] at e
    by_cases hfh' : f = h <;> simp [hfh', show h ≠ 0 by omega] at e ⊢ <;> omega
  · intro c' hc'
    rw [clsList_length_eq_occ, Int.cast_natCast]
    have h1 : 1 ≤ ((c' + 1 : ℕ) : ℤ) := by omega
    have h2 : ((c' + 1 : ℕ) : ℤ) ≤ (h : ℤ) - 1 := by omega
    have e := key (c' + 1) (by omega)
    rw [o_eq_occ] at e
    have h3 : 2 • ((c' + 1 : ℕ) : ZMod (2 * h)) ≠ 0 := by
      have := two_nsmul_ne_zero_of (h := h) _ h1 h2
      rwa [Int.cast_natCast] at this
    simp only [h3, ite_false] at e
    by_cases hfc' : f = c' + 1
    · have : ¬ ((f = 0 ∧ c' + 1 = 0) ∨ (f = h ∧ c' + 1 = h)) := by omega
      simp only [hfc', ite_true] at e ⊢
      omega
    · have : ¬ ((f = 0 ∧ c' + 1 = 0) ∨ (f = h ∧ c' + 1 = h)) := by omega
      simp only [hfc', ite_false, this] at e ⊢
      omega

/-- **Theorem 10.1 (`thm:dims`), `d = 2(r+1)` even, occupancies derived.**  From
`|ℓ| = m` and `N_q ℓ = N_q ρ` alone: there is a unique-by-construction free class `f ∈ [0, h]`
(`occ_even`) and the modulus is `κ · D_0 · D_{q/2} · ∏_c D_c`, `κ = 1` if `f = 0`, else `2`. -/
theorem dims_even_occ {h r m : ℕ} (hm : m + 1 = (2 * r + 2) * h) (l : List ℤ)
    (hlen : l.length = m) (hN : N (2 * h) l = N (2 * h) (rhoZ m))
    (L0 ν0 : ℕ → ℤ)
    (hL0 : ∀ i < (clsList h 0 l).length,
      (clsList h 0 l).getD i 0 = ((2 * h : ℕ) : ℤ) * L0 i)
    (hν0 : ∀ i < (clsList h 0 l).length,
      ν0 i = L0 i - (((clsList h 0 l).length : ℤ) - i))
    (νh : ℕ → ℚ)
    (hνh : ∀ i < (clsList h (h : ℤ) l).length, νh i =
      ((clsList h (h : ℤ) l).getD i 0 : ℚ) / ((2 * h : ℕ) : ℚ) -
        (2 * (((clsList h (h : ℤ) l).length : ℚ) - i) - 1) / 2)
    (y ν : ℕ → ℕ → ℤ)
    (hy : ∀ c < h - 1, ∀ i < (clsList h ((c + 1 : ℕ) : ℤ) l).length,
      orient (2 * h) (((c + 1 : ℕ) : ℤ) : ZMod (2 * h))
          ((clsList h ((c + 1 : ℕ) : ℤ) l).getD i 0) =
        ((c + 1 : ℕ) : ℤ) + ((2 * h : ℕ) : ℤ) * y c i)
    (hν : ∀ c < h - 1, ∀ i < (clsList h ((c + 1 : ℕ) : ℤ) l).length,
      ν c i = y c i - y c ((clsList h ((c + 1 : ℕ) : ℤ) l).length - 1) -
        ((((clsList h ((c + 1 : ℕ) : ℤ) l).length : ℕ) : ℤ) - 1 - i)) :
    ∃ f : ℕ, f ≤ h ∧
      |prodDiv (2 * h) l / prodDiv (2 * h) (rhoZ m)| =
        (if f = 0 then 1 else 2) * |dimSp (clsList h 0 l).length ν0| *
          |dimSoOdd (clsList h (h : ℤ) l).length νh| *
          ∏ c ∈ Finset.range (h - 1), |dimGl (clsList h ((c + 1 : ℕ) : ℤ) l).length (ν c)| := by
  obtain ⟨f, hf, h0, hh', hc⟩ := occ_even hm l hlen hN
  exact ⟨f, hf, dims_even hm l f hf h0 L0 ν0 hL0 hν0 hh' νh hνh hc y ν hy hν⟩

end RhoLine
