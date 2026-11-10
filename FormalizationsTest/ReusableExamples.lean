/-
Usage examples of the reusable layer: one `example` per entry of
`Formalizations/Reusable/manifest.toml`, each consuming the stable name the way a user would.
-/
module

import Formalizations.Reusable

open Formalizations.Reusable Matrix MeasureTheory Filter Topology Real Set

/-- Pappus over `ℚ`: the three meets are collinear. -/
example (A B C a b c : Fin 3 → ℚ) (h₁ : A ⬝ᵥ (B ⨯₃ C) = 0) (h₂ : a ⬝ᵥ (b ⨯₃ c) = 0) :
    ((A ⨯₃ b) ⨯₃ (a ⨯₃ B)) ⬝ᵥ (((A ⨯₃ c) ⨯₃ (a ⨯₃ C)) ⨯₃ ((B ⨯₃ c) ⨯₃ (b ⨯₃ C))) = 0 :=
  pappus_hexagon A B C a b c h₁ h₂

/-- Wolstenholme's inequality, from the defect identity. -/
example (x y z A B C : ℝ) (h : A + B + C = π) :
    2 * y * z * Real.cos A + 2 * z * x * Real.cos B + 2 * x * y * Real.cos C
      ≤ x ^ 2 + y ^ 2 + z ^ 2 := by
  have := wolstenholme_defect_eq_sq_add_sq x y z A B C h
  nlinarith [sq_nonneg (x - z * Real.cos B - y * Real.cos C),
    sq_nonneg (z * Real.sin B - y * Real.sin C)]

/-- Torricelli's trumpet has finite volume. -/
example :
    volume {q : (ℝ × ℝ) × ℝ | 1 ≤ q.2 ∧ Real.sqrt (q.1.1 ^ 2 + q.1.2 ^ 2) ≤ 1 / q.2} ≠ ⊤ := by
  rw [torricelli_trumpet.1]
  exact ENNReal.ofReal_ne_top

/-- The zero set of a solution of `y'' = x y` is not bounded below. -/
example (f f' : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (x * f x) x) : ¬ BddBelow {x | f x = 0} := by
  rintro ⟨m, hm⟩
  obtain ⟨x, hx, h0⟩ := airy_eq_zeros_unbounded_below f f' hf hf' m
  exact absurd (hm h0) (not_le.2 hx)

/-- Glasser's integral at `a = 0`, `b = 1`: `∫_{v>0} v^{-1/2} e^{-v} dv = √π`. -/
example : ∫ v in Ioi (0 : ℝ), v ^ (-(1 : ℝ) / 2) * Real.exp (-0 / v - 1 * v) = Real.sqrt π := by
  simpa using glasser_integral (a := 0) (b := 1) le_rfl one_pos

/-- The product of sines for `n = 6`. -/
example : ∏ k ∈ Finset.Ico (1 : ℕ) 6, 2 * Real.sin (k * π / 6) = 6 := by
  have := prod_two_sin_mul_pi_div 6 (by norm_num)
  push_cast at this
  exact this

/-- `X² − 1` splits over `ℝ`: its signs at `−2, 0, 2` are `+, −, +`. -/
example : (Polynomial.X ^ 2 - 1 : Polynomial ℝ).Splits := by
  refine splits_of_alternating_sign _ ?_ 2 ?_ ![-2, 0, 2] ?_ ?_
  · intro h
    have := congrArg (Polynomial.eval 0) h
    simp at this
  · compute_degree!
  · refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i <;> norm_num
  · intro i
    fin_cases i <;> norm_num

/-- Pomerance: eventually more than half of the `n < x` have `n + 2 ∣ C(2n, n)`. -/
example : ∀ᶠ x : ℕ in atTop,
    (1 / 2 : ℝ) < (((Finset.range x).filter (fun n => n + 2 ∣ Nat.centralBinom n)).card : ℝ) / x :=
  (pomerance_density_add_dvd_centralBinom 2 (by norm_num)).eventually (lt_mem_nhds (by norm_num))

/-- Rank of a block triangular matrix with a `1 × 1` identity corner. -/
example (B : Matrix (Fin 1) (Fin 2) ℚ) (D : Matrix (Fin 2) (Fin 2) ℚ) :
    (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) B 0 D).rank ≤ 1 + D.rank := by
  simpa only [Fintype.card_fin] using
    rank_fromBlocks_zero₂₁_le_card_add_rank (1 : Matrix (Fin 1) (Fin 1) ℚ) B D

/-- Cotes: the harmonic-mean point lies on the polar of `p`. -/
example (f : MvPolynomial (Fin 2) ℝ) (p v : Fin 2 → ℝ) (hp : MvPolynomial.eval p f ≠ 0)
    (hsplit : (MvPolynomial.aeval (fun i => Polynomial.C (p i) + Polynomial.C (v i) * Polynomial.X)
      f).roots.card = (MvPolynomial.aeval
        (fun i => Polynomial.C (p i) + Polynomial.C (v i) * Polynomial.X) f).natDegree)
    (hd : 1 ≤ (MvPolynomial.aeval
        (fun i => Polynomial.C (p i) + Polynomial.C (v i) * Polynomial.X) f).natDegree)
    (hH : ((MvPolynomial.aeval (fun i => Polynomial.C (p i) + Polynomial.C (v i) * Polynomial.X)
      f).roots.map (fun r => r⁻¹)).sum ≠ 0) :
    let g := MvPolynomial.aeval (fun i => Polynomial.C (p i) + Polynomial.C (v i) * Polynomial.X) f
    ∑ i, MvPolynomial.eval p (MvPolynomial.pderiv i f) *
        ((g.natDegree : ℝ) / (g.roots.map (fun r => r⁻¹)).sum * v i)
      = -(g.natDegree : ℝ) * MvPolynomial.eval p f :=
  cotes_harmonic_mean_polar f p v hp _ rfl hsplit hd hH

section V020

-- Entries added in v0.2.0 (the same blocks as in the per-area files).
open Polynomial

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

/-- Eneström–Kakeya: `1 + z/2 + z²/3` (coefficients `1 ≥ 1/2 ≥ 1/3 > 0`) has no zero in the open
unit disc. -/
example {z : ℂ} (hz : ‖z‖ < 1) : (1 : ℂ) + z / 2 + z ^ 2 / 3 ≠ 0 := by
  have h := enestrom_kakeya_ne_zero (n := 2) (fun k => 1 / ((k : ℝ) + 1))
    (fun k _ => by positivity)
    (fun k _ => one_div_le_one_div_of_le (by positivity) (by push_cast; linarith)) hz
  convert h using 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  ring

/-- Subadditivity of the rank: `rank (A + A) ≤ 2 · rank A`. -/
example (A : Matrix (Fin 2) (Fin 3) ℚ) : (A + A).rank ≤ 2 * A.rank := by
  have := matrix_rank_add_le A A
  omega

/-- Cauchy–Binet with more rows than inner columns: the sum is empty, so `det (A * B) = 0`. -/
example (A : Matrix (Fin 3) (Fin 2) ℚ) (B : Matrix (Fin 2) (Fin 3) ℚ) : (A * B).det = 0 := by
  rw [det_mul_eq_sum_det_submatrix_mul_det_submatrix]
  refine Finset.sum_eq_zero fun S _ => absurd S.2 ?_
  have := S.1.card_le_univ
  simp only [Fintype.card_fin] at this ⊢
  omega

/-- Jacobi's formula on the characteristic matrix: `charpoly′ = trace (adjugate (X − M))`. -/
example (M : Matrix (Fin 3) (Fin 3) ℚ) :
    Polynomial.derivative M.charpoly = M.charmatrix.adjugate.trace := by
  have h1 : M.charmatrix.map Polynomial.derivative = 1 := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [charmatrix_apply_eq]
    · simp [charmatrix_apply_ne _ _ _ h, one_apply_ne h]
  rw [charpoly, derivative_det_eq_trace_adjugate_mul, h1, Matrix.mul_one]

/-- Kirchhoff: the determinant of a reduced Laplacian over `ℤ` is nonnegative (it counts the
spanning trees). -/
example {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj] (v₀ : V) :
    0 ≤ ((G.lapMatrix ℤ).submatrix (Subtype.val : {v : V // v ≠ v₀} → V) Subtype.val).det := by
  rw [det_lapMatrix_submatrix_eq_card_spanningTrees ℤ G v₀]
  exact Int.natCast_nonneg _

end V020

section V030

-- Entries added in v0.3.0 (the same blocks as in the per-area files).
open Polynomial
open scoped Kronecker

/-- Every higher derivative of a real-rooted polynomial is real-rooted. -/
example (p : Polynomial ℝ) (hp : p.Splits) (k : ℕ) : ((derivative^[k]) p).Splits := by
  induction k with
  | zero => exact hp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact splits_derivative ih

/-- The reverse of a real-rooted polynomial has as many real roots as its degree. -/
example (p : Polynomial ℝ) (hp : p.Splits) : p.reverse.roots.card = p.reverse.natDegree :=
  splits_iff_card_roots.1 (splits_reverse hp)

/-- A block upper-triangular matrix with identity diagonal blocks has full rank. -/
example (B : Matrix (Fin 2) (Fin 2) ℚ) :
    4 ≤ (fromBlocks (1 : Matrix (Fin 2) (Fin 2) ℚ) B 0 (1 : Matrix (Fin 2) (Fin 2) ℚ)).rank := by
  have h := matrix_rank_add_rank_le_rank_fromBlocks (1 : Matrix (Fin 2) (Fin 2) ℚ) B
    (1 : Matrix (Fin 2) (Fin 2) ℚ)
  simpa only [rank_one, Fintype.card_fin] using h

/-- The Kronecker square of a matrix has the square of its rank. -/
example (A : Matrix (Fin 2) (Fin 3) ℚ) : (A ⊗ₖ A).rank = A.rank ^ 2 := by
  rw [matrix_rank_kronecker, sq]

/-- The trace of the adjugate is the sum of the principal `(n − 1) × (n − 1)` minors. -/
example {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℚ) :
    A.adjugate.trace = ∑ i : n, (A.submatrix ((↑) : {j // j ≠ i} → n) ((↑) : {j // j ≠ i} → n)).det := by
  rw [Matrix.trace]
  exact Finset.sum_congr rfl fun i _ => adjugate_apply_self_eq_det_principal_submatrix A i

/-- Wolstenholme as a divisibility: `p³ ∣ C(2p, p) − 2` for every prime `p ≥ 5`. -/
example (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    (p : ℤ) ^ 3 ∣ (Nat.choose (2 * p) p : ℤ) - 2 := by
  have h := Nat.modEq_iff_dvd.1 (wolstenholme_choose_modEq p hp h5).2.symm
  push_cast at h
  exact h

open Classical in
/-- Counting colourings up to symmetry: `|G| · #orbits = Σ_g |C| ^ (number of cycles of g)`. -/
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

/-- The Hall deficiency is supermodular. -/
example (t : ℕ → Finset ℕ) (s u : Finset ℕ) :
    ((s.card : ℤ) - (s.biUnion t).card) + ((u.card : ℤ) - (u.biUnion t).card) ≤
      (((s ∪ u).card : ℤ) - ((s ∪ u).biUnion t).card) +
        (((s ∩ u).card : ℤ) - ((s ∩ u).biUnion t).card) := by
  have h1 := card_biUnion_submodular t s u
  have h2 := Finset.card_union_add_card_inter s u
  omega

/-- Under Hall's condition, the union of three tight sets is tight. -/
example (t : ℕ → Finset ℕ) (hall : ∀ v : Finset ℕ, v.card ≤ (v.biUnion t).card)
    (s u v : Finset ℕ) (hs : (s.biUnion t).card = s.card) (hu : (u.biUnion t).card = u.card)
    (hv : (v.biUnion t).card = v.card) :
    ((s ∪ u ∪ v).biUnion t).card = (s ∪ u ∪ v).card :=
  (card_biUnion_union_inter_eq_of_tight hall
    (card_biUnion_union_inter_eq_of_tight hall hs hu).1 hv).1

/-- Bondy: one element can be deleted from a family of at most `|X|` sets without losing any. -/
example (X : Finset ℕ) (hX : X.Nonempty) (F : Finset (Finset ℕ)) (hF : F.card ≤ X.card) :
    ∃ x ∈ X, (F.image (fun A => A.erase x)).card = F.card := by
  obtain ⟨x, hx, hinj⟩ := bondy_exists_erase_injOn X hX F hF
  exact ⟨x, hx, Finset.card_image_of_injOn hinj⟩

end V030
