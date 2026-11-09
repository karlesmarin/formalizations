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
