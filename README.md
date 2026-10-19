# 🧮 Formalizations

[![build](https://github.com/karlesmarin/formalizations/actions/workflows/build.yml/badge.svg)](https://github.com/karlesmarin/formalizations/actions/workflows/build.yml)

Lean 4 formalizations by Carles Marín, built on [Mathlib](https://github.com/leanprover-community/mathlib4) and
organized the same way: by mathematical area, one topic per file, every file with a module docstring listing its main
results.

- 🔧 Lean `v4.35.0`; Mathlib pinned in `lakefile.lean` (commit `f0b4c81`).
- ✅ No `sorry`, no `native_decide`, no new axioms. All 442 main results depend only on the standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`), checked by `scripts/check_axioms.sh` on every push (CI).
  The choice-free core of `SetTheory.Ordinal.Gentzen` depends on `propext` alone.
- 🔬 Most files are the machine-checked core of a research note: the identities and finite certificates a paper
  relies on. The paper says exactly which statements are formalized and which are not.

## 🚀 Using it

```
git clone https://github.com/karlesmarin/formalizations.git
cd formalizations
lake exe cache get
lake build
```

Import everything with `import Formalizations`, or a single file, e.g.
`import Formalizations.RingTheory.DGH.Epsilon0`.

## 🗂️ Contents

| Area | File | Main result |
|---|---|---|
| `Algebra.Ring` | `Continuant` | Euler's continuant; `a⁻¹ + r + b⁻¹ = a⁻¹ K(a,r,b) b⁻¹` |
| `Analysis.SpecialFunctions.Integrals` | `LogDivSelf` 🆕 | `∫₁ᴺ log x / x dx = (log N)² / 2` |
| `Analysis.TransformerAttention` | `CriticalExponents` 🆕 | Phase A exponents of the attention decay: `2η² + ηγ_χ + 1 = 0`, `βχ = −1`, `α + χ = 2`, Rushbrooke and Josephson with `d = 1`, the Fisher residual, `η = 2γ` refuted on `(0, 1)`, AM-GM bound `γ_χ ≥ 2√2` |
| | `CardyPDI` 🆕 | `log PDI + ΔH_Cardy = 0` (Phase 7 form), residual `−log 2 / 2` (Phase 8 form); `d/dx artanh x = 1/(1 − x²)` |
| | `Pade` 🆕 | The `[2/2]` minus the `[1/1]` Padé approximant of `e^{−z}` is `2z³/((z + 2)(z² + 6z + 12))`; `θ_eff` closed form |
| | `CayleyMap` 🆕 | Fixed point `z* = (√17 − 3)/2` of `(2 − z)/(2 + z)`, `χ = (5 + √17)/4`, Floquet multiplier `(√17 − 9)/8` with `|μ| < 1` |
| | `RGFlow` 🆕 | `V = γ − γ³/3` gives `−V' ≠ β = −(1 − γ²)/2` (factor 2); the corrected `V = γ/2 − γ³/6`; `tanh(t/2 + c)` solves `γ' = (1 − γ²)/2` |
| | `GammaMobius` 🆕 | The Padé exponent `(2θ − T√2)/(2θ + T√2)` is the Möbius transform `(1 − u)/(1 + u)` of `u = T/(θ√2)` (needs `s² = 2`); the horizon `θ√2 (1 − γ)/(1 + γ)` at the Padé exponent equals `T`; `β = −2u/(1 + u)²` |
| | `HeatCapacity` 🆕 | Erratum to the Hagedorn heat capacity: both derivations give `(log N)²/12`, three times smaller than the published `(log N)²/4` |
| `LinearAlgebra.Matrix` | `FinTwo` | `2×2` identities: polarized Cayley–Hamilton, `det (A + B)`, iterated commutators |
| | `Adjugate` | Diagonal entries of the adjugate are principal minors |
| | `Rank` | `rank (A + B) ≤ rank A + rank B`; nullity under low-rank perturbation; block triangular bounds |
| | `Rank.Kronecker` | `rank (A ⊗ₖ 1) = card p * rank A` |
| | `Charpoly.Jacobi` | Resolvent series and Jacobi's formula for the derivative of the reversed charpoly |
| | `FreeLocus` | Rank and corank lemmas for block and low-rank perturbations |
| | `FreeLocusCertificate` | Soundness of the free-locus certificate ("not flip-poly") |
| `Physics.Particles.GaugeHiggsUnification` | `NotchCentreCharge` 🆕 | The bialternant `N = det (yᵢ^{μⱼ})` of `s_λ(1, −1, t, t⁻¹)` over `ℤ[T;T⁻¹]` vanishes iff `Odd b ∧ ((Odd a ∧ Odd c) ∨ a = c)`; `D(−t) = (−1)^{a+2b+3c} D(t)`; degenerate irreps have even centre charge `a + 2b + 3c` |
| | `BlindCount` 🆕 | The blind set in partition coordinates (two branches) equals `N = 0`; `l₁` is odd on it; the shell `l₁ = 2k+1` has `⌈(k+1)²/2⌉` blind partitions |
| | `CosetCensus` 🆕 | Boundary conditions `[p; q, r; s]` on `S¹/ℤ₂`: the label `(p+q, q+s)` is a complete invariant of the equivalence, `(N+1)²` classes, of which `⌊(N+1)²/2⌋` have a reflection-coset sector |
| | `OddEighths` 🆕 | `SU(7)` moments: `8D ≡ 2A₄ + 3 (mod 6)` and `2W` odd for every bulk content, for both gauge seeds; `8D` odd if the gauge contribution is odd |
| | `R60JointExistence` 🆕 | Farkas certificate: four anomaly-neutral additions realize `±Θ₀₁`, `±Θ₂₃`, so the localized tadpole never obstructs an anomaly-free completion of `(3, 60)` |
| | `R60LocalizedAnomaly` 🆕 | Localized cubic anomalies of the `60` of `SU(4)`: numerators `−6`, `6`; both independent of the Wilson line, the mixed `C² · U(1)` piece not |
| | `ScalarCPSource` 🆕 | `Im (λ (conj v₁ · v₂)²) = 0` for real `λ, v₁, v₂` |
| | `InternalU1MixingNoGo` 🆕 | `Even n₃` and `3 n₃ − 2 n₄ = 1` are incompatible |
| `Physics.Particles.StandardModel.SMEFT` | `AllOrdersSelfCouplings` 🆕 | All orders in `α`: `δκ₄ − 6 δκ₃ = α(3α³ + 30α² + 35α − 4)/(3(α+1)²)`, `δκ₅ − 15 δκ₃`, `δκ₆ − 15 δκ₃` in closed form; dimension-8 breaking at first order; catalog `δκ₇ … δκ₁₂` with `δκ₁₁ = δκ₁₂` |
| | `TopEdgeCollapse` 🆕 | At the degree-12 edge the 11- and 12-point contributions coincide; the 12-point one is `246400 α⁴/(1 + α)²` |
| | `HiggsSelfCouplings` 🆕 | Tree-level matching of the Higgs self-couplings: `O_φ = (vh + h²/2)³`; `c_φ` pieces with `δκ₄ = 6 δκ₃`; `δκ₄ − 6 δκ₃ = −(4/3)(v²/Λ²) C_{H,kin}`, so the ratio is `6` iff `C_{H,kin} = 0`; leading order `δκ₅ − 15 δκ₃ = δκ₆ − 15 δκ₃ = −5 (v²/Λ²) C_{H,kin}` |
| `RingTheory.DGH` | `Basic` | The Dubrovin–Gräter–Hanke stratification `D : Ordinal → Set R` |
| | `JakobsOrder` | Jakobs' order = Dershowitz–Manna order |
| | `Hessenberg` | Jakobs' order through the Hessenberg natural sum |
| | `Absorb` | Absorption of a layer of inverses; `(a⁻¹ + b⁻¹)⁻¹ = b (a + b)⁻¹ a`; Hua's identity `a − (a⁻¹ + (b⁻¹ − a)⁻¹)⁻¹ = a b a` |
| | `Finite` | Finite strata; `D M ω` as a subring |
| | `Epsilon0` | The stratification closes at `ε₀` (`kappa_le_epsilon0`) |
| | `FqLower` | Combinatorial core of `κ(F_q(x)) = ω²` |
| `RingTheory.FreeField.ThreeAxes` | `Basic` | Shared definitions: the block matrix `[[A+B, A],[A, A+C]]`, an explicit `4×4` determinant, square-zero `2×2` matrices, witness matrices |
| | `ExactArc` | Traceless `2×2` squares are scalar; scalar evaluation; characteristic `p` |
| | `Extractors` | Trace and determinant extractors; Fox decomposition of a commutator |
| | `TraceResidue` | Residues along square-zero directions |
| | `DegenerateResidue` | Degenerate-residue identities; explicit witnesses |
| | `WeightedTrinomials` | Hidden commutator in `GL₂`; weighted trinomial curve with `Nᵢ² = 0`; `2×2` Schur inverse over any ring |
| | `AtomCertificate` 🆕 | Integer certificate of a `9×9` atom: `Q·Kᵢ = 16·Qᵢ`, `det Q = 256`, a rank-one identity, and two `9×9` determinants (`5·2⁵⁶`, `2⁴⁹`) via a triangular factorization certificate |
| | `QuaternionResidues` 🆕 | Integral quaternions mod `5`: six rank-one residues, products vanish exactly on inverse pairs, nonzero along reduced words |
| | `InverseIdentities` 🆕 | Inverse identities over any division ring: `(p⁻¹+q⁻¹+r)⁻¹ = q(prq+p+q)⁻¹p`, Woodbury corners of the harmonic matrix, block Schur compression, explicit inverses of chain and cycle matrices |
| | `SizeChainPencil` 🆕 | A diagonal matrix with distinct eigenvalues and the cyclic permutation matrix generate `M_d(K)`; `diag(3,…,d+2) − 1 − C_d²` is invertible (Gershgorin); the `F^{(λ)}` case: invertibility iff `λ ∉ {−1,0,1,2}` |
| | `Criterion` 🆕 | Monotone invariants and stable association; the non-membership criterion with the localization lemma as a named hypothesis; the corank at a representation is a monotone invariant |
| | `ChainPencilConditions` 🆕 | The eight rank conditions (EPIC both sides, `𝒦ᵢᴿ = 𝒦ᵢᴸ = 0`) for the chain pencils `Q₃`, `Q₄`, by `decide` certificates |
| | `ParabolicFamily` 🆕 | The exact arc is the conjugate `Kⁱ U₀ K⁻ⁱ` of an antidiagonal matrix; conjugates of a central square stay central; the parabolic family `N_j = Kʲ N K⁻ʲ = t c_j r_j` with `N_j² = 0` and the cyclic trace law `tr(N_{j₁}⋯N_{j_q}) = t^{2q} ∏ (j_{l+1} − j_l)`; `det (1 + J) = n + 1` |
| | `ArrowMatrix` 🆕 | Explicit two-sided inverse of the arrow matrix `[[diag d, ω], [α, 0]]` over a division ring; its border corner is `−(Σ α d⁻¹ ω)⁻¹` |
| | `PhiCompression` 🆕 | Compression of `φ = Σ α d⁻¹ ω + w d₂⁻¹` over a division ring: explicit two-sided inverse of `[[diag d, −ω d₂], [α, w]]` with `φ⁻¹ = d₂ (M⁻¹)_{∞∞}`; scalar Woodbury `φ⁻¹ = c − c (α T ω) c` from a right inverse `T` of `diag d + ω c α`; two-sided block Schur inverse with upper-left pivot over any ring |
| | `BinomialSizeFamily` 🆕 | Explicit two-sided inverse of `diag Δ + u J` over a division ring with `q = u⁻¹ + Σ Δᵢ⁻¹`, derived from Mathlib's Woodbury identity; `q⁻¹ = u − u (Σ_{i,j} H⁻¹ᵢⱼ) u`; `(yⁱ u y⁻ⁱ + u) yⁱ = yⁱ u + u yⁱ`; `det (diag(0, 1, …, 1) + J) = 1`; at the idempotent point (`U = 1 − E₀₀`, `W = 1`, `Y` the cyclic shift) the `d × d` block matrix `U Yʲ + δᵢⱼ (i = 0 ? W : Yⁱ U)` is invertible for every `d ≥ 1` |
| | `QuaternionCurve` 🆕 | `t i`, `t j`, `t k` in `ℍ[R]` square to `−t²` and anticommute pairwise |
| `SetTheory.Ordinal.Gentzen` | `Acc` 🆕 | Well-foundedness below `ε₀` without choice: a syntactic order `slt` (by `ONote.cmp`) and normal form `SNF` on `ONote`; `acc_slt`, `wf_slt`, `ti_syntactic` depend on `propext` only; bridge `slt_iff_lt`, `SNF_iff_NF` to Mathlib's `<` and `NF` |
| | `TwoPow` 🆕 | `2^α` (`twoPow' (ω·γ + m) = ω^γ · 2^m`) and the cut-elimination inequalities L1–L5 of Gentzen's consistency proof, with their counterexamples at `α = 0, 1`, all on `propext` only; bridge: `twoPow'` denotes `2^α` and equals Mathlib's `ONote.opow` |
| | `Ordinals` 🆕 | The same `2^α` and L1–L5 on Mathlib's `NONote` through `repr` (uses choice); transfinite induction from `NONote.lt_wf` |

`FormalizationsTest/Axioms.lean` prints the axioms of every main result.

## 🔗 Relation to Mathlib and other libraries

Where a statement here is a direct consequence of a Mathlib lemma (kept because a paper cites it
by name), the file says so and proves it in one line from that lemma.

- 🧱 **Block inverses and Schur complements.** Mathlib's block inverse
  (`Matrix.fromBlocks₂₂Invertible`, `Matrix.invOf_fromBlocks₂₂_eq`) is stated over a `CommRing`.
  `InverseIdentities.fromBlocks_mul_schur`, `schur_two` and `WeightedTrinomials.schur_r2` are the
  noncommutative versions over any ring, with one-sided inverses.
- ↗️ **Arrow matrices.** Over a commutative ring the inverse of `[[diag d, ω], [α, 0]]` is a case
  of Mathlib's `Matrix.invOf_fromBlocks₁₁_eq`. `ArrowMatrix` gives it over a division ring, with
  the inverse written out and both products checked.
- 🔄 **Conjugates and rank-one determinants.** `ParabolicFamily.units_conj_mul_conj_eq` is
  Mathlib's `Units.conj_pow` with `n = 2` plus centrality; `det_one_add_allOnes` is
  `Matrix.det_one_add_replicateCol_mul_replicateRow` for the all-ones matrix.
- 🔁 **Woodbury.** Mathlib has the matrix identity over a `Ring` (`Matrix.invOf_add_mul_mul`).
  `woodbury_corner` and `woodbury_sum` read one entry of it for the harmonic matrix
  `diag(b, c) + a 𝟙𝟙ᵀ` over a division ring. `BinomialSizeFamily.rankOne_mul_inv` and
  `rankOneInv_mul` are `Matrix.add_mul_mul_invOf_mul_eq_one` and its primed form for
  `diag Δ + u 𝟙𝟙ᵀ`, with the inverse written out entrywise.
- ➗ **Sums of inverses.** `a⁻¹ + b⁻¹ = a⁻¹ (a + b) b⁻¹` is Mathlib's `inv_add_inv'` /
  `invOf_add_invOf`. `three_term_inv` adds a middle term:
  `(p⁻¹ + q⁻¹ + r)⁻¹ = q (p r q + p + q)⁻¹ p`.
- 🔲 **`2 × 2` matrices.** `FinTwo` gives coordinate-free forms of Mathlib's `charpoly_fin_two`,
  `adjugate_fin_two` and `discr_fin_two`, such as `adjugate A = trace A • 1 − A` and the polarized
  Cayley–Hamilton identity.
- 🧮 **Adjugate.** Mathlib's `Matrix.adjugate_fin_succ_eq_det_submatrix` is stated for `Fin n.succ`.
  `Adjugate` gives the diagonal entries for an arbitrary index type.
- 📏 **Rank.** Mathlib has `LinearMap.rank_add_le`, but no `Matrix.rank_add_le` and no rank bounds
  for block triangular matrices. The same two statements over a field also appear, independently,
  in [complexitylib](https://github.com/SamuelSchlesinger/complexitylib).
  `Criterion.corankInvariant` uses Mathlib's `Matrix.rank_mul_le_left`, `rank_mul_le_right` and
  `rank_mul_eq_{left,right}_of_isUnit_det` for monotonicity and invariance; only the padding step
  (`rank (A ⊕ 1) = rank A + card`) uses the block bounds of `Rank`.
- 🎯 **Diagonal dominance.** `SizeChainPencil.det_matE_real_ne_zero` is an application of Mathlib's
  Gershgorin theorem (`det_ne_zero_of_sum_row_lt_diag`), not a new proof of it. That a diagonal
  matrix with distinct eigenvalues and the cyclic permutation matrix generate the full matrix
  algebra is classical; we did not find it in Mathlib, so `adjoin_cyc_diagonal_eq_top` proves it.
- 🧷 **Stable association.** Mathlib has no stable association of matrices or theory of firs.
  `Criterion` defines stable association and takes the localization lemma, the complete
  factorization and Cohn's Cor. 0.5.5 as a named hypothesis; `ChainPencilConditions` does not
  formalize Cohn's Theorem 5.8.8 (conditions ⇒ atom).
- 🔢 **Ordinals.** Mathlib's natural (Hessenberg) sum moved to
  [combinatorial-games](https://github.com/vihdzp/combinatorial-games) (`NatOrdinal`). `Hessenberg`
  defines it independently, inside Mathlib, through Cantor normal form; the two definitions are
  not proved equal here.
- 🪜 **Ordinal notations below `ε₀`.** Mathlib proves that its normal notations are well founded
  (`NONote.lt_wf`), but its order and normal form on `ONote` are defined through
  `ONote.repr : ONote → Ordinal`, so the proof uses `Classical.choice` (through `Ordinal.lt_wf`);
  so do `ONote.opow` and the core lemma `Nat.pow_lt_pow_right`. `Gentzen.Acc` and
  `Gentzen.TwoPow` redo well-foundedness, transfinite induction, `2^α` and the inequalities of
  Gentzen's cut elimination on a syntactic order and normal form, depending on `propext` only, and
  prove that they agree with Mathlib's (the bridge uses choice). Gentzen's consistency proof itself
  is not formalized here; it has been formalized in Coq by Bryce and Goré (arXiv:2603.00487).
- 📈 **Real special functions.** Mathlib defines `Real.artanh` but, at the pinned commit, has no
  derivative lemma for `artanh` or `tanh`; `CardyPDI.hasDerivAt_artanh` derives the first from
  `Real.artanh_eq_half_log`, and `RGFlow.rg_flow_tanh` uses `tanh = sinh / cosh`. The two-variable
  AM-GM step of `CriticalExponents` is Mathlib's `two_mul_le_add_of_sq_le_mul`, and three of its
  closed forms are instances of `div_mul_cancel₀` and `one_div_mul_cancel`, proved in one line.
  The files in `Analysis.TransformerAttention` port the repository
  [lean-taf](https://github.com/karlesmarin/lean-taf) (Lean `v4.30.0-rc2`), which stays as published.
- ⚛️ **Physics.** Mathlib has no physics; the area name follows
  physlib (`Physlib.Particles.StandardModel`), which formalizes the
  Higgs field and potential but, as far as we found, not these SMEFT coefficient identities.
  `HiggsSelfCouplings` is a set of identities in `ℝ`: the field-redefinition pieces are inputs,
  not derived, and the leading-order identities are consistent with the geometric SMEFT of
  Helset, Martin and Trott (arXiv:2001.01453) and not claimed as new. It and `GammaMobius` port
  two more files of lean-taf. `AllOrdersSelfCouplings` ports `smeft-lean` (Lean `v4.27.0`); there
  the `δκₙ` are rational functions of `α` taken as input, and only the identities between them are
  proved. `GaugeHiggsUnification` collects the certificates of a series of notes on
  six-dimensional `SU(4)` and `SU(7)` gauge-Higgs unification: finite integer checks by `decide`,
  a bialternant over Mathlib's `LaurentPolynomial` (Mathlib has no Schur polynomials), and counts
  over `Finset`; the physical inputs (weights, species vectors, gauge seeds) are data, not derived.
- 📚 **Multisets.** `JakobsOrder` builds on Mathlib's Dershowitz–Manna order
  (`Multiset.IsDershowitzMannaLT`) and characterizes it, on a linear order, as the lexicographic
  order from the largest element.

## 🧾 How the certificates are checked

Large integer facts (determinants of `9×9` matrices, finite tables) are proved with `decide` in the kernel, never with
`native_decide`. A determinant is not expanded: the file provides a factorization `L · M.submatrix σ σ = U` with `L`
lower and `U` upper triangular, and a general lemma (`det_eq_of_certificate`) turns it into `det M`. Checking the
certificate is a matrix multiplication.

## ➕ Adding a formalization

0. 🔎 Check that it is not already formalized: Mathlib (by name, by type pattern with
   [Loogle](https://loogle.lean-lang.org), and by meaning), the Mathlib Archive, other Lean libraries on GitHub, and
   the Isabelle [AFP](https://www.isa-afp.org). If it exists, use it and cite it; if a weaker version exists, say in
   the docstring what is added.
1. Put the file under `Formalizations/<Area>/<Topic>.lean`, following Mathlib's area names.
2. Write it as Mathlib does:
   - the copyright header;
   - `module`;
   - `public import` of the Mathlib modules it needs (never `import Mathlib`);
   - a module docstring `/-! # Title … ## Main results … ## References -/`;
   - `@[expose] public section`.
3. Add its main results to `FormalizationsTest/Axioms.lean`, and the import to `Formalizations.lean`.
4. `lake build` (no warnings) and `sh scripts/check_axioms.sh`.
5. Update this README: a row in the contents table, the count of main results, and the section on the relation to
   Mathlib when relevant.

## 📜 License

Carles Marín (investigador independiente, karlesmarin@gmail.com).
Apache 2.0, as Mathlib. Written with Claude (Anthropic) as an AI assistant; every statement is machine-checked.
