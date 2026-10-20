# 🧮 Formalizations

[![build](https://github.com/karlesmarin/formalizations/actions/workflows/build.yml/badge.svg)](https://github.com/karlesmarin/formalizations/actions/workflows/build.yml)

Lean 4 formalizations by Carles Marín, built on [Mathlib](https://github.com/leanprover-community/mathlib4) and
organized the same way: by mathematical area, one topic per file, every file with a module docstring listing its main
results.

- 🔧 Lean `v4.35.0`; Mathlib pinned in `lakefile.lean` (commit `f0b4c81`).
- ✅ No `sorry`, no `native_decide`, no new axioms. All 2194 main results depend only on the standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`), checked by `scripts/check_axioms.sh` on every push (CI).
  The choice-free core of `SetTheory.Ordinal.Gentzen` depends on `propext` alone.
- 🔬 Most files are the machine-checked core of a research note: the identities and finite certificates a paper
  relies on. The paper says exactly which statements are formalized and which are not.

📖 **API documentation** of every declaration (doc-gen4, rebuilt on every push):
<https://karlesmarin.github.io/formalizations/docs/>

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
| `Analysis.ODE.RungeKutta` | `OrderConditions` 🆕 | Butcher order conditions `γ(t) Φ(t) = 1` over planar rooted trees, reduced to a finite catalogue; Euler, Heun, RK4 (order 4, not 5), Dormand–Prince (order 5), Gauss–Legendre `s = 3` (order 4 in `ℚ(√15)`; order 6 in the denominator-cleared form over `ℤ[√15]` by `decide`); `Φ` invariant under permuting children |
| `Analysis.Polynomial` | `EnestromKakeya` 🆕 | Eneström–Kakeya: positive non-increasing coefficients give no zero in the open unit disk; zeros on the circle are roots of unity; strictly decreasing coefficients give none in the closed disk |
| `Analysis.Polynomial.RealRoots` | `RealRooted` 🆕 | Real-rooted polynomials (`Splits` over `ℝ`): closure, root count; sign alternation at `n + 1` points gives `n` roots; one root per gap of an increasing sequence gives real-rootedness; combinations of interlacing pairs |
| | `Sturm` 🆕 | Sturm's theorem: for squarefree `p`, the number of distinct roots in `(a, b]` is `V(a) − V(b)` for the Sturm sequence; the chain agrees with Mathlib's `Polynomial.sturmSeq`, and `V` is `List.signVariations` of the values |
| | `BudanFourier` 🆕 | Budan–Fourier: the number of roots in `(a, b]` with multiplicity is at most the drop of sign variations of `p, p′, p″, …`, with even difference |
| | `VirtualRoots.Basic` 🆕 | Virtual roots (González-Vega–Lombardi–Mahé): a degree-`d` polynomial has `d` of them, sorted, and they interlace with those of `p′` (Coste et al., Prop. 2.3) |
| | `VirtualRoots.Count` 🆕 | The number of virtual roots in `(a, b]` equals the Budan–Fourier drop `V(a) − V(b)` |
| | `Descartes` 🆕 | The Budan–Fourier count at `0` is Mathlib's `Polynomial.signVariations` |
| | `NewtonInequalities` 🆕 | Newton's inequalities `e_k² C(n,k−1) C(n,k+1) ≥ e_{k−1} e_{k+1} C(n,k)²` for real-rooted polynomials; log-concavity of the normalized means; real-rootedness survives `derivative` and `reverse` |
| `Analysis.SpecialFunctions.Airy` | `PowerSeries` 🆕 | The Airy recurrence `c_{k+3} = c_k/((k+2)(k+3))` gives `y'' = X y` in `ℚ⟦X⟧` |
| | `Basic` 🆕 | The real Airy functions are entire and solve `y'' = x y`; zeros unbounded below (Sturm comparison from Rolle and the IVT); dominant solutions do not decay; a recessive solution by reduction of order and an entire one; infinitely many quantum-bouncer levels |
| | `Perturbation` 🆕 | `w = u²` for `u'' = (x − E) u` satisfies `w''' = 4 (x − E) w' + 2 w` |
| `Analysis.SpecialFunctions.Dilogarithm` | `Basic` 🆕 | The real dilogarithm `Li₂`: `Li₂ 1 = π²/6`, derivative, Euler's reflection, Landen's identity, duplication, values at `φ⁻²`, `φ⁻¹`, `−φ⁻¹`; the Rogers dilogarithm, `L(φ⁻²) = π²/15` |
| | `Clausen` 🆕 | The Clausen function `Cl₂` and Catalan's constant `G = Cl₂(π/2)`; the Bernoulli parabola `∑ cos(nθ)/n²`; `Cl₂ > 0` on `(0, π)`; the two series never vanish together on `(0, 2π)` |
| | `ComplexBoundary` 🆕 | The complex dilogarithm on the closed disk: boundary values `π²B₂(x) + i Cl₂(2πx)`, no zero on the circle, derivatives of the branches `Li₂ + 4π²A + 2πiB log`; a zero of the imaginary part inside the disk (O'Sullivan) |
| | `FiveTerm` 🆕 | Abel's five-term relation for the Rogers dilogarithm |
| `Analysis.SpecialFunctions.Integrals` | `LogDivSelf` 🆕 | `∫₁ᴺ log x / x dx = (log N)² / 2` |
| `Analysis.SpecialFunctions.Trigonometric` | `FejerJackson` 🆕 | The Fejér–Jackson inequality `∑_{k=1}^M sin(kθ)/k > 0` on `(0, π)` |
| `Analysis.TransformerAttention` | `CriticalExponents` 🆕 | Phase A exponents of the attention decay: `2η² + ηγ_χ + 1 = 0`, `βχ = −1`, `α + χ = 2`, Rushbrooke and Josephson with `d = 1`, the Fisher residual, `η = 2γ` refuted on `(0, 1)`, AM-GM bound `γ_χ ≥ 2√2` |
| | `CardyPDI` 🆕 | `log PDI + ΔH_Cardy = 0` (Phase 7 form), residual `−log 2 / 2` (Phase 8 form); `d/dx artanh x = 1/(1 − x²)` |
| | `Pade` 🆕 | The `[2/2]` minus the `[1/1]` Padé approximant of `e^{−z}` is `2z³/((z + 2)(z² + 6z + 12))`; `θ_eff` closed form |
| | `CayleyMap` 🆕 | Fixed point `z* = (√17 − 3)/2` of `(2 − z)/(2 + z)`, `χ = (5 + √17)/4`, Floquet multiplier `(√17 − 9)/8` with `|μ| < 1` |
| | `RGFlow` 🆕 | `V = γ − γ³/3` gives `−V' ≠ β = −(1 − γ²)/2` (factor 2); the corrected `V = γ/2 − γ³/6`; `tanh(t/2 + c)` solves `γ' = (1 − γ²)/2` |
| | `GammaMobius` 🆕 | The Padé exponent `(2θ − T√2)/(2θ + T√2)` is the Möbius transform `(1 − u)/(1 + u)` of `u = T/(θ√2)` (needs `s² = 2`); the horizon `θ√2 (1 − γ)/(1 + γ)` at the Padé exponent equals `T`; `β = −2u/(1 + u)²` |
| | `HeatCapacity` 🆕 | Erratum to the Hagedorn heat capacity: both derivations give `(log N)²/12`, three times smaller than the published `(log N)²/4` |
| `Combinatorics.Additive` | `AddClosedInterval` 🆕 | An additively closed `S ⊆ ℕ` containing `[a, 2a]` contains `[a, ∞)` |
| `Combinatorics.Hall` | `Tight` 🆕 | The neighbourhood function of a set system is submodular; under Hall's condition tight sets are closed under union and intersection |
| `Combinatorics.Matroid` | `Transversal` 🆕 | Partial transversals of a finite set system are the independent sets of a matroid (augmentation through Hall's theorem and tight sets) |
| | `TransversalObstruction` 🆕 | The largest tight subset of a partial transversal decides every insertion and describes the matroid closure |
| `Combinatorics.SimpleGraph` | `OrientedIncMatrix` 🆕 | The oriented incidence matrix `N` and the Gram factorization `N Nᵀ = D − A` |
| `Combinatorics.SimpleGraph.Coloring` | `DeBruijnErdos` 🆕 | De Bruijn–Erdős: a graph is `n`-colorable iff all its finite induced subgraphs are |
| `Combinatorics.SimpleGraph.Ihara` | `Bass` 🆕 | Bass's formula `(1 − u²)^|V| det(1 − uB) = (1 − u²)^|E| det(1 − uA + u²(D − 1))` for the non-backtracking operator `B` |
| | `TraceFormula` 🆕 | `tr(Aᵏ)` counts closed walks; Bass's formula in `R[X]` and its derivative; the generating function of `tr(Bᵏ)` from `A` and `D` |
| | `NbWalkCount` 🆕 | `B` is the `0-1` matrix of the non-backtracking relation; `tr(Bᵏ)` counts closed non-backtracking dart sequences |
| | `NbVanishing` 🆕 | `tr(Bᵏ) = 0` for `0 < k <` girth |
| | `PathTreeLift` 🆕 | Tree-like closed walks (lifts to Godsil's path tree); acyclic edge support implies tree-like |
| | `TreeLikeWalks` 🆕 | Tree-like walk counts, matching power sums `p_k`; below the girth every closed walk is tree-like |
| | `PowerSumGenfun` 🆕 | The power-sum generating function of a multiset is a sum of geometric series |
| | `PowerSumLogDeriv` 🆕 | Power sums times `∏(1 − θX)` give the reverse of the derivative |
| | `ResolventDiag` 🆕 | `(∑ (Mᵏ)ᵢᵢ Xᵏ) · charpolyRev M = charpolyRev (M∖i)` |
| | `GodsilMoment` 🆕 | `∑_v μ(G − v) = X μ′(G)` |
| | `MomentBridge` 🆕 | Closed tree-like walks at `v` ↔ closed walks at the root of `T(G, v)`; Godsil's identity in charpoly form |
| | `MomentAssembly` 🆕 | Godsil's moment theorem: `p_k` = number of closed tree-like walks of length `k` |
| | `GapWindow` 🆕 | The gap law `tr(Aᵏ) − p_k = tr(Bᵏ)` for `1 ≤ k ≤ girth + 1` |
| `Combinatorics.SimpleGraph.MatrixTree` | `Basic` 🆕 | Reduced Laplacian `L₀ = N₀ N₀ᵀ`; `det L₀` as a sum of squared maximal minors (Cauchy–Binet) |
| | `SpanningTreeMinor` 🆕 | A squared maximal minor of `N₀` is `1` iff its edges span a connected subgraph, else `0` |
| | `Kirchhoff` 🆕 | Kirchhoff's matrix-tree theorem: `det L₀` = number of spanning trees, over any integral domain |
| `Combinatorics.SimpleGraph.MatchingPolynomial` | `Basic` 🆕 | The matching polynomial `μ(G) = ∑ (−1)^k m_k X^(n−2k)`: monic of degree `n`, isomorphism invariant, vertex-deletion recurrences for `m_k`, the partition function and `μ` |
| | `RamanujanBound` 🆕 | The bound `2√(k−1)` and the Ramanujan predicate; `2√(k−1) ≤ k` |
| | `Signing` 🆕 | Signed adjacency matrices |
| | `ExpectedCharpoly` 🆕 | `±1` edge signings and the statement of the Godsil–Gutman identity |
| | `GodsilGutman` 🆕 | Godsil–Gutman: the characteristic polynomials of all `±1` signings sum to `#signings • μ(G)`; matchings ↔ edge involutions |
| | `TwoLift` 🆕 | `charpoly [[B, C], [C, B]] = charpoly (B + C) · charpoly (B − C)` (2-lifts) |
| | `PathTree` 🆕 | Godsil's path tree `T(G, u)` is acyclic; prepending the root edge |
| | `MatchingSum` 🆕 | `μ` is multiplicative on disjoint unions, binary and indexed; the recurrence with the vertex removed |
| | `Divisibility` 🆕 | `T(G, u)` minus its root is the union of the `T(G − u, b)`; Godsil's identity `μ(G) μ(T − r) = μ(G − u) μ(T)` |
| | `ForestComponents` 🆕 | `μ(G) = ∏ μ(components)`; `μ(G) ∣ μ(T(G, u))` for connected `G` |
| | `ForestRealRooted` 🆕 | `μ(forest) = charpoly(A)`; Heilmann–Lieb: `μ(G)` is real-rooted for every finite graph |
| | `HeilmannLieb` 🆕 | Interlacing: if `q` alternates at the simple roots of `p`, then `X p − q` is real-rooted and interlaced by `p` |
| | `HeilmannLiebBound` 🆕 | Weighted Gershgorin (Collatz–Wielandt); Heilmann–Lieb bound: the roots of `μ(G)` lie in `[−2√(Δ−1), 2√(Δ−1)]` for maximum degree `≤ Δ`, `Δ ≥ 2` |
| `FieldTheory.Finite` | `CartierOperator` 🆕 | Over `ZMod p`, `(X d/dX)^[p−1]` kills the monomials with exponent divisible by `p` and fixes the others |
| | `OddPowerVandermonde` 🆕 | `k^(p−1)` as an indicator; residue classes in `[−m, m]` biject onto `ZMod p`; Vandermonde weights isolating a monomial; `det [l^e]_{l ≤ (p−1)/2, e odd} ≠ 0` |
| `GroupTheory.FiniteAbelian` | `OddCharacter` 🆕 | In a finite commutative group, a character `χ` with `χ s = −1` (`s² = 1`) trivial on `H` exists iff `s ∉ H`; odd characters of `(ZMod N)ˣ` trivial on `⟨u⟩` |
| `GroupTheory.GroupAction` | `Separation` 🆕 | P. M. Neumann's separation lemma: finite (pretransitive, `#A · #B < #Ω`) and infinite (infinite orbits) versions |
| | `SeparationDichotomy` 🆕 | Averaging identity `∑_g #(gA ∩ B)`; either some `g` separates `A` from `B` or all intersections have size `1` (exact factorization; tilings of `ℤ/n`) |
| | `SectionRegular` 🆕 | `(∑_g #(gA ∩ B)) · #Ω = #A · #B · #G` for transitive actions; section-regular partitions have parts of equal size |
| | `DistinguishingNumber` 🆕 | Distinguishing colorings and numbers; the collineation group of the Fano plane has distinguishing number `4` (by `decide`) |
| `LinearAlgebra` | `PointwiseProductSpan` 🆕 | Over an infinite field, if `V`, `W ≤ ι → K` are stable under a transitive group of signed permutations and `dim V + dim W > card ι`, the products `v * w` span `ι → K` |
| `LinearAlgebra.Matrix` | `FinTwo` | `2×2` identities: polarized Cayley–Hamilton, `det (A + B)`, iterated commutators |
| | `Adjugate` | Diagonal entries of the adjugate are principal minors |
| | `Rank` | `rank (A + B) ≤ rank A + rank B`; nullity under low-rank perturbation; block triangular bounds |
| | `Rank.Kronecker` | `rank (A ⊗ₖ 1) = card p * rank A` |
| | `Charpoly.Jacobi` | Resolvent series and Jacobi's formula for the derivative of the reversed charpoly |
| | `CauchyBinet` 🆕 | The Cauchy–Binet formula `det (A B) = ∑_S det A[·, S] det B[S, ·]` |
| | `WalkCount` 🆕 | Powers of the `0-1` matrix of a decidable relation count directed walks; `tr(Mᵏ)` via cyclic products |
| | `FreeLocus` | Rank and corank lemmas for block and low-rank perturbations |
| | `FreeLocusCertificate` | Soundness of the free-locus certificate ("not flip-poly") |
| `MusicTheory` | `IntervalVector` 🆕 | The interval vector of a pitch-class set in `ℤ/12` is invariant under transposition and inversion |
| | `Fourier` 🆕 | The DFT of a pitch-class set as `ZMod.dft` of its indicator: interval vector = inverse transform of `‖Â‖²`, homometry iff equal power spectrum, Babbitt's hexachord theorem, common tones under inversion from `Â²`, the triple correlation separates a homometric pair, `Â` is a complete invariant |
| | `ParityA6` 🆕 | `Â(6) = #even − #odd` pitch classes, so `Â(6) = 0` iff parity balance; the frequency `m` of `ℤ/(2m)` |
| | `MTransform` 🆕 | Multiplication by a unit permutes the Fourier coefficients (`M₅` exchanges `a₁` and `a₅`); `2‖Â(1)‖² = P + Q√3` with integers read from the interval vector, ordered in `ℤ√3` |
| | `Tiling` 🆕 | `A ⊕ B = ℤ/12` iff `#A · #B = 12` and `Â A k = 0 ∨ Â B k = 0` for `k ≠ 0`, via the discrete convolution theorem |
| | `InversionDFT` 🆕 | Translations are diagonal and inversion swaps `k ↔ −k` on the characters of `ZMod N`; the blocks `span {χ_k, χ_−k}` are dihedral-invariant, irreducible for `k ≠ −k`; self-paired frequencies `{0}` / `{0, N/2}` |
| | `CycleGraphSpectrum` 🆕 | Every circulant is diagonalized by the characters with eigenvalue the DFT of its first column; the characters form a basis; spectrum `2 cos(2πk/12)` of `cycleGraph 12`; abelian Cayley graphs |
| | `CRTCharacters` 🆕 | Under `ℤ/12 ≅ ℤ/3 × ℤ/4`, `χ_k` factors through `ℤ/3` iff `k ∈ {0, 4, 8}` and through `ℤ/4` iff `k ∈ {0, 3, 6, 9}`; the axes are generated by `4` and `3`, the tritone `6` has order `2` |
| | `NeoRiemannian` 🆕 | `T/I` (`DihedralGroup 12`) acts simply transitively on the 24 triads; the centralizer of the `T/I` group in `Equiv.Perm Triad` is the `PLR` group (Crans–Fiore–Satyendra duality); voice-leading sizes of `P`, `L`, `R` |
| | `SixThirty` 🆕 | The set class 6-30: orbit of size 12, stabilizer `{T₀, T₆}`, and its dual (centralizer of the induced action) has order 12, acts simply transitively and has a dihedral presentation |
| | `TonnetzSpectrum` 🆕 | The Tonnetz adjacency matrix is symmetric and bipartite; explicit eigenvectors for `±{3, √5, 2cos(π/12), √3, 1, 2cos(5π/12)}`; `√5 < 2√2` |
| | `TonnetzCompleteness` 🆕 | The 24 eigenvectors form a basis of `ℂ^(ZMod 12 × Bool)`, so these are all the eigenvalues |
| | `DiatonicScale` 🆕 | Myhill's property for the diatonic, not for the whole-tone scale; maximal evenness; generation by fifths; the three-gap theorem in `ℤ/12`; well-formedness |
| | `Temperament` 🆕 | 3-limit regular temperament: the Pythagorean comma generates the kernel of the 12-EDO val; 5- and 7-EDO do not temper it; 12-EDO is meantone; the 5-limit kernel has rank 2 |
| | `CircleOfFifths` 🆕 | The reduction `ℤ² → ℤ/12` kills the comma: twelve fifths close the circle and generate `ℤ/12`; four fifths are a major third |
| | `MaximalEvenness` 🆕 | For strictly convex `V`, the step-gap energy `∑ V(gᵢ)` is minimized exactly by the balanced gap configurations (necessary, not sufficient, for maximal evenness) |
| | `AllPairsEvenness` 🆕 | Double summation by parts for the all-pairs energy; for every convex `V` decreasing at the top, the pentatonic, whole-tone, diatonic and octatonic sets minimize it, uniquely up to `T/I` for strict `V`; censuses by kernel `decide` on bitmasks |
| | `CyclicHuddling` 🆕 | Fourier amplitudes of subsets of `ZMod N` (identified with `ZMod.dft`): transposition, complement, arcs, threshold exchange |
| | `CyclicHuddlingGeometry` 🆕 | Huddling for every `N ≠ 0`: `‖Â(B)(1)‖ ≤ ‖Â(arc #B)(1)‖`, equality exactly for translates of the arc; every unit frequency |
| | `CyclicHuddlingClosedForm` 🆕 | `‖Â(arc m)(1)‖ = sin(πm/N)/sin(π/N)` for `1 < N`; the sharp bound and its equality case; `m ↔ N − m` |
| | `Huddling` 🆕 | Twelve-tone Huddling; through `M₅`, chains of fifths maximize `‖a₅‖` |
| | `DiatonicExtremality` 🆕 | Among 7-sets the diatonic maximizes `‖a₅‖ = 2 + √3 = sin(7π/12)/sin(π/12)` and minimizes every convex all-pairs energy; the two equality classes coincide |
| | `ComplementEnergy` 🆕 | Complement transport of symmetric pair energies; constant row sums iff complementation preserves energy gaps / minimizers |
| | `TranslationInvariantEnergy` 🆕 | Difference potentials on finite abelian groups: one scalar controls the complement correction; a hexachord and its complement have equal energy |
| | `ExtremalityConnections` 🆕 | Homometric sets have equal energies; homometry survives complementation; the pentatonic results from the diatonic by complementation |
| | `MelodicWord` 🆕 | An odd-step statistic of melodic words is antisymmetric under retrograde and invariant under repeated notes; the pitch-class DFT is order-blind |
| `NumberTheory` | `DedekindSum` 🆕 | Dedekind sums via the sawtooth: reciprocity `s(h,k) + s(k,h) = (h² + k² + 1)/(12hk) − 1/4`, `s(h⁻¹, k) = s(h, k)`, the distribution relation, and the prime case of the Petersson–Knopp identity |
| | `FermatQuotient` 🆕 | Shift rule for the Fermat quotient: `q(l + p t) ≡ q(l) − t/l (mod p)` |
| | `OrderOfTwo` 🆕 | For `p ≥ 5`: some odd `j ≤ p − 4` has `2^j = 1` or some even `j ≤ p − 3` has `2^j = −1` iff `ord_p(2) ≢ 2 (mod 4)` |
| `NumberTheory.DirichletCharacter` | `AbelZero` 🆕 | For a primitive `χ` modulo odd `N`: `∑_c χ⁻¹(c) U(ζ^c) = 2 τ (1 − χ(2)) B_{1,χ}`, `U(Z) = 2Z/(Z² − 1)`, by finite Fourier analysis |
| `NumberTheory.MahlerBasis` | `FiniteMahlerBasis` 🆕 | The functions `x ↦ C(x.val, i)`, `i < N`, are a basis of `ZMod N → K` |
| | `ParityAndKernel` 🆕 | An even Mahler expansion with vanishing even coefficients is zero; the kernel of `Δ^r` on `ZMod (p^b) → K` (`char K = p`) is spanned by `C(x, i)`, `i < r` |
| | `LogarithmChange` 🆕 | `q ↦ q ∘ F` and `q ↦ q ∘ F⁻¹`, `F(z) = ((1+p)^z − 1)/p`, are unitriangular in the Mahler basis of `ℤ/p^t → k` |
| | `EvenFunctions` 🆕 | For an even Mahler expansion and odd `k`: `2 c_k = ∑_{i>k} (−1)^i C(i−1, i−k) c_i` |
| | `RankProfile` 🆕 | The arithmetic of the rank profile of Mahler matrices modulo `p` (seed rows, `k*`, rank), given the criterion as a hypothesis |
| `NumberTheory.NumberField.InvariantOrders` | `Saturation` 🆕 | For an order `M ⊇ ℤ[α]` of a quartic field (in coordinates `ℚ⁴`): `ℤ + ℤα + ℤα²` is saturated in `M` iff `M/ℤ[α]` is cyclic |
| | `TriangularBasis` 🆕 | From a triangular basis `ω_k = (αᵏ + P_k(α))/d_k`: `M/ℤ[α] ≅ ℤ/d₁ × ℤ/d₂ × ℤ/d₃`, `d₂ = [A ∩ V₂ : L₂]`, five equivalent conditions, the clause modulo `p` |
| | `BiquadraticIdentities` 🆕 | Louboutin's `T, U, V, W` for a biquadratic quartic: factorisation, twelve certificates and Cramer's rule, resolvent, `4 × 4` determinant forms |
| | `BiquadraticModel` 🆕 | Louboutin's Conjecture 6.1: `ℤ[α]` is Galois-invariant iff `Δ` divides `T, U, V, W`; `gcd(T, U, V, W) = abs θ` |
| | `CubicParity` 🆕 | `M³ = ±1`, `M ≠ ±1`, `F ∘ M = ±F` for the binary cubic form force `c` and `a + b` odd; a Möbius unit lemma |
| | `CyclicPrimeBezout` 🆕 | Bézout certificates for `Φ₅`, `Φ₇` against `(1+t)^ℓ ∓ 1` (`11`, `58`, `86`) and the congruence step for cyclic fields of prime degree |
| | `Discriminant` 🆕 | Biquadratic case: `disc A = g²`, `[A : ℤ[α]] = abs Δ / g`, `d₁ = 1`, the invariant factors `d₂ = m₀/h₀`, `d₃ = I h₀/m₀` |
| | `IndexLemmas` 🆕 | `det[γ_i(ω_l)] ∈ ℤ`; `det[γ_i(∑ m_lk αᵏ)] = Vand · det m`; the cyclic quartic identities `U² + Y² = N² Q₂` and two discriminant identities |
| | `ConjugatePowers` 🆕 | Cyclic prime degree: ratios of differences of conjugates are units; `ℤ[conj αᵏ] ≠ ℤ[conj α]` for `k ≥ 2` under a valuation condition; `ℤ[conj εᵏ] = ℤ[ζ₅]` for `5 ∤ k` |
| | `IndexFormula` 🆕 | For both Galois groups: `[A : ℤ[α]] = J L²/H`, `disc A = D_α (H/(J L²))²`, `d₁ = 1`, `d₂ = LG/H`, `d₃ = JL/G`, `A ∩ (ℚ + ℚα) = ℤ + ℤα` |
| `NumberTheory.NumericalSemigroup` | `GenusBound` 🆕 | A numerical semigroup generated in degrees `≤ D` has genus `g` with `2g ≤ (D − 1)(D − 2)`, equality only for `⟨D − 1, D⟩` |
| `NumberTheory.PrescribedMoments` | `Biquanimous` 🆕 | Every 4-part partition of `n ≥ 3` splits into two halves of equal sum iff `n ∈ {3, 4, 6}`; counts of signed zero sums |
| | `CubicModels` 🆕 | Nodes of the Cayley and Segre cubics; Newton's identities for `e₁ = e₃ = 0`; `(p−1)/2` and `(p−1)(p−3)/8` subsets of `ZMod p` of size 3 and 4 with both moments zero |
| `NumberTheory.SymplecticCharacterOrders` | `Arithmetic` 🆕 | When `p ∣ ∑_{j≤m} j²` (`p ≥ 5`, `3`, `2`), the cases `q = p, 25, 27`; half period and doubling of the column lattices |
| | `Multipliers` 🆕 | The rank of `[½(s(ℓu⁻¹c) − s(u⁻¹c))]` is `d − δ_ℓ`, given the rank of `[s(u⁻¹c)]` |
| | `Segments` 🆕 | Amiot's lemma (an interval of `ℤ/n` is not stable under a unit `≢ ±1`); `#{j ≤ m : j ≡ ±c}` is stable under a unit `≢ ±1` iff `n` divides `2m`, `2m+1` or `2m+2` |
| | `SupportAndIndex` 🆕 | Closed form of `S(c) = ∑_{j≡c} j − ∑_{j≡−c} j`; the arithmetic of the support of the conductor and of the index |
| | `LinearCoefficient` 🆕 | Constant and linear parts of `e_k(2 + x_1, …, 2 + x_m)`, polynomial and `MvPolynomial` forms |
| `NumberTheory.WeightedCharacterSums` | `DigitRecursion` 🆕 | For `χ` completely multiplicative and periodic off the multiples of `q`, `S(m) = ∑_{n≤m} n χ(n)` satisfies `S(qk + r) = s q S(k) + k(T_q + q C(r)) + T(r)`; zeros propagate along base-`q` digits; complete sequences and their pairs version (names `SegmentoII.*` as cited by the paper's blueprint) |
| | `DigitCorollaries` 🆕 | The digit recursion over any commutative ring; families of zeros of `S`, digit blocks, the identities `4χ(2)T = 2(1 − χ(2))T_f` and `fχ(2)C = (1 − 2χ(2))T_f`, the case `χ(2) = 1` |
| | `WeightedHalfSum` 🆕 | For an odd Dirichlet character modulo odd `f`: `∑_{c ≤ (f−1)/2} c χ(c) = (f/2) B_{1,χ} (χ(2)⁻¹ − 1)` and the unweighted twin |
| | `SubsetSumsAndRows` 🆕 | Growth of intervals of subset sums; `∑_{c≤m} c ε(c) ≡ (n² − 1)/8 (mod 2)` for signs `ε`, so it vanishes only if `(2/n) = 1` |
| | `NoZeros` 🆕 | `∑_{n≤m} n (n/q) ≠ 0` for all `m ≥ 1` when `q = 179, 227` (the symbol extended completely multiplicatively with `χ(q) = 1`): a finite certificate checked by `decide +kernel` |
| `Physics.Particles.GaugeHiggsUnification` | `NotchCentreCharge` 🆕 | The bialternant `N = det (yᵢ^{μⱼ})` of `s_λ(1, −1, t, t⁻¹)` over `ℤ[T;T⁻¹]` vanishes iff `Odd b ∧ ((Odd a ∧ Odd c) ∨ a = c)`; `D(−t) = (−1)^{a+2b+3c} D(t)`; degenerate irreps have even centre charge `a + 2b + 3c` |
| | `BlindCount` 🆕 | The blind set in partition coordinates (two branches) equals `N = 0`; `l₁` is odd on it; the shell `l₁ = 2k+1` has `⌈(k+1)²/2⌉` blind partitions |
| | `CosetCensus` 🆕 | Boundary conditions `[p; q, r; s]` on `S¹/ℤ₂`: the label `(p+q, q+s)` is a complete invariant of the equivalence, `(N+1)²` classes, of which `⌊(N+1)²/2⌋` have a reflection-coset sector |
| | `OddEighths` 🆕 | `SU(7)` moments: `8D ≡ 2A₄ + 3 (mod 6)` and `2W` odd for every bulk content, for both gauge seeds; `8D` odd if the gauge contribution is odd |
| | `R60JointExistence` 🆕 | Farkas certificate: four anomaly-neutral additions realize `±Θ₀₁`, `±Θ₂₃`, so the localized tadpole never obstructs an anomaly-free completion of `(3, 60)` |
| | `R60LocalizedAnomaly` 🆕 | Localized cubic anomalies of the `60` of `SU(4)`: numerators `−6`, `6`; both independent of the Wilson line, the mixed `C² · U(1)` piece not |
| | `ScalarCPSource` 🆕 | `Im (λ (conj v₁ · v₂)²) = 0` for real `λ, v₁, v₂` |
| | `InternalU1MixingNoGo` 🆕 | `Even n₃` and `3 n₃ − 2 n₄ = 1` are incompatible |
| | `SU7WeightChannels` 🆕 | Charge channels of `7`, `28`, `48`, `84` of `SU(7)` from their weights; gauge coefficients of both seeds (shift `Δ(8D) = 9`, `ΔA₄ = 9/2`, `ΔW = 0`); the computed moments `(8D, 2A₄)` of the eight bulk multiplets equal the data of `OddEighths` |
| | `USp4WeightMoments` 🆕 | The `13`-dimensional contents `5 + 4 + 4` and `1 + 1 + 1 + 5 + 5` of `USp(4)` have equal weight moments up to degree `3` and differ by `(0, 0, 24, 0, 0)` in degree `4`; dimension, second and fourth moments determine the multiplicities |
| | `HiddenCentreBasis` 🆕 | In the `(1, 5, 4)` basis, dimension, second moment and central action `a + 5b − 4c` determine the multiplicities; the two candidates have central actions `−3`, `13` |
| | `TorusTwistBasis` 🆕 | `2 · periodic = dim + center` in the `(1, 5, 4)` basis; dimension, second moment and periodic count determine the multiplicities |
| | `ChargeQuantization` 🆕 | `p A + q B + r C` is integral on the cocharacters of `S(U(2) × U(3))` iff `t ∣ p, q, r`; the transfer coefficients `(16 − 3p, −3q, −3r)` never satisfy `x + y + 2z = 0` (residue `1 mod 3`) |
| | `WallDeterminants` 🆕 | Rank-one wall determinant `a b x²`; neutral `3 × 3` Gram determinant `a b x² (k + a(1 − d²))` and its sum-of-squares form; rationalized gap `(r + t − z)(r + t + z) = 4rt(1 − c)` |
| | `AlignmentPolynomials` 🆕 | `9p⁴ + 2p²q² + 9q⁴ = 5(p² + q²)² + 4(p² − q²)²`; descent numerators `4e²(e² − 8)`, `−16e²` |
| | `EffectivePotentialAlgebra` 🆕 | Coefficients of the potential in `h r`; third and fourth logarithmic derivatives `c − 3ab + 2a³`, `d − 4ac − 3b² + 12a²b − 6a⁴`; `2 × 2` covariance pullback and minors |
| | `LinearResponseIdentities` 🆕 | The two-pole linear response is independent of the quartic coupling; `(a + b)(a u² + b v²) − (a u + b v)² = a b (u − v)²` |
| `Physics.Particles.StandardModel.AxionCouplings` | `SpinPeriod` 🆕 | Periods `p a + q b + 2 r c ∈ t ℤ` iff `t ∣ p, q, 2r` (spin) versus `t ∣ p, q, r`; for the `q = 6` row of Choi–Forslund–Lam–Shao the spin condition is `18 K₂ + 24 K₃ + K₁ ≡ 0 (mod 36)` and forces `6 ∣ K₁` |
| `Physics.Particles.StandardModel.SMEFT` | `AllOrdersSelfCouplings` 🆕 | All orders in `α`: `δκ₄ − 6 δκ₃ = α(3α³ + 30α² + 35α − 4)/(3(α+1)²)`, `δκ₅ − 15 δκ₃`, `δκ₆ − 15 δκ₃` in closed form; dimension-8 breaking at first order; catalog `δκ₇ … δκ₁₂` with `δκ₁₁ = δκ₁₂` |
| | `TopEdgeCollapse` 🆕 | At the degree-12 edge the 11- and 12-point contributions coincide; the 12-point one is `246400 α⁴/(1 + α)²` |
| | `HiggsSelfCouplings` 🆕 | Tree-level matching of the Higgs self-couplings: `O_φ = (vh + h²/2)³`; `c_φ` pieces with `δκ₄ = 6 δκ₃`; `δκ₄ − 6 δκ₃ = −(4/3)(v²/Λ²) C_{H,kin}`, so the ratio is `6` iff `C_{H,kin} = 0`; leading order `δκ₅ − 15 δκ₃ = δκ₆ − 15 δκ₃ = −5 (v²/Λ²) C_{H,kin}` |
| `Physics.QuantumMechanics.SpeedLimit` | `MargolusLevitin` 🆕 | `1 − (2/π)(x + sin x) ≤ cos x`; Margolus–Levitin: orthogonality at time `τ` forces `π ≤ 2⟨E⟩τ` (`ℏ = 1`) |
| | `MandelstamTamm` 🆕 | `L¹` Mandelstam–Tamm bound `1 ≤ D₁ τ` with `D₁` the mean absolute energy deviation |
| | `AntipodeFloor` 🆕 | `‖∑ wⱼxⱼ/(1 − xⱼz)‖ ≥ ∑ wⱼxⱼ/(1 + xⱼ)` on the unit circle for `wⱼ ≥ 0`, `xⱼ ∈ [0, 1)` |
| `Physics.Supergravity.AnomalyQuantization` | `U2Example` 🆕 | The `U(2)` form `(2 b₀ (m − n)² + b₁ (m + n)²)/8` of Monnier–Moore–Park is integer-valued iff `2 b₀ + b₁ ≡ 0 (mod 8)`; `4 ∣ b₀ ∧ 8 ∣ b₁` is sufficient, not necessary (`(1, 6)`); two samples decide integrality with rational coefficients |
| `Probability.Distributions.Superstatistics` | `LaplaceMixture` 🆕 | A centered Gaussian with exponentially distributed variance (rate `λ`) has a Laplace marginal with rate `√(2λ)`; the Glasser integral `∫ v^{−1/2} e^{−a/v − bv} dv = √(π/b) e^{−2√(ab)}` |
| | `StudentMixture` 🆕 | The Gaussian–Gamma precision mixture is the Student-t density (with the `b^a` normalization); `E[Z²] = 1`, `E[Z⁴] = 3`; variance mixtures `√V · Z` have excess kurtosis `3 Var(V)/E[V]² ≥ 0` |
| `RepresentationTheory.Symplectic` | `ResidueCapacity` 🆕 | The type-C residue identity `2R + 2m = P(x)² + P(2x)` in `ℤ[G]`; `N_q(x) ≥ N_q(ρ)` with equality iff the capacities hold, and then `R x = R ρ` |
| `RingTheory.AffineSemigroup` | `OrbifoldProduct` 🆕 | `(S¹/ℤ₂)^k`: `4^k` distinct generators, `dim = ∑ C(k,j)2^j = 3^k`; `4^k > 2·3^k − 2` for `k ≥ 3`, so (with Fischer–Morris–Shapiro's Cor. 3.4 as hypothesis) not a complete intersection; every generator spans an extreme ray (one-hot block vectors of distinct choices); and too many edges to be a cut ideal |
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
| `RingTheory.HopfAlgebra.ConnesKreimer` | `Coproduct` 🆕 | Planar rooted trees and the admissible-cut coproduct through the `B₊` cocycle; coassociativity up to `List.Perm` (`coprod_coassoc`) |
| | `Basic` 🆕 | The Connes–Kreimer–Foissy algebra `H k = MonoidAlgebra k (FreeMonoid RTree)` is a Mathlib `HopfAlgebra` (`instCKHopf`); both antipode axioms |
| | `Adams` 🆕 | Adams operators `Ψₙ = id^{⋆n}`, `Ψ₋₁ = S`; local nilpotency of `J = id − u∘ε`; the first Eulerian idempotent `e⁽¹⁾ = log_⋆ id` fixes primitives |
| | `Abelianization` 🆕 | The commutative quotient `H k / ⟨ab − ba⟩` (`RingQuot`) is a `HopfAlgebra` (`instHabHopf`) |
| | `Eulerian` 🆕 | On the commutative quotient: `Ψⁿ` are algebra maps, `Ψᵖ ∘ Ψ^q = Ψ^{pq}`, `Ψⁱ ∘ e⁽¹⁾ = i e⁽¹⁾`, and `e⁽¹⁾ ∘ e⁽¹⁾ = e⁽¹⁾` (`eulerian1_idem_ab`) |
| `RingTheory.Polynomial.Chebyshev` | `Docagne` 🆕 | d'Ocagne's identity `S p S (q − 1) − S q S (p − 1) = −S (p − q − 1)` for Mathlib's `Chebyshev.S` |
| `RingTheory.Polynomial.CoefficientRing` | `Division` 🆕 | For monic `F`, `G` with `F G ∈ ℤ[X]`, the subrings generated by the coefficients agree, `A F = A G` |
| | `Operations` 🆕 | Segment polynomials at a primitive `2q`-th root of unity: `A_SU(2m+1) = A_Sp(2m)`, `A_SU(n) = A_SU(q−n)`, `A_SU(n+q) = A_SU(n)` |
| | `Quadratic` 🆕 | `A_SU(n) = A_Sp(q−n−1)` for `q` odd, `n < q` even; for `B = R ⊕ θR`, `θ² = c`: `Algebra.trace` is `2 re + b im`, the trace dual is `(2θ)⁻¹B`, `Ω_{B/R} ≃ B ⧸ (2θ)` |
| | `StableFamilies` 🆕 | If `r` divides `n − 1`, `n` or `n + 1`, the exponents of the `SU(n)` segment modulo `q'` are a multiset invariant under all units (three cases, from one periodicity statement) |
| | `StableIntervals` 🆕 | An affine bijection of `ZMod n` fixing a block of `k` consecutive residues, `2 ≤ k ≤ n − 2`, has `u = ±1`; two Laurent identities for `a1`, `a2` of the spectrum `t^(L−1−2j)` |
| | `Recentering` 🆕 | With `ι μ = μ⁻¹`, a unit `μ^k a ∈ B` (`ι a = a`, `gcd(2k, n) = 1`) puts `μ` in `B`, and `(R[μ])^ι = R` |
| | `Residues` 🆕 | The two top coefficients of `(X − 1)(X^r − 1)^N` and `(X^r − 1)^N /ₘ (X − 1)`; `τ₊, τ₋ ∈ A` from units of `A` |
| `RingTheory.PowerSeries` | `LogMul` 🆕 | `logOf (f g) = logOf f + logOf g` and `logOf (fⁿ) = n • logOf f` for constant coefficient `1`, by uniqueness of antiderivatives; coefficient form for `(1 + X)ᵖ` |
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
  `SpinPeriod` and `U2Example` are integrality criteria for quadratic forms on cocharacter and
  period lattices, for the axion-gauge couplings of Choi, Forslund, Lam and Shao
  (arXiv:2309.03937) and the anomaly coefficients of Monnier, Moore and Park (arXiv:1711.04777);
  the dictionary from characteristic classes to these forms is an input.
- 🌳 **Rooted trees and Hopf algebras.** Mathlib's `RootedTree` (`Mathlib.Order.SuccPred.Tree`) is
  a tree given by its ancestorship order on a carrier type; it has no cuts, no planar structure
  and no isomorphism classes, so `ConnesKreimer` and `RungeKutta` use an inductive type of planar
  trees instead. The `Coalgebra`, `Bialgebra`, `HopfAlgebra`, `MonoidAlgebra`, `RingQuot` and
  convolution (`WithConv`) of Mathlib are used as they are; Mathlib has no Hopf algebra of trees.
  These files port [connes-kreimer-lean](https://github.com/karlesmarin/connes-kreimer-lean),
  [runge-kutta-order-conditions-lean](https://github.com/karlesmarin/runge-kutta-order-conditions-lean)
  and [airy-bouncer-lean](https://github.com/karlesmarin/airy-bouncer-lean) (Lean `v4.30.0-rc2`),
  which stay as published; the adaptation of `ConnesKreimer` to `MonoidAlgebra` as a structure
  follows the port of the same code in [lean-pool](https://github.com/LeanPool/lean-pool).
- 📐 **Power-series logarithm.** Mathlib has `PowerSeries.logOf`, `logOf_exp` and
  `derivative_log_mul_one_add_X`; the original `logOf_exp` and `(1 + X) · (log(1 + X))' = 1` are
  therefore not ported. `LogMul` adds the additivity `logOf_mul` and the power law `logOf_pow`.
- 〰️ **Airy functions.** Mathlib has no Airy functions and no Sturm comparison theorem; `Airy.Basic`
  builds the oscillation argument from Rolle's theorem and the intermediate value theorem.
- 🎼 **Music theory.** Mathlib has no music theory. The Fourier files use Mathlib's discrete
  Fourier transform `ZMod.dft` (`Fourier.Ahat` is `ZMod.dft` of the indicator, and
  `CyclicHuddling.Ahat_eq_dft` identifies the set-sum form with it); `InversionDFT`,
  `CycleGraphSpectrum` and `TonnetzCompleteness` work with the characters `j ↦ stdAddChar (j * k)`
  as vectors and obtain their basis from `ZMod.dft` (`dftChar_eq_smul_invDFT`); Mathlib's
  `ZMod.dft_comp_neg` is the transform-level form of `InversionDFT.inv_dftChar`. `Matrix.circulant`,
  `SimpleGraph.cycleGraph`, `DihedralGroup` and `Subgroup.centralizer` are used as they are; we did
  not find in Mathlib that the centralizer of a transitive action is semiregular, which
  `NeoRiemannian` proves for its use. [Prismriver](https://arxiv.org/abs/2606.19936) (Aniva–Wang) is a
  Lean 4 library of music theory; the overlap with it was not audited. The censuses of
  `AllPairsEvenness` range over all `k`-subsets of `ℤ/12`; they are checked by `decide` in the kernel
  on a bitmask encoding, with a proved bridge to the `Finset` statements. These files port the
  repository [music-math](https://github.com/karlesmarin/music-math) (Lean `v4.30.0-rc2`), which stays
  as published; there the censuses used `native_decide`.
- 📉 **Real roots.** Mathlib has Descartes' rule of signs (`Polynomial.signVariations`,
  `Polynomial.roots_countP_pos_le_signVariations`), sign variations of lists (`List.signVariations`)
  and the algebra of the Sturm sequence (`Polynomial.sturmSeq`), but not Sturm's theorem, the
  Budan–Fourier theorem, virtual roots or Newton's inequalities. `Sturm` keeps its own chain and
  proves that it is `Polynomial.sturmSeq` for `p ≠ 0` (`sturmAux_eq_sturmSeq`) and that its count is
  `List.signVariations` of the values (`signVarAt_eq_signVariations`). Sturm–Tarski and Budan–Fourier
  are formalized in Isabelle/HOL by Li and by Li–Paulson. These files port part of the repository
  [godsil-gutman-lean](https://github.com/karlesmarin/godsil-gutman-lean) (Lean `v4.30.0-rc2`), which
  stays as published.
- 🔗 **Matching polynomials.** Mathlib has matchings as subgraphs (`Subgraph.IsMatching`) but no
  matching polynomial, path tree, Godsil–Gutman identity or Heilmann–Lieb theorem. `MatchingPolynomial`
  counts matchings as sets of pairwise disjoint edges; it uses Mathlib's `SimpleGraph.sum`,
  `deleteIncidenceSet` (vertex deletion keeps the vertex, isolated), Gershgorin, and
  `Matrix.IsHermitian.splits_charpoly` (of which `MSS.charpoly_symmetric_realRooted` is a one-line
  corollary). The files port the matching-polynomial part of godsil-gutman-lean.
- 🕸️ **Ihara zeta and the matrix-tree theorem.** Mathlib has the Laplacian, the degree matrix
  (`SimpleGraph.degMatrix`, used by `Ihara.Bass`), the unoriented incidence matrix and walk counting
  by powers of the adjacency matrix of a simple graph, but no Cauchy–Binet formula, oriented incidence
  matrix, matrix-tree theorem, Hashimoto operator or Ihara zeta function. `WalkCount` is the analogue
  of `adjMatrix_pow_apply_eq_card_walk` for directed relations. The resolvent series, Jacobi's formula
  and Newton's identity used by `Ihara` are those of `LinearAlgebra.Matrix.Charpoly.Jacobi`, and the
  diagonal adjugate entry is `Matrix.adjugate_apply_self_eq_det_submatrix`.
- ∿ **Dilogarithm and quantum speed limits.** Mathlib has no polylogarithm, Clausen function or
  Catalan's constant; `Dilogarithm.Clausen` derives the real part on the circle from Mathlib's
  Fourier expansion of the Bernoulli polynomials (`hasSum_one_div_nat_pow_mul_cos`) and
  `Li₂ 1 = π²/6` from `hasSum_zeta_two`. Mathlib has no quantum mechanics; `SpeedLimit` states the
  bounds for a discrete spectral measure with real sums. Eneström–Kakeya and Fejér–Jackson were not
  found in Mathlib.
- 🧩 **Permutation groups, transversals, colorings.** `Separation` applies Mathlib's B. H. Neumann
  covering lemma (`Subgroup.exists_index_le_card_of_leftCoset_cover`); `DeBruijnErdos` applies
  Mathlib's Rado selection principle (`Finset.rado_selection`, whose docstring cites de Bruijn–Erdős)
  but Mathlib does not state the coloring theorem; `Transversal` builds a Mathlib `Matroid` from
  `IndepMatroid` and Hall's theorem (`Finset.all_card_le_biUnion_card_iff_existsInjective'`);
  `Docagne` extends Mathlib's `Chebyshev.S_sq_add_S_sq`. Mathlib has no distinguishing numbers or
  transversal matroids.
- 🎲 **Gaussian mixtures.** Mathlib has the Gaussian, exponential and Gamma densities
  (`gaussianPDFReal`, `exponentialPDFReal`, `gammaPDFReal`), the Gaussian moment generating function
  and variance, and Fubini's `integral_prod_mul`, all used here; it has no Laplace or Student-t
  distribution and no mixture identities.
- 📚 **Multisets.** `JakobsOrder` builds on Mathlib's Dershowitz–Manna order
  (`Multiset.IsDershowitzMannaLT`) and characterizes it, on a linear order, as the lexicographic
  order from the largest element.
- 🔢 **Character sums and digit recursions.** Mathlib has Dirichlet characters, `legendreSym`,
  `jacobiSym` and the subset sums `Finset.subsetSum` (which `SubsetSumsAndRows.SS` is, by `abbrev`),
  but no generalized Bernoulli number `B_{1,χ}` and no value of a Dirichlet `L`-function at `s = 0`
  for odd `χ`; `WeightedHalfSum` takes `B_{1,χ} ≠ 0` as a hypothesis where it is needed. The
  certificates of `NoZeros` are checked by `decide +kernel`, with a proved bridge from the
  computable symbol to `legendreSym`.
- 🔢 **Orders generated by conjugates.** Mathlib has orders and `AddSubgroup.relIndex` (with
  `relIndex_eq_natAbs_det`, used for the indices), but no theory of the order generated by the
  conjugates of an algebraic integer. `InvariantOrders` works in abstract models (a domain with
  ring endomorphisms permuting the conjugates and "fixed ⇒ integer"; coordinates in `ℚ⁴`); the
  triangular basis of the order is an explicit hypothesis (`Louboutin.Triang`). Mathlib has no
  Dedekind sums; `DedekindSum` proves reciprocity directly.
- 📐 **Mahler bases.** Mathlib has Mahler's theorem for continuous functions on `ℤ_[p]`
  (`NumberTheory.Padics.MahlerBasis`) and forward differences `fwdDiff`; `MahlerBasis` works with the
  finite basis of `ZMod N → K` instead. `AbelZero` uses Mathlib's Gauss sums
  (`gaussSum_mulShift_of_isPrimitive`); `B_{1,χ}` is defined there and reused by `WeightedHalfSum`.
- 🧮 **Coefficient rings.** Mathlib has `Polynomial.restriction` (a polynomial over the subring
  generated by its coefficients), `Polynomial.toSubring` and `map_divByMonic`, used by
  `CoefficientRing.Division`. Mathlib's `QuadraticAlgebra.trace` is defined as `2 re + b im`;
  `Quadratic.trace_quadraticAlgebra` proves that `Algebra.trace` equals it, which we did not find
  in Mathlib.

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
