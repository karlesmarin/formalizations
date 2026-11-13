# 🦉 Isabelle formalizations

Isabelle/HOL versions of some Lean modules of this repository, and entries prepared for the
[Archive of Formal Proofs](https://www.isa-afp.org). They are independent of the Lean build (`lake` only builds
`Formalizations.*`).

- 🔧 Isabelle2026; the `AFP/` sessions on HOL alone also build with Isabelle2025-2. `Kirchhoff_Matrix_Tree` needs
  other AFP entries, and the current AFP release (2026-10-26) is for Isabelle2026.
- ✅ No `sorry`, no `quick_and_dirty`, no external provers (no `smt`); finite facts by `code_simp` (the simplifier),
  never `eval`.
- 🔗 Each port names the Lean module it follows; the AFP entries go further than the Lean (statements for every `n`).

## 🗂️ Ports of Lean modules

| Session | Port of | What is proved |
|---|---|---|
| 📈 `HausdorffFloor/` (`Hausdorff_Floor`) | `Formalizations.Analysis.SpecialFunctions.Polylog.HausdorffFloor` | per-term bound `1/(1+x) ≤ Re (1/(1 − x z))`; a uniform gap `c ≤ |1 − t z|` on `[0,1]` for `z ≠ 1` on the unit circle; for a finite measure and `τ ∈ [0,1)` a.e., the moment series converges at every `z ≠ 1` of the unit circle to `∫ 1/(1 − τ z)`, and its modulus is at least `∫ 1/(1 + τ)` |
| 📈 `PolylogFloor/` (`Polylog_Floor`, on `Hausdorff_Floor`) | `Formalizations.Analysis.SpecialFunctions.Polylog.HausdorffFloor`, `Formalizations.Physics.QuantumMechanics.SpeedLimit.ZetaStateFloor` | the Gamma-density measure `x^(s−1) e^(−x)/Γ(s)` with `τ = e^(−x)` has moments `(k+1)^(−s)` (`gamma_moment`); `η(s) ≤ |Li_s z|` on the unit circle for real `s > 0`, `z ≠ 1` (`polylog_circle_floor`); `η(s) = (1 − 2^(1−s)) ζ(s)` for `s > 1` (`eta_eq`); the zeta state never gets closer to orthogonality than `1 − 2^(1−s)` (`zeta_state_floor`) |
| ⚖️ `AntipodalExamples/` (`Antipodal_Examples`) | `Formalizations.Physics.QuantumMechanics.SpeedLimit.DominantPopulation`, `Formalizations.Analysis.SpecialFunctions.Polylog.AntipodalCounterexamples` | a population above 1/2 keeps the autocorrelation at least `2 p j − 1` (`two_mul_sub_one_le_norm_suminf`); the exact examples: three times monotone (`cex3_*`) and log-convex (`cexLC_*`) coefficients whose modulus on the unit circle drops below its value at `z = −1` (`cex3_normSq`, `cexLC_normSq`) |
| ⏱️ `ZielinskiZych/` (`Zielinski_Zych`) | `Formalizations.Physics.QuantumMechanics.SpeedLimit.ZielinskiZych` | the Zieliński–Zych inequality and bound for `0 < α ≤ 1` (`zz_inequality`, `zielinski_zych`); the fractional moments tend to `1 − p 0` as `α → 0⁺` (`tendsto_fractional_moment`, by Tannery's theorem), and the bound tends to `+∞` or `0` as `p 0` is above or below `1/2` |
| 🧩 `FriezeDominance/` (`Frieze_Dominance`) | `Formalizations.Combinatorics.Frieze.IntegerDominance`, `…Frieze.TwoSignChanges` | two integer Conway–Coxeter friezes of width 11 (quiddities `lower`, `upper`) whose middle rows are strictly ordered at all 14 positions; two of width 12 whose rows 6 differ with no zero and exactly two cyclic sign changes (`Frieze_Two_Sign_Changes`); finite computations by `code_simp` |
| 〰️ `YoungCosine/` (`Young_Cosine`) | — (Isabelle only; the companion Fejér–Jackson inequality is in Lean: `Formalizations.Analysis.SpecialFunctions.Trigonometric.FejerJackson`) | Young's inequality (1913): `−1 ≤ Σ_{k=1}^{n} cos (k x) / k` for every `n` and real `x` (`young_cosine`), by a global minimum on `[0, 2π]` and a double Abel summation at the critical points |
| 🧩 `FriezeFamily/` (`Frieze_Family`) | — (Isabelle only; the first version of `AFP/Integer_Frieze_Rows`) | friezes as lattice polygons; ear insertion keeps friezes; antipodal ear insertion and the diameters; for every `t`, two integer friezes of width `11 + 2t` whose middle rows (diameters) are strictly ordered (`strictly_ordered_middle_rows`); bridge `entry_is_continuant` (entries are continuants of the quiddity `a_k = det (V_(k-1), V_(k+1))`) and the corollary in that language (`strictly_ordered_middle_rows_continuants`) |
| 🔺 `ZLThreeBlockFamily/` (`ZL_Three_Block_Family`) | — (Isabelle only) | the algebraic part of Proposition 6.3 of *Why three blocks?* (doi:10.5281/zenodo.23778502): the two closed forms of the deficit `n/3 − 1/2 − M` of the three-block family (`identity_case1`, `identity_case2`) and its non-negativity for block sizes `x ≥ y ≥ z ≥ 1` (`deficit_case1`, `deficit_case2`); the construction behind `M` and the maximizers are on paper |

The Isabelle proof of the floor avoids Abel's theorem: the partial sums are integrals of geometric sums and converge by dominated convergence.

## 🏛️ Entries prepared for the Archive of Formal Proofs (`AFP/`)

Sessions in the AFP format (`chapter AFP`, with a document: prose, figures, bibliography).

| Session | Depends on | What is proved | Status |
|---|---|---|---|
| 🧩 `Integer_Frieze_Rows` | HOL | for every even `n ≥ 14`, two integer Conway–Coxeter friezes of width `n − 3` whose middle rows are strictly ordered (a negative answer, for integers, to Problem 1 of Tabachnikov, *Math. Intelligencer* 40 (2018)) | 📤 submitted |
| 🧩 `Odd_Frieze_Rows` | `Integer_Frieze_Rows` | for every odd `n ≥ 15`, two integer friezes whose rows `⌊w/2⌋` differ with no zero and exactly two sign changes (`two_sign_changes`) | ⏳ not submitted |
| 🔗 `Heilmann_Lieb` | HOL-Computational_Algebra | the matching polynomial of a finite graph has only real roots, by interlacing | 📤 submitted |
| 🌳 `Godsil_Path_Tree` | `Heilmann_Lieb` | Godsil's path tree: `μ(G−u) μ(T) = μ(G) μ(T−u)`, and the matching polynomial of the component of `u` divides `μ(T)` | ⏳ not submitted |
| 🌲 `Kirchhoff_Matrix_Tree` | `Smith_Normal_Form` (Cauchy–Binet), `Tree_Enumeration` | Kirchhoff's matrix-tree theorem: for a finite simple graph and a root `r`, the determinant of the reduced Laplacian is the number of spanning trees (`matrix_tree`); port of `Formalizations.Combinatorics.SimpleGraph.MatrixTree` | 📤 submitted |
| 〰️ `Young_Cosine` | HOL-Analysis | Young's inequality (1913): `−1 ≤ Σ_{k=1}^{n} cos (k x) / k` for every `n` and real `x` (`young_cosine`); the AFP version of `YoungCosine/` | 📤 submitted |
| 🔺 `Limited_Augmented_Zarankiewicz` | HOL | admissibility lemmas for the limited augmented Zarankiewicz number of Qi, Cui and Xu, for every width: the label lemma (`label_admissible`), the three-block lemma (`blocks_admissible`), vertical pairs (`vertical_pair`), at most one full row (`at_most_one_full_row`), (C2)–(C3) as distance ≥ 3 in the rectangle graph (`C2_iff_not_adj`, `C3_iff_no_common_neighbour`), the endpoint bound `2 \|E₂\| ≤ (n − 2) m − n(n−1)/2 + 1` (`endpoint_bound`) and the weak-gap arithmetic (`weak_gap_arith`); companion of `Formalizations.Combinatorics.Zarankiewicz.LimitedAugmentedThree` | 📤 submitted |
| ⏱️ `Quantum_Speed_Limits` | HOL-Analysis | the Zieliński–Zych bound `π^a ≤ 2 M_a τ^a` for `0 < a ≤ 1` and its limit `a → 0` (`zielinski_zych`, `zz_bound_tendsto_*`); for the qubit–bus–qubit relay with couplings bounded by `G`: the minimal time `π/√2 ≤ G T` by a calibration function (`relay_minimal_time`), the dephasing excess `(2/3) q (1−q)` and the exact integrals of the optimal protocol (`dephasing_excess`, `optimal_protocol_integrals`), the lower bound `(1−ε)/(G² T)` on the integrated bus occupation (`occupation_lower_bound`) and the time–occupation frontier (`occupation_frontier`); with a lossy bus, the exact error floor `P(T) ≤ e^{−γT}/(1 + δ/(G² T))` for any control (`loss_floor`) and the frontier for partial transfer (`partial_frontier`); companion of the paper doi:10.5281/zenodo.23783382 (version 2) | 📤 submitted |
| 🌀 `Polylog_Antipodal_Floor` | HOL-Analysis | the floors of `Hausdorff_Floor`, `Polylog_Floor` and `AntipodalExamples` above in one AFP entry: `η(s) ≤ \|Li_s z\|` on the unit circle for real `s > 0`, `η(s) = (1 − 2^(1−s)) ζ(s)`, the zeta-state floor `1 − 2^(1−s)`, the bound `2 p − 1` of a dominant population and the two exact counterexamples; companion of doi:10.5281/zenodo.20675271 | 📤 submitted |
| ➖ `Perfect_Difference_Sets` | HOL | Erdős problem 1194: a perfect difference set of positive integers exists (`perfect_difference_set_exists`, Lev's greedy construction), and the greedy construction with the least admissible new element has `a_n ≤ 70 n³` (`greedy_upper_bound`); statements as in `erdos_1194.variants` of google-deepmind/formal-conjectures | 📤 submitted |
| ➗ `Sandor_Subset_Sum_Antichain` | HOL | Erdős problem 882: for `m ≥ 1`, no two distinct nonempty subsets of `{2^i + m 2^m : i < m}` have sums dividing one another (`sandor_antichain`); the statement of `erdos_882.variants.sandor` of google-deepmind/formal-conjectures | 📤 submitted |
| 🔣 `Sylvester_Catalecticant` | HOL-Computational_Algebra | Sylvester's catalecticant theorem: a binary form is a sum of `r` `n`-th powers of pairwise non-proportional linear forms iff a nonzero form vanishing at their points annihilates the catalecticant (Hankel) matrix; necessity over any commutative ring (`catalecticant_necessary`), sufficiency over any field, affine and with a point at infinity (`catalecticant_converse_projective_full`) | 📤 submitted |
| 🌀 `Migotti_Cyclotomic` | HOL-Computational_Algebra | Migotti (1883): for distinct primes `p, q` the coefficients of `Φ_pq = (1 − X^(pq))(1 − X)/((1 − X^p)(1 − X^q))` lie in `{−1, 0, 1}` (`migotti`); for coprime `p, q > 0` the quotient is exact (`migotti_exact`). The identification of this quotient with the cyclotomic polynomial is classical and not formalized | 📤 submitted |
| 🔺 `Dunn_Pretty_Deltoid` | HOL-Analysis | the core of Dunn and Pretty's triangle-halving deltoid in the reference triangle: a line through two legs halves the area iff it is tangent to `xy = 1/8` (`bisects_iff_tangent`); cusps, the three segment integrals `3/32 − (ln 2)/8` and the value `(3/4 ln 2 − 1/2)` times the area. Not formalized: the affine reduction and that the deltoid region is the cusp triangle minus the three segments | ⏳ not submitted |
| 🧮 `Unsolvable_Prime_Degree` | HOL-Analysis + AFP `Unsolvable_Quintic` | an irreducible polynomial over `ℚ` of prime degree `p ≥ 5` with exactly two non-real roots has a non-solvable Galois group, hence is not solvable by radicals; and for every prime `p ≥ 5` an explicit such polynomial, `x (x² + 2(k+1)³) ∏_{i=1}^{k} (x² − 4i²) − 2` with `k = (p−3)/2` (Eisenstein at 2; real roots by sign changes; not all roots real by Vieta) | 📤 submitted |
| 🌳 `Chvatal_Tree_Ramsey` | HOL-Library | Chvátal (1977): for every tree `T` with `n` vertices, `R(K₃, T) = 2n − 1` (`chvatal`); upper bound by leaf induction, lower bound by `K_{n−1,n−1}`; corollary: every connected graph with `n` vertices and at most `n − 1` edges has `R(K₃, G) = 2n − 1` (`connected_le_pred_edges_triangle_good`); the statements of `erdos_1182.variants.chvatal` and `F_ge_pred` of google-deepmind/formal-conjectures | ✅ [in the AFP](https://www.isa-afp.org/entries/Chvatal_Tree_Ramsey.html) (11 Nov 2026; the theory here is the published one) |
| 🎨 `Erdos_Rubin_Taylor_Choosability` | HOL-Library + AFP `Marriage` | Erdős–Rubin–Taylor: the least bipartite graph that is not 2-choosable has 6 vertices (`ert_n_two`: `K_{3,3}` is not, every bipartite graph on ≤ 5 vertices is), and `K_{2,…,2}` with `k` parts is `k`-choosable (`ert_multipartite`, Hall's theorem); `erdos_629.variants.n_two` and `ohba_conjecture.variants.erdos_rubin_taylor` of formal-conjectures | 📤 submitted |
| ✂️ `Seymour_Minimal_Cuts` | HOL-Library | Seymour's observation `c(3m+2) ≥ 3^m` for the maximum number of minimal vertex cuts (`seymour`): `m` internally disjoint paths of length 4 between two vertices; `erdos_150.variants.seymour` of formal-conjectures | 📤 submitted |
| 🎯 `Dirac_Critical_Graphs` | HOL-Library | Dirac (1952): the join of two odd cycles `C_{2n+1}` is 6-critical with `4n² + 8n + 3` edges, so `f_6(4n+2) ≥ 4n² + 8n + 3` (`dirac_bound`); `erdos_917.variants.dirac` of formal-conjectures | 📤 submitted |
| 🔢 `Biquadratic_SOS_Length` | HOL-Analysis | sums of squares of bilinear forms attached to a symmetric matrix `H`: representations as pairs of isometries, the determinant of the pencil, rings and chains, a cyclic vector bound, integer coefficients, paired levels, witnesses for `(J − I)/(n − 1)` with `n = 5, 7`, and the Bailey–Craigen orthogonal matrix from a doubly regular tournament |
| 🎨 `Schur_Number_Four` | HOL | the Schur number `S(4) = 44` (`schur4`): `{1..44}` has a Schur-free 4-colouring (witness checked by `code_simp`) and `{1..45}` has none; the colour symmetry is broken in HOL (first appearance of the colours in the order 0, 1, 2, 3, four cases) and each case is refuted by an LRAT proof replayed by the kernel with the method `lrat` of the entry (RUP steps, forward, clause theorems released after their last use; certificates XZ-compressed, 3.8 MB; no oracle) | 📤 submitted |
| ➗ `Consecutive_Coprime_Divisors` | HOL-Computational_Algebra | Erdős–Hall: `τ_⊥(n)`, the number of pairs of consecutive divisors of `n` that are coprime, equals the number of distinct prime factors when each prime exceeds the product of the previous ones; for every `k` there is a squarefree `n` with `k` prime factors and `τ_⊥(n) = k` | 📤 submitted |
| 📉 `Heavy_Tail_Sums` | AFP `Extreme_Value_Theory` | tail calculus of heavy-tailed random variables: the tail of a sum of independent regularly varying variables, Breiman's lemma, closure of the Fréchet domain of attraction, the big-jump principle, a Pareto example showing that independence cannot be dropped, random sums `P(S_N > x) ∼ E[N] P(X > x)` (geometric `N` included), and, assuming the Pollaczek–Khinchine representation, the tail of the stationary waiting time | 📤 submitted |
| 🔢 `Segre_Persistence_SOS` | AFP `Three_Squares` | the elementary parts of a note on the quadratic persistence of Segre varieties (doi:10.5281/zenodo.24036320): for `P^(m−1) × P^2`, the linear algebra of the bound `qp ≤ m` (an antisymmetric 3×3 matrix with two independent kernel vectors vanishes) and the count behind the matching lower bound; facts on sums of squares of bilinear forms with `C₄`-free supports | 📤 submitted |
| 🤝 `Coprime_Divisor_Matchings` | AFP `Jordan_Normal_Form` + HOL-Computational_Algebra | Alekseyev–Beyer de Ryke, *Coprime matchings of divisor sets* (arXiv:2610.37512): Lemma 2.1, if `m = ∏ p_i^(h_i − 1)`, `b > 0`, `gcd(a, b) = 1` and `h_i ≤ p_i` whenever `p_i ∤ b`, the divisors of `m` have a coprime matching with `a, a + b, …, a + (τ(m) − 1) b` (`lemma_2_1`; roots of unity from the fundamental theorem of algebra, Vandermonde times triangular, a nonzero Leibniz term); Theorem 1.2, the conjecture of McNew and Pomerance: `n` is strongly matchable iff `p^p ∤ n` for every prime `p` (`theorem_1_2`). Theorem 1.1, the classification of matchable integers and the asymptotics are not formalized | 📤 submitted |
| 🔢 `Lary_Partitions` | HOL | Coons, Theorem 3 (arXiv:2611.08109): for `k, l ≥ 2` the number `b_{k,l}(n)` of partitions of `n` into powers of `l`, each used at most `k` times, is monotone iff `l ∣ k + 1`, and never strictly monotone (`coons_theorem_3` for the recurrence, `b_count_eq_b`: the recurrence equals the count of digit lists, `coons_theorem_3_count` for the count) | ⏳ not submitted |
| 🧬 `Game_of_Life` | HOL | Conway's Game of Life on `ℤ²` (sets of live cells, rule B3/S23): the step commutes with the symmetries of the square (`step_equivariant`); light-cone locality (`locality`); patterns whose thickenings are disjoint evolve independently (`disjoint_steps_dist`), also for arbitrary families, which gives the free flight of salvos of spaceships (`salvo_flight`, `glider_salvo`); Conway's speed limit, `2(|a| + |b|) ≤ p` for a finite pattern that reappears displaced by `(a, b)` after `p` generations (`speed_limit`), attained by the glider and by the lightweight spaceship (`speed_limit_sharp`, `speed_limit_orthogonal_sharp`); block, blinker, glider, lightweight spaceship and eater 1 by trace replay with a verified executable step (`code_simp`); the Gosper gun emits a glider every 30 generations (`gun_stream`), so a finite pattern has unbounded population (`unbounded_population`) | ⏳ not submitted |

Proof style of the entries (since 11 Nov 2026, after the editor's revision of `Chvatal_Tree_Ramsey`): local
statements are written `have … if … for …` rather than as meta-quantified goals followed by `fix`/`assume`, and
inductions use `proof (induct … rule: …)` with named cases. Eighteen entries were rewritten in that form and
rebuilt; a few statements that do not fit the simple pattern remain to be rewritten by hand.

Further sessions, not submitted to the AFP:

- `RationalGap`: exact witnesses for rational lengths of biquadratic forms; 3 is not a sum of two rational squares; no orthogonal vectors of norms 1, 1, 7 in `ℚ⁵`.
- `BSRRational`: on a `C₄`-free support the coefficient vectors of a sum of squares of bilinear forms are orthogonal; orthonormal vectors and one of norm 7 force three more coordinates over `ℚ` (`seven_embedding`), so a `C₄`-free form with one weight 7 needs at least `|E| + 3` rational squares (`bsr_rational_lower`).
- `SegrePersistence`: the quadratic persistence of `ℙ^{m-1} × ℙ²` is at most `m`, in coordinates: antisymmetric `3 × 3` blocks killing two independent vectors vanish (`segre_width3_upper`), and the count `d − g(m−1) = m − 1` of the lower bound (`segre_width3_count`); a `C₄`-free support has at most `m + C(n,2)` cells (`c4_free_card_le`), and `⌊8m/3⌋ > ⌊(5m+6)/2⌋` for `m ≥ 23` (`gap_pos`); and `BSR(m,n) ≤ mn − max(m,n) + 1` (`bsr_upper`), with the `m × 2` case of Blekherman–Sinn–Smith–Velasco Theorem 1.4 as an explicit hypothesis, so `BSR(4,3) ≤ 9` (`bsr_upper_4_3`).
- `Erdos1186`: `erdos_1186.variants.probabilistic` of formal-conjectures, `δ_k ≤ 1/((k − 1) 2^k)` (`erdos_1186_probabilistic`).
- `BSRWidthThree` (on `SegrePersistence`): the parts of *For m ≥ 2, every m×3 biquadratic sum of squares is a sum of 2m squares* (doi:10.5281/zenodo.24051362) that are formalized. The lower bound `2m` by the witness (`bsr_width_three_lower`); Lemma 2, a Hankel multiplier vanishing on `ker[I P Q]` is zero (`regular_point_algebra`, `regular_point_hankel`); the case `e = 1` of the induction (`width_three_trace`); Corollary 7, `BSR(m,3) ≤ 2m` implies `BSR(m,4) ≤ 3m` and `BSR(m,n) ≤ mn − max(m,n)` (`bsr_width_four`, `bsr_upper_three`, with Theorem 1 as an explicit hypothesis); and the identity comparing it with Blekherman–Sinn–Smith–Velasco Theorem 2.1 (`bssv_wins_from_five`, `width_four_wins`).
- `BSRFourFour`: elementary steps of *Every 4×4 biquadratic sum of squares is a sum of eleven squares* (doi:10.5281/zenodo.24055900): the regular point, a symmetric Hankel multiplier that vanishes on the symmetric tensors is zero (`regular_point_symmetric`); the support count closing Lemma 3 (`support_triples`); the injectivity of the polar multiplier of `(xᵀb)²` (`polar_trace_injective`); and the trace count of Section 5 (`trace_count`). `Supports_Lemma` (on `Rep_Fin_Groups`) has pieces of Lemma 3: the Observation of Section 2 (`observation`), the orthogonal half of the pencil inclusion (`pencil_orthogonal`), a common eigenvector of commuting endomorphisms over an algebraically closed field (`common_eigenvector`, a classical fact proved here), the commuting operators T_b⁻¹T_c (`pencil_operators_commute`), the case s = a = r in full (`case_s_eq_a`) and the case s < a with the inclusion in im T_b and the one-dimensional radical as hypotheses (`case_s_lt_a`). The Segre bound r ≤ (a−1)(b₀−1), the generic b, Lemma 2 and the second-variation arguments are not formalized.
- `FriezeCorollary` (on `AFP/Odd_Frieze_Rows`): Corollary `cor:all` of *Integer frieze patterns and sign changes*: four sign changes fail for every `n ≥ 14` — even `n` by Theorem A (`four_sign_changes_fail_even`, middle rows strictly ordered) and odd `n` by Theorem B (`four_sign_changes_fail_odd`, no zero and exactly two sign changes).
- `SU7Rung`: Proposition `prop:rec` of the note on the certified gap of SU(7) gauge-Higgs unification, the CLASSICAL recursion of a vector partition function in one generator (Beck–Robins; Sturmfels), formalized for any set of contents (`rung_recursion`) and for the SU(7) data: a cell is finite (`su7_cell_finite`) and `N(a, q+6) = N(a, q) − P(a, q)` (`su7_rung_recursion`). Proposition `prop:mono` (the G-window): `μ` strictly decreasing (`mu_strict_anti`), the admissible `x` an interval (`mu_window_interval`), `A₄/x − K/x³ = −6μ/x` (`G_derivative_identity`) and `G` strictly decreasing where `μ > 0` (`G_strictly_decreasing`, with identity (I) of Part VII as a hypothesis). From the note on proton decay, Proposition `prop:identity`: `[SU(2)_L]² U(1)' = ½ Σ_j A_j` (`anomaly_identity`), one generation forces `A = 0` (`one_generation`), three can escape (`three_generations_escape`), and a family-universal quark charge gives `A_j = l_j − l̄` (`universal_quark_charge`, `protection_iff_off_mean`); the doublet content is the note's model input.
- `WeightedPartialSums`: Proposition `prop:ordenalto` (b) of *Weighted partial sums of characters*, in abstract form. For a character of order 4, `T = Σ_R c ε_c + i Σ_N c δ_c` vanishes iff both signed sums vanish (`T4_zero_iff`), and then both plain sums are even (`T4_zero_parity`).

## 🚀 Building

With the official Docker image `makarius/isabelle:Isabelle2026` (or `:Isabelle2025-2` for the AFP sessions):

```
isabelle build -v -d HausdorffFloor Hausdorff_Floor
isabelle build -v -d HausdorffFloor -d PolylogFloor Polylog_Floor
isabelle build -v -D AntipodalExamples
isabelle build -v -D ZielinskiZych
isabelle build -v -D FriezeDominance
isabelle build -v -D YoungCosine
isabelle build -v -d AFP/Integer_Frieze_Rows -D AFP/Odd_Frieze_Rows
isabelle build -v -d AFP/Heilmann_Lieb -D AFP/Godsil_Path_Tree
isabelle build -v -d <afp>/thys -D AFP/Kirchhoff_Matrix_Tree
isabelle build -v -D AFP/Young_Cosine
isabelle build -v -D AFP/Limited_Augmented_Zarankiewicz
isabelle build -v -D AFP/Quantum_Speed_Limits
isabelle build -v -D AFP/Polylog_Antipodal_Floor
isabelle build -v -D AFP/Perfect_Difference_Sets
isabelle build -v -D AFP/Sandor_Subset_Sum_Antichain
isabelle build -v -D ZLThreeBlockFamily
isabelle build -v -D AFP/Sylvester_Catalecticant
isabelle build -v -D AFP/Migotti_Cyclotomic
isabelle build -v -D AFP/Dunn_Pretty_Deltoid
isabelle build -v -d <afp>/thys -D AFP/Unsolvable_Prime_Degree
isabelle build -v -D AFP/Chvatal_Tree_Ramsey
isabelle build -v -d <afp>/thys -D AFP/Erdos_Rubin_Taylor_Choosability
isabelle build -v -D AFP/Seymour_Minimal_Cuts
isabelle build -v -D AFP/Dirac_Critical_Graphs
isabelle build -v -D AFP/Biquadratic_SOS_Length
isabelle build -v -d <afp>/thys -D AFP/Coprime_Divisor_Matchings
isabelle build -v -D AFP/Lary_Partitions
isabelle build -v -D AFP/Game_of_Life
isabelle build -v -D RationalGap
isabelle build -v -D BSRRational
isabelle build -v -D Erdos1186
isabelle build -v -D SegrePersistence
isabelle build -v -d SegrePersistence -D BSRWidthThree
isabelle build -v -D BSRFourFour
isabelle build -v -D WeightedPartialSums
isabelle build -v -D SU7Rung
isabelle build -v -d AFP/Integer_Frieze_Rows -d AFP/Odd_Frieze_Rows -D FriezeCorollary
```

`docker/Dockerfile` adds the LaTeX packages needed to build the documents of the AFP sessions
(`-o document=pdf`).

## 🧱 Sessions from the queue

Sessions that were finished in the working queue and had not been uploaded.

| Session | What is proved |
|---|---|
| `MemoryAccessFloors/` (`Memory_Access_All_Pulses`) | from *No pulse beats the resonant swap* (draft, November 2026). `Memory_Access_All_Pulses`: the bound over ALL control pulses without dephasing (`memory_access_all_pulses`): if `A' = −γ_q A − 2u`, `B' = −γ_m B + 2u` on `[0, T]` with `A, B ≥ 0`, `u² ≤ G² A B`, `A 0 = 1`, `B 0 = 0` and `|γ_q − γ_m|/4 < G`, then `B t ≤ 4G²/(4G² + γ_q γ_m) · exp(−(γ̄/Ω) arctan(2Ω/γ̄))`; the resonant solution in closed form and that it attains the bound (`bound_sharp`); proof by a Lyapunov function in oblique polar coordinates and an exact regularisation at `A = 0`, `B = 0`. `Memory_Access_Floors`: the maximum of the damped vacuum-Rabi transfer for all `t ≥ 0` (`resonant_pulse_max_bound`, `resonant_pulse_max_attained`), symmetry in the two rates, the write-channel identities `1 − F = (1 − p)/6 + (1 − c)/3` and `1 − F_e = (3/2)(1 − F)`, the worst-case fidelity over pure inputs (`worst_case_case_one`, `worst_case_case_two`), the alignment lemma. Not formalized here: the population theorem with dephasing |
