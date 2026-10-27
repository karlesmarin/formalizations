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

The Isabelle proof of the floor avoids Abel's theorem: the partial sums are integrals of geometric sums and converge by dominated convergence.

## 🏛️ Entries prepared for the Archive of Formal Proofs (`AFP/`)

Sessions in the AFP format (`chapter AFP`, with a document: prose, figures, bibliography).

| Session | Depends on | What is proved | Status |
|---|---|---|---|
| 🧩 `Integer_Frieze_Rows` | HOL | for every even `n ≥ 14`, two integer Conway–Coxeter friezes of width `n − 3` whose middle rows are strictly ordered (a negative answer, for integers, to Problem 1 of Tabachnikov, *Math. Intelligencer* 40 (2018)) | 📤 submitted |
| 🧩 `Odd_Frieze_Rows` | `Integer_Frieze_Rows` | for every odd `n ≥ 15`, two integer friezes whose rows `⌊w/2⌋` differ with no zero and exactly two sign changes (`two_sign_changes`) | ⏳ not submitted |
| 🔗 `Heilmann_Lieb` | HOL-Computational_Algebra | the matching polynomial of a finite graph has only real roots, by interlacing | 📤 submitted |
| 🌳 `Godsil_Path_Tree` | `Heilmann_Lieb` | Godsil's path tree: `μ(G−u) μ(T) = μ(G) μ(T−u)`, and the matching polynomial of the component of `u` divides `μ(T)` | ⏳ not submitted |
| 🌲 `Kirchhoff_Matrix_Tree` | `Smith_Normal_Form` (Cauchy–Binet), `Tree_Enumeration` | Kirchhoff's matrix-tree theorem: for a finite simple graph and a root `r`, the determinant of the reduced Laplacian is the number of spanning trees (`matrix_tree`); port of `Formalizations.Combinatorics.SimpleGraph.MatrixTree` | ⏳ not submitted |

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
```

`docker/Dockerfile` adds the LaTeX packages needed to build the documents of the AFP sessions
(`-o document=pdf`).
