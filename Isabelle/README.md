# 🦉 Isabelle formalizations

Isabelle/HOL versions of some Lean modules of this repository, and entries prepared for the
[Archive of Formal Proofs](https://www.isa-afp.org). They are independent of the Lean build (`lake` only builds
`Formalizations.*`).

- 🔧 Isabelle2026; the `AFP/` sessions also build with Isabelle2025-2, the version the AFP uses.
- ✅ No `sorry`, no `quick_and_dirty`, no external provers (no `smt`); finite facts by `code_simp` (the simplifier),
  never `eval`.
- 🔗 Each port names the Lean module it follows; the AFP entries go further than the Lean (statements for every `n`).

## 🗂️ Ports of Lean modules

| Session | Port of | What is proved |
|---|---|---|
| 📈 `HausdorffFloor/` (`Hausdorff_Floor`) | `Formalizations.Analysis.SpecialFunctions.Polylog.HausdorffFloor` | per-term bound `1/(1+x) ≤ Re (1/(1 − x z))`; a uniform gap `c ≤ |1 − t z|` on `[0,1]` for `z ≠ 1` on the unit circle; for a finite measure and `τ ∈ [0,1)` a.e., the moment series converges at every `z ≠ 1` of the unit circle to `∫ 1/(1 − τ z)`, and its modulus is at least `∫ 1/(1 + τ)` |
| 🧩 `FriezeDominance/` (`Frieze_Dominance`) | `Formalizations.Combinatorics.Frieze.IntegerDominance`, `…Frieze.TwoSignChanges` | two integer Conway–Coxeter friezes of width 11 (quiddities `lower`, `upper`) whose middle rows are strictly ordered at all 14 positions; two of width 12 whose rows 6 differ with no zero and exactly two cyclic sign changes (`Frieze_Two_Sign_Changes`); finite computations by `code_simp` |
| 🧩 `FriezeFamily/` (`Frieze_Family`) | — (Isabelle only; the first version of `AFP/Integer_Frieze_Rows`) | friezes as lattice polygons; ear insertion keeps friezes; antipodal ear insertion and the diameters; for every `t`, two integer friezes of width `11 + 2t` whose middle rows (diameters) are strictly ordered (`strictly_ordered_middle_rows`); bridge `entry_is_continuant` (entries are continuants of the quiddity `a_k = det (V_(k-1), V_(k+1))`) and the corollary in that language (`strictly_ordered_middle_rows_continuants`) |

📉 Not ported: the polylogarithm corollary for real `s > 0` (it needs the Gamma-density measure in Isabelle). The proof
avoids Abel's theorem: the partial sums are integrals of geometric sums and converge by dominated convergence.

## 🏛️ Entries prepared for the Archive of Formal Proofs (`AFP/`)

Sessions in the AFP format (`chapter AFP`, with a document: prose, figures, bibliography).

| Session | Depends on | What is proved | Status |
|---|---|---|---|
| 🧩 `Integer_Frieze_Rows` | HOL | for every even `n ≥ 14`, two integer Conway–Coxeter friezes of width `n − 3` whose middle rows are strictly ordered (a negative answer, for integers, to Problem 1 of Tabachnikov, *Math. Intelligencer* 40 (2018)) | 📤 submitted |
| 🧩 `Odd_Frieze_Rows` | `Integer_Frieze_Rows` | for every odd `n ≥ 15`, two integer friezes whose rows `⌊w/2⌋` differ with no zero and exactly two sign changes (`two_sign_changes`) | ⏳ not submitted |
| 🔗 `Heilmann_Lieb` | HOL-Computational_Algebra | the matching polynomial of a finite graph has only real roots, by interlacing | 📤 submitted |
| 🌳 `Godsil_Path_Tree` | `Heilmann_Lieb` | Godsil's path tree: `μ(G−u) μ(T) = μ(G) μ(T−u)`, and the matching polynomial of the component of `u` divides `μ(T)` | ⏳ not submitted |

## 🚀 Building

With the official Docker image `makarius/isabelle:Isabelle2026` (or `:Isabelle2025-2` for the AFP sessions):

```
isabelle build -v -d HausdorffFloor Hausdorff_Floor
isabelle build -v -D FriezeDominance
isabelle build -v -d AFP/Integer_Frieze_Rows -D AFP/Odd_Frieze_Rows
isabelle build -v -d AFP/Heilmann_Lieb -D AFP/Godsil_Path_Tree
```

`docker/Dockerfile` adds the LaTeX packages needed to build the documents of the AFP sessions
(`-o document=pdf`).
