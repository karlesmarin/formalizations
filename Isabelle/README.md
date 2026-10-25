# Isabelle ports

Isabelle/HOL versions of some Lean modules of this repository. They are independent of the Lean build (`lake` only
builds `Formalizations.*`).

| Session | Port of | What is proved |
|---|---|---|
| `HausdorffFloor/` (`Hausdorff_Floor`) | `Formalizations.Analysis.SpecialFunctions.Polylog.HausdorffFloor` | per-term bound `1/(1+x) ≤ Re (1/(1 − x z))`; a uniform gap `c ≤ |1 − t z|` on `[0,1]` for `z ≠ 1` on the unit circle; for a finite measure and `τ ∈ [0,1)` a.e., the moment series converges at every `z ≠ 1` of the unit circle to `∫ 1/(1 − τ z)`, and its modulus is at least `∫ 1/(1 + τ)` |

Not ported: the polylogarithm corollary for real `s > 0` (it needs the Gamma-density measure in Isabelle). The proof
avoids Abel's theorem: the partial sums are integrals of geometric sums and converge by dominated convergence.

Build (Isabelle2026, e.g. with the official Docker image `makarius/isabelle:Isabelle2026`):

```
isabelle build -v -d HausdorffFloor Hausdorff_Floor
```

No `sorry`, no `quick_and_dirty`, no external provers (no `smt`).
