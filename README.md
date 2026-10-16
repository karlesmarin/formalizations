# Formalizations

Lean 4 formalizations by Carles Marín, built on [Mathlib](https://github.com/leanprover-community/mathlib4) and
organized the same way: by mathematical area, one topic per file, every file with a module docstring listing its main
results.

- Lean `v4.35.0`; Mathlib pinned in `lakefile.lean`.
- No `sorry`. Every main result depends only on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`),
  checked in CI by `scripts/check_axioms.sh`.

## Using it

```
git clone https://github.com/karlesmarin/formalizations.git
cd formalizations
lake exe cache get
lake build
```

Import everything with `import Formalizations`, or a single file, e.g.
`import Formalizations.RingTheory.DGH.Epsilon0`.

## Contents

| Area | File | Main result |
|---|---|---|
| `Algebra.Ring` | `Continuant` | Euler's continuant; `a⁻¹ + r + b⁻¹ = a⁻¹ K(a,r,b) b⁻¹` |
| `LinearAlgebra.Matrix` | `FreeLocus` | Rank and corank lemmas for block and low-rank perturbations |
| | `FreeLocusCertificate` | Soundness of the free-locus certificate ("not flip-poly") |
| `RingTheory.DGH` | `Basic` | The Dubrovin–Gräter–Hanke stratification `D : Ordinal → Set R` |
| | `JakobsOrder` | Jakobs' order = Dershowitz–Manna order |
| | `Hessenberg` | Jakobs' order through the Hessenberg natural sum |
| | `Absorb` | Absorption of a layer of inverses; Hua's identity |
| | `Finite` | Finite strata; `D M ω` as a subring |
| | `Epsilon0` | The stratification closes at `ε₀` (`kappa_le_epsilon0`) |
| | `FqLower` | Combinatorial core of `κ(F_q(x)) = ω²` |
| `RingTheory.FreeField.ThreeAxes` | `ExactArc` | Traceless `2×2` squares are scalar; scalar evaluation; characteristic `p` |
| | `Extractors` | Trace and determinant extractors; Fox decomposition of a commutator |
| | `TraceResidue` | Residues along square-zero directions |
| | `DegenerateResidue` | Degenerate-residue identities; explicit witnesses |

`FormalizationsTest/Axioms.lean` prints the axioms of every main result.

## Adding a formalization

1. Put the file under `Formalizations/<Area>/<Topic>.lean`, following Mathlib's area names.
2. Start it with the copyright header, then the imports (Mathlib modules only, never `import Mathlib`), then a module
   docstring `/-! # Title … ## Main results … ## References -/`.
3. Add its main results to `FormalizationsTest/Axioms.lean`, and the import to `Formalizations.lean`.
4. `lake build && sh scripts/check_axioms.sh`.

## License

Apache 2.0, as Mathlib. Written with Claude (Anthropic) as an AI assistant; every statement is machine-checked.
