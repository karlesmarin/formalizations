# 🧮 Formalizations

Lean 4 formalizations by Carles Marín, built on [Mathlib](https://github.com/leanprover-community/mathlib4) and
organized the same way: by mathematical area, one topic per file, every file with a module docstring listing its main
results.

- 🔧 Lean `v4.35.0`; Mathlib pinned in `lakefile.lean`.
- ✅ No `sorry`, no `native_decide`, no new axioms. Every main result depends only on the standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`), checked by `scripts/check_axioms.sh`.
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
| `LinearAlgebra.Matrix` | `FinTwo` | `2×2` identities: polarized Cayley–Hamilton, `det (A + B)`, iterated commutators |
| | `Adjugate` | Diagonal entries of the adjugate are principal minors |
| | `Rank` | `rank (A + B) ≤ rank A + rank B`; nullity under low-rank perturbation; block triangular bounds |
| | `Rank.Kronecker` | `rank (A ⊗ₖ 1) = card p * rank A` |
| | `Charpoly.Jacobi` | Resolvent series and Jacobi's formula for the derivative of the reversed charpoly |
| | `FreeLocus` | Rank and corank lemmas for block and low-rank perturbations |
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
| | `WeightedTrinomials` | Hidden commutator in `GL₂`; weighted trinomial curve with `Nᵢ² = 0`; `2×2` Schur inverse over any ring |
| | `AtomCertificate` 🆕 | Integer certificate of a `9×9` atom: `Q·Kᵢ = 16·Qᵢ`, `det Q = 256`, a rank-one identity, and two `9×9` determinants (`5·2⁵⁶`, `2⁴⁹`) via a triangular factorization certificate |
| | `QuaternionResidues` 🆕 | Integral quaternions mod `5`: six rank-one residues, products vanish exactly on inverse pairs, nonzero along reduced words |

`FormalizationsTest/Axioms.lean` prints the axioms of every main result.

## 🧾 How the certificates are checked

Large integer facts (determinants of `9×9` matrices, finite tables) are proved with `decide` in the kernel, never with
`native_decide`. A determinant is not expanded: the file provides a factorization `L · M.submatrix σ σ = U` with `L`
lower and `U` upper triangular, and a general lemma (`det_eq_of_certificate`) turns it into `det M`. Checking the
certificate is a matrix multiplication.

## ➕ Adding a formalization

1. Put the file under `Formalizations/<Area>/<Topic>.lean`, following Mathlib's area names.
2. Write it as Mathlib does:
   - the copyright header;
   - `module`;
   - `public import` of the Mathlib modules it needs (never `import Mathlib`);
   - a module docstring `/-! # Title … ## Main results … ## References -/`;
   - `@[expose] public section`.
3. Add its main results to `FormalizationsTest/Axioms.lean`, and the import to `Formalizations.lean`.
4. `lake build` (no warnings) and `sh scripts/check_axioms.sh`.

## 📜 License

Carles Marín (investigador independiente, karlesmarin@gmail.com).
Apache 2.0, as Mathlib. Written with Claude (Anthropic) as an AI assistant; every statement is machine-checked.
