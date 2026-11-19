# 📐 Transformer attention, Part I

Eight groups of conditional results related to *Predicting How Transformers Attend*,
formalized in Isabelle2026/HOL. This is an independent Isabelle session; the Lean
modules under `Formalizations/Analysis/TransformerAttention/` remain the source
for the Padé/Möbius identity, maximum entropy power law, and entropy bound.
The overlap is documented in `COINCIDENCIAS_FORMALIZATIONS.md`.

The session contains finite probability, OLS calibration, exponential family,
mixture, quantile, truncation, softmax stability, and cosine integral/RoPE lemmas.
All claims require the hypotheses in their theorem statements. In particular,
the RoPE bridge assumes a score model and does not establish an empirical
exponent for a trained transformer.

## 🔬 Reproduce

Install Isabelle2026 and AFP (snapshot 2026-11-06, `Exp_Log_Integral`). From
the repository root:

```sh
isabelle build -j 1 -o threads=1 -o quick_and_dirty=false -d /path/to/afp/thys -D Isabelle/TransformerAttentionPartI
```

The archived `ci_build_receipt.json` records the source hashes, kernel
dependency audit and negative control. `ci_proof_dependencies.tsv` lists the
audited named facts and their oracle dependencies. AFP is a separate upstream
dependency by Manuel Eberl and other contributors; no AFP source is copied here.

The detailed Spanish explanation and simplified formulas live in the
[research repository](https://github.com/karlesmarin/predicting-how-transformers-attend/tree/session-2026-05-27-gamma-emergence/research_program/theorems_20261118).
