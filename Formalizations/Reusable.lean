/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín, Claude (AI assistant)
-/
module

public import Formalizations.Reusable.AlgebraicGeometry
public import Formalizations.Reusable.Analysis
public import Formalizations.Reusable.Combinatorics
public import Formalizations.Reusable.Geometry
public import Formalizations.Reusable.LinearAlgebra
public import Formalizations.Reusable.MeasureTheory
public import Formalizations.Reusable.Polynomial

/-!
# Reusable layer (v0.2.0)

A small, deliberately maintained layer on top of the archive: general statements, phrased with
Mathlib concepts only, under stable names `Formalizations.Reusable.<name>`. Each theorem is proved
by the archive theorem it re-exposes (`:= Archive.name ...`), so its provenance stays traceable;
the archive itself (one module per paper) is unchanged.

The list, with an English statement, the archive module, the paper and the classical reference of
each entry, is `Formalizations/Reusable/manifest.toml`; usage examples are in
`FormalizationsTest/Reusable<Area>Example.lean` (one per area, minimal import) and
`FormalizationsTest/ReusableExamples.lean` (all of them).

Import the whole layer with `import Formalizations.Reusable`, or one area, e.g.
`import Formalizations.Reusable.Polynomial` (real polynomials and their real roots; it imports no
paper of the archive).
-/
