/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Tactic.Ring

/-!
# The integer-parity kernel of the internal-`U(1)` mixing obstruction

In the six-dimensional `SU(4)` gauge-Higgs unification model, a symmetric-tensor doublet zero
mode requires an even index `n₃`, while the hypercharge equation at the nontrivial internally
mixed angle requires `3 n₃ − 2 n₄ = 1`. The two integer conditions are incompatible. The
physics that produces them (orbifold zero-mode parity and the hypercharge equation) is an input,
not formalized here.

## Main results

* `even_index_hypercharge_obstruction`: `Even n₃` and `3 n₃ − 2 n₄ = 1` are incompatible.
-/

@[expose] public section

namespace GaugeHiggsUnification.InternalU1MixingNoGo

/-- An even `n₃` and the hypercharge equation `3 n₃ − 2 n₄ = 1` are incompatible. -/
theorem even_index_hypercharge_obstruction
    (n₃ n₄ : ℤ) (h_even : Even n₃) (h_charge : 3 * n₃ - 2 * n₄ = 1) :
    False := by
  rcases h_even with ⟨k, hk⟩
  omega

end GaugeHiggsUnification.InternalU1MixingNoGo
