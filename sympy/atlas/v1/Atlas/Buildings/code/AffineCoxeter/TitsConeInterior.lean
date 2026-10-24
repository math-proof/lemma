/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeInterior.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeConvexity

set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup TitsCone

namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- The **interior** of the Tits cone $\mathcal U^\circ$: points which are $\sigma^*_w$-images of
strictly positive vectors $y > 0$, i.e. images of points in the open fundamental chamber. -/
def titsConeInterior (M : CoxeterMatrix B) : Set (B → ℝ) :=
  {x | ∃ (y : B → ℝ), (∀ s, y s > 0) ∧
    ∃ (ws : List B), x = wordAction M ws y}

end TitsCone
