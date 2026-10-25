/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/FiniteProperParabolicsInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeFiniteParabolic.Part4
import Theorem.v1.Atlas.Buildings.code.AffineCoxeter.FiniteProperParabolicsInstance.Part2
set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup TitsCone


namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- Packaging: from `AffineCoxeterHyp` we obtain the two finiteness axioms needed by the rest of
the development (subspan finiteness and hyperplane finiteness of nonposRoots). -/
def finiteProperParabolicsHyp_of_affineCoxeterHyp
    (M : CoxeterMatrix B) (hyp : AffineCoxeterHyp M) :
    FiniteProperParabolicsHyp M where
  finiteRoots_in_subspan_of_subset_finite :=
    finiteRoots_in_subspan_of_AffineCoxeterHyp M hyp
  hyperplane_nonposRoots_finite := by
    intro v₀ hv₀_pos hv₀_radical x hx_hyp
    exact hyperplane_nonposRoots_finite_axiom M hyp v₀ hv₀_pos hv₀_radical x hx_hyp

end TitsCone
