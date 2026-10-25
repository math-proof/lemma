/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Structure.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelector
open Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

namespace shb_DynamicEdgeExploration

variable {D E : Type*} [DecidableEq E]


def firstAdmissible (X : shb_DynamicEdgeExploration D E)
    (admissible : D → E → Bool) (d : D) : Option E :=
  (X.edgeOrder d).find? (admissible d)


end shb_DynamicEdgeExploration
end StatMech.Sharpness
