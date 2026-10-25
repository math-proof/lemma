/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationRealization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelector.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP2CutResummation.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP3Domain
import Instance.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part5
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace shb_BackboneExplorationDomain

variable (d : shb_BackboneExplorationDomain V)


theorem supported_deleteEdges_of_compatible
    {H : SimpleGraph V} {s t : shb_AmbientSegment V}
    (ht : t.Supported H) (hst : compatible s t) :
    t.Supported (H.deleteEdges s.edgeSet) := by
  intro e he
  rw [SimpleGraph.edgeSet_deleteEdges]
  refine ⟨ht e he, ?_⟩
  intro hes
  exact Set.disjoint_left.1 hst hes he


end shb_BackboneExplorationDomain
end
end StatMech.Sharpness
