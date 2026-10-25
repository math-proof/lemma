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
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part4
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace shb_BackboneExplorationDomain

variable (d : shb_BackboneExplorationDomain V)


noncomputable def advance (d : shb_BackboneExplorationDomain V)
    (s : shb_AmbientSegment V) : shb_BackboneExplorationDomain V where
  graph := d.graph.deleteEdges s.edgeSet
  active := d.active.filter (compatible s)
  active_supported := by
    intro t ht
    rw [Finset.mem_filter] at ht
    exact supported_deleteEdges_of_compatible (d.active_supported t ht.1) ht.2

end shb_BackboneExplorationDomain
end
end StatMech.Sharpness
