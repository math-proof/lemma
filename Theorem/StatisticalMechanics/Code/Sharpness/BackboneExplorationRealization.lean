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
import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part2
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

@[simp] theorem shb_AmbientSegment.toPath_edges
    (H : SimpleGraph V) (s : shb_AmbientSegment V) (h : s.Supported H) :
    (s.toPath H h).1.edges = s.2.2.1.edges := by
  exact Walk.edges_transfer _ _


end
end StatMech.Sharpness
