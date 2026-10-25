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
import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part9
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

noncomputable instance (H : SimpleGraph V) [DecidableRel H.Adj]
    (s : shb_AmbientSegment V) :
    DecidablePred (shb_segmentCut H s) := Classical.decPred _


end
end StatMech.Sharpness
