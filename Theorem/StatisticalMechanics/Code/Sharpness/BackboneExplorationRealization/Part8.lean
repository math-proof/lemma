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
import Instance.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part6
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

theorem shb_segment_unrestricted_cut_factor
    (H : SimpleGraph V)
    (β : ℝ) (J : Sym2 V → ℝ) (s : shb_AmbientSegment V) :
    shb_fullWeightMass H β J =
      shb_cutLeftMass H β J (shb_segmentCut H s) *
        shb_cutRightMass H β J (shb_segmentCut H s) := by
  exact shb_tsum_weight_cut_factor H β J (shb_segmentCut H s)


end
end StatMech.Sharpness
