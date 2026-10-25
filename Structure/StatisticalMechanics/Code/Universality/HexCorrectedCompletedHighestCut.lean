/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedCompletedHighestCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.HexCorrectedSideDepth
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedShiftedDivergence
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripExteriorPeriod.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCompletion.Part8
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedCompletedHighestCut


namespace StatMech.Universality

open HexWalk

noncomputable section

set_option maxHeartbeats 800000 in


structure HexCSCompletedHighestCut (T : ℕ) (hT : 1 ≤ T) where
  split : {ts : List ℤ // HexCSNewSideWalk T hT ts} →
    HexCSCompletedTopWalk T hT × HexCSCompletedTopWalk T hT
  split_injective : Function.Injective split
  length_add_five : ∀ d,
    (ofTurns hexAWStart 1 (split d).1.1).endpointNumVertices +
        (ofTurns hexAWStart 1 (split d).2.1).endpointNumVertices =
      (ofTurns hexAWStart 1 d.1).endpointNumVertices + 5


end
end StatMech.Universality
