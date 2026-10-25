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
import Structure.StatisticalMechanics.Code.Universality.HexCorrectedCompletedHighestCut


namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def hexCSCompletedHighestCut
    (T : ℕ) (hT : 1 ≤ T) : HexCSCompletedHighestCut T hT where
  split := hexCSCompletedSplit T hT
  split_injective := hexCSCompletedSplit_injective T hT
  length_add_five := hexCSCompletedSplit_length T hT

end
end StatMech.Universality
