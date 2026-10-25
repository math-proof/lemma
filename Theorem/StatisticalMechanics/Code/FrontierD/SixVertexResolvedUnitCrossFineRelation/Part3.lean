/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedUnitCrossFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopFullMaskFineRelation.Part7
import Def.StatisticalMechanics.Code.FrontierD.SixVertexResolvedUnitCrossFineRelation.Part2


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexLoopDecoratedResolvedUnitCrossTarget_colored
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (source : SixVertexLoopDecoratedPair T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt))
    (cross : FKColoredResolvedUnitCross
      (sixVertexLoopDecoratedPairColored source)) :
    sixVertexLoopDecoratedPairColored
        (sixVertexLoopDecoratedResolvedUnitCrossTarget middle hmiddle_pos
          hmiddle_lt source cross) = cross.target := by
  funext layer
  cases layer <;> exact FKColoredLoopPairing.toCompatible_toColored _

end
end StatMech.FrontierD
