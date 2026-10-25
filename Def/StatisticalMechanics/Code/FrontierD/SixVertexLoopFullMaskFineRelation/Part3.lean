/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullComponentMaskSwap.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopFullMaskFineRelation.Part3


namespace StatMech.FrontierD

noncomputable section

def SixVertexLoopFullMaskFineRelated
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber
      T middle middle profile) : Prop :=
  exists (mask : SixVertexArrows T)
      (hmask : SixVertexFullDisagreementMask
        (sixVertexLoopDecoratedPairColored source.1 false).arrows
        (sixVertexLoopDecoratedPairColored source.1 true).arrows mask)
      (htransfer : sixVertexTorusMaskSeamTransfer mask
        (sixVertexLoopDecoratedPairColored source.1 false).arrows
        (sixVertexLoopDecoratedPairColored source.1 true).arrows = 1),
    target = sixVertexLoopDecoratedFullMaskFineTarget middle hmiddle_pos
      hmiddle_lt profile source mask hmask htransfer

end
end StatMech.FrontierD
