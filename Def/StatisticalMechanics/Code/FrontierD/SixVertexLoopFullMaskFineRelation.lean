/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullComponentMaskSwap.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopFullMaskFineRelation


namespace StatMech.FrontierD

noncomputable section

def sixVertexLoopDecoratedFullMaskFineTarget
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (sixVertexLoopDecoratedPairColored source.1 false).arrows
      (sixVertexLoopDecoratedPairColored source.1 true).arrows mask)
    (htransfer : sixVertexTorusMaskSeamTransfer mask
      (sixVertexLoopDecoratedPairColored source.1 false).arrows
      (sixVertexLoopDecoratedPairColored source.1 true).arrows = 1) :
    SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile := by
  refine ⟨sixVertexLoopDecoratedFullMaskTarget middle hmiddle_pos
    hmiddle_lt source.1 mask hmask htransfer, ?_⟩
  have hfine := sixVertexFullDisagreementColoredTarget_boundedFineRowProfile
    (sixVertexLoopDecoratedPairColored source.1) mask hmask
  rw [← sixVertexLoopDecoratedFullMaskTarget_colored middle hmiddle_pos
    hmiddle_lt source.1 mask hmask htransfer] at hfine
  exact hfine.trans source.2

end
end StatMech.FrontierD
