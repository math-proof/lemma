/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullComponentMaskSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopLexUnitFineRelation
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullComponentMaskSwap.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexLoopDecoratedFullMaskTarget
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (source : SixVertexLoopDecoratedPair T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt))
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (sixVertexLoopDecoratedPairColored source false).arrows
      (sixVertexLoopDecoratedPairColored source true).arrows mask)
    (htransfer : sixVertexTorusMaskSeamTransfer mask
      (sixVertexLoopDecoratedPairColored source false).arrows
      (sixVertexLoopDecoratedPairColored source true).arrows = 1) :
    SixVertexLoopDecoratedPair T middle middle := by
  let colored := sixVertexLoopDecoratedPairColored source
  let target := sixVertexFullDisagreementColoredTarget colored mask hmask
  have hsectors := sixVertexFullDisagreementColoredTarget_middleSectors
    colored mask hmask middle.val
    (by simpa [colored, sixVertexHorizontalLowerSector] using source.1.1.2.2)
    (by simpa [colored, sixVertexHorizontalUpperSector] using source.1.2.2.2)
    hmiddle_pos htransfer
  exact ⟨(⟨(target false).arrows, (target false).iceRule, hsectors.1⟩,
      ⟨(target true).arrows, (target true).iceRule, hsectors.2⟩),
    (target false).toCompatible, (target true).toCompatible⟩

end
end StatMech.FrontierD
