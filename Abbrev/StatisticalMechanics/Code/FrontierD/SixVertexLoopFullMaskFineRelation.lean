/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullComponentMaskSwap.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopFullMaskFineRelation.Part2


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexLoopFullUnitMask
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile) :=
  {mask : SixVertexArrows T //
    SixVertexFullDisagreementMask
        (sixVertexLoopDecoratedPairColored source.1 false).arrows
        (sixVertexLoopDecoratedPairColored source.1 true).arrows mask /\
      sixVertexTorusMaskSeamTransfer mask
        (sixVertexLoopDecoratedPairColored source.1 false).arrows
        (sixVertexLoopDecoratedPairColored source.1 true).arrows = 1}


abbrev SixVertexLoopFullNegativeMask
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (target : SixVertexLoopDecoratedPairFineProfileFiber
      T middle middle profile) :=
  {mask : SixVertexArrows T //
    SixVertexFullDisagreementMask
        (sixVertexLoopDecoratedPairColored target.1 false).arrows
        (sixVertexLoopDecoratedPairColored target.1 true).arrows mask /\
      sixVertexTorusMaskSeamTransfer mask
        (sixVertexLoopDecoratedPairColored target.1 false).arrows
        (sixVertexLoopDecoratedPairColored target.1 true).arrows = -1}

end
end StatMech.FrontierD
