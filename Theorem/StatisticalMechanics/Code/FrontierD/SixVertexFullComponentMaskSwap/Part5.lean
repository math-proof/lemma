/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullComponentMaskSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopLexUnitFineRelation
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFullComponentMaskSwap.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexLoopDecoratedFullMaskTarget_colored
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
    sixVertexLoopDecoratedPairColored
        (sixVertexLoopDecoratedFullMaskTarget middle hmiddle_pos hmiddle_lt
          source mask hmask htransfer) =
      sixVertexFullDisagreementColoredTarget
        (sixVertexLoopDecoratedPairColored source) mask hmask := by
  funext layer
  cases layer <;> exact FKColoredLoopPairing.toCompatible_toColored _

theorem sixVertexLoopDecoratedFullMaskTarget_bigrade
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
    sixVertexLoopDecoratedPairBigrade
        (sixVertexLoopDecoratedFullMaskTarget middle hmiddle_pos hmiddle_lt
          source mask hmask htransfer) =
      sixVertexLoopDecoratedPairBigrade source := by
  rw [sixVertexLoopDecoratedPairBigrade_eq_colored,
    sixVertexLoopDecoratedPairBigrade_eq_colored,
    sixVertexLoopDecoratedFullMaskTarget_colored]
  exact sixVertexFullDisagreementColoredTarget_bigrade _ _ _

end
end StatMech.FrontierD
