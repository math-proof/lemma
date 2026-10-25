/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopDecoratedUnitTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLexComponentColoredSwap.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedLoopBigradeBridge.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalDiagonalDeficit.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexLoopDecoratedUnitTransfer


namespace StatMech.FrontierD

noncomputable section

variable {T : EvenTorus}

theorem sixVertexLoopDecoratedUnitTransferTarget_colored
    (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (source : SixVertexLoopDecoratedPair T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt))
    (hunit : SixVertexLoopDecoratedLexComponentIsUnit middle
      hmiddle_pos hmiddle_lt source) :
    sixVertexLoopDecoratedPairColored
        (sixVertexLoopDecoratedUnitTransferTarget middle
          hmiddle_pos hmiddle_lt source hunit) =
      sixVertexLexDisagreementComponentColoredTarget
        (sixVertexLoopDecoratedPairColored source)
        (sixVertexLoopDecoratedPositiveSeam
          middle hmiddle_pos hmiddle_lt source) := by
  funext layer
  cases layer <;>
    exact FKColoredLoopPairing.toCompatible_toColored _


theorem sixVertexLoopDecoratedUnitTransferTarget_bigrade
    (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (source : SixVertexLoopDecoratedPair T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt))
    (hunit : SixVertexLoopDecoratedLexComponentIsUnit middle
      hmiddle_pos hmiddle_lt source) :
    sixVertexLoopDecoratedPairBigrade
        (sixVertexLoopDecoratedUnitTransferTarget middle
          hmiddle_pos hmiddle_lt source hunit) =
      sixVertexLoopDecoratedPairBigrade source := by
  rw [sixVertexLoopDecoratedPairBigrade_eq_colored,
    sixVertexLoopDecoratedPairBigrade_eq_colored,
    sixVertexLoopDecoratedUnitTransferTarget_colored]
  exact fkColoredFullSwapTarget_bigrade _ _ _

end
end StatMech.FrontierD
