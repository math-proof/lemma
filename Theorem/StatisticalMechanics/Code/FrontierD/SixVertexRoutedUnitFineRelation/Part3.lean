/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRoutedUnitFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedUnitCrossFineRelation.Part6
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexResolvedRoutedKey
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part3


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexLoopDecoratedRoutedUnitFineTarget_bigrade
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexLoopDecoratedPairColored source.1)) :
    sixVertexLoopDecoratedPairBigrade
        (sixVertexLoopDecoratedRoutedUnitFineTarget middle hmiddle_pos
          hmiddle_lt profile source key).1 =
      sixVertexLoopDecoratedPairBigrade source.1 := by
  change sixVertexLoopDecoratedPairBigrade
      (sixVertexLoopDecoratedRoutedUnitTarget middle hmiddle_pos
        hmiddle_lt source.1 key) =
    sixVertexLoopDecoratedPairBigrade source.1
  rw [sixVertexLoopDecoratedPairBigrade_eq_colored,
    sixVertexLoopDecoratedPairBigrade_eq_colored,
    sixVertexLoopDecoratedRoutedUnitTarget_colored]
  exact key.target_bigrade

end
end StatMech.FrontierD
