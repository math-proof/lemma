/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeLoopHallRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeHallRouting.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedLoopBigradeBridge.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedKeySourceRebase.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoAlignedRoutedKey.rebaseToLoopDecoration_target
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (source : SixVertexLoopDecoratedPair T left right)
    (hdegree : SixVertexLocallyDegreeTwo source.1.1.1 source.1.2.1)
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexDegreeTwoAlignedColoredSource source.1.1.2.1
        source.1.2.2.1 hdegree)) :
    (sixVertexDegreeTwoAlignedRoutedKey.rebaseToLoopDecoration
      source hdegree key).splice.target = key.splice.target := by
  apply FKColoredFineTwoCycleUnitTransferRoutedKey.rebase_target

end
end StatMech.FrontierD
