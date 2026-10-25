/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSpliceKeyLayerSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexSpliceKeyLayerSwap.Part7


namespace StatMech.FrontierD

noncomputable section

namespace FKColoredFineTwoCycleUnitTransferSpliceKey

theorem paired_target_distinct
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey source)
    (hsource : SourceSeamDifferenceTwo source)
    (hlayers : key.splice.target false ≠ key.splice.target true) :
    (key.paired hsource false).splice.target ≠
      (key.paired hsource true).splice.target := by
  intro heq
  apply hlayers
  have hfalse := congrFun heq false
  simpa [paired] using hfalse

end FKColoredFineTwoCycleUnitTransferSpliceKey
end
end StatMech.FrontierD
