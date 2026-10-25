/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSpliceKeyLayerSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexSpliceKeyLayerSwap.Part3


namespace StatMech.FrontierD

noncomputable section

namespace FKColoredFineTwoCycleUnitTransferSpliceKey

@[simp] theorem recovers_source
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey source) :
    key.splice.symm.target = source :=
  key.splice.symm_target


theorem target_bigrade
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey source) :
    (fkColoredLoopPairingPairTotalC key.splice.target,
        fkColoredTrueStrandSlotCount key.splice.target) =
      (fkColoredLoopPairingPairTotalC source,
        fkColoredTrueStrandSlotCount source) :=
  key.splice.target_bigrade key.preservesTotalC


theorem target_twoCycleFine
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey source) :
    sixVertexPairAtMostTwoCycleFineRelated
      ((source false).arrows, (source true).arrows)
      ((key.splice.target false).arrows,
        (key.splice.target true).arrows) :=
  ⟨key.twoCycle, key.fine.symm⟩


end FKColoredFineTwoCycleUnitTransferSpliceKey
end
end StatMech.FrontierD
