/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRoutedKeySourceRebase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexRoutedKeySlotColorInvariant.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRoutedKeySourceRebase


namespace StatMech.FrontierD

noncomputable section

theorem FKColoredFineTwoCycleUnitTransferRoutedKey.rebase_target
    {T : EvenTorus} {source rebased : FKColoredLoopPairingPair T}
    (certificate : FKColoredFineTwoCycleUnitTransferRoutedKey source)
    (hcolor : forall slot : FKLayeredStrandSlot T,
      fkColoredLayeredSlotColor rebased slot =
        fkColoredLayeredSlotColor source slot)
    (harrows : forall layer,
      (rebased layer).arrows = (source layer).arrows) :
    (certificate.rebase hcolor harrows).splice.target =
      certificate.splice.target := by
  exact indexedOccurrenceSplice_target_rebase source rebased
    certificate.toFKColoredUnitTransferRoutedKey.targetPairing
    certificate.toFKColoredUnitTransferRoutedKey.occurrenceCount
    certificate.toFKColoredUnitTransferRoutedKey.key
    certificate.toFKColoredUnitTransferRoutedKey.key_injective hcolor
    certificate.toFKColoredUnitTransferRoutedKey.boundaryIntertwining

end
end StatMech.FrontierD
