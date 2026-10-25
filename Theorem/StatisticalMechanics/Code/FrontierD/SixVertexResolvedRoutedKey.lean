/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedRoutedKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexIndexedOccurrenceSplice.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairResolvedInjection.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexResolvedRoutedKey


namespace StatMech.FrontierD

noncomputable section

theorem FKColoredUnitTransferRoutedKey.splice_preservesTotalC
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (certificate : FKColoredUnitTransferRoutedKey source) :
    certificate.splice.PreservesTotalC :=
  certificate.preservesTotalC

theorem FKColoredUnitTransferRoutedKey.splice_seamDelta_false
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (certificate : FKColoredUnitTransferRoutedKey source) :
    certificate.splice.seamDelta false = 1 :=
  certificate.seamDelta_false

theorem FKColoredUnitTransferRoutedKey.splice_seamDelta_true
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (certificate : FKColoredUnitTransferRoutedKey source) :
    certificate.splice.seamDelta true = -1 :=
  certificate.seamDelta_true


theorem FKColoredUnitTransferRoutedKey.target_bigrade
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (certificate : FKColoredUnitTransferRoutedKey source) :
    (fkColoredLoopPairingPairTotalC certificate.splice.target,
        fkColoredTrueStrandSlotCount certificate.splice.target) =
      (fkColoredLoopPairingPairTotalC source,
        fkColoredTrueStrandSlotCount source) :=
  certificate.splice.target_bigrade certificate.splice_preservesTotalC


@[simp] theorem FKColoredUnitTransferRoutedKey.recover
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (certificate : FKColoredUnitTransferRoutedKey source) :
    certificate.splice.symm.target = source :=
  certificate.splice.symm_target


theorem FKColoredUnitTransferRoutedKey.target_middleSectors
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (certificate : FKColoredUnitTransferRoutedKey source)
    (middle : Nat) (hmiddle : 0 < middle)
    (hlower : sixVertexUpCount
        (svTorusVerticalRows T (source false).arrows
          (svFinLast T.height_pos)) = middle - 1)
    (hupper : sixVertexUpCount
        (svTorusVerticalRows T (source true).arrows
          (svFinLast T.height_pos)) = middle + 1) :
    sixVertexUpCount
        (svTorusVerticalRows T (certificate.splice.target false).arrows
          (svFinLast T.height_pos)) = middle /\
      sixVertexUpCount
        (svTorusVerticalRows T (certificate.splice.target true).arrows
          (svFinLast T.height_pos)) = middle :=
  certificate.splice.target_middleSectors middle hmiddle hlower hupper
    certificate.splice_seamDelta_false certificate.splice_seamDelta_true


end
end StatMech.FrontierD
