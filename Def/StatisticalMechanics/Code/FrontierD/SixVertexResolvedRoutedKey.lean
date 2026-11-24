module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexIndexedOccurrenceSplice.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairResolvedInjection.Part2
public import Structure.StatisticalMechanics.Code.FrontierD.SixVertexResolvedRoutedKey


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedRoutedKey.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def FKColoredUnitTransferRoutedKey.splice
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (certificate : FKColoredUnitTransferRoutedKey source) :
    FKColoredStrandSplice source :=
  FKColoredStrandSplice.ofIndexedOccurrences source
    certificate.targetPairing certificate.occurrenceCount certificate.key
    certificate.key_injective certificate.boundaryIntertwining

end
end StatMech.FrontierD
