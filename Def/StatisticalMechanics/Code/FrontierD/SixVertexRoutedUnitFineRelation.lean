module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedUnitCrossFineRelation.Part6
public import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexResolvedRoutedKey
public import Structure.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRoutedUnitFineRelation.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

namespace FKColoredFineTwoCycleUnitTransferRoutedKey

def splice {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey source) :
    FKColoredStrandSplice source :=
  key.toFKColoredUnitTransferRoutedKey.splice

end FKColoredFineTwoCycleUnitTransferRoutedKey
end
end StatMech.FrontierD
