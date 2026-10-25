/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRoutedUnitFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedUnitCrossFineRelation.Part6
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexResolvedRoutedKey
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation


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
