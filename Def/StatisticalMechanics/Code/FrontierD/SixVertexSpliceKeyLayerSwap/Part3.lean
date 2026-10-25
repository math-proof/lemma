/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSpliceKeyLayerSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexSpliceKeyLayerSwap


namespace StatMech.FrontierD

noncomputable section

namespace FKColoredFineTwoCycleUnitTransferSpliceKey

def ofRoutedKey
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey source) :
    FKColoredFineTwoCycleUnitTransferSpliceKey source where
  splice := key.splice
  preservesTotalC := key.toFKColoredUnitTransferRoutedKey.preservesTotalC
  seamDelta_false := key.toFKColoredUnitTransferRoutedKey.seamDelta_false
  seamDelta_true := key.toFKColoredUnitTransferRoutedKey.seamDelta_true
  fine := key.fine
  twoCycle := key.twoCycle


end FKColoredFineTwoCycleUnitTransferSpliceKey
end
end StatMech.FrontierD
