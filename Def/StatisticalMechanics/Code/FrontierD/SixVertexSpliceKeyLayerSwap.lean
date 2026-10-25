/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSpliceKeyLayerSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4


namespace StatMech.FrontierD

noncomputable section

def fkColoredLoopPairingPairSwapLayers
    {T : EvenTorus} (source : FKColoredLoopPairingPair T) :
    FKColoredLoopPairingPair T :=
  fun layer => source (!layer)

end
end StatMech.FrontierD
