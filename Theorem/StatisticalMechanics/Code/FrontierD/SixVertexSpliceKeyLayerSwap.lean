/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSpliceKeyLayerSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexSpliceKeyLayerSwap


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkColoredLoopPairingPairSwapLayers_apply
    {T : EvenTorus} (source : FKColoredLoopPairingPair T) (layer : Bool) :
    fkColoredLoopPairingPairSwapLayers source layer = source (!layer) := rfl

@[simp] theorem fkColoredLoopPairingPairSwapLayers_swap
    {T : EvenTorus} (source : FKColoredLoopPairingPair T) :
    fkColoredLoopPairingPairSwapLayers
        (fkColoredLoopPairingPairSwapLayers source) = source := by
  funext layer
  cases layer <;> rfl


end
end StatMech.FrontierD
