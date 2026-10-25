/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSpliceKeyLayerSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexSpliceKeyLayerSwap.Part5


namespace StatMech.FrontierD

noncomputable section

namespace FKColoredFineTwoCycleUnitTransferSpliceKey

theorem swapSplice_seamDelta_false
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey source)
    (hsource : SourceSeamDifferenceTwo source) :
    key.swapSplice.seamDelta false = 1 := by
  have hswap := key.swapSplice.target_upCount false
  have horiginal := key.splice.target_upCount true
  rw [key.swapSplice_target] at hswap
  change (sixVertexUpCount
      (svTorusVerticalRows T (key.splice.target true).arrows
        (svFinLast T.height_pos)) : Int) = _ at hswap
  rw [key.seamDelta_true] at horiginal
  unfold SourceSeamDifferenceTwo at hsource
  omega

theorem swapSplice_seamDelta_true
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey source)
    (hsource : SourceSeamDifferenceTwo source) :
    key.swapSplice.seamDelta true = -1 := by
  have hswap := key.swapSplice.target_upCount true
  have horiginal := key.splice.target_upCount false
  rw [key.swapSplice_target] at hswap
  change (sixVertexUpCount
      (svTorusVerticalRows T (key.splice.target false).arrows
        (svFinLast T.height_pos)) : Int) = _ at hswap
  rw [key.seamDelta_false] at horiginal
  unfold SourceSeamDifferenceTwo at hsource
  omega


end FKColoredFineTwoCycleUnitTransferSpliceKey
end
end StatMech.FrontierD
