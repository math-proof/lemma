module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedUnitCrossFineRelation.Part6
public import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexResolvedRoutedKey
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part2


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

theorem sixVertexLoopDecoratedRoutedUnitTarget_colored
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (source : SixVertexLoopDecoratedPair T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt))
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexLoopDecoratedPairColored source)) :
    sixVertexLoopDecoratedPairColored
        (sixVertexLoopDecoratedRoutedUnitTarget middle hmiddle_pos
          hmiddle_lt source key) = key.splice.target := by
  funext layer
  cases layer <;> exact FKColoredLoopPairing.toCompatible_toColored _

end
end StatMech.FrontierD
