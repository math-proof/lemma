/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRoutedUnitFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedUnitCrossFineRelation.Part6
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexResolvedRoutedKey
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation


namespace StatMech.FrontierD

noncomputable section

def sixVertexLoopDecoratedRoutedUnitTarget
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (source : SixVertexLoopDecoratedPair T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt))
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexLoopDecoratedPairColored source)) :
    SixVertexLoopDecoratedPair T middle middle := by
  let colored := sixVertexLoopDecoratedPairColored source
  have hsectors := key.toFKColoredUnitTransferRoutedKey.target_middleSectors
    middle.val hmiddle_pos
    (by simpa [colored, sixVertexHorizontalLowerSector] using source.1.1.2.2)
    (by simpa [colored, sixVertexHorizontalUpperSector] using source.1.2.2.2)
  exact ⟨(⟨(key.splice.target false).arrows,
      (key.splice.target false).iceRule, hsectors.1⟩,
    ⟨(key.splice.target true).arrows,
      (key.splice.target true).iceRule, hsectors.2⟩),
    (key.splice.target false).toCompatible,
    (key.splice.target true).toCompatible⟩

end
end StatMech.FrontierD
