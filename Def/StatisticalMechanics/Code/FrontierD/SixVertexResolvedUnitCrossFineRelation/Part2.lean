/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedUnitCrossFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopFullMaskFineRelation.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedUnitCrossFineRelation.Part2


namespace StatMech.FrontierD

noncomputable section

def sixVertexLoopDecoratedResolvedUnitCrossTarget
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (source : SixVertexLoopDecoratedPair T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt))
    (cross : FKColoredResolvedUnitCross
      (sixVertexLoopDecoratedPairColored source)) :
    SixVertexLoopDecoratedPair T middle middle := by
  let colored := sixVertexLoopDecoratedPairColored source
  have hsectors := fkColoredVertexCrossTarget_middleSectors colored
    cross.mask cross.bondCoherent middle.val hmiddle_pos
    (by simpa [colored, sixVertexHorizontalLowerSector] using source.1.1.2.2)
    (by simpa [colored, sixVertexHorizontalUpperSector] using source.1.2.2.2)
    cross.seamDelta_false cross.seamDelta_true
  exact ⟨(⟨(cross.target false).arrows,
      (cross.target false).iceRule, hsectors.1⟩,
    ⟨(cross.target true).arrows,
      (cross.target true).iceRule, hsectors.2⟩),
    (cross.target false).toCompatible,
    (cross.target true).toCompatible⟩

end
end StatMech.FrontierD
