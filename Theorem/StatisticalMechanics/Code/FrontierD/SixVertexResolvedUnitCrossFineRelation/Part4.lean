/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedUnitCrossFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopFullMaskFineRelation.Part7
import Def.StatisticalMechanics.Code.FrontierD.SixVertexResolvedUnitCrossFineRelation.Part3


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexLoopDecoratedResolvedUnitCrossFineTarget_bigrade
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (cross : FKColoredResolvedUnitCross
      (sixVertexLoopDecoratedPairColored source.1)) :
    sixVertexLoopDecoratedPairBigrade
        (sixVertexLoopDecoratedResolvedUnitCrossFineTarget middle
          hmiddle_pos hmiddle_lt profile source cross).1 =
      sixVertexLoopDecoratedPairBigrade source.1 := by
  change sixVertexLoopDecoratedPairBigrade
      (sixVertexLoopDecoratedResolvedUnitCrossTarget middle
        hmiddle_pos hmiddle_lt source.1 cross) =
    sixVertexLoopDecoratedPairBigrade source.1
  rw [sixVertexLoopDecoratedPairBigrade_eq_colored,
    sixVertexLoopDecoratedPairBigrade_eq_colored,
    sixVertexLoopDecoratedResolvedUnitCrossTarget_colored]
  exact cross.target_bigrade


end
end StatMech.FrontierD
