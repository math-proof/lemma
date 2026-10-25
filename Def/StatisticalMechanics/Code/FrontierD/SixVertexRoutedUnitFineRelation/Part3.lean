/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRoutedUnitFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedUnitCrossFineRelation.Part6
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexResolvedRoutedKey
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part2


namespace StatMech.FrontierD

noncomputable section

def sixVertexLoopDecoratedRoutedUnitFineTarget
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexLoopDecoratedPairColored source.1)) :
    SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile := by
  refine ⟨sixVertexLoopDecoratedRoutedUnitTarget middle hmiddle_pos
    hmiddle_lt source.1 key, ?_⟩
  rw [sixVertexLoopDecoratedRoutedUnitTarget_colored]
  exact key.target_fine.trans source.2

end
end StatMech.FrontierD
