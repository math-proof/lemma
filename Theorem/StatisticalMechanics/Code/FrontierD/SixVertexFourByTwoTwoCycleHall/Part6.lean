/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleObstructionRepair.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part6


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByTwoMatchingIndex_fineRelated
    (i : Fin 4 × Fin 50) :
    sixVertexPairAtMostTwoCycleFineRelated
      (sixVertexFourByTwoSourceIndexArrows i)
      (sixVertexFourByTwoTargetIndexArrows
        (sixVertexFourByTwoMatchingIndex i)) := by
  simpa [sixVertexFourByTwoSourceFlatArrows,
    sixVertexFourByTwoTargetFlatArrows,
    sixVertexFourByTwoMatchingIndex] using
      sixVertexFourByTwoMatchingTable_fineRelated
        (finProdFinEquiv (m := 4) (n := 50) i)


end
end StatMech.FrontierD
