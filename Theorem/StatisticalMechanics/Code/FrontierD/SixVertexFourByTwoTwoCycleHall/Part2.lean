/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleObstructionRepair.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part2


namespace StatMech.FrontierD

noncomputable section

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoOrdinaryFlat_fineUnion
    (i : Fin 200) (hordinary : ¬ sixVertexFourByTwoExceptionalFlatIndex i) :
    sixVertexPairUnionHorizontal (sixVertexFourByTwoSourceFlatArrows i) =
        sixVertexPairUnionHorizontal (sixVertexFourByTwoTargetFlatArrows i) /\
      sixVertexPairUnionVertical (sixVertexFourByTwoSourceFlatArrows i) =
        sixVertexPairUnionVertical (sixVertexFourByTwoTargetFlatArrows i) /\
      sixVertexHorizontalPairBoundedFineRowProfile
          ((sixVertexFourByTwoSourceFlatArrows i).1.horizontal,
            (sixVertexFourByTwoSourceFlatArrows i).2.horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile
          ((sixVertexFourByTwoTargetFlatArrows i).1.horizontal,
            (sixVertexFourByTwoTargetFlatArrows i).2.horizontal) := by
  fin_cases i <;>
    simp [sixVertexFourByTwoExceptionalFlatIndex] at hordinary <;>
    decide +revert


end
end StatMech.FrontierD
