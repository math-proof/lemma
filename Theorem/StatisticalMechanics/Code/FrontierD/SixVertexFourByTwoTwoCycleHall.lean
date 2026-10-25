/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleObstructionRepair.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall


namespace StatMech.FrontierD

noncomputable section

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoMatchingTable_injective :
    Function.Injective sixVertexFourByTwoMatchingTable := by
  decide +revert

theorem sixVertexFourByTwoMatchingIndex_injective :
    Function.Injective sixVertexFourByTwoMatchingIndex := by
  exact sixVertexFourByTwoMatchingTable_injective.comp
    (finProdFinEquiv (m := 4) (n := 50)).injective

theorem sixVertexFourByTwoSectorZeroArrows_valid (i : Fin 4) :
    (sixVertexFourByTwoSectorZeroArrows i).IceRule /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByTwoTorus
            (sixVertexFourByTwoSectorZeroArrows i)
            (svFinLast sixVertexFourByTwoTorus.height_pos)) = 0 := by
  fin_cases i <;> decide +revert

theorem sixVertexFourByTwoSectorOneArrows_valid (i : Fin 28) :
    (sixVertexFourByTwoSectorOneArrows i).IceRule /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByTwoTorus
            (sixVertexFourByTwoSectorOneArrows i)
            (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 := by
  fin_cases i <;> decide +revert

theorem sixVertexFourByTwoSectorTwoArrows_valid (i : Fin 50) :
    (sixVertexFourByTwoSectorTwoArrows i).IceRule /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByTwoTorus
            (sixVertexFourByTwoSectorTwoArrows i)
            (svFinLast sixVertexFourByTwoTorus.height_pos)) = 2 := by
  fin_cases i <;> decide +revert

end
end StatMech.FrontierD
