/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleObstructionRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionMatchingNoGo.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleObstructionRepair.Part3


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByTwoExceptional_valid (i : Fin 4) :
    (sixVertexFourByTwoExceptionalSourceFirst i).IceRule /\
      (sixVertexFourByTwoExceptionalSourceSecond i).IceRule /\
      (sixVertexFourByTwoExceptionalTargetFirst i).IceRule /\
      (sixVertexFourByTwoExceptionalTargetSecond i).IceRule /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByTwoTorus
            (sixVertexFourByTwoExceptionalSourceFirst i)
            (svFinLast sixVertexFourByTwoTorus.height_pos)) = 0 /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByTwoTorus
            (sixVertexFourByTwoExceptionalSourceSecond i)
            (svFinLast sixVertexFourByTwoTorus.height_pos)) = 2 /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByTwoTorus
            (sixVertexFourByTwoExceptionalTargetFirst i)
            (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByTwoTorus
            (sixVertexFourByTwoExceptionalTargetSecond i)
            (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 := by
  fin_cases i <;> decide +revert

theorem sixVertexFourByTwoExceptional_related (i : Fin 4) :
    sixVertexPairAtMostTwoCycleRelated
      (sixVertexFourByTwoExceptionalSourceFirst i,
        sixVertexFourByTwoExceptionalSourceSecond i)
      (sixVertexFourByTwoExceptionalTargetFirst i,
        sixVertexFourByTwoExceptionalTargetSecond i) := by
  refine ⟨sixVertexFourByTwoBottomCycleFamily,
    sixVertexFourByTwoExceptionalCycleSign i, ?_, ?_⟩
  · funext v
    rcases v with ⟨x, y⟩
    fin_cases i <;> fin_cases x <;> fin_cases y <;> decide +revert
  · funext v
    rcases v with ⟨x, y⟩
    fin_cases i <;> fin_cases x <;> fin_cases y <;> decide +revert

theorem sixVertexFourByTwoExceptional_fineProfile (i : Fin 4) :
    sixVertexHorizontalPairBoundedFineRowProfile
        ((sixVertexFourByTwoExceptionalSourceFirst i).horizontal,
          (sixVertexFourByTwoExceptionalSourceSecond i).horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile
        ((sixVertexFourByTwoExceptionalTargetFirst i).horizontal,
          (sixVertexFourByTwoExceptionalTargetSecond i).horizontal) := by
  fin_cases i <;> decide +revert


theorem sixVertexFourByTwoExceptional_fineRelated (i : Fin 4) :
    sixVertexPairAtMostTwoCycleFineRelated
      (sixVertexFourByTwoExceptionalSourceFirst i,
        sixVertexFourByTwoExceptionalSourceSecond i)
      (sixVertexFourByTwoExceptionalTargetFirst i,
        sixVertexFourByTwoExceptionalTargetSecond i) :=
  ⟨sixVertexFourByTwoExceptional_related i,
    sixVertexFourByTwoExceptional_fineProfile i⟩

end
end StatMech.FrontierD
