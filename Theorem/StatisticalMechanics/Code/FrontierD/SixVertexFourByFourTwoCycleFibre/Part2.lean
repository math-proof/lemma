/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByFourAudited_valid :
    sixVertexFourByFourAuditedSourceFirst.IceRule /\
      sixVertexFourByFourAuditedSourceSecond.IceRule /\
      sixVertexFourByFourAuditedTargetFirst.IceRule /\
      sixVertexFourByFourAuditedTargetSecond.IceRule /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByFourTorus
            sixVertexFourByFourAuditedSourceFirst
            (svFinLast sixVertexFourByFourTorus.height_pos)) = 1 /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByFourTorus
            sixVertexFourByFourAuditedSourceSecond
            (svFinLast sixVertexFourByFourTorus.height_pos)) = 3 /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByFourTorus
            sixVertexFourByFourAuditedTargetFirst
            (svFinLast sixVertexFourByFourTorus.height_pos)) = 2 /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByFourTorus
            sixVertexFourByFourAuditedTargetSecond
            (svFinLast sixVertexFourByFourTorus.height_pos)) = 2 := by
  decide +revert


theorem sixVertexFourByFourAudited_twoCycleRelated :
    sixVertexPairAtMostTwoCycleRelated
      (sixVertexFourByFourAuditedSourceFirst,
        sixVertexFourByFourAuditedSourceSecond)
      (sixVertexFourByFourAuditedTargetFirst,
        sixVertexFourByFourAuditedTargetSecond) := by
  let family := sixVertexFourByFourOppositeVerticalColumnFamily
    (1 : Fin 4) (2 : Fin 4) (by decide)
  refine ⟨family, true, ?_, ?_⟩
  · funext v
    rcases v with ⟨x, y⟩
    fin_cases x <;> fin_cases y <;> decide +revert
  · funext v
    rcases v with ⟨x, y⟩
    fin_cases x <;> fin_cases y <;> decide +revert

theorem sixVertexFourByFourAudited_fineRelated :
    sixVertexPairAtMostTwoCycleFineRelated
      (sixVertexFourByFourAuditedSourceFirst,
        sixVertexFourByFourAuditedSourceSecond)
      (sixVertexFourByFourAuditedTargetFirst,
        sixVertexFourByFourAuditedTargetSecond) :=
  ⟨sixVertexFourByFourAudited_twoCycleRelated, rfl⟩


end
end StatMech.FrontierD
