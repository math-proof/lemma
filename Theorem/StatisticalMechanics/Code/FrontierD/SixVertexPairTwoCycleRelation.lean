/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCirculation.Part6
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation.Part3


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexPairAtMostTwoCycleRelated_refl
    {T : EvenTorus} (pair : SixVertexArrows T × SixVertexArrows T) :
    sixVertexPairAtMostTwoCycleRelated pair pair := by
  refine ⟨SixVertexAtMostTwoCycleFamily.empty T, true, ?_, ?_⟩
  all_goals funext v
  all_goals simp [sixVertexPairUnionHorizontalDelta,
    sixVertexPairUnionVerticalDelta,
    SixVertexAtMostTwoCycleFamily.horizontalFlow,
    SixVertexAtMostTwoCycleFamily.verticalFlow,
    SixVertexAtMostTwoCycleFamily.empty]


theorem sixVertexPairAtMostTwoCycleRelated_of_union_eq
    {T : EvenTorus}
    {source target : SixVertexArrows T × SixVertexArrows T}
    (hhorizontal : sixVertexPairUnionHorizontal source =
      sixVertexPairUnionHorizontal target)
    (hvertical : sixVertexPairUnionVertical source =
      sixVertexPairUnionVertical target) :
    sixVertexPairAtMostTwoCycleRelated source target := by
  refine ⟨SixVertexAtMostTwoCycleFamily.empty T, true, ?_, ?_⟩
  · funext v
    have h := congrFun hhorizontal v
    simp [sixVertexPairUnionHorizontalDelta,
      SixVertexAtMostTwoCycleFamily.horizontalFlow,
      SixVertexAtMostTwoCycleFamily.empty, h]
  · funext v
    have h := congrFun hvertical v
    simp [sixVertexPairUnionVerticalDelta,
      SixVertexAtMostTwoCycleFamily.verticalFlow,
      SixVertexAtMostTwoCycleFamily.empty, h]

theorem sixVertexPairAtMostTwoCycleFineRelated_refl
    {T : EvenTorus} (pair : SixVertexArrows T × SixVertexArrows T) :
    sixVertexPairAtMostTwoCycleFineRelated pair pair := by
  exact ⟨sixVertexPairAtMostTwoCycleRelated_refl pair, rfl⟩

theorem sixVertexPairAtMostTwoCycleRelated_symm
    {T : EvenTorus} {source target :
      SixVertexArrows T × SixVertexArrows T}
    (hrelated : sixVertexPairAtMostTwoCycleRelated source target) :
    sixVertexPairAtMostTwoCycleRelated target source := by
  rcases hrelated with ⟨family, sign, hhorizontal, hvertical⟩
  refine ⟨family, !sign, ?_, ?_⟩
  · funext v
    have h := congrFun hhorizontal v
    unfold sixVertexPairUnionHorizontalDelta at h ⊢
    cases sign <;> simp at h ⊢ <;> omega
  · funext v
    have h := congrFun hvertical v
    unfold sixVertexPairUnionVerticalDelta at h ⊢
    cases sign <;> simp at h ⊢ <;> omega

theorem sixVertexPairAtMostTwoCycleFineRelated_symm
    {T : EvenTorus} {source target :
      SixVertexArrows T × SixVertexArrows T}
    (hrelated : sixVertexPairAtMostTwoCycleFineRelated source target) :
    sixVertexPairAtMostTwoCycleFineRelated target source := by
  exact ⟨sixVertexPairAtMostTwoCycleRelated_symm hrelated.1,
    hrelated.2.symm⟩


theorem sixVertexPairAtMostTwoCycleFineRelated_totalC
    {T : EvenTorus}
    {source target : SixVertexArrows T × SixVertexArrows T}
    (hrelated : sixVertexPairAtMostTwoCycleFineRelated source target) :
    sixVertexTorusCTypeCount source.1 +
        sixVertexTorusCTypeCount source.2 =
      sixVertexTorusCTypeCount target.1 +
        sixVertexTorusCTypeCount target.2 := by
  have hgrade :
      sixVertexHorizontalPairBigrade
          (source.1.horizontal, source.2.horizontal) =
        sixVertexHorizontalPairBigrade
          (target.1.horizontal, target.2.horizontal) := by
    rw [sixVertexHorizontalPairBigrade_eq_fineRowProfileGrade,
      sixVertexHorizontalPairBigrade_eq_fineRowProfileGrade,
      hrelated.2]
  have hfirst := congrArg Prod.fst hgrade
  simpa [sixVertexHorizontalPairBigrade,
    sixVertexTorusCTypeCount_eq_checkerHorizontal_nontransitionCount] using
      hfirst

end
end StatMech.FrontierD
