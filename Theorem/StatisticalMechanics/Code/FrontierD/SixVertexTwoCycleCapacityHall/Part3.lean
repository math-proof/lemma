/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTwoCycleCapacityHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairedBranchResidualHall.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexTwoCycleCapacityHall
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexPairFineUnionKeyTwoCycleRelated_refl
    {T : EvenTorus} (key : SixVertexPairFineUnionKey T) :
    SixVertexPairFineUnionKeyTwoCycleRelated key key := by
  refine ⟨rfl, SixVertexAtMostTwoCycleFamily.empty T, true, ?_, ?_⟩
  all_goals funext v
  all_goals simp [SixVertexAtMostTwoCycleFamily.horizontalFlow,
    SixVertexAtMostTwoCycleFamily.verticalFlow,
    SixVertexAtMostTwoCycleFamily.empty]

theorem sixVertexPairFineUnionKeyTwoCycleRelated_symm
    {T : EvenTorus} {source target : SixVertexPairFineUnionKey T}
    (hrelated : SixVertexPairFineUnionKeyTwoCycleRelated source target) :
    SixVertexPairFineUnionKeyTwoCycleRelated target source := by
  rcases hrelated with
    ⟨hfine, family, sign, hhorizontal, hvertical⟩
  refine ⟨hfine.symm, family, !sign, ?_, ?_⟩
  · funext v
    have h := congrFun hhorizontal v
    cases sign <;> simp at h ⊢ <;> omega
  · funext v
    have h := congrFun hvertical v
    cases sign <;> simp at h ⊢ <;> omega


theorem sixVertexPairFineUnionKeyTwoCycleRelated_sound
    {T : EvenTorus}
    {source target : SixVertexArrows T × SixVertexArrows T}
    (hrelated : SixVertexPairFineUnionKeyTwoCycleRelated
      (sixVertexPairFineUnionKey source)
      (sixVertexPairFineUnionKey target)) :
    sixVertexPairAtMostTwoCycleFineRelated source target := by
  rcases hrelated with ⟨hfine, family, sign, hhorizontal, hvertical⟩
  refine ⟨⟨family, sign, ?_, ?_⟩, ?_⟩
  · funext v
    have h := congrFun hhorizontal v
    simpa [sixVertexPairFineUnionKey,
      sixVertexPairUnionHorizontalDelta,
      sixVertexPairUnionHorizontal] using h
  · funext v
    have h := congrFun hvertical v
    simpa [sixVertexPairFineUnionKey,
      sixVertexPairUnionVerticalDelta,
      sixVertexPairUnionVertical] using h
  · simpa [sixVertexPairFineUnionKey] using hfine


theorem sixVertexPairFineUnionKeyTwoCycleRelated_complete
    {T : EvenTorus}
    {source target : SixVertexArrows T × SixVertexArrows T}
    (hrelated : sixVertexPairAtMostTwoCycleFineRelated source target) :
    SixVertexPairFineUnionKeyTwoCycleRelated
      (sixVertexPairFineUnionKey source)
      (sixVertexPairFineUnionKey target) := by
  rcases hrelated with
    ⟨⟨family, sign, hhorizontal, hvertical⟩, hfine⟩
  refine ⟨?_, family, sign, ?_, ?_⟩
  · simpa [sixVertexPairFineUnionKey] using hfine
  · funext v
    have h := congrFun hhorizontal v
    simpa [sixVertexPairFineUnionKey,
      sixVertexPairUnionHorizontalDelta,
      sixVertexPairUnionHorizontal] using h
  · funext v
    have h := congrFun hvertical v
    simpa [sixVertexPairFineUnionKey,
      sixVertexPairUnionVerticalDelta,
      sixVertexPairUnionVertical] using h

end
end StatMech.FrontierD
