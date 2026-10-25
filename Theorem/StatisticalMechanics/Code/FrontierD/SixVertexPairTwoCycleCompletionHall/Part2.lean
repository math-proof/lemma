/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleCompletionHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleHall.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleCompletionHall.Part2


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexHorizontalFineProfileCompletionPairUnionEqual.twoCycle
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    {profile : SixVertexHorizontalBoundedFineRowProfile T}
    {source : SixVertexHorizontalFineProfileCompletionPair
      T lower upper profile}
    {target : SixVertexHorizontalFineProfileCompletionPair
      T middle middle profile}
    (hunion : SixVertexHorizontalFineProfileCompletionPairUnionEqual
      source target) :
    SixVertexHorizontalFineProfileCompletionPairTwoCycleRelated
      source target := by
  exact sixVertexPairAtMostTwoCycleRelated_of_union_eq
    hunion.1 hunion.2

theorem fineProfileCompletionPairTwoCycleRelated_equiv_iff
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    {profile : SixVertexHorizontalBoundedFineRowProfile T}
    (source : SixVertexConfigurationPairFineProfileFiber
      T lower upper profile)
    (target : SixVertexConfigurationPairFineProfileFiber
      T middle middle profile) :
    SixVertexHorizontalFineProfileCompletionPairTwoCycleRelated
        (sixVertexConfigurationPairFineProfileFiberEquivHorizontalCompletions
          T lower upper profile source)
        (sixVertexConfigurationPairFineProfileFiberEquivHorizontalCompletions
          T middle middle profile target) <->
      SixVertexConfigurationPairTwoCycleFineProfileRelated
        source target := by
  rw [SixVertexHorizontalFineProfileCompletionPairTwoCycleRelated,
    sixVertexFineProfileCompletionPairArrows_equiv,
    sixVertexFineProfileCompletionPairArrows_equiv]
  constructor
  · intro hrelated
    exact ⟨hrelated, source.2.trans target.2.symm⟩
  · intro hrelated
    exact hrelated.1


end
end StatMech.FrontierD
