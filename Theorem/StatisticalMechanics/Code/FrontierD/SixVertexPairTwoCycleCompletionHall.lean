module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleHall.Part3
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleCompletionHall


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleCompletionHall.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexFineProfileCompletionPairArrows_equiv
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    {profile : SixVertexHorizontalBoundedFineRowProfile T}
    (pair : SixVertexConfigurationPairFineProfileFiber
      T left right profile) :
    sixVertexHorizontalFineProfileCompletionPairArrows
        (sixVertexConfigurationPairFineProfileFiberEquivHorizontalCompletions
          T left right profile pair) =
      (pair.1.1.1, pair.1.2.1) := by
  apply Prod.ext <;> apply SixVertexArrows.ext <;> rfl


end
end StatMech.FrontierD
