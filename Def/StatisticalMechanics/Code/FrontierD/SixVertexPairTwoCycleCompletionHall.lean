/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleCompletionHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleHall.Part3
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleCompletionHall


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalFineProfileCompletionPairArrows
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    {profile : SixVertexHorizontalBoundedFineRowProfile T}
    (completed : SixVertexHorizontalFineProfileCompletionPair
      T left right profile) : SixVertexArrows T × SixVertexArrows T :=
  (sixVertexArrowsOfFields completed.1.1.1 completed.2.1.1.1,
    sixVertexArrowsOfFields completed.1.1.2 completed.2.2.1.1)


def sixVertexConfigurationPairFineProfileFiberEquivHorizontalCompletions
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (profile : SixVertexHorizontalBoundedFineRowProfile T) :
    SixVertexConfigurationPairFineProfileFiber T left right profile ≃
      SixVertexHorizontalFineProfileCompletionPair
        T left right profile where
  toFun pair :=
    ⟨⟨(pair.1.1.1.horizontal, pair.1.2.1.horizontal), pair.2⟩,
      (⟨⟨pair.1.1.1.vertical, pair.1.1.2.1⟩, pair.1.1.2.2⟩,
        ⟨⟨pair.1.2.1.vertical, pair.1.2.2.1⟩, pair.1.2.2.2⟩)⟩
  invFun completed :=
    ⟨(⟨sixVertexArrowsOfFields
          completed.1.1.1 completed.2.1.1.1,
        completed.2.1.1.2, completed.2.1.2⟩,
      ⟨sixVertexArrowsOfFields
          completed.1.1.2 completed.2.2.1.1,
        completed.2.2.1.2, completed.2.2.2⟩),
      completed.1.2⟩
  left_inv pair := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;>
      apply SixVertexArrows.ext <;> rfl
  right_inv completed := by
    rcases completed with
      ⟨⟨⟨firstHorizontal, secondHorizontal⟩, hprofile⟩,
        ⟨⟨⟨firstVertical, firstIce⟩, firstSector⟩,
          ⟨⟨secondVertical, secondIce⟩, secondSector⟩⟩⟩
    rfl

end
end StatMech.FrontierD
