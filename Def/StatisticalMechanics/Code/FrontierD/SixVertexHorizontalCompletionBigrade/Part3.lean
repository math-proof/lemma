/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCheckerHorizontalBigrade
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalCompletionBigrade
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexConfigurationPairBigradeFiberEquivHorizontalCompletions
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (grade : Nat × Nat) :
    {pair : SixVertexMarkedSectorConfiguration T left ×
        SixVertexMarkedSectorConfiguration T right //
      sixVertexConfigurationPairBigrade pair = grade} ≃
      Sigma fun horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade} =>
        SixVertexHorizontalSectorCompletion T left horizontal.1.1 ×
          SixVertexHorizontalSectorCompletion T right horizontal.1.2 where
  toFun pair :=
    ⟨⟨(pair.1.1.1.horizontal, pair.1.2.1.horizontal), by
        rw [← sixVertexConfigurationPairBigrade_eq_horizontalPairBigrade
          pair.1]
        exact pair.2⟩,
      (⟨⟨pair.1.1.1.vertical, pair.1.1.2.1⟩, pair.1.1.2.2⟩,
        ⟨⟨pair.1.2.1.vertical, pair.1.2.2.1⟩, pair.1.2.2.2⟩)⟩
  invFun completed := by
    let first : SixVertexMarkedSectorConfiguration T left :=
      ⟨sixVertexArrowsOfFields completed.1.1.1 completed.2.1.1.1,
        completed.2.1.1.2, completed.2.1.2⟩
    let second : SixVertexMarkedSectorConfiguration T right :=
      ⟨sixVertexArrowsOfFields completed.1.1.2 completed.2.2.1.1,
        completed.2.2.1.2, completed.2.2.2⟩
    exact ⟨(first, second), by
      rw [sixVertexConfigurationPairBigrade_eq_horizontalPairBigrade]
      exact completed.1.2⟩
  left_inv pair := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;>
      apply SixVertexArrows.ext <;> rfl
  right_inv completed := by
    rcases completed with
      ⟨⟨⟨firstHorizontal, secondHorizontal⟩, hgrade⟩,
        ⟨⟨⟨firstVertical, firstIce⟩, firstSector⟩,
          ⟨⟨secondVertical, secondIce⟩, secondSector⟩⟩⟩
    rfl


end
end StatMech.FrontierD
