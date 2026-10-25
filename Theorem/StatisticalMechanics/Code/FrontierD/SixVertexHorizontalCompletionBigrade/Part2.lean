/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCheckerHorizontalBigrade
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalCompletionBigrade.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem card_sixVertexConfigurationPairBigradeFiber_eq_horizontalCompletions
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (grade : Nat × Nat) :
    Fintype.card
        {pair : SixVertexMarkedSectorConfiguration T left ×
            SixVertexMarkedSectorConfiguration T right //
          sixVertexConfigurationPairBigrade pair = grade} =
      ∑ horizontal :
          {horizontal : SixVertexHorizontalField T ×
              SixVertexHorizontalField T //
            sixVertexHorizontalPairBigrade horizontal = grade},
        Fintype.card
            (SixVertexHorizontalSectorCompletion T left horizontal.1.1) *
          Fintype.card
            (SixVertexHorizontalSectorCompletion T right horizontal.1.2) := by
  rw [Fintype.card_congr
    (sixVertexConfigurationPairBigradeFiberEquivHorizontalCompletions
      T left right grade), Fintype.card_sigma]
  simp only [Fintype.card_prod]


end
end StatMech.FrontierD
