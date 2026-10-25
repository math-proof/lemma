/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCheckerHorizontalBigrade
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalCompletionBigrade.Part6
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem card_sixVertexHorizontalSectorCompletion_eq_sum_columnFibers
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T) :
    Fintype.card
        (SixVertexHorizontalSectorCompletion T sector horizontal) =
      ∑ row : SixVertexSector T.width sector.val,
        ∏ i : Fin T.width,
          Fintype.card
            (SixVertexVerticalColumnCompletionAtSeam T horizontal i
              (sixVertexSectorRow row i)) := by
  rw [Fintype.card_congr
      (sixVertexHorizontalSectorCompletionEquivColumns
        T sector horizontal),
    Fintype.card_congr
      (sixVertexColumnCompletionFamilyEquivSectorRow
        T sector horizontal),
    Fintype.card_sigma]
  simp only [Fintype.card_pi]


end
end StatMech.FrontierD
