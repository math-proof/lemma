/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRowDataRepairCounterexampleHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamRowDataRepairRelation.Part4
import Def.StatisticalMechanics.Code.FrontierA.GrahamRowDataRepairCounterexampleHall


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

theorem weightedCollisionRowDataEmbedding_related
    (d : leftRowData weightedCollisionEnds Finset.univ 1 0 2 3) :
    RowDataRepairRelated weightedCollisionEnds Finset.univ 1 0 2 3 d
      (weightedCollisionRowDataEmbedding d) := by
  rw [rowDataRepairRelated_iff_sameMask]
  let c := rowDataToLeftFiber weightedCollisionEnds Finset.univ 1 0 2 3 d
  change fourColorMaskProfile Finset.univ c.1 =
    fourColorMaskProfile Finset.univ
      (rowDataToRightFiber weightedCollisionEnds Finset.univ 1 0 2 3
        (rightFiberToRowData weightedCollisionEnds Finset.univ 1 0 2 3
          (weightedCollisionFiberEmbedding c))).1
  rw [rowDataToRightFiber_leftInverse]
  exact (fourColorMaskProfile_balancedSwap Finset.univ {3} ∅ c.1).symm


theorem weightedCollision_rowDataRepairHall :
    RowDataRepairHall weightedCollisionEnds Finset.univ 1 0 2 3 :=
  rowDataRepairHall_of_related_embedding _ _ _ _ _ _
    weightedCollisionRowDataEmbedding
    weightedCollisionRowDataEmbedding_related

theorem weightedCollision_weightedRowMinor :
    GrahamWeightedRowMinor weightedCollisionEnds Finset.univ 1 0 2 3 :=
  GrahamWeightedRowMinor_of_rowDataRepairHall _ _ _ _ _ _
    weightedCollision_rowDataRepairHall

end StatMech.GrahamGHS.FourColor
