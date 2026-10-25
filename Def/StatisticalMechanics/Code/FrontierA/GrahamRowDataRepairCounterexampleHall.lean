/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRowDataRepairCounterexampleHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamRowDataRepairRelation.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamRowDataRepairCounterexampleHall


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

noncomputable def weightedCollisionFiberEmbedding :
    leftFiber weightedCollisionEnds Finset.univ {1, 0} {0, 2} 0 3 ↪
      rightFiber weightedCollisionEnds Finset.univ {1, 0} {0, 2} 0 3 where
  toFun c := ⟨balancedSwap Finset.univ {3} ∅ c.1,
    weightedCollision_leaf_swap_right c⟩
  inj' := by
    intro c d hcd
    apply Subtype.ext
    have hswap := congrArg Subtype.val hcd
    calc
      c.1 = balancedSwap Finset.univ {3} ∅
          (balancedSwap Finset.univ {3} ∅ c.1) :=
        (balancedSwap_involutive Finset.univ {3} ∅ c.1).symm
      _ = balancedSwap Finset.univ {3} ∅
          (balancedSwap Finset.univ {3} ∅ d.1) := congrArg _ hswap
      _ = d.1 := balancedSwap_involutive Finset.univ {3} ∅ d.1


noncomputable def weightedCollisionRowDataEmbedding :
    leftRowData weightedCollisionEnds Finset.univ 1 0 2 3 ↪
      rightRowData weightedCollisionEnds Finset.univ 1 0 2 3 where
  toFun d := rightFiberToRowData weightedCollisionEnds Finset.univ 1 0 2 3
    (weightedCollisionFiberEmbedding
      (rowDataToLeftFiber weightedCollisionEnds Finset.univ 1 0 2 3 d))
  inj' := by
    intro d e hde
    apply rowDataToLeftFiber_injective
    apply weightedCollisionFiberEmbedding.injective
    exact (rightFiberEquivRowData weightedCollisionEnds Finset.univ 1 0 2 3).injective hde

end StatMech.GrahamGHS.FourColor
