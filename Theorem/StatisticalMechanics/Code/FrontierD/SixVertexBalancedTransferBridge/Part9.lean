/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedBoundaryGluing
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexParticleHole.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part9
open Finset Matrix


namespace StatMech.FrontierD

theorem svHorizontalLocalWeight_eq_torusLocalWeight
    (T : EvenTorus) (c : Real) (omega : SixVertexArrows T)
    (i : Fin T.width) (j : Fin T.height) :
    svHorizontalLocalWeight T.width_pos c
        (svTorusVerticalRows T omega
          (SixVertexArrows.cyclicPred T.height_pos j))
        (svTorusVerticalRows T omega j)
        (svTorusHorizontalRows T omega j) i =
      omega.localWeight c (i, j) := by
  classical
  unfold svHorizontalLocalWeight SixVertexArrows.localWeight
  simp only [svHorizontalIncomingCount, svHorizontalIsC,
    svTorusVerticalRows, svTorusHorizontalRows,
    SixVertexArrows.incomingCount, SixVertexArrows.IsCType]
  apply if_congr
  · omega
  · rfl
  · rfl

theorem svTorusWeight_eq_product_rowWeights
    (T : EvenTorus) (c : Real) (omega : SixVertexArrows T) :
    omega.weight c =
      ∏ j : Fin T.height,
        svHorizontalRowWeight T.width_pos c
          (svTorusVerticalRows T omega
            (SixVertexArrows.cyclicPred T.height_pos j))
          (svTorusVerticalRows T omega j)
          (svTorusHorizontalRows T omega j) := by
  rw [SixVertexArrows.weight, Fintype.prod_prod_type]
  unfold svHorizontalRowWeight
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j hj
  apply Finset.prod_congr rfl
  intro i hi
  exact (svHorizontalLocalWeight_eq_torusLocalWeight T c omega i j).symm

end StatMech.FrontierD
