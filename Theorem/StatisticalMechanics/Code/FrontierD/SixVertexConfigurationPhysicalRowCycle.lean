/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalRowCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalCommonFactor.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexIceRule_iff_horizontalRowTransitions
    {T : EvenTorus} (omega : SixVertexArrows T) :
    omega.IceRule ↔
      forall j : Fin T.height,
        svHorizontalIce T.width_pos
          (svTorusVerticalRows T omega
            (SixVertexArrows.cyclicPred T.height_pos j))
          (svTorusVerticalRows T omega j)
          (svTorusHorizontalRows T omega j) := by
  constructor
  · intro hice j i
    simpa [svHorizontalIncomingCount, svTorusVerticalRows,
      svTorusHorizontalRows, SixVertexArrows.incomingCount,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hice (i, j)
  · intro hrows vertex
    rcases vertex with ⟨i, j⟩
    simpa [svHorizontalIncomingCount, svTorusVerticalRows,
      svTorusHorizontalRows, SixVertexArrows.incomingCount,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hrows j i


end
end StatMech.FrontierD
