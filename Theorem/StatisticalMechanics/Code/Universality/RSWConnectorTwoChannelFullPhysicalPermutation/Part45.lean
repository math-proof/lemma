/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Instance.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part6
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysicalRepairableBoundaryGraph_le
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelFullPhysicalRepairableBoundaryGraph gamma gamma' omega ≤
      faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega) :=
  fun _ _ hfg => hfg.1


theorem rlc_twoChannelFullPhysical_goodReachable_of_repairableBoundaryWalk
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {x y : Site 2}
    (q : (rlc_twoChannelFullPhysicalRepairableBoundaryGraph
      gamma gamma' omega).Walk x y) :
    (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Reachable x y := by
  induction q with
  | nil => exact Reachable.refl _
  | @cons u v z huv p ih => exact huv.2.trans ih


end
end StatMech.Universality
