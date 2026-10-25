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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part85
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelFullPhysicalShiftedEndpointPlacement
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {u : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (p q : Site 2) : Prop :=
  (phb_doubleDualShift p ∈
        jec_leftRegion (c.mapLe (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) ∧
      phb_doubleDualShift q ∉
        jec_leftRegion (c.mapLe (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))) ∨
    ∃ z ∈ c.support,
      z = p ∨ z = ![p 0 - 1, p 1] ∨
        z = phb_doubleDualShift p ∨ z = q ∨
        z = ![q 0 - 1, q 1] ∨ z = phb_doubleDualShift q


end
end StatMech.Universality
