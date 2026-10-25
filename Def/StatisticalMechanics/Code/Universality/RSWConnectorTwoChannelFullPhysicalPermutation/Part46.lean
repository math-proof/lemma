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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part45
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelFullPhysicalContourArcRepairSide {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support) : Prop :=
  (∀ {f g : Site 2},
      s(f, g) ∈ (rlc_orderedContourArc c hx hy).edges →
        (rlc_twoChannelFullPhysicalGoodBoundaryGraph
          gamma gamma' omega).Reachable f g) ∨
    (∀ {f g : Site 2},
      s(f, g) ∈ (rlc_complementaryContourArc c hx hy).edges →
        (rlc_twoChannelFullPhysicalGoodBoundaryGraph
          gamma gamma' omega).Reachable f g)


end
end StatMech.Universality
