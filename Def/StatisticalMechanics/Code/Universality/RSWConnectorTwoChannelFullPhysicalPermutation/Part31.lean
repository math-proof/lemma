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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part30
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelFullPhysicalReflectedLeftTerminalSourceResidue
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (f g : Site 2) : Prop :=
  (¬RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' f g) ∧
    ∃ p q : Site 2,
      sharedPrimalEdge f g = s(p, q) ∧
        (hypercubicLattice 2).Adj p q ∧
        p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        (p ∈ rlc_pathVertices gamma.1 ∨
          (RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
              gamma gamma' p ∧
            RlcTwoChannelFullPhysicalExclusiveReflectedLeftSourceTraceResidue
              gamma gamma' omega p q) ∨
          (p 0 < 0 ∧ ∃ w ∈ rlc_pathVertices gamma.1,
            p = rlc_flipX w) ∨
          p 0 = -2 * n ∨ p 0 = 2 * n ∨
          p 1 = -n ∨ p 1 = n)


end
end StatMech.Universality
