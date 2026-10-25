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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part29
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelFullPhysicalExclusiveReflectedLeftSourceTraceResidue
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (p q : Site 2) : Prop :=
  ∃ z : Site 2,
    (hypercubicLattice 2).Adj p z ∧
      rlc_twoChannelFullAmbientConfig gamma gamma' omega s(p, z) = true ∧
      ((∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
          source.1.map Subtype.val = s(p, z)) ∨
        (s(p, z) ∉ rlc_connectorFourTraceEdges gamma gamma' ∧
          z 0 + q 0 = 2 * p 0 ∧ z 1 + q 1 = 2 * p 1 ∧
          ∀ y : Site 2,
            (hypercubicLattice 2).Adj p y → y ≠ z → y ≠ q →
              ∃ source :
                (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
                source.1.map Subtype.val = s(p, y)))


end
end StatMech.Universality
