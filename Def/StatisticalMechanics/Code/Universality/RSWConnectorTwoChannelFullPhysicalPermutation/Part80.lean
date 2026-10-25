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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part80
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A B : Set (RlcConnectorVertex n))
    {u a b : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (H : (hypercubicLattice 2).Walk a b)
    (f g : Site 2) : Prop :=
  ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g) ∧
      s(rlc_dualReflect f, rlc_dualReflect g) ∉
        rlc_reflectedPathEdges gamma'.1) ∨
    ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
      target.1.map Subtype.val =
          s(rlc_dualReflect f, rlc_dualReflect g) ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1 ∧
        (¬RlcTwoChannelFullPhysicalSourceCarrierGeometry
          gamma gamma' f g) ∧
        ∃ p q : Site 2,
          sharedPrimalEdge f g = s(p, q) ∧
            (hypercubicLattice 2).Adj p q ∧
            p ∈ rlc_twoChannelFullReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A) ∧
            q ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A) ∧
            ((RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
                gamma gamma' p ∧
              RlcTwoChannelFullPhysicalExclusiveReflectedRightSourceTraceResidue
                gamma gamma'
                  (rlc_twoChannelFullPhysicalCutInteriorConfig
                    gamma gamma' A) p q) ∨
              p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) ∧
            (p = a ∨ p = b ∨ q ∈ H.support ∨
              p ∈ c.support ∨ q ∈ c.support)


end
end StatMech.Universality
