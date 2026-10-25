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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part48
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelFullPhysicalTwoArcClassifiedFirstBadAt {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support) : Prop :=
  ∃ (ur vr ul vl : Site 2)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (rr : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (rl : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl),
    rlc_orderedContourArc c hx hy =
        (qr.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
          gamma gamma' omega)).append (.cons hurv rr) ∧
      (rlc_complementaryContourArc c hx hy).reverse =
        (ql.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
          gamma gamma' omega)).append (.cons hulv rl) ∧
      s(ur, vr) ≠ s(ul, vl) ∧
      ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
        gamma gamma' ur vr ∧
      ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
        gamma gamma' ul vl ∧
      (((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry
            gamma gamma' ur vr) ∧
          (rlc_dualReflect ur ∈ rlc_connectorBarrier gamma gamma' ∨
            (rlc_dualReflect ur) 0 = -2 * n ∨
            (rlc_dualReflect ur) 0 = 2 * n ∨
            (rlc_dualReflect ur) 1 = -n ∨
            (rlc_dualReflect ur) 1 = n)) ∨
        ∃ p q : Site 2,
          sharedPrimalEdge ur vr = s(p, q) ∧
            (hypercubicLattice 2).Adj p q ∧
            p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
            q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
            (p ∈ rlc_connectorBarrier gamma gamma' ∨
              p 0 = -2 * n ∨ p 0 = 2 * n ∨
              p 1 = -n ∨ p 1 = n)) ∧
      (((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry
            gamma gamma' ul vl) ∧
          (rlc_dualReflect ul ∈ rlc_connectorBarrier gamma gamma' ∨
            (rlc_dualReflect ul) 0 = -2 * n ∨
            (rlc_dualReflect ul) 0 = 2 * n ∨
            (rlc_dualReflect ul) 1 = -n ∨
            (rlc_dualReflect ul) 1 = n)) ∨
        ∃ p q : Site 2,
          sharedPrimalEdge ul vl = s(p, q) ∧
            (hypercubicLattice 2).Adj p q ∧
            p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
            q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
            (p ∈ rlc_connectorBarrier gamma gamma' ∨
              p 0 = -2 * n ∨ p 0 = 2 * n ∨
              p 1 = -n ∨ p 1 = n))


end
end StatMech.Universality
