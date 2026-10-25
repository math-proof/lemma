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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part51
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelFullPhysicalRightArcShiftedClassifiedBad {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (u v a : Site 2) : Prop :=
  ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' u v) ∧
      RlcTwoChannelFullPhysicalRightArcBadLocation
        gamma gamma' (rlc_dualReflect u) ∧ a ∈ s(u, v)) ∨
    ∃ p q : Site 2,
      sharedPrimalEdge u v = s(p, q) ∧
        (hypercubicLattice 2).Adj p q ∧
        p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' p ∧
        (a = phb_doubleDualShift p ∨ a = phb_doubleDualShift q)


def RlcTwoChannelFullPhysicalLeftArcShiftedClassifiedBad {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (u v a : Site 2) : Prop :=
  ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' u v) ∧
      RlcTwoChannelFullPhysicalLeftArcTargetBadLocation
        gamma gamma' (rlc_dualReflect u) ∧ a ∈ s(u, v)) ∨
    ∃ p q : Site 2,
      sharedPrimalEdge u v = s(p, q) ∧
        (hypercubicLattice 2).Adj p q ∧
        p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' p ∧
        (a = phb_doubleDualShift p ∨ a = phb_doubleDualShift q)


end
end StatMech.Universality
