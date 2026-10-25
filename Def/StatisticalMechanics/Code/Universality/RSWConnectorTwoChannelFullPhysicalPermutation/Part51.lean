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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part50
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelFullPhysicalRightArcBadLocation {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (z : Site 2) : Prop :=
  z ∈ rlc_pathVertices gamma.1 ∨
    RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
      gamma gamma' z ∨
    RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
      gamma gamma' z ∨
    z 0 = -2 * n ∨ z 0 = 2 * n ∨ z 1 = -n ∨ z 1 = n


def RlcTwoChannelFullPhysicalLeftArcTargetBadLocation {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (z : Site 2) : Prop :=
  z ∈ rlc_pathVertices gamma'.1 ∨
    RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
      gamma gamma' z ∨
    RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
      gamma gamma' z ∨
    z 0 = -2 * n ∨ z 0 = 2 * n ∨ z 1 = -n ∨ z 1 = n

def RlcTwoChannelFullPhysicalRightArcClassifiedBad {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (u v : Site 2) : Prop :=
  ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' u v) ∧
      RlcTwoChannelFullPhysicalRightArcBadLocation
        gamma gamma' (rlc_dualReflect u)) ∨
    ∃ p q : Site 2,
      sharedPrimalEdge u v = s(p, q) ∧
        (hypercubicLattice 2).Adj p q ∧
        p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' p

def RlcTwoChannelFullPhysicalLeftArcClassifiedBad {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (u v : Site 2) : Prop :=
  ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' u v) ∧
      RlcTwoChannelFullPhysicalLeftArcTargetBadLocation
        gamma gamma' (rlc_dualReflect u)) ∨
    ∃ p q : Site 2,
      sharedPrimalEdge u v = s(p, q) ∧
        (hypercubicLattice 2).Adj p q ∧
        p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' p


end
end StatMech.Universality
