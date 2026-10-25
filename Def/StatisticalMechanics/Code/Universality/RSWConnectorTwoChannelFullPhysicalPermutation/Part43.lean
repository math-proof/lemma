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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part42
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelFullPhysicalFirstIntersectionOrderedBadSeparation {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') : Prop :=
  ∃ (z x y u v : Site 2)
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)),
    z ∈ rlc_pathVertices gamma.1 ∧
      rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      rlc_flipX (rlc_dualReflect x) ∈
        (right.map rlc_flipXLatticeHom).support ∧
      rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support ∧
      (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Reachable x u ∧
      (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v ∧
      (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Reachable v y ∧
      (((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry
            gamma gamma' u v) ∧
          (rlc_dualReflect u ∈ rlc_pathVertices gamma.1 ∨
            (0 < (rlc_dualReflect u) 0 ∧
              ∃ w ∈ rlc_pathVertices gamma'.1,
                rlc_dualReflect u = rlc_flipX w) ∨
            ((rlc_dualReflect u) 0 < 0 ∧
              ∃ w ∈ rlc_pathVertices gamma.1,
                rlc_dualReflect u = rlc_flipX w) ∨
            (rlc_dualReflect u) 0 = -2 * n ∨
            (rlc_dualReflect u) 0 = 2 * n ∨
            (rlc_dualReflect u) 1 = -n ∨
            (rlc_dualReflect u) 1 = n)) ∨
        ∃ p q : Site 2,
          sharedPrimalEdge u v = s(p, q) ∧
            (hypercubicLattice 2).Adj p q ∧
            p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
            q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
            (p ∈ rlc_pathVertices gamma.1 ∨
              (0 < p 0 ∧ ∃ w ∈ rlc_pathVertices gamma'.1,
                p = rlc_flipX w) ∨
              (p 0 < 0 ∧ ∃ w ∈ rlc_pathVertices gamma.1,
                p = rlc_flipX w) ∨
              p 0 = -2 * n ∨ p 0 = 2 * n ∨
              p 1 = -n ∨ p 1 = n))


end
end StatMech.Universality
