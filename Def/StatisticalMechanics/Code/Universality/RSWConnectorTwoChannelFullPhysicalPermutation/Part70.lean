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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part70
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionAt
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') (z : Site 2) : Prop :=
  ∃ (x y u : Site 2)
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support),
    c.IsCycle ∧
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      rlc_flipX (rlc_dualReflect x) ∈
        (right.map rlc_flipXLatticeHom).support ∧
      rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support ∧
      RlcBookReflectedLeftSuffixRankAt gamma' flipLeft ∧
      RlcBookRightIntersectionRankRealizedAt gamma right ∧
      RlcBookRightPrefixRankAt gamma right ∧
      RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt
        gamma gamma' omega c hx hy ∧
      ((x 0 = -1 ∧ x 1 < -1) ∨ x 0 < -1) ∧
      ((y 0 = -1 ∧ 0 ≤ y 1) ∨ 0 ≤ y 0)


def RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionOnCycle
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {u : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (z : Site 2) : Prop :=
  ∃ (x y : Site 2)
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
    (hx : x ∈ c.support) (hy : y ∈ c.support),
    c.IsCycle ∧
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      rlc_flipX (rlc_dualReflect x) ∈
        (right.map rlc_flipXLatticeHom).support ∧
      rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support ∧
      RlcBookReflectedLeftSuffixRankAt gamma' flipLeft ∧
      RlcBookRightIntersectionRankRealizedAt gamma right ∧
      RlcBookRightPrefixRankAt gamma right ∧
      RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt
        gamma gamma' omega c hx hy ∧
      ((x 0 = -1 ∧ x 1 < -1) ∨ x 0 < -1) ∧
      ((y 0 = -1 ∧ 0 ≤ y 1) ∨ 0 ≤ y 0)


end
end StatMech.Universality
