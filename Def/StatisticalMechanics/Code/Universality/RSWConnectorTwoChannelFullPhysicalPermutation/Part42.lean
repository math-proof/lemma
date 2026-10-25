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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part41
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelFullPhysicalFirstIntersectionOrderedContacts {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') : Prop :=
  ∃ (z x y : Site 2)
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)),
    z ∈ rlc_pathVertices gamma.1 ∧
      rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
      x ∈ (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support ∧
      y ∈ (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support ∧
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      rlc_flipX (rlc_dualReflect x) ∈
        (right.map rlc_flipXLatticeHom).support ∧
      rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support ∧
      RlcBookReflectedLeftSuffixRankAt gamma' flipLeft ∧
      (∀ w ∈ right.support,
        rlc_flipX w ∈ rlc_pathVertices gamma'.1 → w = z) ∧
      RlcBookRightIntersectionRankRealizedAt gamma right ∧
      RlcBookRightIntersectionRankMinimalAt gamma gamma' right


end
end StatMech.Universality
