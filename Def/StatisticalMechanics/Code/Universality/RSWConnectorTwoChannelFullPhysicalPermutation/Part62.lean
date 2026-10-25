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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part61
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelFullPhysicalWallFamilyRowTwoEarlierTraceSegment {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (z x : Site 2) : Prop :=
  ∃ (r q : Site 2) (P : (hypercubicLattice 2).Walk r z),
    r ∈ rlc_bookFlippedTraceIntersectionSet gamma gamma' ∧
      rlc_dualReflect x = r ∧
      (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
        (rlc_ambientCrossingWalk gamma.1).support.idxOf z ∧
      q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma' ∧
      (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤
        (rlc_ambientCrossingWalk gamma.1).support.idxOf r ∧
      (rlc_ambientCrossingWalk gamma.1).support.idxOf q <
        (rlc_ambientCrossingWalk gamma.1).support.idxOf z ∧
      ∀ v ∈ P.support, v ∈ (rlc_ambientCrossingWalk gamma.1).support


def RlcTwoChannelFullPhysicalWallFamilyRowTwoLaterTraceSegment {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z y : Site 2}
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)) : Prop :=
  ∃ (s : Site 2) (P : (hypercubicLattice 2).Walk z s),
    s ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y = rlc_flipX s ∧
      s ∈ flipLeft.support ∧
      (rlc_ambientCrossingWalk gamma.1).support.idxOf z <
        (rlc_ambientCrossingWalk gamma.1).support.idxOf s ∧
      ∀ v ∈ P.support, v ∈ (rlc_ambientCrossingWalk gamma.1).support


end
end StatMech.Universality
