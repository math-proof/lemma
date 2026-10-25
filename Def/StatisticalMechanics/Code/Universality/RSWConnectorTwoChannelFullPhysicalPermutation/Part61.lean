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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part60
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelFullPhysicalWallFamilyRowTwoCandidateBracket {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z x y : Site 2}
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)) : Prop :=
  (∃ r ∈ rlc_bookFlippedTraceIntersectionSet gamma gamma',
      rlc_dualReflect x = r ∧
        (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
          (rlc_ambientCrossingWalk gamma.1).support.idxOf z ∧
        (r = z ∨
          ∃ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
            (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤
                (rlc_ambientCrossingWalk gamma.1).support.idxOf r ∧
              (rlc_ambientCrossingWalk gamma.1).support.idxOf q <
                (rlc_ambientCrossingWalk gamma.1).support.idxOf z)) ∧
    ∃ s ∈ rlc_pathVertices gamma.1,
      rlc_dualReflect y = rlc_flipX s ∧
        s ∈ flipLeft.support ∧
        (s = z ∨
          (rlc_ambientCrossingWalk gamma.1).support.idxOf z <
            (rlc_ambientCrossingWalk gamma.1).support.idxOf s)


def RlcTwoChannelFullPhysicalWallFamilyRowTwoEarlierContact {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (z x : Site 2) : Prop :=
  ∃ r ∈ rlc_bookFlippedTraceIntersectionSet gamma gamma',
    rlc_dualReflect x = r ∧
      (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
        (rlc_ambientCrossingWalk gamma.1).support.idxOf z ∧
      ∃ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
        (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤
            (rlc_ambientCrossingWalk gamma.1).support.idxOf r ∧
          (rlc_ambientCrossingWalk gamma.1).support.idxOf q <
            (rlc_ambientCrossingWalk gamma.1).support.idxOf z


def RlcTwoChannelFullPhysicalWallFamilyRowTwoLaterContact {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z y : Site 2}
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)) : Prop :=
  ∃ s ∈ rlc_pathVertices gamma.1,
    rlc_dualReflect y = rlc_flipX s ∧
      s ∈ flipLeft.support ∧
      (rlc_ambientCrossingWalk gamma.1).support.idxOf z <
        (rlc_ambientCrossingWalk gamma.1).support.idxOf s


def RlcTwoChannelFullPhysicalWallFamilyRowTwoCandidateOrderCases {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z x y : Site 2}
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)) : Prop :=
  (rlc_dualReflect x = z ∧ rlc_dualReflect y = rlc_flipX z) ∨
    (RlcTwoChannelFullPhysicalWallFamilyRowTwoEarlierContact
        gamma gamma' z x ∧
      rlc_dualReflect y = rlc_flipX z) ∨
    (rlc_dualReflect x = z ∧
      RlcTwoChannelFullPhysicalWallFamilyRowTwoLaterContact
        gamma gamma' (z := z) (y := y) flipLeft) ∨
    (RlcTwoChannelFullPhysicalWallFamilyRowTwoEarlierContact
        gamma gamma' z x ∧
      RlcTwoChannelFullPhysicalWallFamilyRowTwoLaterContact
        gamma gamma' (z := z) (y := y) flipLeft)


end
end StatMech.Universality
