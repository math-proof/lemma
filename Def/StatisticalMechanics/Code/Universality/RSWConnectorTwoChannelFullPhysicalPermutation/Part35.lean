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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part34
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcBookRightIntersectionRankRealizedAt {n : Int}
    (gamma : RlcRightDiagonalPath n) {z : Site 2}
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z) : Prop :=
  right.length =
    (rlc_ambientCrossingWalk gamma.1).support.idxOf z


def RlcBookRightPrefixRankAt {n : Int}
    (gamma : RlcRightDiagonalPath n) {z : Site 2}
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z) : Prop :=
  ∀ x ∈ right.support,
    (rlc_ambientCrossingWalk gamma.1).support.idxOf x ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf z


def RlcBookRightIntersectionRankMinimalAt {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z : Site 2}
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z) : Prop :=
  ∀ q (hq : q ∈ rlc_pathVertices gamma.1),
    rlc_flipX q ∈ rlc_pathVertices gamma'.1 →
      right.length ≤
        (rlc_ambientCrossingWalk gamma.1).support.idxOf q


def RlcBookReflectedLeftSuffixRankAt {n : Int}
    (gamma' : RlcLeftDiagonalPath n) {z : Site 2}
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)) : Prop :=
  ∀ x ∈ flipLeft.support,
    (rlc_ambientCrossingWalk gamma'.1).support.idxOf (rlc_flipX z) ≤
      (rlc_ambientCrossingWalk gamma'.1).support.idxOf (rlc_flipX x)


end
end StatMech.Universality
