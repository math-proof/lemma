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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part62
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelFullPhysicalWallFamilyRowTwoTraceSegmentCases {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z x y : Site 2}
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)) : Prop :=
  (rlc_dualReflect x = z ∧ rlc_dualReflect y = rlc_flipX z) ∨
    (RlcTwoChannelFullPhysicalWallFamilyRowTwoEarlierTraceSegment
        gamma gamma' z x ∧
      rlc_dualReflect y = rlc_flipX z) ∨
    (rlc_dualReflect x = z ∧
      RlcTwoChannelFullPhysicalWallFamilyRowTwoLaterTraceSegment
        gamma gamma' (z := z) (y := y) flipLeft) ∨
    (RlcTwoChannelFullPhysicalWallFamilyRowTwoEarlierTraceSegment
        gamma gamma' z x ∧
      RlcTwoChannelFullPhysicalWallFamilyRowTwoLaterTraceSegment
        gamma gamma' (z := z) (y := y) flipLeft)


end
end StatMech.Universality
