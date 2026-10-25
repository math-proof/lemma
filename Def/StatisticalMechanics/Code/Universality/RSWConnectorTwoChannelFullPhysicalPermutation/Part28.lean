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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part27
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (z : Site 2) : Prop :=
  0 < z 0 ∧
    (∃ w ∈ rlc_pathVertices gamma'.1, z = rlc_flipX w) ∧
    z ∉ rlc_pathVertices gamma.1 ∧
    z ∉ rlc_pathVertices gamma'.1


def RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (z : Site 2) : Prop :=
  z 0 < 0 ∧
    (∃ w ∈ rlc_pathVertices gamma.1, z = rlc_flipX w) ∧
    z ∉ rlc_pathVertices gamma.1 ∧
    z ∉ rlc_pathVertices gamma'.1


end
end StatMech.Universality
