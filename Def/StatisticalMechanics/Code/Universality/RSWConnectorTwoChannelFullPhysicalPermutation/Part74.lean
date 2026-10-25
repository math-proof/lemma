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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part74
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelFullPhysicalRetainedSideSelection {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (_hfaith : RlcBookFaithfulTracePair gamma gamma') : Prop :=
  ∀ omega : RlcTwoChannelEdgeConfig gamma gamma',
    rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
        rlc_finiteTwoChannelConnectorEvent gamma gamma' →
      RlcTwoChannelFullPhysicalFilledBoundarySegment gamma gamma' omega


def RlcTwoChannelFullPhysicalContourArcRepairSelection {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (_hfaith : RlcBookFaithfulTracePair gamma gamma') : Prop :=
  ∀ omega : RlcTwoChannelEdgeConfig gamma gamma',
    rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
        rlc_finiteTwoChannelConnectorEvent gamma gamma' →
      ∃ (x y u : Site 2)
        (c : (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
        (hx : x ∈ c.support) (hy : y ∈ c.support),
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
          rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
          RlcTwoChannelFullPhysicalContourArcRepairSide
            gamma gamma' omega c hx hy


end
end StatMech.Universality
