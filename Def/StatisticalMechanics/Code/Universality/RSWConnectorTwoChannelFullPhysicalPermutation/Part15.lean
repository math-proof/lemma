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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part14
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_twoChannelFullPhysicalCutIntersectionTargets {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (A B : Set (RlcConnectorVertex n)) :
    Finset (RlcTwoChannelFullPhysicalTargetEdge gamma gamma') := by
  classical
  exact Finset.univ.filter fun target =>
    rlc_twoChannelFullPhysicalEdgeCrossesCut A
      (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
    rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1


end
end StatMech.Universality
