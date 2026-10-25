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
import Instance.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_twoChannelFullPhysicalVisibleEquiv {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcTwoChannelFullPhysicalTargetEdge gamma gamma' ≃
      RlcTwoChannelFullPhysicalVisibleSourceEdge gamma gamma' :=
  Equiv.ofInjective rlc_twoChannelFullPhysicalSourceEdge
    rlc_twoChannelFullPhysicalSourceEdge_injective


noncomputable def rlc_twoChannelFullPhysicalTargetOfVisibleSource {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (source : RlcTwoChannelFullPhysicalVisibleSourceEdge gamma gamma') :
    RlcTwoChannelFullPhysicalTargetEdge gamma gamma' :=
  (rlc_twoChannelFullPhysicalVisibleEquiv gamma gamma').symm source

end
end StatMech.Universality
