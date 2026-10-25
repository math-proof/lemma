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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_twoChannelFullPhysicalSourceEdge_targetOfVisibleSource
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (source : RlcTwoChannelFullPhysicalVisibleSourceEdge gamma gamma') :
    rlc_twoChannelFullPhysicalSourceEdge
        (rlc_twoChannelFullPhysicalTargetOfVisibleSource source) = source.1 := by
  exact congrArg Subtype.val
    ((rlc_twoChannelFullPhysicalVisibleEquiv gamma gamma').apply_symm_apply
      source)


end
end StatMech.Universality
