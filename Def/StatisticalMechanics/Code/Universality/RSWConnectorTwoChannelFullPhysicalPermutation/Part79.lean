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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part79
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_bookRowOnePhysicalTraceNetworkBracket {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z : Site 2} (hzRight : z ∈ rlc_pathVertices gamma.1) :
    (hypercubicLattice 2).Walk
      (rlc_dualReflect.symm z)
      (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2)) :=
  (rlc_bookSimplePhysicalTraceNetworkBracket gamma gamma' hzRight
    (s := rlc_flipX (gamma'.1.2.1 : Site 2))
    (rlc_bookRowOne_flippedLeftEndpoint_mem gamma')).copy rfl
      (congrArg rlc_dualReflect.symm
        (rlc_flipX_involutive (gamma'.1.2.1 : Site 2)))


end
end StatMech.Universality
