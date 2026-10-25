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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part78
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_bookSimpleTraceNetworkBracket {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {r s : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1) :
    (hypercubicLattice 2).Walk r (rlc_flipX s) := by
  let WR := rlc_ambientCrossingWalk gamma.1
  let WL := rlc_ambientCrossingWalk gamma'.1
  exact ((WR.dropUntil r
    ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 r).2 hr)).append
      (rlc_bookExteriorEndpointDetour gamma gamma')).append
        (WL.takeUntil (rlc_flipX s)
          ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
            gamma'.1 (rlc_flipX s)).2 hsLeft))


noncomputable def rlc_bookSimplePhysicalTraceNetworkBracket {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {r s : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1) :
    (hypercubicLattice 2).Walk
      (rlc_dualReflect.symm r)
      (rlc_dualReflect.symm (rlc_flipX s)) :=
  (rlc_bookSimpleTraceNetworkBracket gamma gamma' hr hsLeft).map
    rlc_dualReflectSymmLatticeHom


end
end StatMech.Universality
