/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelStoppedPathOrientation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part86
import Theorem.StatisticalMechanics.Code.Universality.RSWStoppedPathPIMSProvenance.Part3
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

structure RlcStoppedTwoChannelOrientedCommonCycleState
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') where
  provenance : RlcStoppedExtremalAxisGapProvenance G hn hlt
  anchor : Site 2
  contour : (faceBoundaryGraph
    (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk anchor anchor
  contour_isCycle : contour.IsCycle
  contour_orientation :
    rlc_twoChannelFullFilledReachSet gamma gamma' omega =
      jec_leftRegion (contour.mapLe (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))
  candidate_obstruction :
    ∀ z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
      RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionOnCycle
        gamma gamma' omega contour z


end
end StatMech.Universality
