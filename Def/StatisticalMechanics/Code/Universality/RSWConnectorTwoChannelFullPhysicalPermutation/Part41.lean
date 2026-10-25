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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part40
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_bookOrderedIntersectionCandidateSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Finset (Site 2) :=
  (rlc_bookFlippedTraceIntersectionSet gamma gamma').filter fun z =>
    ∀ q ∈ rlc_bookFlippedTraceIntersectionSet gamma gamma',
      (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤
          (rlc_ambientCrossingWalk gamma.1).support.idxOf z →
        (rlc_ambientCrossingWalk gamma'.1).support.idxOf (rlc_flipX z) ≤
            (rlc_ambientCrossingWalk gamma'.1).support.idxOf (rlc_flipX q) →
          q = z


def rlc_bookOrderedCandidateReverseRank {n : Int}
    (gamma : RlcRightDiagonalPath n) (z : Site 2) : Nat :=
  (rlc_ambientCrossingWalk gamma.1).length -
    (rlc_ambientCrossingWalk gamma.1).support.idxOf z


end
end StatMech.Universality
