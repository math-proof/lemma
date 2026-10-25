/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Theorem.StatisticalMechanics.Code.Foundations.WeightedFiniteInjection
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannel.Part7
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_twoChannelFailureLowestRetainedBoundary
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
      rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'}) :
    RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho.1 :=
  Classical.choice
    (rlc_centralFace_lowestRetainedAnchoredBoundary_of_failure
      gamma gamma' hfaith.toRlcBookPositionedTracePair rho.1 (fun hcentral =>
        rho.2 (rlc_finiteCentralFaceRandomConnectorEvent_subset_twoChannel
          gamma gamma' hcentral)))


def RlcTwoChannelFailureRetainedAnchorTraceIncidence
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
      rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'}) : Prop :=
  RlcCentralFaceRetainedAnchorTraceIncidence
    (rlc_twoChannelFailureLowestRetainedBoundary
      gamma gamma' hfaith rho).boundary


end
end StatMech.Universality
