/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part20
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem
    rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_faithfulCanonicalPIMSRouteHall
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
    (hHall : RlcBookFaithfulCanonicalPIMSRouteHall hinc) :
    rlc_twoChannelForcedDualEventMass gamma gamma' (1 / 2) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ ≤
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  exact
    rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_dynamicRouteHall
      gamma gamma' (rlc_twoChannelCanonicalRoutePlan gamma gamma')
      (rlc_twoChannelCanonicalRouteAvailable
        (rlc_twoChannelPIMSEdgeTargetOfClosure
          (rlc_twoChannelClosureFailureCertificate_of_centralFace
            gamma gamma'
            (rlc_centralFaceClosureFailureCertificate_of_retainedAnchorIncidence
              hinc)))) hHall


theorem
    rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_faithfulPIMSFibrePacking
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
    (packing : RlcTwoChannelCanonicalFibrePacking
      (rlc_twoChannelPIMSEdgeTargetOfClosure
        (rlc_twoChannelClosureFailureCertificate_of_centralFace
          gamma gamma'
          (rlc_centralFaceClosureFailureCertificate_of_retainedAnchorIncidence
            hinc)))) :
    rlc_twoChannelForcedDualEventMass gamma gamma' (1 / 2) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ ≤
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  apply
    rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_faithfulCanonicalPIMSRouteHall
      hinc
  exact packing.hasCodeHall

#print axioms rlc_twoChannelCanonicalRoute_hasCodeHall_of_injective
#print axioms rlc_twoChannel_PIMS_and_exactDiscardedBits_injective
#print axioms
  rlc_twoChannel_PIMSEdgeProjection_and_exactDiscardedBits_injective
#print axioms
  rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_faithfulCanonicalPIMSRouteHall
#print axioms
  rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_faithfulPIMSFibrePacking

end
end StatMech.Universality
