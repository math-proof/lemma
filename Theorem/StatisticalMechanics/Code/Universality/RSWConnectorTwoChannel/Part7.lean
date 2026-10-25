/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Theorem.StatisticalMechanics.Code.Foundations.WeightedFiniteInjection
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannel.Part8
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelForcedDualFailurePushforwardComparison_of_equiv
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 ≤ q)
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (D : ConfigSpace (Sym2 (RlcConnectorVertex n)) ≃
      ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hfailure : ∀ rho,
      rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma' →
        D rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hprob : ∀ rho,
      rlc_twoChannelForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q rho ≤
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q (D rho)) :
    RlcTwoChannelForcedDualFailurePushforwardComparison
      gamma gamma' q := by
  unfold RlcTwoChannelForcedDualFailurePushforwardComparison
  rw [rlc_twoChannelForcedDualFailureImageMass_eq_compl
    gamma gamma' _ _ hclosure]
  exact rlc_twoChannelForcedDualEventMass_compl_le_merged_of_equiv
    gamma gamma' hq D hfailure hprob


theorem rlc_twoChannelForcedDualFailurePushforwardComparison_of_injection
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 ≤ q)
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (D : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
        rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} →
      ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hinj : Function.Injective D)
    (hsuccess : ∀ rho,
      D rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hprob : ∀ rho,
      rlc_twoChannelForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q rho.1 ≤
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q (D rho)) :
    RlcTwoChannelForcedDualFailurePushforwardComparison
      gamma gamma' q := by
  unfold RlcTwoChannelForcedDualFailurePushforwardComparison
  rw [rlc_twoChannelForcedDualFailureImageMass_eq_compl
    gamma gamma' _ _ hclosure]
  exact rlc_twoChannelForcedDualEventMass_compl_le_merged_of_injection
    gamma gamma' hq D hinj hsuccess hprob


theorem
    rlc_twoChannelForcedDualFailurePushforwardComparison_q_one_of_injection
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (D : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
        rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} →
      ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hinj : Function.Injective D)
    (hsuccess : ∀ rho,
      D rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    RlcTwoChannelForcedDualFailurePushforwardComparison
      gamma gamma' 1 := by
  apply rlc_twoChannelForcedDualFailurePushforwardComparison_of_injection
    gamma gamma' le_rfl hclosure D hinj hsuccess
  intro rho
  rw [show BeffaraDC.selfDualPoint 1 = (1 / 2 : Real) by
    norm_num [BeffaraDC.selfDualPoint]]
  exact (rlc_twoChannelForcedDualProb_half_q_one_eq_merged
    gamma gamma' rho.1 (D rho)).le


end
end StatMech.Universality
