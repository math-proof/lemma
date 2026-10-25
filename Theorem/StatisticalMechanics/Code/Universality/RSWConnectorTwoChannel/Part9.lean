/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Theorem.StatisticalMechanics.Code.Foundations.WeightedFiniteInjection
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannel.Part10
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFailureMassComparison_of_PIMS {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real)
    (hfailure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (hpush : RlcTwoChannelPIMSFailurePushforwardComparison
      gamma gamma' p q) :
    RlcTwoChannelFailureMassComparison gamma gamma' p q := by
  unfold RlcTwoChannelFailureMassComparison
  unfold RlcTwoChannelPIMSFailurePushforwardComparison at hpush
  rw [rlc_twoChannel_failureMass_eq_PIMSFailureImageMass
    gamma gamma' p q hfailure]
  exact hpush


theorem rlc_finiteTwoChannelConnectorMass_ge_one_div_one_add_q {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hdual : RlcTwoChannelFailureMassComparison gamma gamma' p q) :
    1 / (1 + q) ≤
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  apply FrontierD.bcEventMass_ge_one_div_one_add_q_of_compl_le_sup_edge
    (rlc_connectorTwoChannelGraph gamma gamma')
    (rlc_connectorSeparateWiring gamma gamma')
    (rlc_connectorRightAnchor gamma) (rlc_connectorLeftAnchor gamma')
    hp hp1 hq (rlc_finiteTwoChannelConnectorEvent gamma gamma')
  simpa only [rlc_connectorMergedWiring] using hdual


theorem rlc_finiteTwoChannelConnectorMass_ge_one_div_one_add_mul {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q distortion : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (hdistortion : 0 <= distortion)
    (hdual :
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') p q
          (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
        distortion *
          FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma') p q
            (rlc_finiteTwoChannelConnectorEvent gamma gamma')) :
    1 / (1 + distortion * q) <=
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  apply
    FrontierD.bcEventMass_ge_one_div_one_add_mul_of_compl_le_mul_sup_edge
      (rlc_connectorTwoChannelGraph gamma gamma')
      (rlc_connectorSeparateWiring gamma gamma')
      (rlc_connectorRightAnchor gamma) (rlc_connectorLeftAnchor gamma')
      hp hp1 hq hdistortion
      (rlc_finiteTwoChannelConnectorEvent gamma gamma')
  simpa only [rlc_connectorMergedWiring] using hdual


theorem
    rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_distorted_forcedDual
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q distortion : Real} (hq : 1 <= q) (hdistortion : 0 <= distortion)
    (hfailure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (hpush :
      rlc_twoChannelForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
        distortion *
          FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (BeffaraDC.selfDualPoint q) q
            (rlc_finiteTwoChannelConnectorEvent gamma gamma')) :
    1 / (1 + distortion * q) <=
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  apply rlc_finiteTwoChannelConnectorMass_ge_one_div_one_add_mul
    gamma gamma' hp hp1 hq hdistortion
  calc
    FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ =
      rlc_twoChannelPIMSFailureImageMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q :=
      rlc_twoChannel_failureMass_eq_PIMSFailureImageMass
        gamma gamma' _ _ hfailure
    _ = rlc_twoChannelForcedDualFailureImageMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q :=
      rlc_twoChannelPIMSFailureImageMass_eq_forcedDual
        gamma gamma' hq0
    _ = rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ :=
      rlc_twoChannelForcedDualFailureImageMass_eq_compl
        gamma gamma' _ _ hfailure
    _ <= distortion *
        FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteTwoChannelConnectorEvent gamma gamma') := hpush


theorem rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_PIMS {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 ≤ q)
    (hfailure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (hpush : RlcTwoChannelForcedDualFailurePushforwardComparison
      gamma gamma' q) :
    1 / (1 + q) ≤
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  apply rlc_finiteTwoChannelConnectorMass_ge_one_div_one_add_q
    gamma gamma' hp hp1 hq
  unfold RlcTwoChannelFailureMassComparison
  calc
    FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ =
      rlc_twoChannelPIMSFailureImageMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q :=
      rlc_twoChannel_failureMass_eq_PIMSFailureImageMass
        gamma gamma' _ _ hfailure
    _ = rlc_twoChannelForcedDualFailureImageMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q :=
      rlc_twoChannelPIMSFailureImageMass_eq_forcedDual
        gamma gamma' hq0
    _ ≤ FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := hpush

end
end StatMech.Universality
