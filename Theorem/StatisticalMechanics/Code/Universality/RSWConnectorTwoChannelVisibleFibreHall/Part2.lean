/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelVisibleFibreHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part43
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelVisibleFibreHall.Part3
open Finset SimpleGraph Set


namespace StatMech.Universality

noncomputable section

theorem
    rlc_twoChannelPIMSPooledVisibleFibreCapacity_iff_exists_compatibleEmbedding
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma') :
    RlcTwoChannelPIMSPooledVisibleFibreCapacity hclosure ↔
      ∃ J : RlcTwoChannelEdgeFailure gamma gamma' ↪
          RlcTwoChannelEdgeSuccess gamma gamma',
        forall rho,
          RlcTwoChannelPIMSPooledVisibleCompatible hclosure rho (J rho) := by
  constructor
  · intro hcapacity
    exact ⟨rlc_twoChannelPooledVisibleEmbeddingOfCapacity hcapacity,
      rlc_twoChannelPooledVisibleEmbeddingOfCapacity_compatible hcapacity⟩
  · rintro ⟨J, hJ⟩ base
    exact Fintype.card_le_of_embedding
      (rlc_twoChannelPooledVisibleFibreEmbeddingOfGlobal J hJ base)


theorem rlc_twoChannelPIMSPooledVisibleFibreCapacity_iff_edgeCodeHall
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma') :
    RlcTwoChannelPIMSPooledVisibleFibreCapacity hclosure ↔
      RlcTwoChannelEdgeCodeHall gamma gamma'
        (RlcTwoChannelPIMSPooledVisibleCompatible hclosure) := by
  rw [rlc_twoChannelEdgeCodeHall_iff_exists_compatibleEmbedding]
  exact
    rlc_twoChannelPIMSPooledVisibleFibreCapacity_iff_exists_compatibleEmbedding
      hclosure


theorem
    rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_pooledVisibleCapacity
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (hcapacity : RlcTwoChannelPIMSPooledVisibleFibreCapacity hclosure) :
    rlc_twoChannelForcedDualEventMass gamma gamma' (1 / 2) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  apply
    rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_edgeCodeHall
      gamma gamma' (RlcTwoChannelPIMSPooledVisibleCompatible hclosure)
  exact
    (rlc_twoChannelPIMSPooledVisibleFibreCapacity_iff_edgeCodeHall
      hclosure).mp hcapacity


theorem
    rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_pooledScoreHall
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    {q : Real} (hq : 1 <= q) (N : Nat)
    (hHall : RlcTwoChannelEdgeCodeHall gamma gamma'
      (RlcTwoChannelPIMSPooledScoreCompatible hclosure N)) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      (Real.sqrt q) ^ N *
        FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  apply
    rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_edgeCodeHall_score
      gamma gamma' hq N
        (RlcTwoChannelPIMSPooledScoreCompatible hclosure N) hHall
  intro rho eta hcompatible
  exact hcompatible.2


theorem
    rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_pooledScoreHall
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    {q : Real} (hq : 1 <= q) (N : Nat)
    (hHall : RlcTwoChannelEdgeCodeHall gamma gamma'
      (RlcTwoChannelPIMSPooledScoreCompatible hclosure N)) :
    1 / (1 + (Real.sqrt q) ^ N * q) <=
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  apply rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_distorted_forcedDual
    gamma gamma' hq (pow_nonneg (Real.sqrt_nonneg q) N) hclosure
  exact
    rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_pooledScoreHall
      gamma gamma' hclosure hq N hHall

end
end StatMech.Universality
