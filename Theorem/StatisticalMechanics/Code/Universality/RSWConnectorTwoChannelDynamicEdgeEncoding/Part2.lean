/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelDynamicEdgeEncoding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelEdgeEncoding.Part2
import Theorem.StatisticalMechanics.Code.FK.SelfDualPointMassScore
import Theorem.StatisticalMechanics.Code.FK.BoundaryScoreLipschitz
import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelEdgeCodeHall_iff_exists_compatibleEmbedding {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (Compatible : RlcTwoChannelEdgeFailure gamma gamma' →
      RlcTwoChannelEdgeSuccess gamma gamma' → Prop) :
    RlcTwoChannelEdgeCodeHall gamma gamma' Compatible ↔
      ∃ J : RlcTwoChannelEdgeFailure gamma gamma' ↪
          RlcTwoChannelEdgeSuccess gamma gamma',
        ∀ rho, Compatible rho (J rho) := by
  classical
  have hhall := Fintype.all_card_le_filter_rel_iff_exists_injective Compatible
  constructor
  · intro h
    have h' : ∀ failures :
        Finset (RlcTwoChannelEdgeFailure gamma gamma'),
        failures.card <=
          (Finset.univ.filter fun eta :
            RlcTwoChannelEdgeSuccess gamma gamma' =>
              ∃ rho ∈ failures, Compatible rho eta).card := by
      simpa only [RlcTwoChannelEdgeCodeHall] using h
    obtain ⟨J, hJ, hcompatible⟩ := hhall.mp h'
    exact ⟨⟨J, hJ⟩, hcompatible⟩
  · rintro ⟨J, hcompatible⟩
    simpa only [RlcTwoChannelEdgeCodeHall] using
      (hhall.mpr ⟨J, J.injective, hcompatible⟩)


theorem rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_edgeCodeHall
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (Compatible : RlcTwoChannelEdgeFailure gamma gamma' →
      RlcTwoChannelEdgeSuccess gamma gamma' → Prop)
    (hHall : RlcTwoChannelEdgeCodeHall gamma gamma' Compatible) :
    rlc_twoChannelForcedDualEventMass gamma gamma' (1 / 2) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  obtain ⟨J, _hcompatible⟩ :=
    (rlc_twoChannelEdgeCodeHall_iff_exists_compatibleEmbedding
      gamma gamma' Compatible).mp hHall
  exact
    rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_edgeEmbedding
      gamma gamma' J


theorem rlc_twoChannelForcedDualEventMass_compl_le_merged_of_edgeCodeHall
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (Compatible : RlcTwoChannelEdgeFailure gamma gamma' →
      RlcTwoChannelEdgeSuccess gamma gamma' → Prop)
    (hHall : RlcTwoChannelEdgeCodeHall gamma gamma' Compatible)
    (hdom : ∀ rho eta, Compatible rho eta →
      rlc_twoChannelForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) <=
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1)) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  obtain ⟨J, hcompatible⟩ :=
    (rlc_twoChannelEdgeCodeHall_iff_exists_compatibleEmbedding
      gamma gamma' Compatible).mp hHall
  apply rlc_twoChannelForcedDualEventMass_compl_le_merged_of_edgeEmbedding
    gamma gamma' hq J
  intro rho
  exact hdom rho (J rho) (hcompatible rho)


theorem
    rlc_twoChannelForcedDualEventMass_compl_le_mul_merged_of_edgeCodeHall
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q distortion : Real} (hq : 1 <= q) (hdistortion : 0 <= distortion)
    (Compatible : RlcTwoChannelEdgeFailure gamma gamma' ->
      RlcTwoChannelEdgeSuccess gamma gamma' -> Prop)
    (hHall : RlcTwoChannelEdgeCodeHall gamma gamma' Compatible)
    (hdom : forall rho eta, Compatible rho eta ->
      rlc_twoChannelForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) <=
        distortion *
          FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (BeffaraDC.selfDualPoint q) q
            (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1)) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      distortion *
        FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  obtain ⟨J, hcompatible⟩ :=
    (rlc_twoChannelEdgeCodeHall_iff_exists_compatibleEmbedding
      gamma gamma' Compatible).mp hHall
  apply
    rlc_twoChannelForcedDualEventMass_compl_le_mul_merged_of_edgeEmbedding
      gamma gamma' hq hdistortion J
  intro rho
  exact hdom rho (J rho) (hcompatible rho)


theorem
    rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_edgeCodeHall_score
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q) (N : Nat)
    (Compatible : RlcTwoChannelEdgeFailure gamma gamma' ->
      RlcTwoChannelEdgeSuccess gamma gamma' -> Prop)
    (hHall : RlcTwoChannelEdgeCodeHall gamma gamma' Compatible)
    (hscore : forall rho eta, Compatible rho eta ->
      FK.openCount (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) +
          2 * FK.numClustersBC
            (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorSeparateWiring gamma gamma')
            (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) <=
        FK.openCount (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) +
          2 * FK.numClustersBC
            (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) + N) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      (Real.sqrt q) ^ N *
        FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  apply
    rlc_twoChannelForcedDualEventMass_compl_le_mul_merged_of_edgeCodeHall
      gamma gamma' hq (pow_nonneg (Real.sqrt_nonneg q) N) Compatible hHall
  intro rho eta hcompatible
  rw [← rlc_twoChannel_bcProb_separate_selfDual_eq_forcedDualProb
    gamma gamma' _ (zero_lt_one.trans_le hq)]
  exact FK.bcProb_selfDualPoint_le_sqrt_pow_of_score_le
    (rlc_connectorTwoChannelGraph gamma gamma')
    (rlc_connectorSeparateWiring gamma gamma')
    (rlc_connectorMergedWiring gamma gamma')
    le_sup_left hq N _ _ (hscore rho eta hcompatible)


theorem rlc_twoChannel_score_le_hamming_add_two
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega eta : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.openCount (rlc_connectorTwoChannelGraph gamma gamma') omega +
        2 * FK.numClustersBC
          (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') omega <=
      FK.openCount (rlc_connectorTwoChannelGraph gamma gamma') eta +
        2 * FK.numClustersBC
          (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma') eta +
        FK.configHammingCount (rlc_connectorTwoChannelGraph gamma gamma')
          omega eta + 2 := by
  apply FK.bcScore_le_add_configHammingCount_add_boundaryGap
    (rlc_connectorTwoChannelGraph gamma gamma')
    (rlc_connectorSeparateWiring gamma gamma')
    (rlc_connectorMergedWiring gamma gamma') 1 omega eta
  simpa only [rlc_connectorMergedWiring, Nat.add_comm] using
    StatMech.FrontierD.numClustersBC_le_sup_edge_add_one
      (rlc_connectorTwoChannelGraph gamma gamma')
      (rlc_connectorSeparateWiring gamma gamma')
      (rlc_connectorRightAnchor gamma) (rlc_connectorLeftAnchor gamma') eta


theorem
    rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_edgeCodeHall_hamming
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q) (K : Nat)
    (Compatible : RlcTwoChannelEdgeFailure gamma gamma' ->
      RlcTwoChannelEdgeSuccess gamma gamma' -> Prop)
    (hHall : RlcTwoChannelEdgeCodeHall gamma gamma' Compatible)
    (hHamming : forall rho eta, Compatible rho eta ->
      FK.configHammingCount (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1)
        (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) <= K) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      (Real.sqrt q) ^ (K + 2) *
        FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  apply
    rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_edgeCodeHall_score
      gamma gamma' hq (K + 2) Compatible hHall
  intro rho eta hcompatible
  have hScore := rlc_twoChannel_score_le_hamming_add_two gamma gamma'
    (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1)
    (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1)
  have hDistance := hHamming rho eta hcompatible
  omega


theorem
    rlc_twoChannelForcedDualEventMass_compl_le_qpow_merged_of_edgeCodeHall_score
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q) (N : Nat)
    (Compatible : RlcTwoChannelEdgeFailure gamma gamma' ->
      RlcTwoChannelEdgeSuccess gamma gamma' -> Prop)
    (hHall : RlcTwoChannelEdgeCodeHall gamma gamma' Compatible)
    (hscore : forall rho eta, Compatible rho eta ->
      FK.openCount (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) +
          2 * FK.numClustersBC
            (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorSeparateWiring gamma gamma')
            (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) <=
        FK.openCount (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) +
          2 * FK.numClustersBC
            (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) + N) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      q ^ N *
        FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  apply
    rlc_twoChannelForcedDualEventMass_compl_le_mul_merged_of_edgeCodeHall
      gamma gamma' hq (pow_nonneg (by linarith) N) Compatible hHall
  intro rho eta hcompatible
  rw [← rlc_twoChannel_bcProb_separate_selfDual_eq_forcedDualProb
    gamma gamma' _ (zero_lt_one.trans_le hq)]
  exact FK.bcProb_selfDualPoint_le_qpow_of_score_le
    (rlc_connectorTwoChannelGraph gamma gamma')
    (rlc_connectorSeparateWiring gamma gamma')
    (rlc_connectorMergedWiring gamma gamma')
    le_sup_left hq N _ _ (hscore rho eta hcompatible)


end
end StatMech.Universality
