/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Theorem.StatisticalMechanics.Code.Foundations.WeightedFiniteInjection
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannel.Part9
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelForcedDualEventMass_compl_le_merged_of_partitioned_injections
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (R : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
      rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} -> Prop)
    (Dgood : {rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
        rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} // R rho} ->
      ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (Dbad : {rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
        rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} // ¬ R rho} ->
      ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hgoodInj : Function.Injective Dgood)
    (hbadInj : Function.Injective Dbad)
    (hrange : Disjoint (Set.range Dgood) (Set.range Dbad))
    (hgoodSuccess : forall rho,
      Dgood rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hbadSuccess : forall rho,
      Dbad rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hgoodProb : forall rho,
      rlc_twoChannelForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q rho.1.1 <=
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q (Dgood rho))
    (hbadProb : forall rho,
      rlc_twoChannelForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q rho.1.1 <=
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q (Dbad rho)) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  classical
  let source := {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
    rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'}
  let D : source -> ConfigSpace (Sym2 (RlcConnectorVertex n)) := fun rho =>
    if h : R rho then Dgood ⟨rho, h⟩ else Dbad ⟨rho, h⟩
  have hDinj : Function.Injective D := by
    intro rho eta hD
    by_cases hrho : R rho
    · by_cases heta : R eta
      · simp only [D, dif_pos hrho, dif_pos heta] at hD
        have hsub := hgoodInj hD
        exact Subtype.ext (congrArg (fun z => z.1.1) hsub)
      · simp only [D, dif_pos hrho, dif_neg heta] at hD
        exfalso
        exact Set.disjoint_left.mp hrange
          ⟨⟨rho, hrho⟩, rfl⟩ ⟨⟨eta, heta⟩, hD.symm⟩
    · by_cases heta : R eta
      · simp only [D, dif_neg hrho, dif_pos heta] at hD
        exfalso
        exact Set.disjoint_left.mp hrange
          ⟨⟨eta, heta⟩, rfl⟩ ⟨⟨rho, hrho⟩, hD⟩
      · simp only [D, dif_neg hrho, dif_neg heta] at hD
        have hsub := hbadInj hD
        exact Subtype.ext (congrArg (fun z => z.1.1) hsub)
  apply rlc_twoChannelForcedDualEventMass_compl_le_merged_of_injection
    gamma gamma' hq D hDinj
  · intro rho
    by_cases hrho : R rho
    · simpa only [D, dif_pos hrho] using hgoodSuccess ⟨rho, hrho⟩
    · simpa only [D, dif_neg hrho] using hbadSuccess ⟨rho, hrho⟩
  · intro rho
    by_cases hrho : R rho
    · simpa only [D, dif_pos hrho] using hgoodProb ⟨rho, hrho⟩
    · simpa only [D, dif_neg hrho] using hbadProb ⟨rho, hrho⟩


theorem rlc_twoChannelForcedDualFailurePushforwardComparison_of_anchoredIncidenceInjections
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {q : Real} (hq : 1 <= q)
    (Dincidence : {rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
        rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} //
          RlcTwoChannelFailureRetainedAnchorTraceIncidence
            gamma gamma' hfaith rho} ->
      ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (Dmissing : {rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
        rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} //
          ¬ RlcTwoChannelFailureRetainedAnchorTraceIncidence
            gamma gamma' hfaith rho} ->
      ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hincidenceInj : Function.Injective Dincidence)
    (hmissingInj : Function.Injective Dmissing)
    (hrange : Disjoint (Set.range Dincidence) (Set.range Dmissing))
    (hincidenceSuccess : forall rho,
      Dincidence rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hmissingSuccess : forall rho,
      Dmissing rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hincidenceProb : forall rho,
      rlc_twoChannelForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q rho.1.1 <=
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q (Dincidence rho))
    (hmissingProb : forall rho,
      rlc_twoChannelForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q rho.1.1 <=
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q (Dmissing rho)) :
    RlcTwoChannelForcedDualFailurePushforwardComparison gamma gamma' q := by
  classical
  unfold RlcTwoChannelForcedDualFailurePushforwardComparison
  calc
    rlc_twoChannelForcedDualFailureImageMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q <=
      rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ := by
      unfold rlc_twoChannelForcedDualFailureImageMass
        rlc_twoChannelForcedDualEventMass
      apply Finset.sum_le_sum
      intro rho _
      have hq0 : 0 < q := zero_lt_one.trans_le hq
      obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
      by_cases hsource :
          rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma'
      · simp [hsource]
      · have hcomp : rho ∈
            (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ := by
          simpa using hsource
        simp only [Set.indicator_of_mem hcomp, one_mul]
        by_cases hpims : rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
            rlc_finiteTwoChannelConnectorEvent gamma gamma'
        · simp [hpims]
        · simp only [Set.indicator_of_notMem hpims, zero_mul]
          exact rlc_twoChannelForcedDualProb_nonneg
            gamma gamma' hp hp1 hq0 rho
    _ <= FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
      apply rlc_twoChannelForcedDualEventMass_compl_le_merged_of_partitioned_injections
        gamma gamma' hq
        (RlcTwoChannelFailureRetainedAnchorTraceIncidence
          gamma gamma' hfaith)
        Dincidence Dmissing hincidenceInj hmissingInj hrange
        hincidenceSuccess hmissingSuccess hincidenceProb hmissingProb


theorem rlc_twoChannelForcedDualFailurePushforwardComparison_q_one_of_anchoredIncidenceInjections
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (Dincidence : {rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
        rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} //
          RlcTwoChannelFailureRetainedAnchorTraceIncidence
            gamma gamma' hfaith rho} ->
      ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (Dmissing : {rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
        rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} //
          ¬ RlcTwoChannelFailureRetainedAnchorTraceIncidence
            gamma gamma' hfaith rho} ->
      ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hincidenceInj : Function.Injective Dincidence)
    (hmissingInj : Function.Injective Dmissing)
    (hrange : Disjoint (Set.range Dincidence) (Set.range Dmissing))
    (hincidenceSuccess : forall rho,
      Dincidence rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hmissingSuccess : forall rho,
      Dmissing rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    RlcTwoChannelForcedDualFailurePushforwardComparison gamma gamma' 1 := by
  apply rlc_twoChannelForcedDualFailurePushforwardComparison_of_anchoredIncidenceInjections
    gamma gamma' hfaith le_rfl Dincidence Dmissing hincidenceInj hmissingInj
      hrange hincidenceSuccess hmissingSuccess
  · intro rho
    rw [show BeffaraDC.selfDualPoint 1 = (1 / 2 : Real) by
      norm_num [BeffaraDC.selfDualPoint]]
    exact (rlc_twoChannelForcedDualProb_half_q_one_eq_merged
      gamma gamma' rho.1.1 (Dincidence rho)).le
  · intro rho
    rw [show BeffaraDC.selfDualPoint 1 = (1 / 2 : Real) by
      norm_num [BeffaraDC.selfDualPoint]]
    exact (rlc_twoChannelForcedDualProb_half_q_one_eq_merged
      gamma gamma' rho.1.1 (Dmissing rho)).le


theorem rlc_twoChannelConnector_glues_horizontal (n : Int) (_hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    rlc_pathOpen gamma.1 ∩ rlc_pathOpen gamma'.1 ∩
        (rlc_connectorRestrictConfig ⁻¹'
          rlc_finiteTwoChannelConnectorEvent gamma gamma') ⊆
      horizontalCrossingEvent (-2 * n) (2 * n) (-n) n := by
  intro omega homega
  obtain ⟨⟨hgamma, hgamma'⟩, x, y, hx, hy, hxy⟩ := homega
  obtain ⟨_hxSmall, hxToRightSmall⟩ :=
    rlc_pathOpen_connected_finish gamma.1 omega hgamma hx
  obtain ⟨_hySmall, hleftToYSmall⟩ :=
    rlc_pathOpen_connected_start gamma'.1 omega hgamma' hy
  have hrightSub : rect 0 (2 * n) (-n) n ⊆
      rect (-2 * n) (2 * n) (-n) n := by
    intro z hz
    rw [mem_rect] at hz ⊢
    omega
  have hleftSub : rect (-2 * n) 0 (-n) n ⊆
      rect (-2 * n) (2 * n) (-n) n := by
    intro z hz
    rw [mem_rect] at hz ⊢
    omega
  have hxToRight := StatMech.RSW.Strip.connectedWithin_mono_set omega
    hrightSub hxToRightSmall
  have hleftToY := StatMech.RSW.Strip.connectedWithin_mono_set omega
    hleftSub hleftToYSmall
  let hom : FK.openSub (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorRestrictConfig omega) →g
      openSubgraphInduce 2 omega
        (rect (-2 * n) (2 * n) (-n) n) := {
    toFun z := ⟨z.1, z.2⟩
    map_rel' := by
      intro a b hab
      rw [FK.openSub_adj] at hab
      rcases hab with ⟨habGraph, habOpen⟩
      have habLat : (hypercubicLattice 2).Adj a.1 b.1 := by
        rcases habGraph.1 with habCentral | habReflected
        · exact habCentral.1
        · exact habReflected.1
      exact ⟨habLat, by simpa [rlc_connectorRestrictConfig,
        Sym2.map_mk] using habOpen⟩
  }
  have hxyAmbient : ConnectedWithin 2 omega
      (rect (-2 * n) (2 * n) (-n) n) ⟨x.1, x.2⟩ ⟨y.1, y.2⟩ :=
    hxy.map hom
  let xL : leftSide (-2 * n) (2 * n) (-n) n :=
    ⟨gamma'.1.1, by
      rw [mem_leftSide, mem_rect]
      have h := gamma'.1.1.2
      rw [mem_leftSide, mem_rect] at h
      exact ⟨⟨by omega, by omega, h.1.2.2.1, h.1.2.2.2⟩, h.2⟩⟩
  let yR : rightSide (-2 * n) (2 * n) (-n) n :=
    ⟨gamma.1.2.1, by
      rw [mem_rightSide, mem_rect]
      have h := gamma.1.2.1.2
      rw [mem_rightSide, mem_rect] at h
      exact ⟨⟨by omega, by omega, h.1.2.2.1, h.1.2.2.2⟩, h.2⟩⟩
  refine ⟨xL, yR, ?_⟩
  exact hleftToY.trans (hxyAmbient.symm.trans hxToRight)


end
end StatMech.Universality
