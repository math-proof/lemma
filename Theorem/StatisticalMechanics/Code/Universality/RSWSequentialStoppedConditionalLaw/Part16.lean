/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedExplorationBridge
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassCapstone.Part2
import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Def.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part16
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorExteriorFibreCondEventMass_eq_activeInduced {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) :
    rlc_connectorExteriorFibreCondEventMass
        gamma gamma' H B psi p q =
      FK.activeBCProbOf (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorExteriorInducedWiring gamma gamma' H B psi)
        (fun _ => p) q (rlc_connectorActiveEvent gamma gamma') := by
  classical
  unfold rlc_connectorExteriorFibreCondEventMass FK.activeBCProbOf
    FK.activeBCMean
  apply Finset.sum_congr rfl
  intro eta _
  rw [rlc_connectorExteriorFibre_condBcProb_eq_induced
    gamma gamma' H B hGH psi hp hp1 eta]


theorem rlc_connectorExteriorFibreCondEventMass_eq_induced {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    rlc_connectorExteriorFibreCondEventMass
        gamma gamma' H B psi p q =
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorExteriorInducedWiring gamma gamma' H B psi) p q
        (rlc_finiteConnectorEvent gamma gamma') := by
  classical
  rw [rlc_connectorExteriorFibreCondEventMass_eq_activeInduced
      gamma gamma' H B hGH psi hp hp1,
    FK.activeBCProbOf_eq_bcProb_preimage
      (rlc_connectorFiniteGraph gamma gamma')
      (rlc_connectorExteriorInducedWiring gamma gamma' H B psi)
      hp hp1 hq,
    rlc_connectorActiveEvent_preimage]
  rfl

set_option maxHeartbeats 800000 in


theorem rlc_connectorExteriorFibreCondEventMass_eq_ambientSum {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (p q : Real) :
    rlc_connectorExteriorFibreCondEventMass
        gamma gamma' H B psi p q =
      ∑ rho,
        (rlc_finiteConnectorEvent gamma gamma').indicator
            (fun _ => (1 : Real)) rho *
          FK.condBcProb H B p q
            (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi rho := by
  classical
  let S := FK.condFibre
    (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi
  let term := fun rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) =>
    (rlc_finiteConnectorEvent gamma gamma').indicator
        (fun _ => (1 : Real)) rho *
      FK.condBcProb H B p q
        (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi rho
  have hrestrict : (∑ rho, term rho) = ∑ rho ∈ S, term rho := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro rho _ hrho
    have hnot : ¬ FK.AgreesOff
        (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi rho := by
      rw [FK.mem_condFibre] at hrho
      exact hrho
    unfold term FK.condBcProb
    rw [if_neg hnot, mul_zero]
  symm
  calc
    (∑ rho, term rho) = ∑ rho ∈ S, term rho := hrestrict
    _ = ∑ rho : {rho // rho ∈ S}, term rho :=
      Finset.sum_subtype S (fun _ => Iff.rfl) term
    _ = ∑ eta, term ((rlc_connectorExteriorFibreEquiv
        gamma gamma' psi) eta) :=
      (Equiv.sum_comp (rlc_connectorExteriorFibreEquiv gamma gamma' psi)
        (fun rho => term rho.1)).symm
    _ = rlc_connectorExteriorFibreCondEventMass
        gamma gamma' H B psi p q := by
      unfold rlc_connectorExteriorFibreCondEventMass term
      apply Finset.sum_congr rfl
      intro eta _
      change
        (rlc_finiteConnectorEvent gamma gamma').indicator
            (fun _ => (1 : Real))
            (rlc_connectorExteriorFibreConfig gamma gamma' psi eta) *
          FK.condBcProb H B p q
            (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi
            (rlc_connectorExteriorFibreConfig gamma gamma' psi eta) =
        (rlc_connectorActiveEvent gamma gamma').indicator
            (fun _ => (1 : Real)) eta *
          FK.condBcProb H B p q
            (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi
            (rlc_connectorExteriorFibreConfig gamma gamma' psi eta)
      have hevent :
          rlc_connectorExteriorFibreConfig gamma gamma' psi eta ∈
              rlc_finiteConnectorEvent gamma gamma' ↔
            eta ∈ rlc_connectorActiveEvent gamma gamma' := by
        rw [← rlc_connectorActiveEvent_preimage]
        simp only [Set.mem_preimage,
          rlc_connectorExteriorFibreConfig_restrictActive]
      by_cases heta : eta ∈ rlc_connectorActiveEvent gamma gamma'
      · rw [Set.indicator_of_mem heta,
          Set.indicator_of_mem (hevent.mpr heta)]
      · simp only [Set.indicator_of_notMem heta,
          Set.indicator_of_notMem (fun h => heta (hevent.mp h)),
          zero_mul]


theorem rlc_connectorExteriorFibreCondEventMass_ge_separate {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (F : RlcConnectorCompatibleExteriorFibre gamma gamma' H psi)
    {q : Real} (hq : 1 ≤ q) :
    FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') ≤
      rlc_connectorExteriorFibreCondEventMass gamma gamma' H B psi
        (BeffaraDC.selfDualPoint q) q := by
  classical
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  rw [rlc_connectorExteriorFibreCondEventMass_eq_induced
    gamma gamma' H B F.connector_le psi hp hp1 hq0]
  exact FK.bcProb_mono_bc
    (rlc_connectorFiniteGraph gamma gamma')
    (rlc_connectorSeparateWiring gamma gamma')
    (rlc_connectorExteriorInducedWiring gamma gamma' H B psi)
    (F.separate_le_inducedWiring B) hp hp1 hq
    (rlc_finiteConnectorEvent_isIncreasing gamma gamma')


theorem RlcSequentialExtremalExplorationState.connectorConditionalMass_ge_separate
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (S : RlcSequentialExtremalExplorationState gamma gamma')
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
    (hTH : rlc_connectorTraceWiring gamma gamma' ≤ H)
    {q : Real} (hq : 1 ≤ q) :
    FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') ≤
      rlc_connectorExteriorFibreCondEventMass gamma gamma' H B
        (rlc_connectorRestrictConfig S.rawConfig)
        (BeffaraDC.selfDualPoint q) q :=
  rlc_connectorExteriorFibreCondEventMass_ge_separate
    gamma gamma' H B (rlc_connectorRestrictConfig S.rawConfig)
      (S.toCompatibleExteriorFibre H hGH hTH) hq


theorem rlc_connectorOutsideEventMass_lower {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (S : Set (ConfigSpace (Sym2 (RlcConnectorVertex n))))
    (hS : FK.DependsOnOutside
      (rlc_connectorFiniteGraph gamma gamma').edgeFinset S)
    (hcompat : ∀ {psi}, psi ∈ S →
      RlcConnectorCompatibleExteriorFibre gamma gamma' H psi)
    {q : Real} (hq : 1 ≤ q) :
    FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') *
      (∑ rho, S.indicator (fun _ => (1 : Real)) rho *
        FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho) ≤
    ∑ rho,
      ((rlc_finiteConnectorEvent gamma gamma') ∩ S).indicator
          (fun _ => (1 : Real)) rho *
        FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho := by
  classical
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  let F := (rlc_connectorFiniteGraph gamma gamma').edgeFinset
  let A := rlc_finiteConnectorEvent gamma gamma'
  let alpha := FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
    (rlc_connectorSeparateWiring gamma gamma')
    (BeffaraDC.selfDualPoint q) q A
  change alpha *
      (∑ rho, S.indicator (fun _ => (1 : Real)) rho *
        FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho) ≤
    ∑ rho, (A ∩ S).indicator (fun _ => (1 : Real)) rho *
      FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho
  rw [FK.bcProb_fibre_decompose H B hp hp1 hq0 F (A ∩ S),
    FK.bcProb_fibre_decompose H B hp hp1 hq0 F S,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro psi hpsi
  rw [FK.fibreReps, Finset.mem_filter] at hpsi
  let mass := ∑ sigma ∈ FK.condFibre F psi,
    FK.bcProb H B (BeffaraDC.selfDualPoint q) q sigma
  have hmass : 0 ≤ mass := Finset.sum_nonneg fun sigma _ =>
    FK.bcProb_nonneg H B hp hp1 hq0 sigma
  have hScond :
      (∑ rho, S.indicator (fun _ => (1 : Real)) rho *
          FK.condBcProb H B (BeffaraDC.selfDualPoint q) q F psi rho) =
        S.indicator (fun _ => (1 : Real)) psi :=
    FK.condBcProb_sum_outside H B hp hp1 hq0 hS hpsi.2
  have hAScond :
      (∑ rho, (A ∩ S).indicator (fun _ => (1 : Real)) rho *
          FK.condBcProb H B (BeffaraDC.selfDualPoint q) q F psi rho) =
        S.indicator (fun _ => (1 : Real)) psi *
          (∑ rho, A.indicator (fun _ => (1 : Real)) rho *
            FK.condBcProb H B (BeffaraDC.selfDualPoint q) q F psi rho) :=
    FK.condBcProb_cross_outside H B hS
  rw [hScond, hAScond]
  by_cases hpsiS : psi ∈ S
  · have hres := rlc_connectorExteriorFibreCondEventMass_ge_separate
      gamma gamma' H B psi (hcompat hpsiS) hq
    rw [rlc_connectorExteriorFibreCondEventMass_eq_ambientSum
      gamma gamma' H B psi (BeffaraDC.selfDualPoint q) q] at hres
    change alpha ≤
      ∑ rho, A.indicator (fun _ => (1 : Real)) rho *
        FK.condBcProb H B (BeffaraDC.selfDualPoint q) q F psi rho at hres
    rw [Set.indicator_of_mem hpsiS]
    simp only [mul_one, one_mul]
    change alpha * mass ≤ mass *
      (∑ rho, A.indicator (fun _ => (1 : Real)) rho *
        FK.condBcProb H B (BeffaraDC.selfDualPoint q) q F psi rho)
    calc
      alpha * mass = mass * alpha := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hres hmass
  · simp [Set.indicator_of_notMem hpsiS]


theorem rlc_finiteExtremalPairCandidate_connectorMass_lower {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
    (hTH : rlc_connectorTraceWiring gamma gamma' ≤ H)
    (hdisj : Disjoint
      (rlc_finiteExtremalPairCandidateEdges gamma gamma')
      (rlc_connectorFiniteGraph gamma gamma').edgeFinset)
    {q : Real} (hq : 1 ≤ q) :
    FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') *
      (∑ rho,
        (rlc_finiteExtremalPairCandidate gamma gamma').indicator
            (fun _ => (1 : Real)) rho *
          FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho) ≤
    ∑ rho,
      ((rlc_finiteConnectorEvent gamma gamma') ∩
          rlc_finiteExtremalPairCandidate gamma gamma').indicator
          (fun _ => (1 : Real)) rho *
        FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho := by
  classical
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  let F := (rlc_connectorFiniteGraph gamma gamma').edgeFinset
  let A := rlc_finiteConnectorEvent gamma gamma'
  let S := rlc_finiteExtremalPairCandidate gamma gamma'
  let alpha := FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
    (rlc_connectorSeparateWiring gamma gamma')
    (BeffaraDC.selfDualPoint q) q A
  have hS : FK.DependsOnOutside F S := by
    exact rlc_finiteExtremalPairCandidate_dependsOnOutside
      gamma gamma' hdisj
  change alpha *
      (∑ rho, S.indicator (fun _ => (1 : Real)) rho *
        FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho) ≤
    ∑ rho, (A ∩ S).indicator (fun _ => (1 : Real)) rho *
      FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho
  rw [FK.bcProb_fibre_decompose H B hp hp1 hq0 F (A ∩ S),
    FK.bcProb_fibre_decompose H B hp hp1 hq0 F S,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro psi hpsi
  rw [FK.fibreReps, Finset.mem_filter] at hpsi
  let mass := ∑ sigma ∈ FK.condFibre F psi,
    FK.bcProb H B (BeffaraDC.selfDualPoint q) q sigma
  have hmass : 0 ≤ mass := Finset.sum_nonneg fun sigma _ =>
    FK.bcProb_nonneg H B hp hp1 hq0 sigma
  have hScond :
      (∑ rho, S.indicator (fun _ => (1 : Real)) rho *
          FK.condBcProb H B (BeffaraDC.selfDualPoint q) q F psi rho) =
        S.indicator (fun _ => (1 : Real)) psi :=
    FK.condBcProb_sum_outside H B hp hp1 hq0 hS hpsi.2
  have hAScond :
      (∑ rho, (A ∩ S).indicator (fun _ => (1 : Real)) rho *
          FK.condBcProb H B (BeffaraDC.selfDualPoint q) q F psi rho) =
        S.indicator (fun _ => (1 : Real)) psi *
          (∑ rho, A.indicator (fun _ => (1 : Real)) rho *
            FK.condBcProb H B (BeffaraDC.selfDualPoint q) q F psi rho) :=
    FK.condBcProb_cross_outside H B hS
  rw [hScond, hAScond]
  by_cases hpsiS : psi ∈ S
  · have hcompat : RlcConnectorCompatibleExteriorFibre
        gamma gamma' H psi := by
      apply rlc_finiteExtremalPairCandidate_compatibleExteriorFibre
        gamma gamma' H hGH hTH
      exact hpsiS
    have hres := rlc_connectorExteriorFibreCondEventMass_ge_separate
      gamma gamma' H B psi hcompat hq
    rw [rlc_connectorExteriorFibreCondEventMass_eq_ambientSum
      gamma gamma' H B psi (BeffaraDC.selfDualPoint q) q] at hres
    change alpha ≤
      ∑ rho, A.indicator (fun _ => (1 : Real)) rho *
        FK.condBcProb H B (BeffaraDC.selfDualPoint q) q F psi rho at hres
    rw [Set.indicator_of_mem hpsiS]
    simp only [mul_one, one_mul]
    change alpha * mass ≤ mass *
      (∑ rho, A.indicator (fun _ => (1 : Real)) rho *
        FK.condBcProb H B (BeffaraDC.selfDualPoint q) q F psi rho)
    calc
      alpha * mass = mass * alpha := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hres hmass
  · simp [Set.indicator_of_notMem hpsiS]


theorem RlcBookFaithfulStratumReplacement.finiteExtremalPairCandidate_connectorMass_lower
    {n : Int}
    {gamma delta : RlcRightDiagonalPath n}
    {gamma' delta' : RlcLeftDiagonalPath n}
    (R : RlcBookFaithfulStratumReplacement gamma gamma' delta delta')
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hGH : rlc_connectorFiniteGraph delta delta' ≤ H)
    (hTH : rlc_connectorTraceWiring delta delta' ≤ H)
    {q : Real} (hq : 1 ≤ q) :
    FK.bcEventMass (rlc_connectorFiniteGraph delta delta')
        (rlc_connectorSeparateWiring delta delta')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent delta delta') *
      (∑ rho,
        (rlc_finiteExtremalPairCandidate gamma gamma').indicator
            (fun _ => (1 : Real)) rho *
          FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho) ≤
    ∑ rho,
      ((rlc_finiteConnectorEvent delta delta') ∩
          rlc_finiteExtremalPairCandidate gamma gamma').indicator
          (fun _ => (1 : Real)) rho *
        FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho := by
  apply rlc_connectorOutsideEventMass_lower delta delta' H B
    (rlc_finiteExtremalPairCandidate gamma gamma')
  · intro psi rho hagree
    apply indic_iff
    apply rlc_finiteExtremalPairCandidate_dependsOn
    intro e he
    exact (hagree e (fun heG =>
      (Finset.disjoint_left.mp
        R.finiteExtremalPairCandidateEdges_disjoint_connector) he heG)).symm
  · intro psi hpsi
    exact R.compatibleExteriorFibre H hGH hTH hpsi
  · exact hq


theorem RlcBookFaithfulStratumReplacement.finiteExtremalPairCandidate_connectorMass_selfDual_ge
    {n : Int}
    {gamma delta : RlcRightDiagonalPath n}
    {gamma' delta' : RlcLeftDiagonalPath n}
    (R : RlcBookFaithfulStratumReplacement gamma gamma' delta delta')
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hGH : rlc_connectorFiniteGraph delta delta' ≤ H)
    (hTH : rlc_connectorTraceWiring delta delta' ≤ H)
    {q : Real} (hq : 1 ≤ q)
    (hdual :
      rlc_connectorForcedDualEventMass delta delta'
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent delta delta')ᶜ ≤
        FK.bcEventMass (rlc_connectorFiniteGraph delta delta')
          (rlc_connectorMergedWiring delta delta')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent delta delta')) :
    1 / (1 + q) *
      (∑ rho,
        (rlc_finiteExtremalPairCandidate gamma gamma').indicator
            (fun _ => (1 : Real)) rho *
          FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho) ≤
    ∑ rho,
      ((rlc_finiteConnectorEvent delta delta') ∩
          rlc_finiteExtremalPairCandidate gamma gamma').indicator
          (fun _ => (1 : Real)) rho *
        FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  let stratumMass := ∑ rho,
    (rlc_finiteExtremalPairCandidate gamma gamma').indicator
        (fun _ => (1 : Real)) rho *
      FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho
  have hmass : 0 ≤ stratumMass := Finset.sum_nonneg fun rho _ =>
    mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) rho)
      (FK.bcProb_nonneg H B hp hp1 hq0 rho)
  have hfloor := rlc_finiteConnectorMass_selfDual_ge_one_div_one_add_q
    delta delta' hq hdual
  have haggregate :=
    R.finiteExtremalPairCandidate_connectorMass_lower H B hGH hTH hq
  change 1 / (1 + q) * stratumMass ≤ _
  calc
    1 / (1 + q) * stratumMass ≤
        FK.bcEventMass (rlc_connectorFiniteGraph delta delta')
            (rlc_connectorSeparateWiring delta delta')
            (BeffaraDC.selfDualPoint q) q
            (rlc_finiteConnectorEvent delta delta') * stratumMass :=
      mul_le_mul_of_nonneg_right hfloor hmass
    _ ≤ _ := haggregate


theorem RlcBookFaithfulTracePair.finiteExtremalPairCandidate_connectorMass_lower
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
    (hTH : rlc_connectorTraceWiring gamma gamma' ≤ H)
    {q : Real} (hq : 1 ≤ q) :
    FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') *
      (∑ rho,
        (rlc_finiteExtremalPairCandidate gamma gamma').indicator
            (fun _ => (1 : Real)) rho *
          FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho) ≤
    ∑ rho,
      ((rlc_finiteConnectorEvent gamma gamma') ∩
          rlc_finiteExtremalPairCandidate gamma gamma').indicator
          (fun _ => (1 : Real)) rho *
        FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho :=
  rlc_finiteExtremalPairCandidate_connectorMass_lower
    gamma gamma' H B hGH hTH
      hfaith.finiteExtremalPairCandidateEdges_disjoint_connector hq


theorem RlcBookFaithfulTracePair.finiteExtremalPairCandidate_connectorMass_selfDual_ge
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (H B : SimpleGraph (RlcConnectorVertex n))
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
    (hTH : rlc_connectorTraceWiring gamma gamma' ≤ H)
    {q : Real} (hq : 1 ≤ q)
    (hdual :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')ᶜ ≤
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')) :
    1 / (1 + q) *
      (∑ rho,
        (rlc_finiteExtremalPairCandidate gamma gamma').indicator
            (fun _ => (1 : Real)) rho *
          FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho) ≤
    ∑ rho,
      ((rlc_finiteConnectorEvent gamma gamma') ∩
          rlc_finiteExtremalPairCandidate gamma gamma').indicator
          (fun _ => (1 : Real)) rho *
        FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  let stratumMass := ∑ rho,
    (rlc_finiteExtremalPairCandidate gamma gamma').indicator
        (fun _ => (1 : Real)) rho *
      FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho
  have hmass : 0 ≤ stratumMass := Finset.sum_nonneg fun rho _ =>
    mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) rho)
      (FK.bcProb_nonneg H B hp hp1 hq0 rho)
  have hfloor := rlc_finiteConnectorMass_selfDual_ge_one_div_one_add_q
    gamma gamma' hq hdual
  have haggregate :=
    hfaith.finiteExtremalPairCandidate_connectorMass_lower
      H B hGH hTH hq
  change 1 / (1 + q) * stratumMass ≤ _
  calc
    1 / (1 + q) * stratumMass ≤
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma') * stratumMass :=
      mul_le_mul_of_nonneg_right hfloor hmass
    _ ≤ _ := haggregate

end
end StatMech.Universality
