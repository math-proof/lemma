/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededMassObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassCapstone.Part2
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Theorem.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDualityObstruction.Part6
import Def.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassObstruction.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem scaleTwoGapNorthSouthEdges_subset :
    scaleTwoGapNorthSouthEdges ⊆
      (rlc_axisGapFiniteGraph rlc_scaleTwoDoubleFailureGap).edgeFinset := by
  intro e he
  simp only [scaleTwoGapNorthSouthEdges, Finset.mem_insert,
    Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · exact scaleTwoGapNorthEdge_mem
  · exact scaleTwoGapSouthEdge_mem

theorem scaleTwoGapNorthEastEdges_subset :
    scaleTwoGapNorthEastEdges ⊆
      (rlc_axisGapFiniteGraph rlc_scaleTwoDoubleFailureGap).edgeFinset := by
  intro e he
  simp only [scaleTwoGapNorthEastEdges, Finset.mem_insert,
    Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · exact scaleTwoGapNorthEdge_mem
  · exact scaleTwoGapEastEdge_mem

theorem scaleTwoGapNorthSouthEastEdges_subset :
    scaleTwoGapNorthSouthEastEdges ⊆
      (rlc_axisGapFiniteGraph rlc_scaleTwoDoubleFailureGap).edgeFinset := by
  intro e he
  simp only [scaleTwoGapNorthSouthEastEdges, Finset.mem_insert,
    Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · exact scaleTwoGapNorthEdge_mem
  · exact scaleTwoGapSouthEdge_mem
  · exact scaleTwoGapEastEdge_mem

theorem scaleTwoGapNorthSouthEdges_card :
    scaleTwoGapNorthSouthEdges.card = 2 := by
  simp [scaleTwoGapNorthSouthEdges, scaleTwoGapNorthEdge,
    scaleTwoGapSouthEdge, scaleTwoGapNorth, scaleTwoGapSouth,
    scaleTwoGapCenter, Sym2.eq_iff]

theorem scaleTwoGapNorthEastEdges_card :
    scaleTwoGapNorthEastEdges.card = 2 := by
  simp [scaleTwoGapNorthEastEdges, scaleTwoGapNorthEdge,
    scaleTwoGapEastEdge, scaleTwoGapNorth, scaleTwoGapEast,
    scaleTwoGapCenter, Sym2.eq_iff]

theorem scaleTwoGapNorthSouthEastEdges_card :
    scaleTwoGapNorthSouthEastEdges.card = 3 := by
  simp [scaleTwoGapNorthSouthEastEdges, scaleTwoGapNorthEdge,
    scaleTwoGapSouthEdge, scaleTwoGapEastEdge, scaleTwoGapNorth,
    scaleTwoGapSouth, scaleTwoGapEast, scaleTwoGapCenter, Sym2.eq_iff]

theorem bcEventMass_compl_eq_one_sub
    {V : Type*} [Fintype V] [DecidableEq V]
    (G C : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel C.Adj]
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace (Sym2 V))) :
    FK.bcEventMass G C p q Aᶜ = 1 - FK.bcEventMass G C p q A := by
  unfold FK.bcEventMass
  calc
    _ = ∑ omega : ConfigSpace (Sym2 V),
        (1 - A.indicator (fun _ => (1 : Real)) omega) *
          FK.bcProb G C p q omega := by
      apply Finset.sum_congr rfl
      intro omega _
      by_cases hA : omega ∈ A <;> simp [hA]
    _ = (∑ omega : ConfigSpace (Sym2 V), FK.bcProb G C p q omega) -
        ∑ omega : ConfigSpace (Sym2 V),
          A.indicator (fun _ => (1 : Real)) omega *
            FK.bcProb G C p q omega := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro omega _
      ring
    _ = _ := by rw [FK.bcProb_sum_eq_one G C hp hp1 hq]


theorem rlc_scaleTwoAxisGap_failureMass_q_one_eq_five_eighths :
    FK.bcEventMass
        (rlc_axisGapFiniteGraph rlc_scaleTwoDoubleFailureGap)
        (rlc_connectorSeparateWiring rlc_scaleTwoDoubleFailureRight
          rlc_scaleTwoDoubleFailureLeft)
        (BeffaraDC.selfDualPoint 1) 1
        (rlc_finiteAxisGapConnectorEvent rlc_scaleTwoDoubleFailureGap)ᶜ =
      5 / 8 := by
  classical
  have hsd : BeffaraDC.selfDualPoint 1 = (1 / 2 : Real) := by
    norm_num [BeffaraDC.selfDualPoint]
  rw [bcEventMass_compl_eq_one_sub _ _
    (by rw [hsd]; norm_num) (by rw [hsd]; norm_num) one_pos]
  rw [hsd]
  unfold FK.bcEventMass
  simp_rw [BeffaraDC.SymmetricDomain.bcProb_one_eq_fkProb_one]
  have hsuccess :
      (∑ rho : ConfigSpace (Sym2 ScaleTwoConnectorVertex),
        (rlc_finiteAxisGapConnectorEvent
          rlc_scaleTwoDoubleFailureGap).indicator
            (fun _ => (1 : Real)) rho *
          FK.fkProb (rlc_axisGapFiniteGraph
            rlc_scaleTwoDoubleFailureGap) (1 / 2) 1 rho) =
        (1 / 2 : Real) ^ scaleTwoGapNorthSouthEdges.card +
          (1 / 2 : Real) ^ scaleTwoGapNorthEastEdges.card -
            (1 / 2 : Real) ^ scaleTwoGapNorthSouthEastEdges.card := by
    calc
      _ = ∑ rho : ConfigSpace (Sym2 ScaleTwoConnectorVertex),
          ((if ∀ e ∈ scaleTwoGapNorthSouthEdges, rho e = true
              then (1 : Real) else 0) +
            (if ∀ e ∈ scaleTwoGapNorthEastEdges, rho e = true
              then (1 : Real) else 0) -
            (if ∀ e ∈ scaleTwoGapNorthSouthEastEdges, rho e = true
              then (1 : Real) else 0)) *
            FK.fkProb (rlc_axisGapFiniteGraph
              rlc_scaleTwoDoubleFailureGap) (1 / 2) 1 rho := by
        apply Finset.sum_congr rfl
        intro rho _
        rw [Set.indicator_apply]
        by_cases hn : rho scaleTwoGapNorthEdge = true <;>
          by_cases hs : rho scaleTwoGapSouthEdge = true <;>
          by_cases he : rho scaleTwoGapEastEdge = true <;>
          simp [scaleTwoGap_source_event_iff, hn, hs, he,
            scaleTwoGapNorthSouthEdges, scaleTwoGapNorthEastEdges,
            scaleTwoGapNorthSouthEastEdges]
      _ = (∑ rho : ConfigSpace (Sym2 ScaleTwoConnectorVertex),
            (if ∀ e ∈ scaleTwoGapNorthSouthEdges, rho e = true
              then (1 : Real) else 0) *
              FK.fkProb (rlc_axisGapFiniteGraph
                rlc_scaleTwoDoubleFailureGap) (1 / 2) 1 rho) +
          (∑ rho : ConfigSpace (Sym2 ScaleTwoConnectorVertex),
            (if ∀ e ∈ scaleTwoGapNorthEastEdges, rho e = true
              then (1 : Real) else 0) *
              FK.fkProb (rlc_axisGapFiniteGraph
                rlc_scaleTwoDoubleFailureGap) (1 / 2) 1 rho) -
          (∑ rho : ConfigSpace (Sym2 ScaleTwoConnectorVertex),
            (if ∀ e ∈ scaleTwoGapNorthSouthEastEdges, rho e = true
              then (1 : Real) else 0) *
              FK.fkProb (rlc_axisGapFiniteGraph
                rlc_scaleTwoDoubleFailureGap) (1 / 2) 1 rho) := by
        simp only [add_mul, sub_mul, Finset.sum_sub_distrib,
          Finset.sum_add_distrib]
      _ = _ := by
        rw [FK.fkProbOne_cylinder (G := rlc_axisGapFiniteGraph
              rlc_scaleTwoDoubleFailureGap) (by norm_num) (by norm_num)
            scaleTwoGapNorthSouthEdges scaleTwoGapNorthSouthEdges_subset,
          FK.fkProbOne_cylinder (G := rlc_axisGapFiniteGraph
              rlc_scaleTwoDoubleFailureGap) (by norm_num) (by norm_num)
            scaleTwoGapNorthEastEdges scaleTwoGapNorthEastEdges_subset,
          FK.fkProbOne_cylinder (G := rlc_axisGapFiniteGraph
              rlc_scaleTwoDoubleFailureGap) (by norm_num) (by norm_num)
            scaleTwoGapNorthSouthEastEdges
              scaleTwoGapNorthSouthEastEdges_subset]
  rw [hsuccess, scaleTwoGapNorthSouthEdges_card,
    scaleTwoGapNorthEastEdges_card, scaleTwoGapNorthSouthEastEdges_card]
  norm_num

theorem scaleTwoGap_PIMS_success_implies_west_closed
    (rho : ConfigSpace (Sym2 ScaleTwoConnectorVertex))
    (hsuccess : rlc_axisGapPIMSMixedReflectedConfig
        rlc_scaleTwoDoubleFailureGap rho ∈
      rlc_finiteAxisGapConnectorEvent rlc_scaleTwoDoubleFailureGap) :
    rho scaleTwoGapWestEdge = false := by
  let rho' := rlc_axisGapPIMSMixedReflectedConfig
    rlc_scaleTwoDoubleFailureGap rho
  have hnorth : rho' scaleTwoGapNorthEdge = true :=
    (scaleTwoGap_source_event_iff rho').mp hsuccess |>.1
  change rlc_axisGapPIMSMixedReflectedConfig
      rlc_scaleTwoDoubleFailureGap rho scaleTwoGapNorthEdge = true at hnorth
  rw [rlc_axisGapPIMSMixedReflectedConfig_apply] at hnorth
  have herase : scaleTwoGapNorthEdge.map Subtype.val =
      s((![0, -1] : Site 2), ![0, 0]) := by
    rfl
  rw [herase] at hnorth
  have hpims : rlc_pimsEdgeEquiv
      s((![0, -1] : Site 2), ![0, 0]) =
        s((![-1, -1] : Site 2), ![0, -1]) := by
    simpa using rlc_pimsEdgeEquiv_vertical 0 (-1)
  rw [hpims, rlc_axisGapAmbientMixedConfig_supportEdge
    rlc_scaleTwoDoubleFailureGap rho rlc_scaleTwoAxisGap_westEdge_mem] at hnorth
  have hlift : rlc_axisGapEdgeLift rlc_scaleTwoDoubleFailureGap
      s((![-1, -1] : Site 2), ![0, -1])
        rlc_scaleTwoAxisGap_westEdge_mem = scaleTwoGapWestEdge := by
    apply Sym2.map.injective Subtype.val_injective
    rw [rlc_axisGapEdgeLift_map]
    rfl
  rw [hlift] at hnorth
  simpa using hnorth

theorem scaleTwoGap_west_closed_mass_eq_half :
    FK.bcEventMass
        (rlc_axisGapFiniteGraph rlc_scaleTwoDoubleFailureGap)
        (rlc_connectorSeparateWiring rlc_scaleTwoDoubleFailureRight
          rlc_scaleTwoDoubleFailureLeft)
        (BeffaraDC.selfDualPoint 1) 1
        {rho | rho scaleTwoGapWestEdge = false} = 1 / 2 := by
  have hsd : BeffaraDC.selfDualPoint 1 = (1 / 2 : Real) := by
    norm_num [BeffaraDC.selfDualPoint]
  let A : Set (ConfigSpace (Sym2 ScaleTwoConnectorVertex)) :=
    {rho | rho scaleTwoGapWestEdge = true}
  have hcompl : {rho : ConfigSpace (Sym2 ScaleTwoConnectorVertex) |
      rho scaleTwoGapWestEdge = false} = Aᶜ := by
    ext rho
    simp [A]
  rw [hcompl, bcEventMass_compl_eq_one_sub _ _
    (by rw [hsd]; norm_num) (by rw [hsd]; norm_num) one_pos, hsd]
  unfold FK.bcEventMass
  simp_rw [BeffaraDC.SymmetricDomain.bcProb_one_eq_fkProb_one]
  have hsingle : ({scaleTwoGapWestEdge} :
      Finset (Sym2 ScaleTwoConnectorVertex)) ⊆
        (rlc_axisGapFiniteGraph
          rlc_scaleTwoDoubleFailureGap).edgeFinset := by
    simpa using scaleTwoGapWestEdge_mem
  rw [show (∑ rho : ConfigSpace (Sym2 ScaleTwoConnectorVertex),
      A.indicator (fun _ => (1 : Real)) rho *
        FK.fkProb (rlc_axisGapFiniteGraph
          rlc_scaleTwoDoubleFailureGap) (1 / 2) 1 rho) =
      ∑ rho : ConfigSpace (Sym2 ScaleTwoConnectorVertex),
        (if ∀ e ∈ ({scaleTwoGapWestEdge} :
            Finset (Sym2 ScaleTwoConnectorVertex)), rho e = true
          then (1 : Real) else 0) *
          FK.fkProb (rlc_axisGapFiniteGraph
            rlc_scaleTwoDoubleFailureGap) (1 / 2) 1 rho by
    apply Finset.sum_congr rfl
    intro rho _
    by_cases hw : rho scaleTwoGapWestEdge = true <;> simp [A, hw]]
  rw [FK.fkProbOne_cylinder (G := rlc_axisGapFiniteGraph
      rlc_scaleTwoDoubleFailureGap) (by norm_num) (by norm_num)
    {scaleTwoGapWestEdge} hsingle]
  norm_num


theorem rlc_scaleTwoAxisGap_PIMSSourceSuccessMass_q_one_le_half :
    rlc_axisGapPIMSSourceSuccessMass rlc_scaleTwoDoubleFailureGap 1 ≤
      1 / 2 := by
  unfold rlc_axisGapPIMSSourceSuccessMass FK.bcEventMass
  rw [show BeffaraDC.selfDualPoint 1 = (1 / 2 : Real) by
    norm_num [BeffaraDC.selfDualPoint]]
  calc
    _ ≤ ∑ rho : ConfigSpace (Sym2 ScaleTwoConnectorVertex),
        {rho | rho scaleTwoGapWestEdge = false}.indicator
          (fun _ => (1 : Real)) rho *
        FK.bcProb (rlc_axisGapFiniteGraph rlc_scaleTwoDoubleFailureGap)
          (rlc_connectorSeparateWiring rlc_scaleTwoDoubleFailureRight
            rlc_scaleTwoDoubleFailureLeft) (1 / 2) 1 rho := by
      apply Finset.sum_le_sum
      intro rho _
      apply mul_le_mul_of_nonneg_right
      · by_cases hs : rlc_axisGapPIMSMixedReflectedConfig
            rlc_scaleTwoDoubleFailureGap rho ∈
              rlc_finiteAxisGapConnectorEvent rlc_scaleTwoDoubleFailureGap
        · have hw := scaleTwoGap_PIMS_success_implies_west_closed rho hs
          simp [hs, hw]
        · by_cases hw : rho scaleTwoGapWestEdge = false <;>
            simp [hs, hw]
      · exact FK.bcProb_nonneg _ _ (by norm_num) (by norm_num) one_pos rho
    _ = 1 / 2 := by
      have hsd : BeffaraDC.selfDualPoint 1 = (1 / 2 : Real) := by
        norm_num [BeffaraDC.selfDualPoint]
      simpa [FK.bcEventMass, hsd] using scaleTwoGap_west_closed_mass_eq_half


theorem rlc_scaleTwoAxisGap_not_PIMSFailureMassTransport :
    ¬ RlcAxisGapPIMSFailureMassTransport
      rlc_scaleTwoDoubleFailureGap 1 := by
  intro htransport
  unfold RlcAxisGapPIMSFailureMassTransport at htransport
  rw [rlc_scaleTwoAxisGap_failureMass_q_one_eq_five_eighths] at htransport
  have h := htransport.trans
    rlc_scaleTwoAxisGap_PIMSSourceSuccessMass_q_one_le_half
  norm_num at h

end
end StatMech.Universality
