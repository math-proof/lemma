/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Theorem.StatisticalMechanics.Code.Foundations.WeightedFiniteInjection
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannel.Part7
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelPIMSFailureImageMass_eq_forcedDual {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 0 < q) :
    rlc_twoChannelPIMSFailureImageMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q =
      rlc_twoChannelForcedDualFailureImageMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q := by
  unfold rlc_twoChannelPIMSFailureImageMass
    rlc_twoChannelForcedDualFailureImageMass
  apply Finset.sum_congr rfl
  intro rho _
  rw [rlc_twoChannel_bcProb_separate_selfDual_eq_forcedDualProb
    gamma gamma' rho hq]


theorem rlc_twoChannel_failureMass_eq_PIMSFailureImageMass {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real)
    (hfailure : RlcTwoChannelClosureFailureCertificate gamma gamma') :
    FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ =
      rlc_twoChannelPIMSFailureImageMass gamma gamma' p q := by
  classical
  unfold FK.bcEventMass rlc_twoChannelPIMSFailureImageMass
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hrho : rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma'
  · rw [Set.indicator_of_notMem (by simpa using hrho)]
    simp
  · rw [Set.indicator_of_mem (by simpa using hrho),
      Set.indicator_of_mem
        (rlc_twoChannelPIMS_success_of_closureFailureCertificate
          gamma gamma' hfailure rho hrho)]
    simp


theorem rlc_twoChannelForcedDualFailureImageMass_eq_compl {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real)
    (hfailure : RlcTwoChannelClosureFailureCertificate gamma gamma') :
    rlc_twoChannelForcedDualFailureImageMass gamma gamma' p q =
      rlc_twoChannelForcedDualEventMass gamma gamma' p q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ := by
  classical
  unfold rlc_twoChannelForcedDualFailureImageMass
    rlc_twoChannelForcedDualEventMass
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hrho : rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma'
  · rw [Set.indicator_of_notMem (by simpa using hrho)]
    simp
  · rw [Set.indicator_of_mem (by simpa using hrho),
      Set.indicator_of_mem
        (rlc_twoChannelPIMS_success_of_closureFailureCertificate
          gamma gamma' hfailure rho hrho)]
    simp


theorem rlc_twoChannelForcedDualEventMass_compl_le_merged_of_equiv {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 ≤ q)
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
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ ≤
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  classical
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  unfold rlc_twoChannelForcedDualEventMass FK.bcEventMass
  rw [← Equiv.sum_comp D (fun eta :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) =>
      (rlc_finiteTwoChannelConnectorEvent gamma gamma').indicator
        (fun _ => (1 : Real)) eta *
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q eta)]
  apply Finset.sum_le_sum
  intro rho _
  by_cases hrho : rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma'
  · rw [Set.indicator_of_notMem (by simpa using hrho)]
    simp only [zero_mul]
    exact mul_nonneg (by
      by_cases hD : D rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma'
      <;> simp [hD])
      (FK.bcProb_nonneg (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma') hp hp1 hq0 (D rho))
  · rw [Set.indicator_of_mem (by simpa using hrho),
      Set.indicator_of_mem (hfailure rho hrho)]
    simpa using hprob rho


theorem rlc_twoChannelForcedDualEventMass_compl_le_merged_of_injection
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 ≤ q)
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
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ ≤
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  classical
  let A := rlc_finiteTwoChannelConnectorEvent gamma gamma'
  let source := {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) // rho ∉ A}
  let range : Set (ConfigSpace (Sym2 (RlcConnectorVertex n))) := Set.range D
  let e : source ≃ range := Equiv.ofInjective D hinj
  have hrange : range ⊆ A := by
    rintro eta ⟨rho, rfl⟩
    exact hsuccess rho
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  unfold rlc_twoChannelForcedDualEventMass FK.bcEventMass
  calc
    (∑ rho : ConfigSpace (Sym2 (RlcConnectorVertex n)),
        Aᶜ.indicator (fun _ => (1 : Real)) rho *
          rlc_twoChannelForcedDualProb gamma gamma'
            (BeffaraDC.selfDualPoint q) q rho) =
        ∑ rho : source,
          rlc_twoChannelForcedDualProb gamma gamma'
            (BeffaraDC.selfDualPoint q) q rho.1 := by
      calc
        _ = ∑ rho ∈ Finset.univ.filter (fun rho => rho ∉ A),
            rlc_twoChannelForcedDualProb gamma gamma'
              (BeffaraDC.selfDualPoint q) q rho := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro rho _
          by_cases hrho : rho ∈ A <;> simp [hrho]
        _ = _ := Finset.sum_subtype
          (Finset.univ.filter (fun rho => rho ∉ A))
            (by intro rho; simp only [Finset.mem_filter, Finset.mem_univ,
              true_and]) (fun rho =>
            rlc_twoChannelForcedDualProb gamma gamma'
              (BeffaraDC.selfDualPoint q) q rho)
    _ ≤ ∑ rho : source,
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q (D rho) := by
      exact Finset.sum_le_sum fun rho _ => hprob rho
    _ = ∑ eta : range,
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q eta.1 := by
      exact Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = ∑ eta ∈ Finset.univ.filter (fun eta => eta ∈ range),
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q eta :=
      (Finset.sum_subtype
        (Finset.univ.filter (fun eta => eta ∈ range))
          (by
            intro eta
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            change eta ∈ Set.range D ↔ eta ∈ Set.range D
            rfl) (fun eta =>
          FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (BeffaraDC.selfDualPoint q) q eta)).symm
    _ ≤ ∑ eta ∈ Finset.univ.filter (fun eta => eta ∈ A),
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q eta := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro eta heta
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heta ⊢
        exact hrange heta
      · intro eta _ _
        exact FK.bcProb_nonneg (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma') hp hp1 hq0 eta
    _ = ∑ eta : {eta : ConfigSpace (Sym2 (RlcConnectorVertex n)) // eta ∈ A},
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q eta.1 :=
      Finset.sum_subtype
        (Finset.univ.filter (fun eta => eta ∈ A))
          (by intro eta; simp only [Finset.mem_filter, Finset.mem_univ,
            true_and]) (fun eta =>
          FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (BeffaraDC.selfDualPoint q) q eta)
    _ = ∑ eta : ConfigSpace (Sym2 (RlcConnectorVertex n)),
        A.indicator (fun _ => (1 : Real)) eta *
          FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (BeffaraDC.selfDualPoint q) q eta := by
      rw [← Finset.sum_subtype
        (Finset.univ.filter (fun eta => eta ∈ A))
          (by intro eta; simp only [Finset.mem_filter, Finset.mem_univ,
            true_and]) (fun eta =>
          FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (BeffaraDC.selfDualPoint q) q eta), Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro eta _
      by_cases heta : eta ∈ A <;> simp [heta]


theorem
    rlc_twoChannelForcedDualEventMass_compl_le_mul_merged_of_injection
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q distortion : Real} (hq : 1 ≤ q) (hdistortion : 0 ≤ distortion)
    (D : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
        rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} →
      ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hinj : Function.Injective D)
    (hsuccess : ∀ rho,
      D rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hprob : ∀ rho,
      rlc_twoChannelForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q rho.1 ≤
        distortion *
          FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (BeffaraDC.selfDualPoint q) q (D rho)) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ ≤
      distortion *
        FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  classical
  let A := rlc_finiteTwoChannelConnectorEvent gamma gamma'
  let source := {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) // rho ∉ A}
  let targetWeight := fun eta : ConfigSpace (Sym2 (RlcConnectorVertex n)) =>
    A.indicator (fun eta =>
      FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q eta) eta
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  have hsum := Fintype.sum_le_mul_sum_of_injective
    D hinj
    (fun rho : source =>
      rlc_twoChannelForcedDualProb gamma gamma'
        (BeffaraDC.selfDualPoint q) q rho.1)
    targetWeight distortion hdistortion
    (fun eta => by
      by_cases heta : eta ∈ A
      · simp only [targetWeight, Set.indicator_of_mem heta]
        exact FK.bcProb_nonneg
          (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma') hp hp1 hq0 eta
      · simp [targetWeight, heta])
    (fun rho => by
      have htargetD : targetWeight (D rho) =
          FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (BeffaraDC.selfDualPoint q) q (D rho) := by
        have hDA : D rho ∈ A := hsuccess rho
        simp [targetWeight, hDA]
      rw [htargetD]
      exact hprob rho)
  unfold rlc_twoChannelForcedDualEventMass FK.bcEventMass
  calc
    (∑ rho : ConfigSpace (Sym2 (RlcConnectorVertex n)),
        Aᶜ.indicator (fun _ => (1 : Real)) rho *
          rlc_twoChannelForcedDualProb gamma gamma'
            (BeffaraDC.selfDualPoint q) q rho) =
        ∑ rho : source,
          rlc_twoChannelForcedDualProb gamma gamma'
            (BeffaraDC.selfDualPoint q) q rho.1 := by
      calc
        _ = ∑ rho ∈ Finset.univ.filter (fun rho => rho ∉ A),
            rlc_twoChannelForcedDualProb gamma gamma'
              (BeffaraDC.selfDualPoint q) q rho := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro rho _
          by_cases hrho : rho ∈ A <;> simp [hrho]
        _ = _ := Finset.sum_subtype
          (Finset.univ.filter (fun rho => rho ∉ A))
            (by
              intro rho
              simp only [Finset.mem_filter, Finset.mem_univ, true_and])
            (fun rho => rlc_twoChannelForcedDualProb gamma gamma'
              (BeffaraDC.selfDualPoint q) q rho)
    _ ≤ distortion * ∑ eta, targetWeight eta := hsum
    _ = distortion *
        ∑ eta : ConfigSpace (Sym2 (RlcConnectorVertex n)),
          A.indicator (fun _ => (1 : Real)) eta *
            FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
              (rlc_connectorMergedWiring gamma gamma')
              (BeffaraDC.selfDualPoint q) q eta := by
      congr 1
      apply Finset.sum_congr rfl
      intro eta _
      by_cases heta : eta ∈ A <;> simp [targetWeight, heta]


end
end StatMech.Universality
