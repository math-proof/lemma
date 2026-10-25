/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Theorem.StatisticalMechanics.Code.Foundations.WeightedFiniteInjection
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannel.Part5
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelForcedDualProb_nonneg {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    0 ≤ rlc_twoChannelForcedDualProb gamma gamma' p q rho := by
  unfold rlc_twoChannelForcedDualProb
  exact div_nonneg
    (le_of_lt (BeffaraDC.pfd_dualWeight_pos
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
      (FK.openSub
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' rho)) hp hp1 hq))
    (le_of_lt (rlc_twoChannelForcedDualZ_pos
      gamma gamma' hp hp1 hq))


theorem rlc_bcProb_half_q_one_uniform {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C D : SimpleGraph V) [DecidableRel C.Adj] [DecidableRel D.Adj]
    (rho eta : ConfigSpace (Sym2 V)) :
    FK.bcProb G C (1 / 2 : Real) 1 rho =
      FK.bcProb G D (1 / 2 : Real) 1 eta := by
  classical
  unfold FK.bcProb FK.bcZ FK.bcWeight FK.edgeProduct
  simp only [one_pow, mul_one]
  have huniform (omega : ConfigSpace (Sym2 V)) :
      (∏ e ∈ G.edgeFinset,
        if omega e = true then (1 / 2 : Real) else 1 - 1 / 2) =
      (1 / 2 : Real) ^ G.edgeFinset.card := by
    calc
      _ = ∏ _e ∈ G.edgeFinset, (1 / 2 : Real) := by
        apply Finset.prod_congr rfl
        intro e _
        split <;> norm_num
      _ = _ := by simp
  simp_rw [huniform]


theorem rlc_twoChannelForcedDualProb_half_q_one_eq_merged {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho eta : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_twoChannelForcedDualProb gamma gamma' (1 / 2) 1 rho =
      FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1 eta := by
  have hdual := rlc_twoChannel_bcProb_separate_eq_forcedDualProb
    gamma gamma' rho (p := (1 / 2 : Real)) (q := (1 : Real))
      (by norm_num) (by norm_num) (by norm_num)
  norm_num [BeffaraDC.dualParam] at hdual
  rw [← hdual]
  exact rlc_bcProb_half_q_one_uniform
    (rlc_connectorTwoChannelGraph gamma gamma')
    (rlc_connectorSeparateWiring gamma gamma')
    (rlc_connectorMergedWiring gamma gamma') rho eta


theorem rlc_twoChannelForcedDualSingletonMass_le_merged_of_mem {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho eta : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (heta : eta ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    rlc_twoChannelForcedDualEventMass gamma gamma' (1 / 2) 1 {rho} ≤
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  classical
  unfold rlc_twoChannelForcedDualEventMass FK.bcEventMass
  calc
    (∑ omega : ConfigSpace (Sym2 (RlcConnectorVertex n)),
        ({rho} : Set (ConfigSpace (Sym2 (RlcConnectorVertex n)))).indicator
          (fun _ => (1 : Real)) omega *
          rlc_twoChannelForcedDualProb gamma gamma' (1 / 2) 1 omega) =
      rlc_twoChannelForcedDualProb gamma gamma' (1 / 2) 1 rho := by
        rw [Finset.sum_eq_single rho]
        · simp
        · intro omega _ hne
          simp [hne]
        · simp
    _ = FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1 eta :=
      rlc_twoChannelForcedDualProb_half_q_one_eq_merged
        gamma gamma' rho eta
    _ ≤ ∑ omega : ConfigSpace (Sym2 (RlcConnectorVertex n)),
        (rlc_finiteTwoChannelConnectorEvent gamma gamma').indicator
          (fun _ => (1 : Real)) omega *
          FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1 omega := by
      have hle := Finset.single_le_sum (s := Finset.univ)
        (f := fun omega : ConfigSpace (Sym2 (RlcConnectorVertex n)) =>
          (rlc_finiteTwoChannelConnectorEvent gamma gamma').indicator
            (fun _ => (1 : Real)) omega *
            FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
              (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1 omega)
        (fun omega _ => mul_nonneg
          (Set.indicator_nonneg (fun _ _ => zero_le_one) omega)
          (FK.bcProb_nonneg (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma') (by norm_num)
              (by norm_num) (by norm_num) omega))
        (Finset.mem_univ eta)
      simpa [heta] using hle

theorem rlc_twoChannel_bcEventMass_separate_eq_forcedDualEventMass {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (A : Set (ConfigSpace (Sym2 (RlcConnectorVertex n))))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q A =
      rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.dualParam p q) q A := by
  unfold FK.bcEventMass rlc_twoChannelForcedDualEventMass
  apply Finset.sum_congr rfl
  intro rho _
  rw [rlc_twoChannel_bcProb_separate_eq_forcedDualProb
    gamma gamma' rho hp hp1 hq]

theorem rlc_twoChannel_bcEventMass_separate_selfDual_eq_forcedDualEventMass
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A : Set (ConfigSpace (Sym2 (RlcConnectorVertex n))))
    {q : Real} (hq : 0 < q) :
    FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q A =
      rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q A := by
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq
  simpa only [BeffaraDC.selfDualPoint_is_fixed hq] using
    rlc_twoChannel_bcEventMass_separate_eq_forcedDualEventMass
      gamma gamma' A hp hp1 hq

theorem rlc_twoChannel_bcProb_separate_selfDual_eq_forcedDualProb
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {q : Real} (hq : 0 < q) :
    FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q rho =
      rlc_twoChannelForcedDualProb gamma gamma'
        (BeffaraDC.selfDualPoint q) q rho := by
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq
  simpa only [BeffaraDC.selfDualPoint_is_fixed hq] using
    rlc_twoChannel_bcProb_separate_eq_forcedDualProb
      gamma gamma' rho hp hp1 hq


theorem rlc_finiteCentralFaceClosureConnectorEvent_subset_twoChannel
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' ⊆
      rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
  intro rho hclosure
  have hanchorsClosure :
      (FK.openSub (rlc_connectorCentralFaceClosureGraph gamma gamma') rho ⊔
        rlc_connectorTraceWiring gamma gamma').Reachable
          (rlc_connectorRightAnchor gamma)
          (rlc_connectorLeftAnchor gamma') :=
    (rlc_exists_connector_iff_traceAnchors gamma gamma'
      (FK.openSub (rlc_connectorCentralFaceClosureGraph gamma gamma') rho)).1
        hclosure
  have hopenLe :
      FK.openSub (rlc_connectorCentralFaceClosureGraph gamma gamma') rho ≤
        FK.openSub (rlc_connectorTwoChannelGraph gamma gamma') rho ⊔
          rlc_connectorTraceWiring gamma gamma' := by
    intro x y hxy
    rw [FK.openSub_adj] at hxy
    rw [rlc_connectorCentralFaceClosureGraph_eq_twoChannel_sup_trace]
      at hxy
    rcases hxy.1 with htwo | htrace
    · exact Or.inl ⟨htwo, hxy.2⟩
    · exact Or.inr htrace
  have hanchorsTwo :
      (FK.openSub (rlc_connectorTwoChannelGraph gamma gamma') rho ⊔
        rlc_connectorTraceWiring gamma gamma').Reachable
          (rlc_connectorRightAnchor gamma)
          (rlc_connectorLeftAnchor gamma') :=
    hanchorsClosure.mono <| sup_le hopenLe le_sup_right
  exact (rlc_exists_connector_iff_traceAnchors gamma gamma'
    (FK.openSub (rlc_connectorTwoChannelGraph gamma gamma') rho)).2
      hanchorsTwo


theorem rlc_centralFacePIMS_twoChannel_success_of_closure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hclosure : rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
      rlc_finiteCentralFaceClosureConnectorEvent gamma gamma') :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
      rlc_finiteTwoChannelConnectorEvent gamma gamma' :=
  rlc_finiteCentralFaceClosureConnectorEvent_subset_twoChannel
    gamma gamma' hclosure


end
end StatMech.Universality
