/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalTraceContact
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Theorem.StatisticalMechanics.Code.FK.WeightedParameterMonotoneClosed
import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part97
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorPIMSVariableExteriorEvent_iff_wired {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rho ∈ rlc_connectorPIMSVariableExteriorEvent gamma gamma' ↔
      rho ∈ rlc_connectorPIMSVariableWiredEvent gamma gamma' := by
  constructor <;> rintro ⟨x, y, hx, hy, hxy⟩
  · exact ⟨x, y, hx, hy,
      (rlc_connectorPIMSExterior_sup_reachable_iff_wiring
        gamma gamma' _ x y).mp hxy⟩
  · exact ⟨x, y, hx, hy,
      (rlc_connectorPIMSExterior_sup_reachable_iff_wiring
        gamma gamma' _ x y).mpr hxy⟩


theorem rlc_connectorPIMSVariableExteriorEvent_iff_assemble {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rho ∈ rlc_connectorPIMSVariableExteriorEvent gamma gamma' ↔
      rlc_connectorPIMSAssembleConfig gamma gamma' rho ∈
        rlc_finiteConnectorEvent gamma gamma' := by
  unfold rlc_connectorPIMSVariableExteriorEvent rlc_finiteConnectorEvent
  simp only [Set.mem_setOf_eq]
  rw [rlc_openSub_PIMSAssembleConfig]


theorem rlc_PIMS_mem_finiteConnectorEvent_iff_variableExterior {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorPIMSReflectedConfig gamma gamma' tau ∈
        rlc_finiteConnectorEvent gamma gamma' ↔
      rlc_connectorPIMSReflectedConfig gamma gamma' tau ∈
        rlc_connectorPIMSVariableExteriorEvent gamma gamma' := by
  unfold rlc_finiteConnectorEvent rlc_connectorPIMSVariableExteriorEvent
  simp only [Set.mem_setOf_eq]
  rw [rlc_openSub_PIMS_eq_variable_sup_exterior]


theorem rlc_connectorPIMSVariableExteriorEvent_isIncreasing {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    IsIncreasing (rlc_connectorPIMSVariableExteriorEvent gamma gamma') := by
  intro rho sigma hrs
  rintro ⟨x, y, hx, hy, hxy⟩
  refine ⟨x, y, hx, hy, hxy.mono ?_⟩
  intro u v huv
  rw [SimpleGraph.sup_adj, FK.openSub_adj] at huv ⊢
  rcases huv with ⟨hvar, hopen⟩ | hext
  · exact Or.inl ⟨hvar, hrs _ hopen⟩
  · exact Or.inr hext

theorem rlc_connectorPIMSVariableWiredEvent_isIncreasing {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    IsIncreasing (rlc_connectorPIMSVariableWiredEvent gamma gamma') := by
  intro rho sigma hrs hrho
  rw [← rlc_connectorPIMSVariableExteriorEvent_iff_wired] at hrho ⊢
  exact rlc_connectorPIMSVariableExteriorEvent_isIncreasing
    gamma gamma' hrs hrho


theorem rlc_connectorPIMSReflectedConfig_mem_event_of_reflectedDual
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hdual : rlc_connectorReflectedDualConfig gamma gamma' tau ∈
      rlc_finiteConnectorEvent gamma gamma') :
    rlc_connectorPIMSReflectedConfig gamma gamma' tau ∈
      rlc_finiteConnectorEvent gamma gamma' :=
  rlc_finiteConnectorEvent_isIncreasing gamma gamma'
    (rlc_connectorReflectedDualConfig_le_PIMS gamma gamma' tau) hdual


theorem rlc_connectorForcedDualEventMass_reflected_le_PIMS {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    rlc_connectorForcedDualEventMass gamma gamma' p q
        (rlc_connectorReflectedDualConfig gamma gamma' ⁻¹'
          rlc_finiteConnectorEvent gamma gamma') <=
      rlc_connectorForcedDualEventMass gamma gamma' p q
        (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
          rlc_finiteConnectorEvent gamma gamma') := by
  apply rlc_connectorForcedDualEventMass_mono gamma gamma' hp hp1 hq
  intro tau htau
  exact rlc_connectorPIMSReflectedConfig_mem_event_of_reflectedDual
    gamma gamma' tau htau


theorem rlc_connectorPIMSCollaredReflectedConfig_mem_event_of_reflectedDual
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hdual : rlc_connectorReflectedDualConfig gamma gamma' tau ∈
      rlc_finiteConnectorEvent gamma gamma') :
    rlc_connectorPIMSCollaredReflectedConfig gamma gamma' tau ∈
      rlc_finiteConnectorEvent gamma gamma' :=
  rlc_finiteConnectorEvent_isIncreasing gamma gamma'
    (rlc_connectorReflectedDualConfig_le_PIMSCollared
      gamma gamma' tau) hdual


theorem rlc_connectorForcedDualEventMass_reflected_le_PIMSCollared
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    rlc_connectorForcedDualEventMass gamma gamma' p q
        (rlc_connectorReflectedDualConfig gamma gamma' ⁻¹'
          rlc_finiteConnectorEvent gamma gamma') <=
      rlc_connectorForcedDualEventMass gamma gamma' p q
        (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' ⁻¹'
          rlc_finiteConnectorEvent gamma gamma') := by
  apply rlc_connectorForcedDualEventMass_mono gamma gamma' hp hp1 hq
  intro tau htau
  exact
    rlc_connectorPIMSCollaredReflectedConfig_mem_event_of_reflectedDual
      gamma gamma' tau htau


theorem rlc_connectorPIMS_pushforward_le_merged_of_inducedWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (C : SimpleGraph (RlcConnectorVertex n)) [DecidableRel C.Adj]
    (hC : C <= rlc_connectorMergedWiring gamma gamma')
    (hpush :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') =
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') C
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')) :
    rlc_connectorForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
          rlc_finiteConnectorEvent gamma gamma') <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  rw [hpush]
  exact FK.bcProb_mono_bc
    (rlc_connectorFiniteGraph gamma gamma') C
    (rlc_connectorMergedWiring gamma gamma') hC hp hp1 hq
    (rlc_finiteConnectorEvent_isIncreasing gamma gamma')


theorem rlc_connectorPIMS_pushforward_le_merged_of_inducedMixture
    {n : Int} {I : Type*} [Fintype I] [DecidableEq I]
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (w : I → Real) (C : I → SimpleGraph (RlcConnectorVertex n))
    [∀ i, DecidableRel (C i).Adj]
    (hw : ∀ i, 0 <= w i) (hwSum : ∑ i, w i = 1)
    (hC : ∀ i, C i <= rlc_connectorMergedWiring gamma gamma')
    (hpush :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') =
        ∑ i, w i *
          FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (C i)
            (BeffaraDC.selfDualPoint q) q
            (rlc_finiteConnectorEvent gamma gamma')) :
    rlc_connectorForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
          rlc_finiteConnectorEvent gamma gamma') <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  rw [hpush]
  calc
    (∑ i, w i *
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (C i)
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')) <=
        ∑ i, w i *
          FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (BeffaraDC.selfDualPoint q) q
            (rlc_finiteConnectorEvent gamma gamma') := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      exact FK.bcProb_mono_bc
        (rlc_connectorFiniteGraph gamma gamma') (C i)
        (rlc_connectorMergedWiring gamma gamma') (hC i) hp hp1 hq
        (rlc_finiteConnectorEvent_isIncreasing gamma gamma')
    _ = FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma') := by
      rw [← Finset.sum_mul, hwSum, one_mul]


theorem rlc_connectorPIMS_pushforward_le_merged_of_weightedMixture
    {n : Int} {I : Type*} [Fintype I] [DecidableEq I]
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (w : I → Real) (C : I → SimpleGraph (RlcConnectorVertex n))
    [∀ i, DecidableRel (C i).Adj]
    (pf : I → Sym2 (RlcConnectorVertex n) → Real)
    (hw : ∀ i, 0 <= w i) (hwSum : ∑ i, w i = 1)
    (hC : ∀ i, C i <= rlc_connectorMergedWiring gamma gamma')
    (hpf0 : ∀ i e, 0 <= pf i e)
    (hpf1 : ∀ i e, pf i e < 1)
    (hpfle : ∀ i e, pf i e <= BeffaraDC.selfDualPoint q)
    (hpush :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') =
        ∑ i, w i *
          (∑ omega,
            (rlc_finiteConnectorEvent gamma gamma').indicator
                (fun _ => (1 : Real)) omega *
              FK.bcProbW (rlc_connectorFiniteGraph gamma gamma')
                (C i) (pf i) q omega)) :
    rlc_connectorForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
          rlc_finiteConnectorEvent gamma gamma') <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  rw [hpush]
  let target := FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
    (rlc_connectorMergedWiring gamma gamma')
    (BeffaraDC.selfDualPoint q) q
    (rlc_finiteConnectorEvent gamma gamma')
  calc
    (∑ i, w i *
        (∑ omega,
          (rlc_finiteConnectorEvent gamma gamma').indicator
              (fun _ => (1 : Real)) omega *
            FK.bcProbW (rlc_connectorFiniteGraph gamma gamma')
              (C i) (pf i) q omega)) <=
        ∑ i, w i * target := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      have hparam := FK.bcProbW_mono_params_of_nonneg
        (rlc_connectorFiniteGraph gamma gamma') (C i)
        (hpf0 i) (hpf1 i) (fun _ => hp.le) (fun _ => hp1)
        (hpfle i) hq (rlc_finiteConnectorEvent_isIncreasing gamma gamma')
      have hboundary := FK.bcProbW_mono_bc
        (rlc_connectorFiniteGraph gamma gamma') (C i)
        (rlc_connectorMergedWiring gamma gamma') (hC i)
        (fun _ => hp) (fun _ => hp1) hq
        (rlc_finiteConnectorEvent_isIncreasing gamma gamma')
      exact hparam.trans (by
        simpa only [FK.bcProbW_const, FK.bcEventMass, target]
          using hboundary)
    _ = target := by rw [← Finset.sum_mul, hwSum, one_mul]


theorem rlc_connectorPIMSCollared_pushforward_le_merged_of_weightedMixture
    {n : Int} {I : Type*} [Fintype I] [DecidableEq I]
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (w : I → Real) (C : I → SimpleGraph (RlcConnectorVertex n))
    [∀ i, DecidableRel (C i).Adj]
    (hw : ∀ i, 0 <= w i) (hwSum : ∑ i, w i = 1)
    (hC : ∀ i, C i <= rlc_connectorMergedWiring gamma gamma')
    (hpush :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') =
        ∑ i, w i *
          (∑ omega,
            (rlc_finiteConnectorEvent gamma gamma').indicator
                (fun _ => (1 : Real)) omega *
              FK.bcProbW (rlc_connectorFiniteGraph gamma gamma')
                (C i)
                (rlc_connectorPIMSCollaredParameter gamma gamma'
                  (BeffaraDC.selfDualPoint q)) q omega)) :
    rlc_connectorForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' ⁻¹'
          rlc_finiteConnectorEvent gamma gamma') <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  have hpf0 : ∀ e, 0 <=
      rlc_connectorPIMSCollaredParameter gamma gamma'
        (BeffaraDC.selfDualPoint q) e := by
    intro e
    by_cases he : rlc_pimsEdgeEquiv (e.map Subtype.val) ∈
        rlc_connectorEdges gamma gamma'
    · rw [rlc_connectorPIMSCollaredParameter_of_preimage_connector
        gamma gamma' _ e he]
      exact hp.le
    · rw [rlc_connectorPIMSCollaredParameter_of_preimage_exterior
        gamma gamma' _ e he]
  have hpf1 : ∀ e,
      rlc_connectorPIMSCollaredParameter gamma gamma'
          (BeffaraDC.selfDualPoint q) e < 1 := by
    intro e
    by_cases he : rlc_pimsEdgeEquiv (e.map Subtype.val) ∈
        rlc_connectorEdges gamma gamma'
    · rw [rlc_connectorPIMSCollaredParameter_of_preimage_connector
        gamma gamma' _ e he]
      exact hp1
    · rw [rlc_connectorPIMSCollaredParameter_of_preimage_exterior
        gamma gamma' _ e he]
      exact zero_lt_one
  have hpfle : ∀ e,
      rlc_connectorPIMSCollaredParameter gamma gamma'
          (BeffaraDC.selfDualPoint q) e <=
        BeffaraDC.selfDualPoint q := by
    intro e
    by_cases he : rlc_pimsEdgeEquiv (e.map Subtype.val) ∈
        rlc_connectorEdges gamma gamma'
    · rw [rlc_connectorPIMSCollaredParameter_of_preimage_connector
        gamma gamma' _ e he]
    · rw [rlc_connectorPIMSCollaredParameter_of_preimage_exterior
        gamma gamma' _ e he]
      exact hp.le
  rw [hpush]
  let target := FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
    (rlc_connectorMergedWiring gamma gamma')
    (BeffaraDC.selfDualPoint q) q
    (rlc_finiteConnectorEvent gamma gamma')
  calc
    (∑ i, w i *
        (∑ omega,
          (rlc_finiteConnectorEvent gamma gamma').indicator
              (fun _ => (1 : Real)) omega *
            FK.bcProbW (rlc_connectorFiniteGraph gamma gamma')
              (C i)
              (rlc_connectorPIMSCollaredParameter gamma gamma'
                (BeffaraDC.selfDualPoint q)) q omega)) <=
        ∑ i, w i * target := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      have hparam := FK.bcProbW_mono_params_of_nonneg
        (rlc_connectorFiniteGraph gamma gamma') (C i)
        hpf0 hpf1 (fun _ => hp.le) (fun _ => hp1) hpfle hq
        (rlc_finiteConnectorEvent_isIncreasing gamma gamma')
      have hboundary := FK.bcProbW_mono_bc
        (rlc_connectorFiniteGraph gamma gamma') (C i)
        (rlc_connectorMergedWiring gamma gamma') (hC i)
        (fun _ => hp) (fun _ => hp1) hq
        (rlc_finiteConnectorEvent_isIncreasing gamma gamma')
      exact hparam.trans (by
        simpa only [FK.bcProbW_const, FK.bcEventMass, target]
          using hboundary)
    _ = target := by rw [← Finset.sum_mul, hwSum, one_mul]


theorem
    rlc_connectorPIMSCollared_pushforward_le_merged_of_componentMixture
    {n : Int} {I : Type*} [Fintype I] [DecidableEq I]
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (w : I → Real)
    (tauExt : I → ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hw : ∀ i, 0 <= w i) (hwSum : ∑ i, w i = 1)
    (hpush :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') =
        ∑ i, w i *
          (∑ omega,
            (rlc_finiteConnectorEvent gamma gamma').indicator
                (fun _ => (1 : Real)) omega *
              FK.bcProbW (rlc_connectorFiniteGraph gamma gamma')
                (rlc_connectorComponentWiring
                  (rlc_connectorPIMSCollaredExteriorOpenGraph
                    gamma gamma' (tauExt i)))
                (rlc_connectorPIMSCollaredParameter gamma gamma'
                  (BeffaraDC.selfDualPoint q)) q omega)) :
    rlc_connectorForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' ⁻¹'
          rlc_finiteConnectorEvent gamma gamma') <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  exact
    rlc_connectorPIMSCollared_pushforward_le_merged_of_weightedMixture
      gamma gamma' hq w
      (fun i => rlc_connectorComponentWiring
        (rlc_connectorPIMSCollaredExteriorOpenGraph
          gamma gamma' (tauExt i)))
      hw hwSum
      (fun i => rlc_connectorPIMSCollaredInducedWiring_le_merged
        gamma gamma' (tauExt i)) hpush


theorem rlc_finiteConnectorEvent_iff_traceAnchors {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    tau ∈ rlc_finiteConnectorEvent gamma gamma' ↔
      (FK.openSub (rlc_connectorFiniteGraph gamma gamma') tau ⊔
        rlc_connectorTraceWiring gamma gamma').Reachable
          (rlc_connectorRightAnchor gamma)
          (rlc_connectorLeftAnchor gamma') := by
  let H := FK.openSub (rlc_connectorFiniteGraph gamma gamma') tau
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    have hright := (rlc_connectorTraceWiring_reachable_right gamma gamma'
      (rlc_connectorRightAnchor_onRight gamma) hx).mono
        (show rlc_connectorTraceWiring gamma gamma' ≤
          H ⊔ rlc_connectorTraceWiring gamma gamma' from le_sup_right)
    have hmiddle : (H ⊔ rlc_connectorTraceWiring gamma gamma').Reachable x y :=
      hxy.mono le_sup_left
    have hleft := (rlc_connectorTraceWiring_reachable_left gamma gamma'
      hy (rlc_connectorLeftAnchor_onLeft gamma')).mono
        (show rlc_connectorTraceWiring gamma gamma' ≤
          H ⊔ rlc_connectorTraceWiring gamma gamma' from le_sup_right)
    exact hright.trans (hmiddle.trans hleft)
  · intro hanchors
    by_contra hno
    have hpropagate : ∀ {u v : RlcConnectorVertex n},
        (H ⊔ rlc_connectorSeparateWiring gamma gamma').Walk u v →
        (∃ x, rlc_connectorOnRight gamma x ∧ H.Reachable x u) →
        ∃ x, rlc_connectorOnRight gamma x ∧ H.Reachable x v := by
      intro u v w
      induction w with
      | nil => exact fun hu => hu
      | @cons u v z huv w ih =>
          intro hu
          apply ih
          rcases huv with hH | hsep
          · obtain ⟨x, hx, hxu⟩ := hu
            exact ⟨x, hx, hxu.trans hH.reachable⟩
          · rw [rlc_connectorSeparateWiring, SimpleGraph.sup_adj] at hsep
            rcases hsep with hright | hleft
            · rw [Lattice.boundaryCliqueGraph_adj] at hright
              exact ⟨v, hright.2.2, Reachable.refl _⟩
            · rw [Lattice.boundaryCliqueGraph_adj] at hleft
              obtain ⟨x, hx, hxu⟩ := hu
              exact False.elim (hno ⟨x, u, hx, hleft.2.1, hxu⟩)
    have hanchorsSeparate :
        (H ⊔ rlc_connectorSeparateWiring gamma gamma').Reachable
          (rlc_connectorRightAnchor gamma)
          (rlc_connectorLeftAnchor gamma') :=
      (rlc_connectorTraceWiring_reachable_iff_separateWiring gamma gamma' H
        (rlc_connectorRightAnchor gamma)
        (rlc_connectorLeftAnchor gamma')).mp hanchors
    obtain ⟨w⟩ := hanchorsSeparate
    obtain ⟨x, hx, hxleft⟩ := hpropagate w
      ⟨rlc_connectorRightAnchor gamma,
        rlc_connectorRightAnchor_onRight gamma, Reachable.refl _⟩
    exact hno ⟨x, rlc_connectorLeftAnchor gamma', hx,
      rlc_connectorLeftAnchor_onLeft gamma', hxleft⟩


theorem rlc_connectorPIMSVariableExteriorEvent_iff_variable_of_exterior_le
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hext : rlc_connectorPIMSExteriorGraph gamma gamma' ≤
      rlc_connectorSeparateWiring gamma gamma') :
    rho ∈ rlc_connectorPIMSVariableExteriorEvent gamma gamma' ↔
      rlc_connectorPIMSVariableConfig gamma gamma' rho ∈
        rlc_finiteConnectorEvent gamma gamma' := by
  let H := FK.openSub (rlc_connectorPIMSVariableGraph gamma gamma') rho
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    have hxySeparate :
        (H ⊔ rlc_connectorSeparateWiring gamma gamma').Reachable x y :=
      hxy.mono (sup_le_sup_left hext H)
    have hxyTrace :
        (H ⊔ rlc_connectorTraceWiring gamma gamma').Reachable x y :=
      (rlc_connectorTraceWiring_reachable_iff_separateWiring
        gamma gamma' H x y).mpr hxySeparate
    have hright :
        (H ⊔ rlc_connectorTraceWiring gamma gamma').Reachable
          (rlc_connectorRightAnchor gamma) x :=
      (rlc_connectorTraceWiring_reachable_right gamma gamma'
        (rlc_connectorRightAnchor_onRight gamma) hx).mono le_sup_right
    have hleft :
        (H ⊔ rlc_connectorTraceWiring gamma gamma').Reachable y
          (rlc_connectorLeftAnchor gamma') :=
      (rlc_connectorTraceWiring_reachable_left gamma gamma' hy
        (rlc_connectorLeftAnchor_onLeft gamma')).mono le_sup_right
    rw [rlc_finiteConnectorEvent_iff_traceAnchors,
      rlc_openSub_PIMSVariableConfig]
    exact hright.trans (hxyTrace.trans hleft)
  · intro hrho
    obtain ⟨x, y, hx, hy, hxy⟩ := hrho
    rw [rlc_openSub_PIMSVariableConfig] at hxy
    exact ⟨x, y, hx, hy, hxy.mono le_sup_left⟩


theorem rlc_connectorPIMSVariableExteriorEvent_iff_variable_of_wiring_le
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hwire : rlc_connectorPIMSExteriorWiring gamma gamma' ≤
      rlc_connectorSeparateWiring gamma gamma') :
    rho ∈ rlc_connectorPIMSVariableExteriorEvent gamma gamma' ↔
      rlc_connectorPIMSVariableConfig gamma gamma' rho ∈
        rlc_finiteConnectorEvent gamma gamma' := by
  apply rlc_connectorPIMSVariableExteriorEvent_iff_variable_of_exterior_le
  intro x y hxy
  exact hwire ⟨hxy.ne, hxy.reachable⟩


theorem rlc_connectorPIMSVariableExteriorEvent_iff_variable_of_traceLocal
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hlocal : RlcConnectorPIMSExteriorTraceLocal gamma gamma') :
    rho ∈ rlc_connectorPIMSVariableExteriorEvent gamma gamma' ↔
      rlc_connectorPIMSVariableConfig gamma gamma' rho ∈
        rlc_finiteConnectorEvent gamma gamma' :=
  rlc_connectorPIMSVariableExteriorEvent_iff_variable_of_exterior_le
    gamma gamma' rho
      ((rlc_connectorPIMSExteriorTraceLocal_iff_le_separateWiring
        gamma gamma').mp hlocal)


theorem rlc_PIMS_mem_finiteConnectorEvent_iff_variable_of_traceLocal
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hlocal : RlcConnectorPIMSExteriorTraceLocal gamma gamma') :
    rlc_connectorPIMSReflectedConfig gamma gamma' tau ∈
        rlc_finiteConnectorEvent gamma gamma' ↔
      rlc_connectorPIMSVariableConfig gamma gamma'
          (rlc_connectorPIMSReflectedConfig gamma gamma' tau) ∈
        rlc_finiteConnectorEvent gamma gamma' := by
  rw [rlc_PIMS_mem_finiteConnectorEvent_iff_variableExterior]
  exact rlc_connectorPIMSVariableExteriorEvent_iff_variable_of_traceLocal
    gamma gamma' _ hlocal


theorem rlc_PIMS_mem_finiteConnectorEvent_iff_variable_of_extremalSelection
    {n : Int}
    (hselection : RlcConnectorPIMSExtremalSelectionExteriorLocality n)
    (pair : RlcDiagonalPathPair n)
    {omega : ConfigSpace (Sym2 (Site 2))}
    (hpair : omega ∈ rlc_extremalPairCandidate pair)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorPIMSReflectedConfig pair.1 pair.2 tau ∈
        rlc_finiteConnectorEvent pair.1 pair.2 ↔
      rlc_connectorPIMSVariableConfig pair.1 pair.2
          (rlc_connectorPIMSReflectedConfig pair.1 pair.2 tau) ∈
        rlc_finiteConnectorEvent pair.1 pair.2 :=
  rlc_PIMS_mem_finiteConnectorEvent_iff_variable_of_traceLocal
    pair.1 pair.2 tau (hselection pair ⟨omega, hpair⟩)


theorem rlc_finiteConnectorEvent_iff_augmented_forceTrace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    tau ∈ rlc_finiteConnectorEvent gamma gamma' ↔
      (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' tau)).Reachable
          (rlc_connectorRightAnchor gamma)
          (rlc_connectorLeftAnchor gamma') := by
  rw [rlc_openSub_augmented_forceTrace]
  exact rlc_finiteConnectorEvent_iff_traceAnchors gamma gamma' tau


theorem rlc_finiteConnectorMass_ge_one_div_one_add_q {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (hdual :
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') p q
          (rlc_finiteConnectorEvent gamma gamma')ᶜ <=
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma') p q
          (rlc_finiteConnectorEvent gamma gamma')) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q
        (rlc_finiteConnectorEvent gamma gamma') := by
  apply FrontierD.bcEventMass_ge_one_div_one_add_q_of_compl_le_sup_edge
    (rlc_connectorFiniteGraph gamma gamma')
    (rlc_connectorSeparateWiring gamma gamma')
    (rlc_connectorRightAnchor gamma) (rlc_connectorLeftAnchor gamma')
    hp hp1 hq (rlc_finiteConnectorEvent gamma gamma')
  simpa only [rlc_connectorMergedWiring] using hdual


theorem rlc_finiteConnectorMass_selfDual_ge_one_div_one_add_q {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (hdual :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')ᶜ <=
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  apply rlc_finiteConnectorMass_ge_one_div_one_add_q
    gamma gamma' hp hp1 hq
  rw [rlc_bcEventMass_separate_selfDual_eq_forcedDualEventMass
    gamma gamma' (rlc_finiteConnectorEvent gamma gamma')ᶜ hq0]
  exact hdual


theorem rlc_finiteConnectorMass_selfDual_ge_of_reflected_equiv {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (D : ConfigSpace (Sym2 (RlcConnectorVertex n)) ≃
      ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hfailure : ∀ tau,
      tau ∉ rlc_finiteConnectorEvent gamma gamma' →
        D tau ∈ rlc_finiteConnectorEvent gamma gamma')
    (hprob : ∀ tau,
      rlc_connectorForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q tau <=
        FK.bcProb (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q (D tau)) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  apply rlc_finiteConnectorMass_selfDual_ge_one_div_one_add_q
    gamma gamma' hq
  exact rlc_connectorForcedDualEventMass_compl_le_merged_of_equiv
    gamma gamma' hq (rlc_finiteConnectorEvent gamma gamma')
      D hfailure hprob


theorem rlc_finiteConnectorMass_selfDual_ge_of_reflected_map_domination
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (F : ConfigSpace (Sym2 (RlcConnectorVertex n)) →
      ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hfailure : ∀ tau,
      tau ∉ rlc_finiteConnectorEvent gamma gamma' →
        F tau ∈ rlc_finiteConnectorEvent gamma gamma')
    (hdom :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (F ⁻¹' rlc_finiteConnectorEvent gamma gamma') <=
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  apply rlc_finiteConnectorMass_selfDual_ge_one_div_one_add_q
    gamma gamma' hq
  apply (rlc_connectorForcedDualEventMass_mono gamma gamma'
    hp hp1 hq0 ?_).trans hdom
  intro tau htau
  exact hfailure tau (by simpa using htau)


theorem rlc_finiteConnectorMass_selfDual_ge_of_reflectedDual_domination
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (hfailure : ∀ tau,
      tau ∉ rlc_finiteConnectorEvent gamma gamma' →
        rlc_connectorReflectedDualConfig gamma gamma' tau ∈
          rlc_finiteConnectorEvent gamma gamma')
    (hdom :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorReflectedDualConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') <=
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  exact rlc_finiteConnectorMass_selfDual_ge_of_reflected_map_domination
    gamma gamma' hq (rlc_connectorReflectedDualConfig gamma gamma')
      hfailure hdom


theorem rlc_finiteConnectorMass_selfDual_ge_of_PIMSReflected_domination
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (hfailure : ∀ tau,
      tau ∉ rlc_finiteConnectorEvent gamma gamma' →
        rlc_connectorPIMSReflectedConfig gamma gamma' tau ∈
          rlc_finiteConnectorEvent gamma gamma')
    (hdom :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') <=
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  exact rlc_finiteConnectorMass_selfDual_ge_of_reflected_map_domination
    gamma gamma' hq (rlc_connectorPIMSReflectedConfig gamma gamma')
      hfailure hdom


theorem rlc_finiteConnectorMass_selfDual_ge_of_PIMSArc_domination
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (harc : ∀ tau,
      tau ∉ rlc_finiteConnectorEvent gamma gamma' →
        RlcConnectorPIMSSupportedArc gamma gamma' tau)
    (hdom :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') <=
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  apply rlc_finiteConnectorMass_selfDual_ge_of_PIMSReflected_domination
    gamma gamma' hq
  · intro tau hno
    exact rlc_connectorPIMSReflectedConfig_mem_event_of_supportedArc
      gamma gamma' tau (harc tau hno)
  · exact hdom


theorem rlc_finiteConnectorMass_selfDual_ge_of_PIMSActualSelectedArc_domination
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (harc : ∀ tau,
      tau ∉ rlc_finiteConnectorEvent gamma gamma' →
        RlcConnectorPIMSActualSelectedArc gamma gamma' tau)
    (hdom :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') <=
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  apply rlc_finiteConnectorMass_selfDual_ge_of_PIMSReflected_domination
    gamma gamma' hq
  · intro tau hno
    exact rlc_connectorPIMSReflectedConfig_mem_event_of_actualSelectedArc
      gamma gamma' tau (harc tau hno)
  · exact hdom


theorem rlc_finiteConnectorMass_selfDual_ge_of_PIMSBoundaryArc_domination
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (harc : ∀ tau,
      tau ∉ rlc_finiteConnectorEvent gamma gamma' →
        RlcConnectorPIMSBoundaryArc gamma gamma' tau)
    (hdom :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') <=
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma')) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  apply rlc_finiteConnectorMass_selfDual_ge_of_PIMSActualSelectedArc_domination
    gamma gamma' hq
  · intro tau hno
    exact rlc_connectorPIMSActualSelectedArc_of_boundaryArc_of_failure
      gamma gamma' tau hno (harc tau hno)
  · exact hdom


theorem rlc_finiteConnectorMass_selfDual_ge_of_PIMSBoundaryArc_inducedWiring
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (C : SimpleGraph (RlcConnectorVertex n)) [DecidableRel C.Adj]
    (hC : C <= rlc_connectorMergedWiring gamma gamma')
    (hpush :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') =
        FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') C
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteConnectorEvent gamma gamma'))
    (harc : ∀ tau,
      tau ∉ rlc_finiteConnectorEvent gamma gamma' →
        RlcConnectorPIMSBoundaryArc gamma gamma' tau) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  apply rlc_finiteConnectorMass_selfDual_ge_of_PIMSBoundaryArc_domination
    gamma gamma' hq harc
  exact rlc_connectorPIMS_pushforward_le_merged_of_inducedWiring
    gamma gamma' hq C hC hpush


theorem rlc_finiteConnectorMass_selfDual_ge_of_PIMSBoundaryArc_inducedMixture
    {n : Int} {I : Type*} [Fintype I] [DecidableEq I]
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (w : I → Real) (C : I → SimpleGraph (RlcConnectorVertex n))
    [∀ i, DecidableRel (C i).Adj]
    (hw : ∀ i, 0 <= w i) (hwSum : ∑ i, w i = 1)
    (hC : ∀ i, C i <= rlc_connectorMergedWiring gamma gamma')
    (hpush :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') =
        ∑ i, w i *
          FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (C i)
            (BeffaraDC.selfDualPoint q) q
            (rlc_finiteConnectorEvent gamma gamma'))
    (harc : ∀ tau,
      tau ∉ rlc_finiteConnectorEvent gamma gamma' →
        RlcConnectorPIMSBoundaryArc gamma gamma' tau) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  apply rlc_finiteConnectorMass_selfDual_ge_of_PIMSBoundaryArc_domination
    gamma gamma' hq harc
  exact rlc_connectorPIMS_pushforward_le_merged_of_inducedMixture
    gamma gamma' hq w C hw hwSum hC hpush


theorem rlc_finiteConnectorMass_selfDual_ge_of_PIMSFilledBoundary_inducedMixture
    {n : Int} {I : Type*} [Fintype I] [DecidableEq I]
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (w : I → Real) (C : I → SimpleGraph (RlcConnectorVertex n))
    [∀ i, DecidableRel (C i).Adj]
    (hw : ∀ i, 0 <= w i) (hwSum : ∑ i, w i = 1)
    (hC : ∀ i, C i <= rlc_connectorMergedWiring gamma gamma')
    (hpush :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') =
        ∑ i, w i *
          FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (C i)
            (BeffaraDC.selfDualPoint q) q
            (rlc_finiteConnectorEvent gamma gamma'))
    (hgeom : ∀ tau,
      tau ∉ rlc_finiteConnectorEvent gamma gamma' →
        RlcConnectorPIMSFilledBoundaryContacts gamma gamma' tau ∧
          RlcConnectorPIMSFilledBoundaryTargetSupported gamma gamma' tau) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  apply rlc_finiteConnectorMass_selfDual_ge_of_PIMSReflected_domination
    gamma gamma' hq
  · intro tau hno
    exact rlc_connectorPIMSReflectedConfig_mem_event_of_filledBoundary
      gamma gamma' tau hno (hgeom tau hno).1 (hgeom tau hno).2
  · exact rlc_connectorPIMS_pushforward_le_merged_of_inducedMixture
      gamma gamma' hq w C hw hwSum hC hpush


theorem
    rlc_finiteConnectorMass_selfDual_ge_of_PIMSCollared_componentMixture
    {n : Int} {I : Type*} [Fintype I] [DecidableEq I]
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (w : I → Real)
    (tauExt : I → ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hw : ∀ i, 0 <= w i) (hwSum : ∑ i, w i = 1)
    (hfailure : ∀ tau,
      tau ∉ rlc_finiteConnectorEvent gamma gamma' →
        rlc_connectorReflectedDualConfig gamma gamma' tau ∈
          rlc_finiteConnectorEvent gamma gamma')
    (hpush :
      rlc_connectorForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' ⁻¹'
            rlc_finiteConnectorEvent gamma gamma') =
        ∑ i, w i *
          (∑ omega,
            (rlc_finiteConnectorEvent gamma gamma').indicator
                (fun _ => (1 : Real)) omega *
              FK.bcProbW (rlc_connectorFiniteGraph gamma gamma')
                (rlc_connectorComponentWiring
                  (rlc_connectorPIMSCollaredExteriorOpenGraph
                    gamma gamma' (tauExt i)))
                (rlc_connectorPIMSCollaredParameter gamma gamma'
                  (BeffaraDC.selfDualPoint q)) q omega)) :
    1 / (1 + q) <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteConnectorEvent gamma gamma') := by
  apply rlc_finiteConnectorMass_selfDual_ge_of_reflectedDual_domination
    gamma gamma' hq hfailure
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  exact (rlc_connectorForcedDualEventMass_reflected_le_PIMSCollared
    gamma gamma' hp hp1 hq0).trans
      (rlc_connectorPIMSCollared_pushforward_le_merged_of_componentMixture
        gamma gamma' hq w tauExt hw hwSum hpush)

end
end StatMech.Universality
