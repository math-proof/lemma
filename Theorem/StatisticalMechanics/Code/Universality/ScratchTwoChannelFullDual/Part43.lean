/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part52
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannelFaithfulFaceConnectorEvent_of_failure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    rlc_twoChannelFaithfulDualConfig gamma gamma' omega ∈
      rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma' := by
  let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'
  let K := FK.openSub P.G
    (rlc_connectorForceTraceConfig gamma gamma'
      (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))
  obtain ⟨x, y, hx, hy, hxPath, hyPath⟩ :=
    rlc_twoChannelFullFilledBoundaryContacts_of_faithful_failure
      gamma gamma' hfaith omega hno
  obtain ⟨a⟩ := rlc_twoChannelFullFilledFaceBoundary_reachable
    gamma gamma' omega hx hy
  let hle := rlc_twoChannelFullFilledBoundary_le_openFaceDual
    gamma gamma' omega
  have hface : (openSubgraph 2 (fci_faceDualConfig
      (rlc_twoChannelFullAmbientConfig gamma gamma' omega))).Reachable x y :=
    ⟨a.mapLe hle⟩
  have hregion : (whb_faceRegion (jei_pushGraph P K)).Reachable x y :=
    hface.mono (rlc_twoChannelFullFaceDual_le_pfdRegion
      gamma gamma' omega)
  have hdual : (BeffaraDC.pfdClosedDual P K).Reachable
      (BeffaraDC.pfdFace P x) (BeffaraDC.pfdFace P y) :=
    BeffaraDC.pfd_regionReachable_to_dual P K hregion
  have hindexed : (FK.indexedOpenGraph
      (rlc_twoChannelFaithfulEnds gamma gamma')
      (rlc_twoChannelFaithfulDualConfig gamma gamma' omega)).Reachable
        (BeffaraDC.pfdFace P x) (BeffaraDC.pfdFace P y) := by
    rw [rlc_twoChannelFaithful_indexedOpenGraph_eq_pfdClosedDual]
    exact hdual
  let xr : RlcConnectorVertex n :=
    ⟨rlc_dualReflect x,
      rlc_rightPathVertex_mem_connectorBox gamma hxPath⟩
  let yl : RlcConnectorVertex n :=
    ⟨rlc_dualReflect y,
      rlc_leftPathVertex_mem_connectorBox gamma' hyPath⟩
  refine ⟨BeffaraDC.pfdFace P x, BeffaraDC.pfdFace P y, ?_, ?_, hindexed⟩
  · refine ⟨xr, ?_, ?_⟩
    · exact hxPath
    · simp [xr, P]
  · refine ⟨yl, ?_, ?_⟩
    · exact hyPath
    · simp [yl, P]


theorem rlc_twoChannelFaithfulFaceConnectorEvent_to_ambientReachable
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hconn : rlc_twoChannelFaithfulDualConfig gamma gamma' omega ∈
      rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') :
    ∃ x y : RlcConnectorVertex n,
      rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
      (openSubgraph 2 (rlc_dualReflectConfig
        (rlc_twoChannelFullAmbientConfig gamma gamma' omega))).Reachable
          x.1 y.1 := by
  let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'
  let K := FK.openSub P.G
    (rlc_connectorForceTraceConfig gamma gamma'
      (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))
  obtain ⟨C, D, ⟨x, hx, hC⟩, ⟨y, hy, hD⟩, hdual⟩ := hconn
  have hdual' : (BeffaraDC.pfdClosedDual P K).Reachable
      (BeffaraDC.pfdFace P (rlc_dualReflect.symm x.1))
      (BeffaraDC.pfdFace P (rlc_dualReflect.symm y.1)) := by
    rw [← hC, ← hD]
    rw [← rlc_twoChannelFaithful_indexedOpenGraph_eq_pfdClosedDual]
    exact hdual
  have hregion := (BeffaraDC.pfd_regionReachable_iff_dual P K
    (FK.openSub_le P.G
      (rlc_connectorForceTraceConfig gamma gamma'
        (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))).mpr hdual'
  have hface : (openSubgraph 2 (fci_faceDualConfig
      (rlc_twoChannelFullAmbientConfig gamma gamma' omega))).Reachable
        (rlc_dualReflect.symm x.1) (rlc_dualReflect.symm y.1) := by
    rw [rlc_twoChannelFullFaceDual_eq_pfdRegion]
    exact hregion
  obtain ⟨w⟩ := hface
  have hreflected := (w.map (rlc_dualReflectOpenHom
    (rlc_twoChannelFullAmbientConfig gamma gamma' omega))).reachable
  refine ⟨x, y, hx, hy, ?_⟩
  simpa [rlc_dualReflectOpenHom] using hreflected


theorem rlc_twoChannelFaithfulFaceConnectorEvent_to_indexedOuterReachable
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hconn : rlc_twoChannelFaithfulDualConfig gamma gamma' omega ∈
      rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') :
    ∃ x y : RlcConnectorVertex n,
      rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
      (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).Reachable
        (rlc_twoChannelIndexedOuterTarget gamma gamma' x)
        (rlc_twoChannelIndexedOuterTarget gamma gamma' y) := by
  let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'
  let K := FK.openSub P.G
    (rlc_connectorForceTraceConfig gamma gamma'
      (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))
  obtain ⟨C, D, ⟨x, hx, hC⟩, ⟨y, hy, hD⟩, hdual⟩ := hconn
  have hdual' : (BeffaraDC.pfdClosedDual P K).Reachable
      (BeffaraDC.pfdFace P (rlc_dualReflect.symm x.1))
      (BeffaraDC.pfdFace P (rlc_dualReflect.symm y.1)) := by
    rw [← hC, ← hD]
    rw [← rlc_twoChannelFaithful_indexedOpenGraph_eq_pfdClosedDual]
    exact hdual
  refine ⟨x, y, hx, hy, ?_⟩
  exact rlc_twoChannelIndexedOuterTargets_reachable_of_pfd
    gamma gamma' omega x y hdual'


theorem rlc_twoChannelFaithfulFaceConnectorEvent_iff_indexedOuterReachable
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelFaithfulDualConfig gamma gamma' omega ∈
        rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma' ↔
      ∃ x y : RlcConnectorVertex n,
        rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
        (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).Reachable
          (rlc_twoChannelIndexedOuterTarget gamma gamma' x)
          (rlc_twoChannelIndexedOuterTarget gamma gamma' y) := by
  constructor
  · exact rlc_twoChannelFaithfulFaceConnectorEvent_to_indexedOuterReachable
      gamma gamma' omega
  · rintro ⟨x, y, hx, hy, hxy⟩
    let C := BeffaraDC.pfdFace
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
      (rlc_dualReflect.symm x.1)
    let D := BeffaraDC.pfdFace
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
      (rlc_dualReflect.symm y.1)
    refine ⟨C, D, ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, ?_⟩
    have hpfd := (rlc_twoChannelIndexedOuter_reachable_iff_pfd
      gamma gamma' omega
      (rlc_twoChannelIndexedOuterTarget gamma gamma' x)
      (rlc_twoChannelIndexedOuterTarget gamma gamma' y)).mp hxy
    rw [rlc_twoChannelFaithful_indexedOpenGraph_eq_pfdClosedDual]
    simpa [C, D, rlc_twoChannelIndexedFaceProjection,
      rlc_twoChannelIndexedOuterTarget] using hpfd


theorem rlc_twoChannelFailure_to_indexedOuterReachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    ∃ x y : RlcConnectorVertex n,
      rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
      (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).Reachable
        (rlc_twoChannelIndexedOuterTarget gamma gamma' x)
        (rlc_twoChannelIndexedOuterTarget gamma gamma' y) := by
  apply rlc_twoChannelFaithfulFaceConnectorEvent_to_indexedOuterReachable
    gamma gamma' omega
  exact rlc_twoChannelFaithfulFaceConnectorEvent_of_failure
    gamma gamma' hfaith omega hno

theorem rlc_twoChannelFaithfulFaceConnectorEvent_isIncreasing {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    IsIncreasing
      (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') := by
  intro eta eta' heta
  rintro ⟨C, D, hC, hD, hreach⟩
  refine ⟨C, D, hC, hD, hreach.mono ?_⟩
  intro x y hxy
  simp only [FK.indexedOpenGraph, SimpleGraph.fromEdgeSet_adj,
    Set.mem_setOf_eq] at hxy ⊢
  obtain ⟨⟨e, he, hopen⟩, hne⟩ := hxy
  refine ⟨⟨e, he, ?_⟩, hne⟩
  apply Bool.eq_true_of_not_eq_false
  intro hfalse
  have hle := heta e
  rw [hopen, hfalse] at hle
  exact (show ¬((true : Bool) ≤ false) by decide) hle


theorem rlc_twoChannelFaithfulFaceFree_le_merged {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    (⊥ : SimpleGraph (RlcTwoChannelFaithfulFace gamma gamma')) ≤
      rlc_twoChannelFaithfulFaceMergedWiring gamma gamma' :=
  bot_le


theorem rlc_twoChannelFaithfulFaceIndexedMass_free_le_merged {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    FK.indexedBcEventMass (rlc_twoChannelFaithfulEnds gamma gamma') ⊥ p q
        (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') ≤
      FK.indexedBcEventMass (rlc_twoChannelFaithfulEnds gamma gamma')
        (rlc_twoChannelFaithfulFaceMergedWiring gamma gamma') p q
        (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') := by
  exact FK.indexedBcEventMass_mono_bc
    (rlc_twoChannelFaithfulEnds gamma gamma') ⊥
    (rlc_twoChannelFaithfulFaceMergedWiring gamma gamma')
    (rlc_twoChannelFaithfulFaceFree_le_merged gamma gamma')
    hp hp1 hq
    (rlc_twoChannelFaithfulFaceConnectorEvent_isIncreasing gamma gamma')


theorem rlc_twoChannelFaithfulForcedDualEdgeConnectorMass_le_merged {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    rlc_twoChannelFaithfulForcedDualEdgeEventMass gamma gamma' p q
        (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') ≤
      FK.indexedBcEventMass (rlc_twoChannelFaithfulEnds gamma gamma')
        (rlc_twoChannelFaithfulFaceMergedWiring gamma gamma') p q
        (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') := by
  rw [rlc_twoChannelFaithfulForcedDualEdgeEventMass_eq_indexed
    gamma gamma' hp1 q]
  exact rlc_twoChannelFaithfulFaceIndexedMass_free_le_merged
    gamma gamma' hp hp1 hq


theorem rlc_twoChannelFailure_subset_faithfulFacePullback {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ ⊆
      rlc_twoChannelFaithfulFullPullbackEvent gamma gamma'
        (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') := by
  intro rho hno
  have hnoEdge : rlc_twoChannelEdgeConfigExtend gamma gamma'
      (rlc_twoChannelConfigSplitEquiv gamma gamma' rho).1 ∉
        rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
    intro hedge
    exact hno ((rlc_twoChannel_split_fst_mem_event_iff
      gamma gamma' rho).mp hedge)
  exact rlc_twoChannelFaithfulFaceConnectorEvent_of_failure
    gamma gamma' hfaith
      (rlc_twoChannelConfigSplitEquiv gamma gamma' rho).1 hnoEdge


theorem rlc_twoChannelForcedDualFailureMass_le_faithfulMerged {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    rlc_twoChannelForcedDualEventMass gamma gamma' p q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ ≤
      FK.indexedBcEventMass (rlc_twoChannelFaithfulEnds gamma gamma')
        (rlc_twoChannelFaithfulFaceMergedWiring gamma gamma') p q
        (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') := by
  calc
    rlc_twoChannelForcedDualEventMass gamma gamma' p q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ ≤
      rlc_twoChannelForcedDualEventMass gamma gamma' p q
        (rlc_twoChannelFaithfulFullPullbackEvent gamma gamma'
          (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma')) :=
      by
        unfold rlc_twoChannelForcedDualEventMass
        apply Finset.sum_le_sum
        intro rho _
        by_cases hfail : rho ∈
            (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ
        · have hpull := rlc_twoChannelFailure_subset_faithfulFacePullback
            gamma gamma' hfaith hfail
          simp [hfail, hpull]
        · by_cases hpull : rho ∈
              rlc_twoChannelFaithfulFullPullbackEvent gamma gamma'
                (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma')
          · simp [hfail, hpull,
              rlc_twoChannelForcedDualProb_nonneg gamma gamma' hp hp1
                (lt_of_lt_of_le zero_lt_one hq) rho]
          · simp [hfail, hpull]
    _ = rlc_twoChannelFaithfulForcedDualEdgeEventMass gamma gamma' p q
        (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') :=
      rlc_twoChannelForcedDualEventMass_faithfulPullback_eq_edge
        gamma gamma' hp hp1 (lt_of_lt_of_le zero_lt_one hq)
          (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma')
    _ ≤ FK.indexedBcEventMass (rlc_twoChannelFaithfulEnds gamma gamma')
        (rlc_twoChannelFaithfulFaceMergedWiring gamma gamma') p q
        (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') :=
      rlc_twoChannelFaithfulForcedDualEdgeConnectorMass_le_merged
        gamma gamma' hp hp1 hq


theorem rlc_twoChannelFaithfulFaceIndexedMass_mono_merged {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    FK.indexedBcEventMass (rlc_twoChannelFaithfulEnds gamma gamma')
        (rlc_twoChannelFaithfulFaceSeparateWiring gamma gamma') p q
        (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') ≤
      FK.indexedBcEventMass (rlc_twoChannelFaithfulEnds gamma gamma')
        (rlc_twoChannelFaithfulFaceMergedWiring gamma gamma') p q
        (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') := by
  exact FK.indexedBcEventMass_mono_bc
    (rlc_twoChannelFaithfulEnds gamma gamma')
    (rlc_twoChannelFaithfulFaceSeparateWiring gamma gamma')
    (rlc_twoChannelFaithfulFaceMergedWiring gamma gamma')
    (rlc_twoChannelFaithfulFaceSeparateWiring_le_merged gamma gamma')
    hp hp1 hq
    (rlc_twoChannelFaithfulFaceConnectorEvent_isIncreasing gamma gamma')

end
end StatMech.Universality
