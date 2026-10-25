/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part74
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysicalRetainedSideSelection_of_contourArcRepairSelection
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hrepair : RlcTwoChannelFullPhysicalContourArcRepairSelection
      gamma gamma' hfaith) :
    RlcTwoChannelFullPhysicalRetainedSideSelection
      gamma gamma' hfaith := by
  intro omega hno
  obtain ⟨x, y, u, c, hx, hy, hxPath, hyPath, hside⟩ :=
    hrepair omega hno
  exact
    rlc_twoChannelFullPhysicalFilledBoundarySegment_of_contourArcRepairSide
      c hx hy hxPath hyPath hside


theorem rlc_twoChannelFullPhysicalStaticCutIntersection_of_retainedSideSelection
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hselection : RlcTwoChannelFullPhysicalRetainedSideSelection
      gamma gamma' hfaith) :
    RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hfaith := by
  intro A B hAright hAleft hBright hBleft
  let omega := rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A
  have hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma' :=
    rlc_twoChannelFullPhysicalCutInteriorConfig_failure
      gamma gamma' A hAright hAleft
  obtain ⟨x, y, a, hxPath, hyPath, hsupported⟩ :=
    hselection omega hno
  have hxBox : rlc_dualReflect x ∈
      rect (-2 * n) (2 * n) (-n) n :=
    rlc_rightPathVertex_mem_connectorBox gamma hxPath
  have hyBox : rlc_dualReflect y ∈
      rect (-2 * n) (2 * n) (-n) n :=
    rlc_leftPathVertex_mem_connectorBox gamma' hyPath
  have hxB : rlc_dualReflect x ∈
      rlc_twoChannelFullPhysicalLiftVertexCut B := by
    exact ⟨hxBox, hBright ⟨rlc_dualReflect x, hxBox⟩ hxPath⟩
  have hyB : rlc_dualReflect y ∉
      rlc_twoChannelFullPhysicalLiftVertexCut B := by
    intro hy
    exact hBleft ⟨rlc_dualReflect y, hyBox⟩ hyPath
      ((rlc_twoChannelFullPhysicalLiftVertexCut_mem B
        ⟨rlc_dualReflect y, hyBox⟩).mp hy)
  obtain ⟨f, g, hfgEdge, hfB, hgB⟩ :=
    rlc_walk_pred_first_exit a
      (fun z => rlc_dualReflect z ∈
        rlc_twoChannelFullPhysicalLiftVertexCut B) hxB hyB
  have hfg : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g :=
    a.adj_of_mem_edges hfgEdge
  obtain ⟨target, htarget⟩ := hsupported s(f, g) hfgEdge
  have htarget' : target.1.1.map Subtype.val =
      s(rlc_dualReflect f, rlc_dualReflect g) := by
    simpa [Sym2.map_mk] using htarget
  have hgood : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Adj f g := ⟨hfg, target, htarget'⟩
  have hcarrier : RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
      gamma gamma' f g :=
    (rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
      gamma gamma' omega).1 hgood |>.2
  obtain ⟨target', htarget'', hsourceCross⟩ :=
    rlc_twoChannelFullPhysical_boundaryCarrier_source_crosses_staticCut
      gamma gamma' A hAright hAleft hfg hcarrier
  have htargetEq : target' = target := by
    apply Subtype.ext
    apply Subtype.ext
    apply Sym2.map.injective Subtype.val_injective
    exact htarget''.trans htarget'.symm
  subst target'
  have htargetCross :
      rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1 := by
    induction hedge : target.1.1 using Sym2.inductionOn with
    | _ u v =>
        have huvSite : s(u.1, v.1) =
            s(rlc_dualReflect f, rlc_dualReflect g) := by
          simpa [hedge, Sym2.map_mk] using htarget'
        rw [Sym2.eq_iff] at huvSite
        have hcross :
            (u ∈ B ∧ v ∉ B) ∨ (v ∈ B ∧ u ∉ B) := by
          rcases huvSite with ⟨huf, hvg⟩ | ⟨hug, hvf⟩
          · left
            refine ⟨?_, ?_⟩
            · exact (rlc_twoChannelFullPhysicalLiftVertexCut_mem B u).mp
                (by simpa [huf] using hfB)
            · intro hv
              exact hgB
                ((rlc_twoChannelFullPhysicalLiftVertexCut_mem B v).mpr
                  hv |> fun h => by simpa [hvg] using h)
          · right
            refine ⟨?_, ?_⟩
            · exact (rlc_twoChannelFullPhysicalLiftVertexCut_mem B v).mp
                (by simpa [hvf] using hfB)
            · intro hu
              exact hgB
                ((rlc_twoChannelFullPhysicalLiftVertexCut_mem B u).mpr
                  hu |> fun h => by simpa [hug] using h)
        exact ⟨u, v, rfl, hcross⟩
  obtain ⟨u, v, hsource, hcrossA⟩ := hsourceCross
  obtain ⟨p, q, htargetEdge, hcrossB⟩ := htargetCross
  exact ⟨target, p, q, u, v, htargetEdge, hsource,
    hcrossA, hcrossB⟩


theorem rlc_twoChannelFullPhysicalRetainedSideSelection_of_goodComponents
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hcomponents : ∀ omega : RlcTwoChannelEdgeConfig gamma gamma',
      rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
          rlc_finiteTwoChannelConnectorEvent gamma gamma' →
        RlcTwoChannelFullPhysicalGoodComponentContacts
          gamma gamma' omega) :
    RlcTwoChannelFullPhysicalRetainedSideSelection
      gamma gamma' hfaith := by
  intro omega hno
  exact rlc_twoChannelFullPhysicalFilledBoundarySegment_of_goodComponent
    (hcomponents omega hno)


theorem rlc_twoChannelFullPhysicalPermutationSuccess_of_retainedSideSelection
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hselection : RlcTwoChannelFullPhysicalRetainedSideSelection
      gamma gamma' hfaith) :
    RlcTwoChannelFullPhysicalPermutationSuccess gamma gamma' hfaith := by
  intro rho
  exact
    rlc_twoChannelFullPhysicalPermConfig_success_of_filledBoundarySegment
      rho.1 (hselection rho.1 rho.2)


theorem rlc_twoChannelFullPhysicalPermutationSuccess_of_contourArcRepairSelection
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hrepair : RlcTwoChannelFullPhysicalContourArcRepairSelection
      gamma gamma' hfaith) :
    RlcTwoChannelFullPhysicalPermutationSuccess
      gamma gamma' hfaith :=
  rlc_twoChannelFullPhysicalPermutationSuccess_of_retainedSideSelection
    hfaith
    (rlc_twoChannelFullPhysicalRetainedSideSelection_of_contourArcRepairSelection
      hfaith hrepair)

theorem rlc_twoChannelFullPhysicalRetainedSideSelection_of_contactCycleSelection
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hselection : RlcTwoChannelFullPhysicalContactCycleSelection
      gamma gamma' hfaith) :
    RlcTwoChannelFullPhysicalRetainedSideSelection gamma gamma' hfaith := by
  intro omega hno
  exact
    rlc_twoChannelFullPhysicalFilledBoundarySegment_of_contactCycleCertificate
      (hselection omega hno)


theorem rlc_twoChannelFullPhysicalStaticCutIntersection_of_contactCycleSelection
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hselection : RlcTwoChannelFullPhysicalContactCycleSelection
      gamma gamma' hfaith) :
    RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hfaith :=
  rlc_twoChannelFullPhysicalStaticCutIntersection_of_retainedSideSelection
    hfaith
    (rlc_twoChannelFullPhysicalRetainedSideSelection_of_contactCycleSelection
      hfaith hselection)


theorem
    rlc_twoChannelFullPhysicalGoodComponentContacts_of_staticCutConnectivity
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutConnectivity
      gamma gamma' hfaith)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega := by
  let A : Set (RlcConnectorVertex n) :=
    {z | z.1 ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega}
  have hAright : ∀ x : RlcConnectorVertex n,
      rlc_connectorOnRight gamma x → x ∈ A := by
    intro x hx
    exact rlc_twoChannelFullReachSet_subset_filled gamma gamma' omega
      (rlc_rightPathVertex_mem_twoChannelFullReachSet
        gamma gamma' omega hx)
  have hAleft : ∀ y : RlcConnectorVertex n,
      rlc_connectorOnLeft gamma' y → y ∉ A := by
    intro y hy hyA
    have hyExt :=
      rlc_leftPathVertex_mem_twoChannelFullExteriorSet_of_failure
        gamma gamma' hfaith.toRlcBookPositionedTracePair omega hno hy
    exact hyA hyExt
  obtain ⟨x, y, hxPath, hyPath, hxy⟩ :=
    hstatic A hAright hAleft
  let inverseDual : RlcConnectorVertex n → Site 2 :=
    fun z => rlc_dualReflect.symm z.1
  let hom :
      rlc_twoChannelFullPhysicalCutTargetGraphAt gamma gamma' A →g
        rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega :=
    { toFun := inverseDual
      map_rel' := by
        intro a b hab
        obtain ⟨target, htarget, p, q, hsource, hcross⟩ := hab
        obtain ⟨_target, _htarget, hboundary⟩ :=
          (rlc_twoChannelFullPhysicalCutTargetGraphAt_adj_iff_faceBoundary
            gamma gamma' A a b).mp
              ⟨target, htarget, p, q, hsource, hcross⟩
        refine ⟨?_, target, ?_⟩
        · rw [faceBoundaryGraph_adj]
          refine ⟨hboundary.1, ?_⟩
          have hpims : rlc_pimsEdgeEquiv (s(a.1, b.1)) =
              sharedPrimalEdge (rlc_dualReflect.symm a.1)
                (rlc_dualReflect.symm b.1) := by
            simpa using
              rlc_pimsEdgeEquiv_reflected_mk_of_adj hboundary.1
          have hsourceSite : s(p.1, q.1) =
              sharedPrimalEdge (rlc_dualReflect.symm a.1)
                (rlc_dualReflect.symm b.1) := by
            calc
              s(p.1, q.1) =
                  (rlc_twoChannelFullPhysicalSourceEdge target).1.map
                    Subtype.val := by rw [hsource, Sym2.map_mk]
              _ = rlc_pimsEdgeEquiv
                    (target.1.1.map Subtype.val) :=
                rlc_twoChannelFullPhysicalSourceEdge_map target
              _ = rlc_pimsEdgeEquiv (s(a.1, b.1)) := by
                rw [htarget, Sym2.map_mk]
              _ = _ := hpims
          rw [← hsourceSite, bdEdge_mk]
          change
            (p.1 ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
                q.1 ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega) ∨
              (q.1 ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
                p.1 ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
            at hcross
          rcases hcross with hpq | hqp
          · exact ⟨fun _ => hpq.2, fun _ => hpq.1⟩
          · exact ⟨fun hp => (hqp.2 hp).elim,
              fun hnq => (hnq hqp.1).elim⟩
        · rw [htarget, Sym2.map_mk]
          simp [inverseDual] }
  refine ⟨inverseDual x, inverseDual y, hxy.map hom, ?_, ?_⟩
  · simpa [inverseDual, rlc_connectorOnRight] using hxPath
  · simpa [inverseDual, rlc_connectorOnLeft] using hyPath


theorem rlc_twoChannelFullPhysicalContactCycleSelection_of_staticCutConnectivity
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutConnectivity
      gamma gamma' hfaith) :
    RlcTwoChannelFullPhysicalContactCycleSelection
      gamma gamma' hfaith := by
  rw [rlc_twoChannelFullPhysicalContactCycleSelection_iff_goodComponents
    hfaith]
  intro omega hno
  exact
    rlc_twoChannelFullPhysicalGoodComponentContacts_of_staticCutConnectivity
      hfaith hstatic omega hno


theorem rlc_twoChannelFullPhysicalContactCycleSelection_iff_staticCutConnectivity
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    RlcTwoChannelFullPhysicalContactCycleSelection gamma gamma' hfaith ↔
      RlcTwoChannelFullPhysicalStaticCutConnectivity
        gamma gamma' hfaith := by
  constructor
  · intro hselection
    exact
      rlc_twoChannelFullPhysicalStaticCutConnectivity_of_cutIntersection
        hfaith
        (rlc_twoChannelFullPhysicalStaticCutIntersection_of_contactCycleSelection
          hfaith hselection)
  · exact
      rlc_twoChannelFullPhysicalContactCycleSelection_of_staticCutConnectivity
        hfaith


theorem
    rlc_twoChannelFullPhysicalStaticCutConnectivity_iff_cutInteriorGoodComponents
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    RlcTwoChannelFullPhysicalStaticCutConnectivity gamma gamma' hfaith ↔
      ∀ (A : Set (RlcConnectorVertex n)),
        (∀ x, rlc_connectorOnRight gamma x → x ∈ A) →
        (∀ y, rlc_connectorOnLeft gamma' y → y ∉ A) →
          RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig
              gamma gamma' A) := by
  constructor
  · intro hstatic A hAright hAleft
    apply
      rlc_twoChannelFullPhysicalGoodComponentContacts_of_staticCutConnectivity
        hfaith hstatic
    exact rlc_twoChannelFullPhysicalCutInteriorConfig_failure
      gamma gamma' A hAright hAleft
  · intro hcomponents A hAright hAleft
    exact
      rlc_twoChannelFullPhysical_staticCutTargetConnector_of_goodComponent
        gamma gamma' A hAright hAleft
          (hcomponents A hAright hAleft)

theorem rlc_twoChannelFullPhysicalPermutationSuccess_of_contactCycleSelection
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hselection : RlcTwoChannelFullPhysicalContactCycleSelection
      gamma gamma' hfaith) :
    RlcTwoChannelFullPhysicalPermutationSuccess gamma gamma' hfaith :=
  rlc_twoChannelFullPhysicalPermutationSuccess_of_retainedSideSelection
    hfaith
    (rlc_twoChannelFullPhysicalRetainedSideSelection_of_contactCycleSelection
      hfaith hselection)


theorem rlc_twoChannelPIMSPooledVisibleFibreCapacity_of_fullPhysicalSuccess
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hphysical : RlcTwoChannelFullPhysicalPermutationSuccess
      gamma gamma' hfaith) :
    RlcTwoChannelPIMSPooledVisibleFibreCapacity hclosure :=
  (rlc_twoChannelPIMSPooledVisibleFibreCapacity_iff_exists_compatibleEmbedding
    hclosure).mpr
      ⟨rlc_twoChannelFullPhysicalSuccessEmbedding hfaith hphysical,
        rlc_twoChannelFullPhysicalSuccessEmbedding_compatible
          hclosure hfaith hphysical⟩


theorem
    rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_fullPhysicalSuccess
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hphysical : RlcTwoChannelFullPhysicalPermutationSuccess
      gamma gamma' hfaith)
    {q : Real} (hq : 1 <= q) (N : Nat)
    (hscore : RlcTwoChannelFullPhysicalPermutationScoreDefect
      gamma gamma' N) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      (Real.sqrt q) ^ N *
        FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  apply
    rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_pooledScoreHall
      gamma gamma' hclosure hq N
  exact rlc_twoChannelPIMSPooledScoreHall_of_fullPhysicalSuccess
    hclosure hfaith hphysical N hscore


theorem
    rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_fullPhysicalSuccess_scoreDefect
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hphysical : RlcTwoChannelFullPhysicalPermutationSuccess
      gamma gamma' hfaith)
    {q : Real} (hq : 1 <= q) (N : Nat)
    (hscore : RlcTwoChannelFullPhysicalPermutationScoreDefect
      gamma gamma' N) :
    1 / (1 + (Real.sqrt q) ^ N * q) <=
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  apply rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_pooledScoreHall
    gamma gamma' hclosure hq N
  exact rlc_twoChannelPIMSPooledScoreHall_of_fullPhysicalSuccess
    hclosure hfaith hphysical N hscore


theorem
    rlc_twoChannelForcedDualFailurePushforwardComparison_q_one_of_fullPhysicalSuccess
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hphysical : RlcTwoChannelFullPhysicalPermutationSuccess
      gamma gamma' hfaith) :
    RlcTwoChannelForcedDualFailurePushforwardComparison gamma gamma' 1 := by
  have hcapacity : RlcTwoChannelPIMSPooledVisibleFibreCapacity hclosure :=
    rlc_twoChannelPIMSPooledVisibleFibreCapacity_of_fullPhysicalSuccess
      hclosure hfaith hphysical
  unfold RlcTwoChannelForcedDualFailurePushforwardComparison
  rw [rlc_twoChannelForcedDualFailureImageMass_eq_compl
    gamma gamma' _ _ hclosure]
  convert
    rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_pooledVisibleCapacity
      gamma gamma' hclosure hcapacity using 1 <;>
    norm_num [BeffaraDC.selfDualPoint]


theorem
    rlc_finiteTwoChannelConnectorMass_selfDual_ge_half_of_fullPhysicalSuccess
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hphysical : RlcTwoChannelFullPhysicalPermutationSuccess
      gamma gamma' hfaith) :
    (1 / 2 : Real) <=
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint 1) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  convert rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_PIMS
    gamma gamma' le_rfl hclosure
      (rlc_twoChannelForcedDualFailurePushforwardComparison_q_one_of_fullPhysicalSuccess
        hclosure hfaith hphysical) using 1 <;> norm_num


theorem
    rlc_finiteTwoChannelConnectorMass_selfDual_ge_half_of_contactCycleSelection
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hselection : RlcTwoChannelFullPhysicalContactCycleSelection
      gamma gamma' hfaith) :
    (1 / 2 : Real) <=
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint 1) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') :=
  rlc_finiteTwoChannelConnectorMass_selfDual_ge_half_of_fullPhysicalSuccess
    hclosure hfaith
      (rlc_twoChannelFullPhysicalPermutationSuccess_of_contactCycleSelection
        hfaith hselection)


theorem rlc_walk_idxOf_le_of_getVert_eq
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a b z : V} (W : G.Walk a b) {k : Nat}
    (hk : k ≤ W.length) (hget : W.getVert k = z) :
    W.support.idxOf z ≤ k := by
  induction W generalizing k with
  | nil =>
      have hk0 : k = 0 := by simpa using hk
      subst k
      simp only [SimpleGraph.Walk.getVert_zero] at hget
      simp [hget]
  | @cons a v b h W ih =>
      cases k with
      | zero =>
          simp only [SimpleGraph.Walk.getVert_zero] at hget
          simp [hget]
      | succ k =>
          have hk' : k ≤ W.length := by simpa using hk
          have hget' : W.getVert k = z := by simpa using hget
          by_cases ha : a = z
          · simp [ha]
          · simpa [ha] using Nat.succ_le_succ (ih hk' hget')


theorem rlc_walk_exists_contact_extrema_around_offSupport
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a b u : V} (W : G.Walk a b) (C : G.Walk u u)
    {k : Nat} (hkLength : k ≤ W.length)
    (ha : a ∈ C.support) (hb : b ∈ C.support)
    (hkOff : W.getVert k ∉ C.support) :
    ∃ i j : Nat,
      i < k ∧ k < j ∧ j ≤ W.length ∧
        W.getVert i ∈ C.support ∧ W.getVert j ∈ C.support ∧
        ∀ l : Nat, i < l → l < j → W.getVert l ∉ C.support := by
  classical
  let L : Finset Nat := (Finset.range (k + 1)).filter fun i =>
    W.getVert i ∈ C.support
  have hzeroL : 0 ∈ L := by
    simp [L, ha]
  obtain ⟨i, hiL, hiMax⟩ := Finset.exists_max_image L id ⟨0, hzeroL⟩
  have hiInfo := Finset.mem_filter.mp hiL
  have hik : i ≤ k := by
    have := Finset.mem_range.mp hiInfo.1
    omega
  have hikStrict : i < k := by
    apply lt_of_le_of_ne hik
    intro hikEq
    apply hkOff
    simpa [hikEq] using hiInfo.2
  let R : Finset Nat := (Finset.Icc k W.length).filter fun j =>
    W.getVert j ∈ C.support
  have hlengthR : W.length ∈ R := by
    have hget : W.getVert W.length = b := W.getVert_length
    simp [R, hkLength, hget, hb]
  obtain ⟨j, hjR, hjMin⟩ := Finset.exists_min_image R id ⟨W.length, hlengthR⟩
  have hjInfo := Finset.mem_filter.mp hjR
  have hkj : k ≤ j := (Finset.mem_Icc.mp hjInfo.1).1
  have hjLength : j ≤ W.length := (Finset.mem_Icc.mp hjInfo.1).2
  have hkjStrict : k < j := by
    apply lt_of_le_of_ne hkj
    intro hkjEq
    apply hkOff
    simpa [← hkjEq] using hjInfo.2
  refine ⟨i, j, hikStrict, hkjStrict, hjLength, hiInfo.2, hjInfo.2, ?_⟩
  intro l hil hlj hlContact
  rcases le_total l k with hlk | hkl
  · have hlL : l ∈ L := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), hlContact⟩
    have hli : l ≤ i := by simpa using hiMax l hlL
    omega
  · have hlR : l ∈ R := Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hkl, by omega⟩, hlContact⟩
    have hjl : j ≤ l := by simpa using hjMin l hlR
    omega


theorem rlc_walk_exists_contact_extrema_around_offSupport_of_contacts
    {V : Type*} [DecidableEq V] {G K : SimpleGraph V}
    {a b u : V} (W : G.Walk a b) (C : K.Walk u u)
    {k : Nat} (hkOff : W.getVert k ∉ C.support)
    (hbefore : ∃ i : Nat, i < k ∧ W.getVert i ∈ C.support)
    (hafter : ∃ j : Nat,
      k < j ∧ j ≤ W.length ∧ W.getVert j ∈ C.support) :
    ∃ i j : Nat,
      i < k ∧ k < j ∧ j ≤ W.length ∧
        W.getVert i ∈ C.support ∧ W.getVert j ∈ C.support ∧
        ∀ l : Nat, i < l → l < j → W.getVert l ∉ C.support := by
  classical
  let L : Finset Nat := (Finset.range (k + 1)).filter fun i =>
    W.getVert i ∈ C.support
  obtain ⟨i0, hi0k, hi0C⟩ := hbefore
  have hi0L : i0 ∈ L := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega), hi0C⟩
  obtain ⟨i, hiL, hiMax⟩ :=
    Finset.exists_max_image L id ⟨i0, hi0L⟩
  have hiInfo := Finset.mem_filter.mp hiL
  have hik : i ≤ k := by
    have := Finset.mem_range.mp hiInfo.1
    omega
  have hikStrict : i < k := by
    apply lt_of_le_of_ne hik
    intro hikEq
    apply hkOff
    simpa [hikEq] using hiInfo.2
  let R : Finset Nat := (Finset.Icc k W.length).filter fun j =>
    W.getVert j ∈ C.support
  obtain ⟨j0, hkj0, hj0Length, hj0C⟩ := hafter
  have hj0R : j0 ∈ R := Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hkj0.le, hj0Length⟩, hj0C⟩
  obtain ⟨j, hjR, hjMin⟩ :=
    Finset.exists_min_image R id ⟨j0, hj0R⟩
  have hjInfo := Finset.mem_filter.mp hjR
  have hkj : k ≤ j := (Finset.mem_Icc.mp hjInfo.1).1
  have hjLength : j ≤ W.length := (Finset.mem_Icc.mp hjInfo.1).2
  have hkjStrict : k < j := by
    apply lt_of_le_of_ne hkj
    intro hkjEq
    apply hkOff
    simpa [← hkjEq] using hjInfo.2
  refine ⟨i, j, hikStrict, hkjStrict, hjLength,
    hiInfo.2, hjInfo.2, ?_⟩
  intro l hil hlj hlContact
  rcases le_total l k with hlk | hkl
  · have hlL : l ∈ L := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), hlContact⟩
    have hli : l ≤ i := by simpa using hiMax l hlL
    omega
  · have hlR : l ∈ R := Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hkl, by omega⟩, hlContact⟩
    have hjl : j ≤ l := by simpa using hjMin l hlR
    omega


theorem rlc_walk_prefix_reversePrefix_contact_interval
    {V : Type*} [DecidableEq V] {G K : SimpleGraph V}
    {a b u z : V} (W : G.Walk a b) (C : K.Walk u u)
    (hzW : z ∈ W.support) (hzC : z ∉ C.support)
    (hprefix : ∃ v ∈ (W.takeUntil z hzW).support, v ∈ C.support)
    (hsuffix : ∃ v ∈ (W.reverse.takeUntil z (by
      simpa [SimpleGraph.Walk.support_reverse] using hzW)).support,
        v ∈ C.support) :
    ∃ i j : Nat,
      i < W.support.idxOf z ∧ W.support.idxOf z < j ∧
        j ≤ W.length ∧ W.getVert i ∈ C.support ∧
        W.getVert j ∈ C.support ∧
        ∀ l : Nat, i < l → l < j → W.getVert l ∉ C.support := by
  obtain ⟨v, hvPrefix, hvC⟩ := hprefix
  have hvW : v ∈ W.support :=
    W.support_takeUntil_subset_support hzW hvPrefix
  let i0 := W.support.idxOf v
  have hi0Get : W.getVert i0 = v := W.getVert_support_idxOf hvW
  have hi0zLe : i0 ≤ W.support.idxOf z :=
    rlc_idxOf_le_of_mem_takeUntil W hzW hvPrefix
  have hi0z : i0 < W.support.idxOf z := by
    apply lt_of_le_of_ne hi0zLe
    intro hieq
    apply hzC
    have hzGet := W.getVert_support_idxOf hzW
    have hvz : v = z := by
      rw [← hi0Get, ← hzGet, hieq]
    exact hvz ▸ hvC
  have hzWRev : z ∈ W.reverse.support := by
    simpa [SimpleGraph.Walk.support_reverse] using hzW
  obtain ⟨v', hvSuffix, hv'C⟩ := hsuffix
  have hvWRev : v' ∈ W.reverse.support :=
    W.reverse.support_takeUntil_subset_support hzWRev hvSuffix
  let l0 := W.reverse.support.idxOf v'
  let j0 := W.length - l0
  have hl0Length : l0 ≤ W.length := by
    have hl := List.idxOf_lt_length_of_mem hvWRev
    rw [SimpleGraph.Walk.length_support,
      SimpleGraph.Walk.length_reverse] at hl
    omega
  have hl0GetRev : W.reverse.getVert l0 = v' :=
    W.reverse.getVert_support_idxOf hvWRev
  have hj0Get : W.getVert j0 = v' := by
    dsimp only [j0]
    rw [← SimpleGraph.Walk.getVert_reverse]
    exact hl0GetRev
  have hl0zLe : l0 ≤ W.reverse.support.idxOf z :=
    rlc_idxOf_le_of_mem_takeUntil W.reverse hzWRev hvSuffix
  have hl0z : l0 < W.reverse.support.idxOf z := by
    apply lt_of_le_of_ne hl0zLe
    intro hleq
    apply hzC
    have hzGetRev := W.reverse.getVert_support_idxOf hzWRev
    have hvz : v' = z := by
      rw [← hl0GetRev, ← hzGetRev, hleq]
    exact hvz ▸ hv'C
  have hzRevLength : W.reverse.support.idxOf z ≤ W.length := by
    have hzlt := List.idxOf_lt_length_of_mem hzWRev
    rw [SimpleGraph.Walk.length_support,
      SimpleGraph.Walk.length_reverse] at hzlt
    omega
  have hj0Length : j0 ≤ W.length := by
    dsimp only [j0]
    omega
  have hzLastGetRev := W.reverse.getVert_support_idxOf hzWRev
  rw [SimpleGraph.Walk.getVert_reverse] at hzLastGetRev
  have hfirstLast : W.support.idxOf z ≤
      W.length - W.reverse.support.idxOf z :=
    rlc_walk_idxOf_le_of_getVert_eq W (by omega) hzLastGetRev
  have hzj0 : W.support.idxOf z < j0 := by
    dsimp only [j0]
    omega
  have hzGet : W.getVert (W.support.idxOf z) = z :=
    W.getVert_support_idxOf hzW
  have hzOff : W.getVert (W.support.idxOf z) ∉ C.support := by
    simpa [hzGet] using hzC
  exact
    rlc_walk_exists_contact_extrema_around_offSupport_of_contacts
      W C hzOff ⟨i0, hi0z, by simpa [hi0Get] using hvC⟩
        ⟨j0, hzj0, hj0Length, by simpa [hj0Get] using hv'C⟩


theorem rlc_walk_exists_edge_index
    {V : Type*} {G : SimpleGraph V} {a b x y : V}
    (W : G.Walk a b) (hxy : s(x, y) ∈ W.edges) :
    ∃ k : Nat, k < W.length ∧
      ((W.getVert k = x ∧ W.getVert (k + 1) = y) ∨
        (W.getVert k = y ∧ W.getVert (k + 1) = x)) := by
  induction W with
  | nil => simp at hxy
  | @cons a v b h W ih =>
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at hxy
      rcases hxy with hhead | htail
      · refine ⟨0, by simp, ?_⟩
        simp only [SimpleGraph.Walk.getVert_zero,
          SimpleGraph.Walk.getVert_cons_succ, Nat.zero_add]
        rw [Sym2.eq_iff] at hhead
        rcases hhead with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
      · obtain ⟨k, hk, hget⟩ := ih htail
        refine ⟨k + 1, by simpa using Nat.succ_lt_succ hk, ?_⟩
        simpa [Nat.add_assoc] using hget


theorem rlc_walk_edge_prefix_reversePrefix_contact_interval
    {V : Type*} [DecidableEq V] {G K : SimpleGraph V}
    {a b u x y zR zL : V} (W : G.Walk a b) (C : K.Walk u u)
    (hxy : s(x, y) ∈ W.edges)
    (hzR : zR ∈ s(x, y)) (hzL : zL ∈ s(x, y))
    (hedgeOff : ∀ z ∈ s(x, y), z ∉ C.support)
    (hzRW : zR ∈ W.support) (hzLWRev : zL ∈ W.reverse.support)
    (hprefix : ∃ v ∈ (W.takeUntil zR hzRW).support,
      v ∈ C.support)
    (hsuffix : ∃ v ∈ (W.reverse.takeUntil zL hzLWRev).support,
      v ∈ C.support) :
    ∃ k i j : Nat,
      k < W.length ∧ s(W.getVert k, W.getVert (k + 1)) = s(x, y) ∧
        i < k ∧ k + 1 < j ∧ j ≤ W.length ∧
        W.getVert i ∈ C.support ∧ W.getVert j ∈ C.support ∧
        ∀ l : Nat, i < l → l < j → W.getVert l ∉ C.support := by
  obtain ⟨k, hkLength, hkxy⟩ := rlc_walk_exists_edge_index W hxy
  have hedgeGet : s(W.getVert k, W.getVert (k + 1)) = s(x, y) := by
    rcases hkxy with ⟨hkx, hky⟩ | ⟨hky, hkx⟩
    · rw [hkx, hky]
    · rw [hky, hkx, Sym2.eq_swap]
  have hkLe : k ≤ W.length := hkLength.le
  have hk1Le : k + 1 ≤ W.length := by omega
  have hkOff : W.getVert k ∉ C.support :=
    hedgeOff _ (by
      rw [← hedgeGet]
      exact Sym2.mem_mk_left _ _)
  have hk1Off : W.getVert (k + 1) ∉ C.support :=
    hedgeOff _ (by
      rw [← hedgeGet]
      exact Sym2.mem_mk_right _ _)
  have hzRAt : zR = W.getVert k ∨ zR = W.getVert (k + 1) := by
    rw [← hedgeGet, Sym2.mem_iff] at hzR
    exact hzR
  have hzLAt : zL = W.getVert k ∨ zL = W.getVert (k + 1) := by
    rw [← hedgeGet, Sym2.mem_iff] at hzL
    exact hzL
  obtain ⟨vR, hvRPrefix, hvRC⟩ := hprefix
  have hvRW : vR ∈ W.support :=
    W.support_takeUntil_subset_support hzRW hvRPrefix
  let i0 := W.support.idxOf vR
  have hi0Get : W.getVert i0 = vR := W.getVert_support_idxOf hvRW
  have hi0RLe : i0 ≤ W.support.idxOf zR :=
    rlc_idxOf_le_of_mem_takeUntil W hzRW hvRPrefix
  have hzROff : zR ∉ C.support := hedgeOff zR hzR
  have hi0R : i0 < W.support.idxOf zR := by
    apply lt_of_le_of_ne hi0RLe
    intro hieq
    apply hzROff
    have hzRGet := W.getVert_support_idxOf hzRW
    have hvz : vR = zR := by
      rw [← hi0Get, ← hzRGet, hieq]
    exact hvz ▸ hvRC
  have hzRIdxLe : W.support.idxOf zR ≤ k + 1 := by
    rcases hzRAt with hzRAt | hzRAt
    · exact rlc_walk_idxOf_le_of_getVert_eq W hkLe hzRAt.symm |>.trans
        (Nat.le_succ k)
    · exact rlc_walk_idxOf_le_of_getVert_eq W hk1Le hzRAt.symm
  have hi0k : i0 < k := by
    have hi0Le : i0 ≤ k := by omega
    apply lt_of_le_of_ne hi0Le
    intro hi0eq
    apply hkOff
    rw [← hi0eq, hi0Get]
    exact hvRC
  obtain ⟨vL, hvLSuffix, hvLC⟩ := hsuffix
  have hvLWRev : vL ∈ W.reverse.support :=
    W.reverse.support_takeUntil_subset_support hzLWRev hvLSuffix
  let l0 := W.reverse.support.idxOf vL
  let j0 := W.length - l0
  have hl0Length : l0 ≤ W.length := by
    have hl := List.idxOf_lt_length_of_mem hvLWRev
    rw [SimpleGraph.Walk.length_support,
      SimpleGraph.Walk.length_reverse] at hl
    omega
  have hl0GetRev : W.reverse.getVert l0 = vL :=
    W.reverse.getVert_support_idxOf hvLWRev
  have hj0Get : W.getVert j0 = vL := by
    dsimp only [j0]
    rw [← SimpleGraph.Walk.getVert_reverse]
    exact hl0GetRev
  have hl0LLe : l0 ≤ W.reverse.support.idxOf zL :=
    rlc_idxOf_le_of_mem_takeUntil W.reverse hzLWRev hvLSuffix
  have hzLOff : zL ∉ C.support := hedgeOff zL hzL
  have hl0L : l0 < W.reverse.support.idxOf zL := by
    apply lt_of_le_of_ne hl0LLe
    intro hleq
    apply hzLOff
    have hzLGetRev := W.reverse.getVert_support_idxOf hzLWRev
    have hvz : vL = zL := by
      rw [← hl0GetRev, ← hzLGetRev, hleq]
    exact hvz ▸ hvLC
  have hzLRevLength : W.reverse.support.idxOf zL ≤ W.length := by
    have hzlt := List.idxOf_lt_length_of_mem hzLWRev
    rw [SimpleGraph.Walk.length_support,
      SimpleGraph.Walk.length_reverse] at hzlt
    omega
  have hzLLastGe : k ≤ W.length - W.reverse.support.idxOf zL := by
    have hzLRevAt :
        W.reverse.getVert (W.length - k) = zL ∨
          W.reverse.getVert (W.length - (k + 1)) = zL := by
      rcases hzLAt with hzLAt | hzLAt
      · left
        rw [SimpleGraph.Walk.getVert_reverse]
        rw [Nat.sub_sub_self hkLe]
        exact hzLAt.symm
      · right
        rw [SimpleGraph.Walk.getVert_reverse]
        rw [Nat.sub_sub_self hk1Le]
        exact hzLAt.symm
    rcases hzLRevAt with hzLRevAt | hzLRevAt
    · have hidx := rlc_walk_idxOf_le_of_getVert_eq W.reverse
          (by simp) hzLRevAt
      omega
    · have hidx := rlc_walk_idxOf_le_of_getVert_eq W.reverse
          (by simp) hzLRevAt
      omega
  have hj0Length : j0 ≤ W.length := by
    dsimp only [j0]
    omega
  have hkj0 : k + 1 < j0 := by
    have hkj0Le : k + 1 ≤ j0 := by
      dsimp only [j0]
      omega
    apply lt_of_le_of_ne hkj0Le
    intro heq
    apply hk1Off
    rw [heq, hj0Get]
    exact hvLC
  obtain ⟨i, j, hik, hkj, hjLength, hiC, hjC, hbetween⟩ :=
    rlc_walk_exists_contact_extrema_around_offSupport_of_contacts
      W C hkOff ⟨i0, hi0k, by simpa [hi0Get] using hvRC⟩
        ⟨j0, by omega, hj0Length, by simpa [hj0Get] using hvLC⟩
  have hk1j : k + 1 < j := by
    have hk1jLe : k + 1 ≤ j := by omega
    apply lt_of_le_of_ne hk1jLe
    intro heq
    apply hk1Off
    rw [heq]
    exact hjC
  exact ⟨k, i, j, hkLength, hedgeGet, hik, hk1j, hjLength,
    hiC, hjC, hbetween⟩


theorem rlc_walk_support_subset_loop_or_contact_interval
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a b u : V} (W : G.Walk a b) (C : G.Walk u u)
    (ha : a ∈ C.support) (hb : b ∈ C.support) :
    (∀ z ∈ W.support, z ∈ C.support) ∨
      ∃ k i j : Nat,
        i < k ∧ k < j ∧ j ≤ W.length ∧
          W.getVert k ∉ C.support ∧
          W.getVert i ∈ C.support ∧ W.getVert j ∈ C.support ∧
          ∀ l : Nat, i < l → l < j → W.getVert l ∉ C.support := by
  classical
  by_cases hall : ∀ z ∈ W.support, z ∈ C.support
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨z, hzW, hzOff⟩ := hall
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hzW
    obtain ⟨k, hzk, hkLength⟩ := hzW
    have hkOff : W.getVert k ∉ C.support := by
      simpa [← hzk] using hzOff
    obtain ⟨i, j, hik, hkj, hjLength, hi, hj, hbetween⟩ :=
      rlc_walk_exists_contact_extrema_around_offSupport
        W C hkLength ha hb hkOff
    exact ⟨k, i, j, hik, hkj, hjLength, hkOff, hi, hj, hbetween⟩


theorem rlc_twoChannelFullPhysical_wallFamilyRowTwo_axisContactInterval
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u x y ur vr ul vl : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hvrC : vr ∈ c.support) (hvlC : vl ∈ c.support)
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (hurv : (hypercubicLattice 2).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (T : (hypercubicLattice 2).Walk vr vl)
    (hTprov : ∀ v ∈ T.support,
      v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨
        ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
          phb_doubleDualShift a = v) :
    ∃ (v : Site 2) (k : Nat),
      k ≤ T.length ∧ T.getVert k = v ∧ v 0 = -1 ∧
        (v ∈ c.support ∨
          ∃ i j : Nat,
            i < k ∧ k < j ∧ j ≤ T.length ∧
              T.getVert i ∈ c.support ∧ T.getVert j ∈ c.support ∧
              ∀ l : Nat, i < l → l < j →
                T.getVert l ∉ c.support) := by
  obtain ⟨v, hvT, hv0, _hvProv⟩ :=
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_transverseWalk_axisProvenance
      hrow hurv hulv T hTprov
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hvT
  obtain ⟨k, hkv, hkLength⟩ := hvT
  refine ⟨v, k, hkLength, hkv, hv0, ?_⟩
  by_cases hvC : v ∈ c.support
  · exact Or.inl hvC
  · right
    let C := c.mapLe (faceBoundaryGraph_le
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega))
    have hvrC' : vr ∈ C.support := by
      simpa [C, SimpleGraph.Walk.support_mapLe_eq_support] using hvrC
    have hvlC' : vl ∈ C.support := by
      simpa [C, SimpleGraph.Walk.support_mapLe_eq_support] using hvlC
    have hkOff : T.getVert k ∉ C.support := by
      simpa [C, SimpleGraph.Walk.support_mapLe_eq_support, hkv] using hvC
    obtain ⟨i, j, hik, hkj, hjLength, hi, hj, hbetween⟩ :=
      rlc_walk_exists_contact_extrema_around_offSupport
        T C hkLength hvrC' hvlC' hkOff
    refine ⟨i, j, hik, hkj, hjLength, ?_, ?_, ?_⟩
    · simpa [C, SimpleGraph.Walk.support_mapLe_eq_support] using hi
    · simpa [C, SimpleGraph.Walk.support_mapLe_eq_support] using hj
    · intro l hil hlj hlC
      exact hbetween l hil hlj (by
        simpa [C, SimpleGraph.Walk.support_mapLe_eq_support] using hlC)


theorem rlc_walk_ordered_to_complementary_contact_interval
    {G K : SimpleGraph (Site 2)}
    {u x y a b : Site 2} (c : G.Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (W : K.Walk a b)
    (ha : a ∈ (rlc_orderedContourArc c hx hy).support)
    (hb : b ∈ (rlc_complementaryContourArc c hx hy).support) :
    (∃ z ∈ W.support,
        z ∈ (rlc_orderedContourArc c hx hy).support ∧
          z ∈ (rlc_complementaryContourArc c hx hy).support) ∨
      ∃ i j : Nat,
        i < j ∧ j ≤ W.length ∧
          W.getVert i ∈ (rlc_orderedContourArc c hx hy).support ∧
          W.getVert j ∈ (rlc_complementaryContourArc c hx hy).support ∧
          ∀ l : Nat, i < l → l < j → W.getVert l ∉ c.support := by
  obtain ⟨i, j, _hzeroI, hij, _hjLength, _hlength, hi, hj,
      hiLast, hjFirst⟩ :=
    rlc_walk_exists_last_lower_first_upper_contact W
      (fun z => z ∈ (rlc_orderedContourArc c hx hy).support)
      (fun z => z ∈ (rlc_complementaryContourArc c hx hy).support)
      (i0 := 0) (j0 := W.length) (by omega) (by omega)
      (by simpa using ha) (by simpa using hb)
  by_cases hijEq : i = j
  · left
    refine ⟨W.getVert i, W.getVert_mem_support i, hi, ?_⟩
    simpa [hijEq] using hj
  · right
    have hijStrict : i < j := lt_of_le_of_ne hij hijEq
    refine ⟨i, j, hijStrict, by omega, hi, hj, ?_⟩
    intro l hil hlj hlc
    rcases rlc_contourContactArcs_support_cover c hx hy hlc with
      hlOrdered | hlComplementary
    · have hli := hiLast l (by omega) hlOrdered
      omega
    · have hjl := hjFirst l (by omega) (by omega) hlComplementary
      omega


theorem rlc_twoChannelFullPhysical_twoFirstBad_cycleSupport_cases
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u x y ur vr ul vl k : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (rr : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (rl : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
    (hdecR : rlc_orderedContourArc c hx hy =
      (qr.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
        gamma gamma' omega)).append (.cons hurv rr))
    (hdecL : (rlc_complementaryContourArc c hx hy).reverse =
      (ql.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
        gamma gamma' omega)).append (.cons hulv rl))
    (hk : k ∈ c.support) :
    k ∈ qr.support ∨ k = ur ∨ k = vr ∨ k ∈ rr.support ∨
      k ∈ ql.support ∨ k = ul ∨ k = vl ∨ k ∈ rl.support := by
  rcases rlc_contourContactArcs_support_cover c hx hy hk with
      hkOrdered | hkComplementary
  · rw [hdecR, SimpleGraph.Walk.mem_support_append_iff] at hkOrdered
    rcases hkOrdered with hkQr | hkBad
    · exact Or.inl (by
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hkQr)
    · simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hkBad
      rcases hkBad with hkur | hkRr
      · exact Or.inr (Or.inl hkur)
      · exact Or.inr (Or.inr (Or.inr (Or.inl hkRr)))
  · have hkReverse : k ∈
        (rlc_complementaryContourArc c hx hy).reverse.support := by
      simpa [SimpleGraph.Walk.support_reverse] using hkComplementary
    rw [hdecL, SimpleGraph.Walk.mem_support_append_iff] at hkReverse
    rcases hkReverse with hkQl | hkBad
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hkQl)))))
    · simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hkBad
      rcases hkBad with hkul | hkRl
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl hkul)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr hkRl))))))


theorem rlc_twoChannelFullPhysical_twoFirstBad_noncarrierEdge_cases
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u x y ur vr ul vl f g : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (rr : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (rl : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
    (hdecR : rlc_orderedContourArc c hx hy =
      (qr.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
        gamma gamma' omega)).append (.cons hurv rr))
    (hdecL : (rlc_complementaryContourArc c hx hy).reverse =
      (ql.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
        gamma gamma' omega)).append (.cons hulv rl))
    (hfgCycle : s(f, g) ∈ c.edges)
    (hfgBad :
      ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g) :
    s(f, g) = s(ur, vr) ∨ s(f, g) ∈ rr.edges ∨
      s(f, g) = s(ul, vl) ∨ s(f, g) ∈ rl.edges := by
  rcases rlc_contourContactArcs_edges_cover c hx hy hfgCycle with
      hfgOrdered | hfgComplementary
  · rw [hdecR, SimpleGraph.Walk.edges_append, List.mem_append] at hfgOrdered
    rcases hfgOrdered with hfgQr | hfgBadR
    · have hfgGood :
          (rlc_twoChannelFullPhysicalGoodBoundaryGraph
            gamma gamma' omega).Adj f g :=
        qr.adj_of_mem_edges (by
          simpa [SimpleGraph.Walk.edges_mapLe_eq_edges] using hfgQr)
      exact False.elim (hfgBad
        ((rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
          gamma gamma' omega).1 hfgGood).2)
    · simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at hfgBadR
      exact hfgBadR.elim (fun h => Or.inl h)
        (fun h => Or.inr (Or.inl h))
  · have hfgReverse : s(f, g) ∈
        (rlc_complementaryContourArc c hx hy).reverse.edges := by
      simpa [SimpleGraph.Walk.edges_reverse] using hfgComplementary
    rw [hdecL, SimpleGraph.Walk.edges_append, List.mem_append] at hfgReverse
    rcases hfgReverse with hfgQl | hfgBadL
    · have hfgGood :
          (rlc_twoChannelFullPhysicalGoodBoundaryGraph
            gamma gamma' omega).Adj f g :=
        ql.adj_of_mem_edges (by
          simpa [SimpleGraph.Walk.edges_mapLe_eq_edges] using hfgQl)
      exact False.elim (hfgBad
        ((rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
          gamma gamma' omega).1 hfgGood).2)
    · simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at hfgBadL
      exact hfgBadL.elim (fun h => Or.inr (Or.inr (Or.inl h)))
        (fun h => Or.inr (Or.inr (Or.inr h)))


theorem
    rlc_twoChannelFullPhysical_noncarrierEdge_eq_firstExit_or_mem_remainder
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y u v f g : Site 2}
    (w : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk x y)
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x u)
    (r : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk v y)
    (huv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
    (hdecomp : w =
      (q.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
        gamma gamma' omega)).append (.cons huv r))
    (hfg : s(f, g) ∈ w.edges)
    (hfgBad :
      ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g) :
    s(f, g) = s(u, v) ∨ s(f, g) ∈ r.edges := by
  rw [hdecomp, SimpleGraph.Walk.edges_append, List.mem_append] at hfg
  rcases hfg with hfgQ | hfgExit
  · have hfgGood :
        (rlc_twoChannelFullPhysicalGoodBoundaryGraph
          gamma gamma' omega).Adj f g :=
      q.adj_of_mem_edges (by
        simpa [SimpleGraph.Walk.edges_mapLe_eq_edges] using hfgQ)
    exact False.elim (hfgBad
      ((rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
        gamma gamma' omega).1 hfgGood).2)
  · simpa only [SimpleGraph.Walk.edges_cons, List.mem_cons] using hfgExit


theorem rlc_twoChannelFullPhysical_firstExit_of_noncarrierEdge_mem
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y f g : Site 2}
    (w : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk x y)
    (hfg : s(f, g) ∈ w.edges)
    (hfgBad :
      ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g) :
    ∃ (u v : Site 2)
      (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Walk x u)
      (r : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk v y)
      (huv : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v),
      ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' u v ∧
        w = (q.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
          gamma gamma' omega)).append (.cons huv r) ∧
        (s(f, g) = s(u, v) ∨ s(f, g) ∈ r.edges) ∧
        r.length < w.length := by
  rcases rlc_walk_subgraph_lift_or_first_exit_decomp
      (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega) w with
      ⟨q, hq⟩ | ⟨u, v, q, r, huv, huvBad, hdecomp⟩
  · have hfgMap : s(f, g) ∈
        (q.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
          gamma gamma' omega)).edges := by
      rw [hq]
      exact hfg
    have hfgGood :
        (rlc_twoChannelFullPhysicalGoodBoundaryGraph
          gamma gamma' omega).Adj f g :=
      q.adj_of_mem_edges (by
        simpa [SimpleGraph.Walk.edges_mapLe_eq_edges] using hfgMap)
    exact False.elim (hfgBad
      ((rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
        gamma gamma' omega).1 hfgGood).2)
  · have huvCarrierBad :
        ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
          gamma gamma' u v := by
      intro huvCarrier
      exact huvBad
        ((rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
          gamma gamma' omega).2 ⟨huv, huvCarrier⟩)
    have hrLength : r.length < w.length := by
      have hlength := congrArg SimpleGraph.Walk.length hdecomp
      simp at hlength
      omega
    have hfgRemainder :=
      rlc_twoChannelFullPhysical_noncarrierEdge_eq_firstExit_or_mem_remainder
        w q r huv hdecomp hfg hfgBad
    exact ⟨u, v, q, r, huv, huvCarrierBad, hdecomp,
      hfgRemainder, hrLength⟩


theorem
    rlc_twoChannelFullPhysical_twoFirstBad_noncarrierEdge_exact_or_reverseFirstExit
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u x y ur vr ul vl f g : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (rr : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (rl : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
    (hdecR : rlc_orderedContourArc c hx hy =
      (qr.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
        gamma gamma' omega)).append (.cons hurv rr))
    (hdecL : (rlc_complementaryContourArc c hx hy).reverse =
      (ql.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
        gamma gamma' omega)).append (.cons hulv rl))
    (hfgCycle : s(f, g) ∈ c.edges)
    (hfgBad :
      ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g) :
    s(f, g) = s(ur, vr) ∨
      (∃ (u' v' : Site 2)
        (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
          gamma gamma' omega).Walk y u')
        (r : (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk v' vr)
        (huv : (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u' v'),
        ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
            gamma gamma' u' v' ∧
          rr.reverse =
            (q.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
              gamma gamma' omega)).append (.cons huv r) ∧
          (s(f, g) = s(u', v') ∨ s(f, g) ∈ r.edges) ∧
          r.length < rr.length) ∨
      s(f, g) = s(ul, vl) ∨
      ∃ (u' v' : Site 2)
        (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
          gamma gamma' omega).Walk x u')
        (r : (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk v' vl)
        (huv : (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u' v'),
        ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
            gamma gamma' u' v' ∧
          rl.reverse =
            (q.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
              gamma gamma' omega)).append (.cons huv r) ∧
          (s(f, g) = s(u', v') ∨ s(f, g) ∈ r.edges) ∧
          r.length < rl.length := by
  rcases rlc_twoChannelFullPhysical_twoFirstBad_noncarrierEdge_cases
      c hx hy qr rr ql rl hurv hulv hdecR hdecL hfgCycle hfgBad with
      hbadR | hrr | hbadL | hrl
  · exact Or.inl hbadR
  · right; left
    obtain ⟨u', v', q, r, huv, hbad, hdecomp, hfgRemainder, hlength⟩ :=
      rlc_twoChannelFullPhysical_firstExit_of_noncarrierEdge_mem
        rr.reverse (by
          simpa [SimpleGraph.Walk.edges_reverse] using hrr) hfgBad
    exact ⟨u', v', q, r, huv, hbad, hdecomp, hfgRemainder,
      by simpa using hlength⟩
  · right; right; left
    exact hbadL
  · right; right; right
    obtain ⟨u', v', q, r, huv, hbad, hdecomp, hfgRemainder, hlength⟩ :=
      rlc_twoChannelFullPhysical_firstExit_of_noncarrierEdge_mem
        rl.reverse (by
          simpa [SimpleGraph.Walk.edges_reverse] using hrl) hfgBad
    exact ⟨u', v', q, r, huv, hbad, hdecomp, hfgRemainder,
      by simpa using hlength⟩


theorem rlc_twoChannelFullPhysical_rightArcClassifiedBad_of_goodPrefix
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {x u v : Site 2}
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x u)
    (huv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
    (hbad :
      ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' u v) :
    RlcTwoChannelFullPhysicalRightArcClassifiedBad
      gamma gamma' omega u v := by
  have hxBarrier : rlc_dualReflect x ∈
      rlc_connectorBarrier gamma gamma' := by
    simp [rlc_connectorBarrier, hxPath]
  have hxBox : rlc_dualReflect x ∈ rlc_connectorBox n := by
    simpa [rlc_connectorBox] using
      (rlc_rightPathVertex_mem_connectorBox gamma hxPath)
  rcases rlc_twoChannelFullPhysical_boundaryBad_target_or_sourceNotPlanar
      gamma gamma' omega huv hbad with htarget | hsource
  · left
    refine ⟨htarget, ?_⟩
    rcases rlc_twoChannelFullPhysical_targetBad_near_barrier_or_boxBoundary
        hxBarrier hxBox q huv htarget with hbarrier | hboundary
    · rcases rlc_connectorBarrier_original_or_exclusive_strict_reflected
          gamma gamma' hbarrier with
        hright | hleft | hflipLeft | hflipRight
      · exact Or.inl hright
      · exact False.elim
          ((rlc_twoChannelFullPhysical_noGood_rightWalk_end_not_leftContact
            hnoGood hxPath q) hleft)
      · exact Or.inr (Or.inl hflipLeft)
      · exact Or.inr (Or.inr (Or.inl hflipRight))
    · exact Or.inr (Or.inr (Or.inr hboundary))
  · right
    obtain ⟨p, p', hp, hpAdj, hpReach, hpOut, hpPlace⟩ :=
      rlc_twoChannelFullPhysical_sourceBad_inside_barrier_or_boxBoundary
        gamma gamma' omega huv hsource
    refine ⟨p, p', hp, hpAdj, hpReach, hpOut, ?_⟩
    rcases hpPlace with hpBarrier | hpBoundary
    · rcases rlc_connectorBarrier_original_or_exclusive_strict_reflected
          gamma gamma' hpBarrier with
        hpRight | hpLeft | hpFlipLeft | hpFlipRight
      · exact Or.inl hpRight
      · exact False.elim
          ((rlc_leftPathVertex_not_mem_twoChannelFullReachSet_of_failure
            gamma gamma' omega hno hpLeft) hpReach)
      · exact Or.inr (Or.inl hpFlipLeft)
      · exact Or.inr (Or.inr (Or.inl hpFlipRight))
    · exact Or.inr (Or.inr (Or.inr hpBoundary))


theorem
    rlc_twoChannelFullPhysical_goodReachable_of_rightClassifiedBadRepairs
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {x y : Site 2}
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (a : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk x y)
    (hrepair : ∀ {u v : Site 2},
      RlcTwoChannelFullPhysicalRightArcClassifiedBad
          gamma gamma' omega u v →
        ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
          gamma gamma' u v →
        (rlc_twoChannelFullPhysicalGoodBoundaryGraph
          gamma gamma' omega).Reachable u v) :
    (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Reachable x y := by
  have hbuild : ∀ {u v : Site 2}
      (w : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u v),
      (rlc_twoChannelFullPhysicalGoodBoundaryGraph
          gamma gamma' omega).Reachable x u →
        (rlc_twoChannelFullPhysicalGoodBoundaryGraph
          gamma gamma' omega).Reachable x v := by
    intro u v w
    induction w with
    | nil => exact fun hu => hu
    | @cons u v z huv p ih =>
        intro hxu
        have huvReach : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
            gamma gamma' omega).Reachable u v := by
          by_cases hcarrier :
              RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
                gamma gamma' u v
          · exact
              ((rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
                gamma gamma' omega).2 ⟨huv, hcarrier⟩).reachable
          · obtain ⟨q⟩ := hxu
            exact hrepair
              (rlc_twoChannelFullPhysical_rightArcClassifiedBad_of_goodPrefix
                hno hnoGood hxPath q huv hcarrier) hcarrier
        exact ih (hxu.trans huvReach)
  exact hbuild a (Reachable.refl _)


theorem
    rlc_twoChannelFullPhysical_goodComponent_of_rightClassifiedBadRepairs
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hrepair : ∀ {f g : Site 2},
      RlcTwoChannelFullPhysicalRightArcClassifiedBad
          gamma gamma' omega f g →
        ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
          gamma gamma' f g →
        (rlc_twoChannelFullPhysicalGoodBoundaryGraph
          gamma gamma' omega).Reachable f g) :
    RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega := by
  exact ⟨x, y,
    rlc_twoChannelFullPhysical_goodReachable_of_rightClassifiedBadRepairs
      hno hnoGood hxPath (rlc_orderedContourArc c hx hy) hrepair,
    hxPath, hyPath⟩


theorem
    rlc_twoChannelFullPhysical_firstUnrepairableRightClassifiedBad
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
    ∃ (ur vr : Site 2)
      (qRepair : (rlc_twoChannelFullPhysicalRepairableBoundaryGraph
        gamma gamma' omega).Walk x ur)
      (qGood : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Walk x ur)
      (rr : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y)
      (hurv : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr),
      rlc_orderedContourArc c hx hy =
          (qRepair.mapLe
            (rlc_twoChannelFullPhysicalRepairableBoundaryGraph_le
              gamma gamma' omega)).append (.cons hurv rr) ∧
        rr.length < (rlc_orderedContourArc c hx hy).length ∧
        ¬(rlc_twoChannelFullPhysicalGoodBoundaryGraph
          gamma gamma' omega).Reachable ur vr ∧
        ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
          gamma gamma' ur vr ∧
        RlcTwoChannelFullPhysicalRightArcClassifiedBad
          gamma gamma' omega ur vr := by
  let a := rlc_orderedContourArc c hx hy
  let hle := rlc_twoChannelFullPhysicalRepairableBoundaryGraph_le
    gamma gamma' omega
  rcases rlc_walk_subgraph_lift_or_first_exit_decomp hle a with
      ⟨qRepair, hq⟩ |
      ⟨ur, vr, qRepair, rr, hurv, hurvBad, hdecomp⟩
  · have hxy :=
      rlc_twoChannelFullPhysical_goodReachable_of_repairableBoundaryWalk
        gamma gamma' omega qRepair
    exact False.elim (hnoGood ⟨x, y, hxy, hxPath, hyPath⟩)
  · have hxu :=
      rlc_twoChannelFullPhysical_goodReachable_of_repairableBoundaryWalk
        gamma gamma' omega qRepair
    obtain ⟨qGood⟩ := hxu
    have hnotReach : ¬(rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Reachable ur vr := by
      intro hreach
      exact hurvBad ⟨hurv, hreach⟩
    have hbad :
        ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
          gamma gamma' ur vr := by
      intro hcarrier
      exact hnotReach
        ((rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
          gamma gamma' omega).2 ⟨hurv, hcarrier⟩).reachable
    refine ⟨ur, vr, qRepair, qGood, rr, hurv, ?_, ?_, hnotReach, hbad, ?_⟩
    · simpa [a, hle] using hdecomp
    · have hdecomp' : rlc_orderedContourArc c hx hy =
          (qRepair.mapLe hle).append (.cons hurv rr) := by
        simpa [a, hle] using hdecomp
      rw [hdecomp']
      simp
      omega
    · exact
        rlc_twoChannelFullPhysical_rightArcClassifiedBad_of_goodPrefix
          hno hnoGood hxPath qGood hurv hbad


theorem rlc_twoChannelFullPhysical_leftArcClassifiedBad_of_goodPrefix
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {y u v : Site 2}
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y u)
    (huv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
    (hbad :
      ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' u v) :
    RlcTwoChannelFullPhysicalLeftArcClassifiedBad
      gamma gamma' omega u v := by
  have hyBarrier : rlc_dualReflect y ∈
      rlc_connectorBarrier gamma gamma' := by
    simp [rlc_connectorBarrier, hyPath]
  have hyBox : rlc_dualReflect y ∈ rlc_connectorBox n := by
    simpa [rlc_connectorBox] using
      (rlc_leftPathVertex_mem_connectorBox gamma' hyPath)
  rcases rlc_twoChannelFullPhysical_boundaryBad_target_or_sourceNotPlanar
      gamma gamma' omega huv hbad with htarget | hsource
  · left
    refine ⟨htarget, ?_⟩
    rcases rlc_twoChannelFullPhysical_targetBad_near_barrier_or_boxBoundary
        hyBarrier hyBox q huv htarget with hbarrier | hboundary
    · rcases rlc_connectorBarrier_original_or_exclusive_strict_reflected
          gamma gamma' hbarrier with
        hright | hleft | hflipLeft | hflipRight
      · exact False.elim
          ((rlc_twoChannelFullPhysical_noGood_leftWalk_end_not_rightContact
            hnoGood hyPath q) hright)
      · exact Or.inl hleft
      · exact Or.inr (Or.inl hflipLeft)
      · exact Or.inr (Or.inr (Or.inl hflipRight))
    · exact Or.inr (Or.inr (Or.inr hboundary))
  · right
    obtain ⟨p, p', hp, hpAdj, hpReach, hpOut, hpPlace⟩ :=
      rlc_twoChannelFullPhysical_sourceBad_inside_barrier_or_boxBoundary
        gamma gamma' omega huv hsource
    refine ⟨p, p', hp, hpAdj, hpReach, hpOut, ?_⟩
    rcases hpPlace with hpBarrier | hpBoundary
    · rcases rlc_connectorBarrier_original_or_exclusive_strict_reflected
          gamma gamma' hpBarrier with
        hpRight | hpLeft | hpFlipLeft | hpFlipRight
      · exact Or.inl hpRight
      · exact False.elim
          ((rlc_leftPathVertex_not_mem_twoChannelFullReachSet_of_failure
            gamma gamma' omega hno hpLeft) hpReach)
      · exact Or.inr (Or.inl hpFlipLeft)
      · exact Or.inr (Or.inr (Or.inl hpFlipRight))
    · exact Or.inr (Or.inr (Or.inr hpBoundary))


theorem
    rlc_twoChannelFullPhysical_firstUnrepairableLeftClassifiedBad
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
    ∃ (ul vl : Site 2)
      (qRepair : (rlc_twoChannelFullPhysicalRepairableBoundaryGraph
        gamma gamma' omega).Walk y ul)
      (qGood : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Walk y ul)
      (rl : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x)
      (hulv : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl),
      (rlc_complementaryContourArc c hx hy).reverse =
          (qRepair.mapLe
            (rlc_twoChannelFullPhysicalRepairableBoundaryGraph_le
              gamma gamma' omega)).append (.cons hulv rl) ∧
        rl.length <
          (rlc_complementaryContourArc c hx hy).reverse.length ∧
        ¬(rlc_twoChannelFullPhysicalGoodBoundaryGraph
          gamma gamma' omega).Reachable ul vl ∧
        ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
          gamma gamma' ul vl ∧
        RlcTwoChannelFullPhysicalLeftArcClassifiedBad
          gamma gamma' omega ul vl := by
  let a := (rlc_complementaryContourArc c hx hy).reverse
  let hle := rlc_twoChannelFullPhysicalRepairableBoundaryGraph_le
    gamma gamma' omega
  rcases rlc_walk_subgraph_lift_or_first_exit_decomp hle a with
      ⟨qRepair, hq⟩ |
      ⟨ul, vl, qRepair, rl, hulv, hulvBad, hdecomp⟩
  · have hyx :=
      rlc_twoChannelFullPhysical_goodReachable_of_repairableBoundaryWalk
        gamma gamma' omega qRepair
    exact False.elim (hnoGood ⟨x, y, hyx.symm, hxPath, hyPath⟩)
  · have hyu :=
      rlc_twoChannelFullPhysical_goodReachable_of_repairableBoundaryWalk
        gamma gamma' omega qRepair
    obtain ⟨qGood⟩ := hyu
    have hnotReach : ¬(rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Reachable ul vl := by
      intro hreach
      exact hulvBad ⟨hulv, hreach⟩
    have hbad :
        ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
          gamma gamma' ul vl := by
      intro hcarrier
      exact hnotReach
        ((rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
          gamma gamma' omega).2 ⟨hulv, hcarrier⟩).reachable
    refine ⟨ul, vl, qRepair, qGood, rl, hulv, ?_, ?_, hnotReach, hbad, ?_⟩
    · simpa [a, hle] using hdecomp
    · have hdecomp' : (rlc_complementaryContourArc c hx hy).reverse =
          (qRepair.mapLe hle).append (.cons hulv rl) := by
        simpa [a, hle] using hdecomp
      rw [hdecomp']
      simp
      omega
    · exact
        rlc_twoChannelFullPhysical_leftArcClassifiedBad_of_goodPrefix
          hno hnoGood hyPath qGood hulv hbad


theorem
    rlc_twoChannelFullPhysical_unrepairableTerminalProductClassification
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
    ∃ (ur vr ul vl : Site 2)
      (qRepairR : (rlc_twoChannelFullPhysicalRepairableBoundaryGraph
        gamma gamma' omega).Walk x ur)
      (qRepairL : (rlc_twoChannelFullPhysicalRepairableBoundaryGraph
        gamma gamma' omega).Walk y ul)
      (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Walk x ur)
      (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Walk y ul)
      (rr : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y)
      (rl : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x)
      (hurv : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
      (hulv : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl),
      rlc_orderedContourArc c hx hy =
          (qRepairR.mapLe
            (rlc_twoChannelFullPhysicalRepairableBoundaryGraph_le
              gamma gamma' omega)).append (.cons hurv rr) ∧
        (rlc_complementaryContourArc c hx hy).reverse =
          (qRepairL.mapLe
            (rlc_twoChannelFullPhysicalRepairableBoundaryGraph_le
              gamma gamma' omega)).append (.cons hulv rl) ∧
        rr.length < (rlc_orderedContourArc c hx hy).length ∧
        rl.length <
          (rlc_complementaryContourArc c hx hy).reverse.length ∧
        ¬(rlc_twoChannelFullPhysicalGoodBoundaryGraph
          gamma gamma' omega).Reachable ur vr ∧
        ¬(rlc_twoChannelFullPhysicalGoodBoundaryGraph
          gamma gamma' omega).Reachable ul vl ∧
        ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
          gamma gamma' ur vr ∧
        ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
          gamma gamma' ul vl ∧
        RlcTwoChannelFullPhysicalRightArcClassifiedBad
          gamma gamma' omega ur vr ∧
        RlcTwoChannelFullPhysicalLeftArcClassifiedBad
          gamma gamma' omega ul vl ∧
        RlcTwoChannelFullPhysicalWallTerminalProductClassification
          gamma gamma' omega (vr := vr) (vl := vl) qr ql := by
  obtain ⟨ur, vr, qRepairR, qr, rr, hurv, hdecR, hlenR,
      hnotR, hbadR, hclassR⟩ :=
    rlc_twoChannelFullPhysical_firstUnrepairableRightClassifiedBad
      hno hnoGood c hx hy hxPath hyPath
  obtain ⟨ul, vl, qRepairL, ql, rl, hulv, hdecL, hlenL,
      hnotL, hbadL, hclassL⟩ :=
    rlc_twoChannelFullPhysical_firstUnrepairableLeftClassifiedBad
      hno hnoGood c hx hy hxPath hyPath
  exact ⟨ur, vr, ul, vl, qRepairR, qRepairL, qr, ql, rr, rl,
    hurv, hulv, hdecR, hdecL, hlenR, hlenL,
    hnotR, hnotL, hbadR, hbadL,
    hclassR, hclassL,
    rlc_twoChannelFullPhysical_wallTerminalProductClassification
      hfaith qr ql hxPath hyPath hclassR hclassL⟩


theorem
    rlc_twoChannelFullPhysical_orderedWallAlternative_of_product
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {z x y ur vr ul vl : Site 2}
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hxOrder : rlc_flipX (rlc_dualReflect x) ∈
      (right.map rlc_flipXLatticeHom).support)
    (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
    (hfirst : ∀ w ∈ right.support,
      rlc_flipX w ∈ rlc_pathVertices gamma'.1 → w = z)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (hproduct : RlcTwoChannelFullPhysicalWallTerminalProductClassification
      gamma gamma' omega (vr := vr) (vl := vl) qr ql) :
    (∃ e ∈ qr.edges,
        Sym2.map rlc_dualReflect e ∉
          rlc_connectorFourTraceEdges gamma gamma') ∨
      (∃ e ∈ ql.edges,
        Sym2.map rlc_dualReflect e ∉
          rlc_connectorFourTraceEdges gamma gamma') ∨
      RlcTwoChannelFullPhysicalRightArcNonExclusiveLocalizedBad
        gamma gamma' omega ur vr ∨
      RlcTwoChannelFullPhysicalLeftArcNonExclusiveLocalizedBad
        gamma gamma' omega ul vl ∨
      (RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyTable
          gamma gamma' omega qr ql ∧
        RlcTwoChannelFullPhysicalOrderedWallFamilyOutcome
          gamma gamma' omega flipLeft qr ql) := by
  rcases hproduct.rightPrefix with hallR | hnonwallR
  · rcases hproduct.leftPrefix with hallL | hnonwallL
    · rcases hproduct.rightTerminal with hlocR | hlocalizedR
      · rcases hproduct.leftTerminal with hlocL | hlocalizedL
        · have htable :=
            rlc_twoChannelFullPhysical_twoArcWallFamilyTruthTable
              hfaith right flipLeft qr ql hxPath hyPath hxOrder hyOrder
                hfirst hallR hallL hlocR hlocL
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨
            hproduct.terminalTable hallR hallL hlocR hlocL,
            rlc_twoChannelFullPhysical_twoArcWallFamily_orderedOutcome
              hfaith hnoGood hzRight hzLeft hxPath hyPath flipLeft qr ql
                hlocR hlocL htable⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hlocalizedL.2)))
      · exact Or.inr (Or.inr (Or.inl hlocalizedR.2))
    · exact Or.inr (Or.inl hnonwallL)
  · exact Or.inl hnonwallR


theorem
    rlc_twoChannelFullPhysical_exactOrderedWallAlternative_of_product
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {z x y ur vr ul vl : Site 2}
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hxOrder : rlc_flipX (rlc_dualReflect x) ∈
      (right.map rlc_flipXLatticeHom).support)
    (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
    (hfirst : ∀ w ∈ right.support,
      rlc_flipX w ∈ rlc_pathVertices gamma'.1 → w = z)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (hproduct : RlcTwoChannelFullPhysicalWallTerminalProductClassification
      gamma gamma' omega (vr := vr) (vl := vl) qr ql) :
    (∃ e ∈ qr.edges,
        Sym2.map rlc_dualReflect e ∉
          rlc_connectorFourTraceEdges gamma gamma') ∨
      (∃ e ∈ ql.edges,
        Sym2.map rlc_dualReflect e ∉
          rlc_connectorFourTraceEdges gamma gamma') ∨
      RlcTwoChannelFullPhysicalRightArcNonExclusiveLocalizedBad
        gamma gamma' omega ur vr ∨
      RlcTwoChannelFullPhysicalLeftArcNonExclusiveLocalizedBad
        gamma gamma' omega ul vl ∨
      RlcTwoChannelFullPhysicalExactOrderedWallTerminalRows
        gamma gamma' omega flipLeft qr ql := by
  rcases hproduct.rightPrefix with hallR | hnonwallR
  · rcases hproduct.leftPrefix with hallL | hnonwallL
    · rcases hproduct.rightTerminal with hlocR | hlocalizedR
      · rcases hproduct.leftTerminal with hlocL | hlocalizedL
        · exact Or.inr (Or.inr (Or.inr (Or.inr
            (rlc_twoChannelFullPhysical_exactOrderedWallTerminalRows
              hfaith hnoGood right flipLeft hzRight hzLeft hxPath hyPath
                hxOrder hyOrder hfirst qr ql
                (hproduct.terminalTable hallR hallL hlocR hlocL)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hlocalizedL.2)))
      · exact Or.inr (Or.inr (Or.inl hlocalizedR.2))
    · exact Or.inr (Or.inl hnonwallL)
  · exact Or.inl hnonwallR


end
end StatMech.Universality
