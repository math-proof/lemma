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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part96
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorPIMSSupportedArc_of_boundaryArc_of_failure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteConnectorEvent gamma gamma')
    (harc : RlcConnectorPIMSBoundaryArc gamma gamma' tau) :
    RlcConnectorPIMSSupportedArc gamma gamma' tau := by
  obtain ⟨x, y, a, hx, hy, htarget⟩ := harc
  let eta := rlc_maskConfig (rlc_connectorEdges gamma gamma')
    (rlc_connectorAmbientMixedConfig gamma gamma' tau)
  let hle := rlc_faceBoundaryGraph_le_openFaceDual gamma gamma'
    (rlc_connectorAmbientMixedConfig gamma gamma' tau)
  let c := rlc_dualReflectOpenWalk eta (a.mapLe hle)
  have hyBox : rlc_dualReflect y ∈
      (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)) :=
    rlc_leftPathVertex_mem_connectorBox gamma' hy
  refine ⟨rlc_dualReflect x, rlc_dualReflect y, c, hx, hy, ?_, htarget, ?_⟩
  · exact rlc_walk_support_mem_connectorBox_of_connectorEdges
      gamma gamma' c hyBox htarget
  · exact rlc_connector_reflectedFaceBoundaryWalk_preimage_not_trace_of_failure
      gamma gamma' tau hno a


theorem rlc_connectorPIMSActualSelectedArc_of_boundaryArc_of_failure
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteConnectorEvent gamma gamma')
    (harc : RlcConnectorPIMSBoundaryArc gamma gamma' tau) :
    RlcConnectorPIMSActualSelectedArc gamma gamma' tau := by
  obtain ⟨x, y, a, hx, hy, htarget⟩ := harc
  let eta := rlc_maskConfig (rlc_connectorEdges gamma gamma')
    (rlc_connectorAmbientMixedConfig gamma gamma' tau)
  let hle := rlc_faceBoundaryGraph_le_openFaceDual gamma gamma'
    (rlc_connectorAmbientMixedConfig gamma gamma' tau)
  let c := rlc_dualReflectOpenWalk eta (a.mapLe hle)
  have hnotTrace : ∀ e ∈ c.edges, rlc_pimsEdgeEquiv e ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 :=
    rlc_connector_reflectedFaceBoundaryWalk_preimage_not_trace_of_failure
      gamma gamma' tau hno a
  have hyBox : rlc_dualReflect y ∈
      (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)) :=
    rlc_leftPathVertex_mem_connectorBox gamma' hy
  refine ⟨rlc_dualReflect x, rlc_dualReflect y, c, hx, hy, ?_,
    htarget, ?_⟩
  · exact rlc_walk_support_mem_connectorBox_of_connectorEdges
      gamma gamma' c hyBox htarget
  · intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        exact rlc_connectorPIMSSourceOpenCase_of_maskedDual_open
          gamma gamma' tau s(u, v) (hnotTrace s(u, v) he)
            (c.adj_of_mem_edges he).2


theorem rlc_connectorPIMSSupportedArc_of_actualSelectedArc {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (harc : RlcConnectorPIMSActualSelectedArc gamma gamma' tau) :
    RlcConnectorPIMSSupportedArc gamma gamma' tau := by
  obtain ⟨x, y, c, hx, hy, hsupp, htarget, hsource⟩ := harc
  exact ⟨x, y, c, hx, hy, hsupp, htarget, fun e he =>
    rlc_connectorPIMSSourceOpenCase_not_trace
      gamma gamma' tau (hsource e he)⟩


theorem rlc_connectorPIMS_openWalk_of_maskedDual_walk {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {x y : Site 2}
    (c : (openSubgraph 2 (rlc_dualReflectConfig
      (rlc_maskConfig (rlc_connectorEdges gamma gamma')
        (rlc_connectorAmbientMixedConfig gamma gamma' tau)))).Walk x y)
    (hsupport : ∀ z ∈ c.support,
      z ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)))
    (htarget : ∀ e ∈ c.edges,
      e ∈ rlc_connectorEdges gamma gamma')
    (hnotTrace : ∀ e ∈ c.edges,
      rlc_pimsEdgeEquiv e ∉
        rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    Nonempty ((FK.openSub (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorPIMSReflectedConfig gamma gamma' tau)).Walk
          ⟨x, hsupport x c.start_mem_support⟩
          ⟨y, hsupport y c.end_mem_support⟩) := by
  let cbox := c.induce
    (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)) hsupport
  refine ⟨cbox.transfer
    (FK.openSub (rlc_connectorFiniteGraph gamma gamma')
      (rlc_connectorPIMSReflectedConfig gamma gamma' tau)) ?_⟩
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      let hom := (SimpleGraph.Embedding.induce
        (G := openSubgraph 2 (rlc_dualReflectConfig
          (rlc_maskConfig (rlc_connectorEdges gamma gamma')
            (rlc_connectorAmbientMixedConfig gamma gamma' tau))))
        (rect (-2 * n) (2 * n) (-n) n : Set (Site 2))).toHom
      have hec : s((u : Site 2), (v : Site 2)) ∈ c.edges := by
        have hmap : s((u : Site 2), (v : Site 2)) ∈
            List.map (Sym2.map hom) cbox.edges :=
          List.mem_map.mpr ⟨s(u, v), he, by rfl⟩
        rw [← SimpleGraph.Walk.edges_map hom cbox] at hmap
        simpa [hom, cbox] using hmap
      have hadj := c.adj_of_mem_edges hec
      rw [SimpleGraph.mem_edgeSet, FK.openSub_adj]
      refine ⟨⟨hadj.1, htarget _ hec⟩, ?_⟩
      exact rlc_connectorPIMSReflectedConfig_open_of_masked_open
        gamma gamma' tau s(u, v)
        (by simpa [Sym2.map_mk] using hnotTrace _ hec)
        (by simpa [Sym2.map_mk] using hadj.2)


theorem rlc_connectorPIMSReflectedConfig_mem_event_of_supportedArc {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (harc : RlcConnectorPIMSSupportedArc gamma gamma' tau) :
    rlc_connectorPIMSReflectedConfig gamma gamma' tau ∈
      rlc_finiteConnectorEvent gamma gamma' := by
  obtain ⟨x, y, c, hx, hy, hsupp, htarget, hnotTrace⟩ := harc
  obtain ⟨cfinite⟩ := rlc_connectorPIMS_openWalk_of_maskedDual_walk
    gamma gamma' tau c hsupp htarget hnotTrace
  exact ⟨⟨x, hsupp x c.start_mem_support⟩,
    ⟨y, hsupp y c.end_mem_support⟩, hx, hy, ⟨cfinite⟩⟩


theorem rlc_connectorPIMSReflectedConfig_mem_event_of_actualSelectedArc
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (harc : RlcConnectorPIMSActualSelectedArc gamma gamma' tau) :
    rlc_connectorPIMSReflectedConfig gamma gamma' tau ∈
      rlc_finiteConnectorEvent gamma gamma' := by
  exact rlc_connectorPIMSReflectedConfig_mem_event_of_supportedArc
    gamma gamma' tau
      (rlc_connectorPIMSSupportedArc_of_actualSelectedArc
        gamma gamma' tau harc)


theorem rlc_traceSplitCounterexample_PIMS_actualSelectedArc :
    RlcConnectorPIMSActualSelectedArc rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft
      rlc_traceSplitCounterexampleFiniteAllClosed := by
  exact rlc_connectorPIMSActualSelectedArc_of_boundaryArc_of_failure
    rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft
    rlc_traceSplitCounterexampleFiniteAllClosed
    rlc_traceSplitCounterexample_finiteAllClosed_failure
    rlc_traceSplitCounterexample_finiteAllClosed_boundaryArc


theorem rlc_traceSplitCounterexample_PIMS_firstEdge_source_exterior :
    let e := s((![0, -1] : Site 2), ![0, 0])
    rlc_pimsEdgeEquiv e ∉ rlc_connectorEdges
        rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft ∧
      rlc_pimsEdgeEquiv e ∉
        rlc_pathEdges rlc_traceSplitCounterexampleRight.1 ∪
          rlc_pathEdges rlc_traceSplitCounterexampleLeft.1 := by
  dsimp only
  have hpims : rlc_pimsEdgeEquiv
      s((![0, -1] : Site 2), ![0, 0]) =
        s((![-1, -1] : Site 2), ![0, -1]) := by
    simpa using rlc_pimsEdgeEquiv_vertical 0 (-1)
  rw [hpims]
  constructor
  · intro he
    rw [rlc_connectorEdges, Finset.mem_filter] at he
    obtain ⟨z, hzRegion, hze⟩ := he.2
    apply rlc_originRegion_not_barrier hzRegion
    rw [Sym2.mem_iff] at hze
    rcases hze with rfl | rfl <;>
      rw [rlc_connectorBarrier,
        rlc_traceSplitCounterexample_right_vertices] <;>
      simp [rlc_flipX, rlc_flipXFun]
  · intro he
    rcases Finset.mem_union.mp he with hright | hleft
    · have hends := rlc_pathEdge_endpoints_mem_vertices
        rlc_traceSplitCounterexampleRight.1 hright
      rw [rlc_traceSplitCounterexample_right_vertices] at hends
      simp at hends
    · have hends := rlc_pathEdge_endpoints_mem_vertices
        rlc_traceSplitCounterexampleLeft.1 hleft
      rw [rlc_traceSplitCounterexample_left_vertices] at hends
      simp at hends

theorem rlc_traceSplitCounterexample_PIMS_success_via_boundaryArc :
    rlc_connectorPIMSReflectedConfig rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft
        rlc_traceSplitCounterexampleFiniteAllClosed ∈
      rlc_finiteConnectorEvent rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft := by
  apply rlc_connectorPIMSReflectedConfig_mem_event_of_actualSelectedArc
    rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft
    rlc_traceSplitCounterexampleFiniteAllClosed
  exact rlc_traceSplitCounterexample_PIMS_actualSelectedArc


theorem rlc_connectorPIMSReflectedConfig_mem_event_of_filledBoundary
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteConnectorEvent gamma gamma')
    (hcontacts : RlcConnectorPIMSFilledBoundaryContacts gamma gamma' tau)
    (htarget : RlcConnectorPIMSFilledBoundaryTargetSupported gamma gamma' tau) :
    rlc_connectorPIMSReflectedConfig gamma gamma' tau ∈
      rlc_finiteConnectorEvent gamma gamma' := by
  apply rlc_connectorPIMSReflectedConfig_mem_event_of_supportedArc
    gamma gamma' tau
  apply rlc_connectorPIMSSupportedArc_of_boundaryArc_of_failure
    gamma gamma' tau hno
  exact rlc_connectorPIMSBoundaryArc_of_filledBoundary
    gamma gamma' tau hcontacts htarget


theorem rlc_finiteConnectorEvent_isIncreasing {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    IsIncreasing (rlc_finiteConnectorEvent gamma gamma') := by
  intro omega tau hot
  rintro ⟨x, y, hx, hy, hxy⟩
  refine ⟨x, y, hx, hy, hxy.mono ?_⟩
  intro u v huv
  rw [FK.openSub_adj] at huv ⊢
  exact ⟨huv.1, hot _ huv.2⟩


end
end StatMech.Universality
