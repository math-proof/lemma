/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWContactFreeSourceArc
import Theorem.StatisticalMechanics.Code.Universality.RSWAxisOrContactObstruction.Part2
import Def.StatisticalMechanics.Code.Universality.RSWSourceArcPlacement.Part4
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


@[simp] theorem rlc_traceSplitCounterexample_boundaryArc_edges
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hK : rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2))) :
    (rlc_traceSplitCounterexample_boundaryArc omega hK).edges =
      [s((![-1, -2] : Site 2), ![-1, -1]),
        s((![-1, -1] : Site 2), ![0, -1]),
        s((![0, -1] : Site 2), ![1, -1])] := by
  rfl

theorem rlc_traceSplitCounterexample_boundaryArc_rightContact :
    rlc_dualReflect (![-1, -2] : Site 2) ∈
      rlc_pathVertices rlc_traceSplitCounterexampleRight.1 := by
  rw [rlc_traceSplitCounterexample_right_vertices]
  simp [rlc_dualReflect, rlc_dualReflectFun]

theorem rlc_traceSplitCounterexample_boundaryArc_leftContact :
    rlc_dualReflect (![1, -1] : Site 2) ∈
      rlc_pathVertices rlc_traceSplitCounterexampleLeft.1 := by
  rw [rlc_traceSplitCounterexample_left_vertices]
  simp [rlc_dualReflect, rlc_dualReflectFun]

theorem rlc_traceSplitCounterexample_one_zero_mem_axisGapRegion :
    (![1, 0] : Site 2) ∈
      rlc_axisGapRegion rlc_windingSideCounterexampleGap := by
  let G := rlc_windingSideCounterexampleGap
  let A := rlc_connectorAllowed rlc_traceSplitCounterexampleRight
    rlc_traceSplitCounterexampleLeft
  have hseed : G.seedVertex ∈ A :=
    G.seedVertex_mem_allowed_of_lt (by norm_num) (by
      change (-1 : ℤ) + 1 < 1
      omega)
  have hz : (![1, 0] : Site 2) ∈ A := by
    rw [show A = rlc_connectorAllowed rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft by rfl]
    rw [rlc_connectorAllowed, Finset.mem_sdiff]
    constructor
    · simp [rlc_connectorBox, mem_rect]
    · rw [rlc_connectorBarrier,
        rlc_traceSplitCounterexample_right_vertices,
        rlc_traceSplitCounterexample_left_vertices]
      simp [rlc_flipX, rlc_flipXFun]
  have hadj :
      ((hypercubicLattice 2).induce (A : Set (Site 2))).Adj
        ⟨G.seedVertex, by simpa using hseed⟩
        ⟨![1, 0], by simpa using hz⟩ := by
    change (hypercubicLattice 2).Adj G.seedVertex (![1, 0] : Site 2)
    simp [G, RlcAxisBarrierGap.seedVertex,
      rlc_windingSideCounterexampleGap, hypercubicLattice_adj,
      Fin.sum_univ_two]
  have hzSet : (![1, 0] : Site 2) ∈ rlc_axisGapRegionSet G :=
    ⟨hz, hseed, hadj.reachable⟩
  simpa [G, rlc_axisGapRegion] using hzSet

theorem rlc_traceSplitCounterexample_right_first_edge :
    s((![0, -1] : Site 2), ![1, -1]) ∈
      rlc_pathEdges rlc_traceSplitCounterexampleRight.1 := by
  let W := rlc_ambientCrossingWalk rlc_traceSplitCounterexampleRight.1
  have hstart : (rlc_traceSplitCounterexampleRight.1.1 : Site 2) =
      ![0, -1] := by
    have hmem : (rlc_traceSplitCounterexampleRight.1.1 : Site 2) ∈
        rlc_pathVertices rlc_traceSplitCounterexampleRight.1 :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
        rlc_traceSplitCounterexampleRight.1 _).mp
          (rlc_ambientCrossingWalk
            rlc_traceSplitCounterexampleRight.1).start_mem_support
    have hx : (rlc_traceSplitCounterexampleRight.1.1 : Site 2) 0 = 0 := by
      have hside := rlc_traceSplitCounterexampleRight.1.1.2
      rw [mem_leftSide] at hside
      exact hside.2
    rw [rlc_traceSplitCounterexample_right_vertices] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hmem | hmem | hmem | hmem
    · exact hmem
    · rw [hmem] at hx
      simp at hx
    · rw [hmem] at hx
      simp at hx
    · rw [hmem] at hx
      simp at hx
  have hnil : ¬ W.Nil := by
    apply SimpleGraph.Walk.not_nil_of_ne
    intro heq
    have hxStart : (rlc_traceSplitCounterexampleRight.1.1 : Site 2) 0 = 0 := by
      have hside := rlc_traceSplitCounterexampleRight.1.1.2
      rw [mem_leftSide] at hside
      exact hside.2
    have hxEnd : (rlc_traceSplitCounterexampleRight.1.2.1 : Site 2) 0 = 2 := by
      have hside := rlc_traceSplitCounterexampleRight.1.2.1.2
      rw [mem_rightSide] at hside
      simpa using hside.2
    have hxEq := congrArg (fun z : Site 2 => z 0) heq
    have : (0 : ℤ) = 2 := hxStart.symm.trans (hxEq.trans hxEnd)
    norm_num at this
  have hsndSupport : W.snd ∈ W.support :=
    List.mem_of_mem_tail (W.snd_mem_tail_support hnil)
  have hsndVertices : W.snd ∈
      rlc_pathVertices rlc_traceSplitCounterexampleRight.1 :=
    rlc_ambientCrossingWalk_support_mem_pathVertices
      rlc_traceSplitCounterexampleRight.1 hsndSupport
  rw [rlc_traceSplitCounterexample_right_vertices] at hsndVertices
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsndVertices
  have hadj := W.adj_snd hnil
  change (hypercubicLattice 2).Adj
    (rlc_traceSplitCounterexampleRight.1.1 : Site 2) W.snd at hadj
  have hadj0 : (hypercubicLattice 2).Adj
      (![0, -1] : Site 2) W.snd := by
    simpa only [hstart] using hadj
  have hsnd : W.snd = (![1, -1] : Site 2) := by
    rcases hsndVertices with hsnd | hsnd | hsnd | hsnd
    · rw [hsnd] at hadj0
      simp at hadj0
    · exact hsnd
    · rw [hsnd, hypercubicLattice_adj, Fin.sum_univ_two] at hadj0
      norm_num at hadj0
    · rw [hsnd, hypercubicLattice_adj, Fin.sum_univ_two] at hadj0
      norm_num at hadj0
  have he := W.mk_start_snd_mem_edges hnil
  change s((rlc_traceSplitCounterexampleRight.1.1 : Site 2), W.snd) ∈
    W.edges at he
  have he' : s((![0, -1] : Site 2), ![1, -1]) ∈ W.edges := by
    simpa only [hstart, hsnd] using he
  exact rlc_ambientCrossingWalk_edge_mem_pathEdges
    rlc_traceSplitCounterexampleRight.1 he'

theorem rlc_traceSplitCounterexample_boundaryArc_relaxed₀₁ :
    rlc_contourEdgeRelaxedLocal rlc_windingSideCounterexampleGap
      (![-1, -2] : Site 2) ![-1, -1] := by
  unfold rlc_contourEdgeRelaxedLocal
  right
  constructor
  · unfold rlc_reflectedTargetLocallySupported
    right
    left
    change rlc_edgeBoxIncidentGap rlc_windingSideCounterexampleGap
      s((![0, -1] : Site 2), ![0, 0])
    constructor
    · intro z hz
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl <;> simp [mem_rect]
    · refine ⟨![0, 0], ?_, by simp⟩
      simpa [RlcAxisBarrierGap.seedVertex,
        rlc_windingSideCounterexampleGap] using
          (rlc_windingSideCounterexampleGap.seedVertex_mem_region_of_lt
            (by norm_num) (by change (-1 : ℤ) + 1 < 1; omega))
  · unfold rlc_boundarySourceLocallySupported
    right
    left
    unfold rlc_reflectedPathEdges
    rw [Finset.mem_image]
    refine ⟨s((![0, -1] : Site 2), ![1, -1]), ?_, ?_⟩
    · exact rlc_traceSplitCounterexample_right_first_edge
    · simp [sharedPrimalEdge, Sym2.map_mk, rlc_flipX, rlc_flipXFun]

theorem rlc_traceSplitCounterexample_boundaryArc_relaxed₁₂ :
    rlc_contourEdgeRelaxedLocal rlc_windingSideCounterexampleGap
      (![-1, -1] : Site 2) ![0, -1] := by
  unfold rlc_contourEdgeRelaxedLocal
  right
  constructor
  · unfold rlc_reflectedTargetLocallySupported
    right
    left
    change rlc_edgeBoxIncidentGap rlc_windingSideCounterexampleGap
      s((![0, 0] : Site 2), ![1, 0])
    constructor
    · intro z hz
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl <;> simp [mem_rect]
    · refine ⟨![0, 0], ?_, by simp⟩
      simpa [RlcAxisBarrierGap.seedVertex,
        rlc_windingSideCounterexampleGap] using
          (rlc_windingSideCounterexampleGap.seedVertex_mem_region_of_lt
            (by norm_num) (by change (-1 : ℤ) + 1 < 1; omega))
  · unfold rlc_boundarySourceLocallySupported
    left
    change rlc_edgeBoxIncidentGap rlc_windingSideCounterexampleGap
      s((![0, -1] : Site 2), ![0, 0])
    constructor
    · intro z hz
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl <;> simp [mem_rect]
    · refine ⟨![0, 0], ?_, by simp⟩
      simpa [RlcAxisBarrierGap.seedVertex,
        rlc_windingSideCounterexampleGap] using
          (rlc_windingSideCounterexampleGap.seedVertex_mem_region_of_lt
            (by norm_num) (by change (-1 : ℤ) + 1 < 1; omega))

theorem rlc_traceSplitCounterexample_boundaryArc_relaxed₂₃ :
    rlc_contourEdgeRelaxedLocal rlc_windingSideCounterexampleGap
      (![0, -1] : Site 2) ![1, -1] := by
  unfold rlc_contourEdgeRelaxedLocal
  right
  constructor
  · unfold rlc_reflectedTargetLocallySupported
    right
    left
    change rlc_edgeBoxIncidentGap rlc_windingSideCounterexampleGap
      s((![1, 0] : Site 2), ![2, 0])
    constructor
    · intro z hz
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl <;> simp [mem_rect]
    · exact ⟨![1, 0],
        rlc_traceSplitCounterexample_one_zero_mem_axisGapRegion, by simp⟩
  · unfold rlc_boundarySourceLocallySupported
    left
    change rlc_edgeBoxIncidentGap rlc_windingSideCounterexampleGap
      s((![1, -1] : Site 2), ![1, 0])
    constructor
    · intro z hz
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl <;> simp [mem_rect]
    · exact ⟨![1, 0],
        rlc_traceSplitCounterexample_one_zero_mem_axisGapRegion, by simp⟩

theorem rlc_traceSplitCounterexample_boundaryArc_relaxed
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hK : rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2))) :
    ∀ {f g : Site 2},
      s(f, g) ∈
          (rlc_traceSplitCounterexample_boundaryArc omega hK).edges →
        rlc_contourEdgeRelaxedLocal
          rlc_windingSideCounterexampleGap f g := by
  intro f g hfg
  rw [rlc_traceSplitCounterexample_boundaryArc_edges] at hfg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfg
  rcases hfg with hfg | hfg | hfg
  · exact rlc_contourEdgeRelaxedLocal_of_mk_eq
      rlc_windingSideCounterexampleGap (latAdj_top (-1) (-2)) hfg
        rlc_traceSplitCounterexample_boundaryArc_relaxed₀₁
  · exact rlc_contourEdgeRelaxedLocal_of_mk_eq
      rlc_windingSideCounterexampleGap (latAdj_right (-1) (-1)) hfg
        rlc_traceSplitCounterexample_boundaryArc_relaxed₁₂
  · exact rlc_contourEdgeRelaxedLocal_of_mk_eq
      rlc_windingSideCounterexampleGap (latAdj_right 0 (-1)) hfg
        rlc_traceSplitCounterexample_boundaryArc_relaxed₂₃


theorem rlc_traceSplitCounterexample_not_defectCut_of_reachSet_eq
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hK : rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2))) :
    ¬ RlcRelaxedLocalDefectsSeparateTraces
      rlc_windingSideCounterexampleGap omega := by
  intro hcut
  let a := rlc_traceSplitCounterexample_boundaryArc omega hK
  obtain ⟨f, g, hfg, hbad⟩ := hcut a
    rlc_traceSplitCounterexample_boundaryArc_rightContact
    rlc_traceSplitCounterexample_boundaryArc_leftContact
  exact hbad (rlc_traceSplitCounterexample_boundaryArc_relaxed omega hK hfg)


theorem rlc_windingSideCounterexample_not_defectCut :
    ¬ RlcRelaxedLocalDefectsSeparateTraces
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig :=
  rlc_traceSplitCounterexample_not_defectCut_of_reachSet_eq
    rlc_windingSideCounterexampleConfig
    rlc_windingSideCounterexample_reachSet_eq


theorem rlc_axisOrContactCounterexample_not_defectCut :
    ¬ RlcRelaxedLocalDefectsSeparateTraces
      rlc_windingSideCounterexampleGap
      rlc_axisOrContactCounterexampleConfig :=
  rlc_traceSplitCounterexample_not_defectCut_of_reachSet_eq
    rlc_axisOrContactCounterexampleConfig
    rlc_axisOrContactCounterexample_reachSet_eq


theorem rlc_axisOrContactCounterexample_dual_success :
    rlc_dualReflectConfig rlc_axisOrContactCounterexampleConfig ∈
      rlc_mixedWiredConnectorEvent rlc_windingSideCounterexampleGap := by
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_not_defectCut
    rlc_windingSideCounterexampleGap (by norm_num)
      (by change (-1 : ℤ) + 1 < 1; omega)
      rlc_axisOrContactCounterexampleConfig
      rlc_axisOrContactCounterexample_not_defectCut

end Universality
end StatMech
