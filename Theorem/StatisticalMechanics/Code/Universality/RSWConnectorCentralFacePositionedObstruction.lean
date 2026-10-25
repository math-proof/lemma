/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFacePositionedObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceScaleOneAudit.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem wall_right :
    s((![1, 0] : Site 2), ![1, 1]) ∈
      rlc_connectorFourTraceEdges rlc_traceSplitCounterexampleRight
        rlc_axisReturnCounterexampleLeft := by
  rw [rlc_connectorFourTraceEdges]
  apply Finset.mem_union_right
  rw [rlc_connectorReflectedTraceEdges, Finset.mem_union]
  right
  rw [rlc_reflectedPathEdges]
  apply Finset.mem_image.mpr
  refine ⟨s((![-1, 0] : Site 2), ![-1, 1]), ?_, ?_⟩
  · rw [rlc_axisReturnCounterexample_left_edges]
    simp
  · simp [rlc_flipX, rlc_flipXFun, Sym2.map_mk]

theorem wall_left :
    s((![0, 0] : Site 2), ![0, 1]) ∈
      rlc_connectorFourTraceEdges rlc_traceSplitCounterexampleRight
        rlc_axisReturnCounterexampleLeft := by
  rw [rlc_connectorFourTraceEdges]
  apply Finset.mem_union_left
  rw [Finset.mem_union]
  right
  rw [rlc_axisReturnCounterexample_left_edges]
  simp

theorem wall_bottom :
    s((![0, 0] : Site 2), ![1, 0]) ∈
      rlc_connectorFourTraceEdges rlc_traceSplitCounterexampleRight
        rlc_axisReturnCounterexampleLeft := by
  rw [rlc_connectorFourTraceEdges]
  apply Finset.mem_union_right
  rw [rlc_connectorReflectedTraceEdges, Finset.mem_union]
  right
  rw [rlc_reflectedPathEdges]
  apply Finset.mem_image.mpr
  refine ⟨s((![-1, 0] : Site 2), ![0, 0]), ?_, ?_⟩
  · rw [rlc_axisReturnCounterexample_left_edges]
    simp
  · simpa [rlc_flipX, rlc_flipXFun, Sym2.map_mk] using
      (Sym2.eq_swap : s((![1, 0] : Site 2), ![0, 0]) =
        s(![0, 0], ![1, 0]))

theorem isolated (z : RlcConnectorFaceVertex 1) :
    ¬ (rlc_connectorFiniteFaceCutGraph rlc_traceSplitCounterexampleRight
      rlc_axisReturnCounterexampleLeft).Adj
        ⟨rlc_connectorCentralFace,
          rlc_connectorCentralFace_mem_faceBox (by norm_num)⟩ z := by
  intro h
  change (rlc_connectorFourTraceFaceCutGraph
    rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft).Adj
      rlc_connectorCentralFace (z : Site 2) at h
  rw [rlc_connectorFourTraceFaceCutGraph_adj] at h
  rcases face_adj_dir h.1 with hz | hz | hz | hz
  · have : (z : Site 2) = ![1, 0] := by simpa [rlc_connectorCentralFace] using hz
    rw [this] at h
    apply h.2
    simpa [rlc_connectorCentralFace, sharedPrimalEdge] using wall_right
  · have : (z : Site 2) = ![-1, 0] := by simpa [rlc_connectorCentralFace] using hz
    rw [this] at h
    apply h.2
    simpa [rlc_connectorCentralFace, sharedPrimalEdge] using wall_left
  · have : (z : Site 2) = ![0, 1] := by simpa [rlc_connectorCentralFace] using hz
    have hzbox := z.2
    rw [this] at hzbox
    simp [rlc_connectorFaceBox, mem_rect] at hzbox
  · have : (z : Site 2) = ![0, -1] := by simpa [rlc_connectorCentralFace] using hz
    rw [this] at h
    apply h.2
    simpa [rlc_connectorCentralFace, sharedPrimalEdge] using wall_bottom

theorem rlc_axisReturnCounterexample_centralFaceRegion_eq_singleton :
    rlc_connectorCentralFaceRegion rlc_traceSplitCounterexampleRight
      rlc_axisReturnCounterexampleLeft = {rlc_connectorCentralFace} := by
  ext f
  constructor
  · intro hf
    have hfset : f ∈ rlc_connectorCentralFaceRegionSet
        rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft := by
      simpa [rlc_connectorCentralFaceRegion] using hf
    obtain ⟨hfb, hsb, hreach⟩ := hfset
    obtain ⟨w⟩ := hreach
    cases w with
    | nil => simp
    | cons hfirst _ => exact False.elim (isolated _ hfirst)
  · intro hf
    simp only [Finset.mem_singleton] at hf
    subst f
    exact rlc_connectorCentralFace_mem_region _ _ (by norm_num)

end
end StatMech.Universality
