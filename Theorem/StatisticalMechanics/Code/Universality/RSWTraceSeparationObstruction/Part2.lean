/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceSeparationObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWTraceSeparation.Part3
import Def.StatisticalMechanics.Code.Universality.RSWTraceSeparationObstruction.Part2
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

theorem rlc_traceSplitCounterexample_right_vertices :
    rlc_pathVertices rlc_traceSplitCounterexampleRight.1 =
      {![0, -1], ![1, -1], ![2, -1], ![2, 0]} := by
  simp [rlc_traceSplitCounterexampleRight, rlc_pathVertices,
    tsc_walk, tsc_v0, tsc_v1, tsc_v2, tsc_v3,
    SimpleGraph.Walk.toPath, SimpleGraph.Walk.bypass]


theorem rlc_traceSplitCounterexample_right_edges :
    rlc_pathEdges rlc_traceSplitCounterexampleRight.1 =
      {s((![0, -1] : Site 2), ![1, -1]),
        s((![1, -1] : Site 2), ![2, -1]),
        s((![2, -1] : Site 2), ![2, 0])} := by
  simp [rlc_traceSplitCounterexampleRight, rlc_pathEdges,
    tsc_walk, tsc_v0, tsc_v1, tsc_v2, tsc_v3,
    SimpleGraph.Walk.toPath, SimpleGraph.Walk.bypass]


theorem rlc_traceSplitCounterexample_left_vertices :
    rlc_pathVertices rlc_traceSplitCounterexampleLeft.1 =
      {![-2, 0], ![-2, 1], ![-1, 1], ![0, 1]} := by
  rw [show rlc_traceSplitCounterexampleLeft =
      rlc_rot180RightPath rlc_traceSplitCounterexampleRight by rfl,
    rlc_pathVertices_rot180RightPath,
    rlc_traceSplitCounterexample_right_vertices]
  ext z
  simp [rlc_rot180, rlc_rot180Fun, or_comm, or_left_comm]


theorem rlc_traceSplitCounterexample_left_edges :
    rlc_pathEdges rlc_traceSplitCounterexampleLeft.1 =
      {s((![-2, 0] : Site 2), ![-2, 1]),
        s((![-2, 1] : Site 2), ![-1, 1]),
        s((![-1, 1] : Site 2), ![0, 1])} := by
  rw [show rlc_traceSplitCounterexampleLeft =
      rlc_rot180RightPath rlc_traceSplitCounterexampleRight by rfl,
    rlc_pathEdges_rot180RightPath,
    rlc_traceSplitCounterexample_right_edges]
  ext e
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨a, (rfl | rfl | rfl), rfl⟩
    all_goals
      simp [rlc_rot180, rlc_rot180Fun, Sym2.map_mk,
        Sym2.eq_iff, site2_eq]
  · rintro (rfl | rfl | rfl)
    · exact ⟨s((![2, -1] : Site 2), ![2, 0]), by simp,
        by
          simpa [rlc_rot180, rlc_rot180Fun, Sym2.map_mk] using
            (Sym2.eq_swap : s((![-2, 1] : Site 2), ![-2, 0]) =
              s(![-2, 0], ![-2, 1]))⟩
    · exact ⟨s((![1, -1] : Site 2), ![2, -1]), by simp,
        by
          simpa [rlc_rot180, rlc_rot180Fun, Sym2.map_mk] using
            (Sym2.eq_swap : s((![-1, 1] : Site 2), ![-2, 1]) =
              s(![-2, 1], ![-1, 1]))⟩
    · exact ⟨s((![0, -1] : Site 2), ![1, -1]), by simp,
        by
          simpa [rlc_rot180, rlc_rot180Fun, Sym2.map_mk] using
            (Sym2.eq_swap : s((![0, 1] : Site 2), ![-1, 1]) =
              s(![-1, 1], ![0, 1]))⟩


theorem rlc_traceSplitCounterexample_right_preimage_avoids_traces
    {x : Site 2}
    (hx : x ∈ rlc_pathVertices rlc_traceSplitCounterexampleRight.1) :
    rlc_primalDualReflect.symm x ∉
        rlc_pathVertices rlc_traceSplitCounterexampleRight.1 ∧
      rlc_primalDualReflect.symm x ∉
        rlc_pathVertices rlc_traceSplitCounterexampleLeft.1 := by
  rw [rlc_traceSplitCounterexample_right_vertices] at hx ⊢
  rw [rlc_traceSplitCounterexample_left_vertices]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with rfl | rfl | rfl | rfl <;>
    simp [rlc_primalDualReflect, rlc_primalDualReflectInvFun]


theorem rlc_tracePreimagesSplit_counterexample_right :
    ¬ RlcTracePreimagesSplit rlc_traceSplitCounterexampleRight.1
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
  rintro ⟨x, hx, y, hy, hxy⟩
  obtain ⟨hxRight, hxLeft⟩ :=
    rlc_traceSplitCounterexample_right_preimage_avoids_traces hx
  obtain ⟨hyRight, hyLeft⟩ :=
    rlc_traceSplitCounterexample_right_preimage_avoids_traces hy
  rcases hxy with hxy | hxy
  · exact hxRight hxy.1
  · exact hxLeft hxy.1


theorem rlc_lowestHighestTracePreimageSplit_counterexample :
    ¬ RlcLowestHighestTracePreimageSplit
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
  intro h
  exact rlc_tracePreimagesSplit_counterexample_right h.1

end Universality
end StatMech
