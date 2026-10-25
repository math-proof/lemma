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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part23
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_extremalSelection_one_zero_mem_originRegion :
    (![1, 0] : Site 2) ∈ rlc_connectorOriginRegion
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
  rw [rlc_connectorOriginRegion]
  simp only [Set.Finite.mem_toFinset]
  let z : Site 2 := ![1, 0]
  have hz : z ∈ rlc_connectorAllowed rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft := by
    rw [rlc_connectorAllowed, Finset.mem_sdiff]
    constructor
    · simp [z, rlc_connectorBox, mem_rect]
    · rw [rlc_connectorBarrier,
        rlc_traceSplitCounterexample_right_vertices,
        rlc_traceSplitCounterexample_left_vertices]
      simp [z, rlc_flipX, rlc_flipXFun]
  have ho : origin 2 ∈ rlc_connectorAllowed
      rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft := by
    rw [rlc_connectorAllowed, Finset.mem_sdiff]
    constructor
    · simp [rlc_connectorBox, mem_rect, origin]
    · rw [show origin 2 = (![0, 0] : Site 2) by
        ext i
        fin_cases i <;> rfl]
      rw [rlc_connectorBarrier,
        rlc_traceSplitCounterexample_right_vertices,
        rlc_traceSplitCounterexample_left_vertices]
      simp [rlc_flipX, rlc_flipXFun]
  refine ⟨hz, ho, ?_⟩
  exact (show ((hypercubicLattice 2).induce
      (rlc_connectorAllowed rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft : Set (Site 2))).Adj
      ⟨origin 2, ho⟩ ⟨z, hz⟩ by
        change (hypercubicLattice 2).Adj (origin 2) z
        simp [z, hypercubicLattice_adj, Fin.sum_univ_two, origin]).reachable

theorem rlc_extremalSelection_bad_target_mem_connectorEdges :
    s((![1, 0] : Site 2), ![2, 0]) ∈ rlc_connectorEdges
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
  rw [rlc_connectorEdges, Finset.mem_filter]
  constructor
  · rw [mem_edgesWithinFinset]
    exact ⟨![1, 0], by simp [rlc_connectorBox, mem_rect],
      ![2, 0], by simp [rlc_connectorBox, mem_rect], rfl⟩
  · exact ⟨![1, 0], rlc_extremalSelection_one_zero_mem_originRegion,
      Sym2.mem_mk_left _ _⟩

theorem rlc_extremalSelection_bad_source_not_connectorEdges :
    s((![-2, -1] : Site 2), ![-2, 0]) ∉ rlc_connectorEdges
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
  intro hsource
  rw [rlc_connectorEdges, Finset.mem_filter] at hsource
  obtain ⟨z, hzRegion, hzEdge⟩ := hsource.2
  have hzSet : z ∈ rlc_connectorOriginRegionSet
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
    simpa [rlc_connectorOriginRegion] using hzRegion
  obtain ⟨hzAllowed, _ho, _hreach⟩ := hzSet
  have hzNotBarrier := (Finset.mem_sdiff.mp hzAllowed).2
  rw [Sym2.mem_iff] at hzEdge
  rcases hzEdge with rfl | rfl
  · apply hzNotBarrier
    rw [rlc_connectorBarrier,
      rlc_traceSplitCounterexample_right_vertices,
      rlc_traceSplitCounterexample_left_vertices]
    simp [rlc_flipX, rlc_flipXFun]
  · apply hzNotBarrier
    rw [rlc_connectorBarrier,
      rlc_traceSplitCounterexample_right_vertices,
      rlc_traceSplitCounterexample_left_vertices]
    simp [rlc_flipX, rlc_flipXFun]

theorem rlc_extremalSelection_bad_source_not_traceEdges :
    s((![-2, -1] : Site 2), ![-2, 0]) ∉
      rlc_pathEdges rlc_traceSplitCounterexampleRight.1 ∪
        rlc_pathEdges rlc_traceSplitCounterexampleLeft.1 := by
  intro hsource
  rcases Finset.mem_union.mp hsource with hright | hleft
  · have hends := rlc_pathEdge_endpoints_mem_vertices
      rlc_traceSplitCounterexampleRight.1 hright
    rw [rlc_traceSplitCounterexample_right_vertices] at hends
    simp at hends
  · have hends := rlc_pathEdge_endpoints_mem_vertices
      rlc_traceSplitCounterexampleLeft.1 hleft
    rw [rlc_traceSplitCounterexample_left_vertices] at hends
    simp at hends


theorem rlc_extremalSelection_exterior_badEdge :
    (rlc_connectorPIMSExteriorGraph
      rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft).Adj
        rlc_extremalSelectionExteriorBadX
        rlc_extremalSelectionExteriorBadY ∧
      ¬ ((rlc_connectorOnRight rlc_traceSplitCounterexampleRight
            rlc_extremalSelectionExteriorBadX ∧
          rlc_connectorOnRight rlc_traceSplitCounterexampleRight
            rlc_extremalSelectionExteriorBadY) ∨
        (rlc_connectorOnLeft rlc_traceSplitCounterexampleLeft
            rlc_extremalSelectionExteriorBadX ∧
          rlc_connectorOnLeft rlc_traceSplitCounterexampleLeft
            rlc_extremalSelectionExteriorBadY)) := by
  constructor
  · refine ⟨⟨?_, rlc_extremalSelection_bad_target_mem_connectorEdges⟩,
      ?_, ?_⟩
    · simp [rlc_extremalSelectionExteriorBadX,
        rlc_extremalSelectionExteriorBadY, hypercubicLattice_adj,
        Fin.sum_univ_two]
    · simpa [rlc_extremalSelectionExteriorBadX,
        rlc_extremalSelectionExteriorBadY, Sym2.map_mk,
        rlc_pimsEdgeEquiv_horizontal] using
          rlc_extremalSelection_bad_source_not_connectorEdges
    · simpa [rlc_extremalSelectionExteriorBadX,
        rlc_extremalSelectionExteriorBadY, Sym2.map_mk,
        rlc_pimsEdgeEquiv_horizontal] using
          rlc_extremalSelection_bad_source_not_traceEdges
  · rintro (⟨hx, _hy⟩ | ⟨hx, _hy⟩)
    · change (![1, 0] : Site 2) ∈
        rlc_pathVertices rlc_traceSplitCounterexampleRight.1 at hx
      rw [rlc_traceSplitCounterexample_right_vertices] at hx
      simp at hx
    · change (![1, 0] : Site 2) ∈
        rlc_pathVertices rlc_traceSplitCounterexampleLeft.1 at hx
      rw [rlc_traceSplitCounterexample_left_vertices] at hx
      simp at hx


theorem not_rlc_connectorPIMSExtremalSelectionExteriorLocality :
    ¬ RlcConnectorPIMSExtremalSelectionExteriorLocality 1 := by
  rw [not_rlc_connectorPIMSExtremalSelectionExteriorLocality_iff]
  exact ⟨(rlc_traceSplitCounterexampleRight,
      rlc_traceSplitCounterexampleLeft),
    rlc_extremalSelectionCounterexampleConfig,
    rlc_extremalSelectionExteriorBadX,
    rlc_extremalSelectionExteriorBadY,
    rlc_extremalSelection_extremalPairCandidate,
    rlc_extremalSelection_exterior_badEdge.1,
    rlc_extremalSelection_exterior_badEdge.2⟩


theorem rlc_connectorPIMSExteriorGraph_le_separateWiring_of_extremalSelection
    {n : Int}
    (hselection : RlcConnectorPIMSExtremalSelectionExteriorLocality n)
    (pair : RlcDiagonalPathPair n)
    {omega : ConfigSpace (Sym2 (Site 2))}
    (hpair : omega ∈ rlc_extremalPairCandidate pair) :
    rlc_connectorPIMSExteriorGraph pair.1 pair.2 ≤
      rlc_connectorSeparateWiring pair.1 pair.2 :=
  (rlc_connectorPIMSExteriorTraceLocal_iff_le_separateWiring
    pair.1 pair.2).mp (hselection pair ⟨omega, hpair⟩)


end
end StatMech.Universality
