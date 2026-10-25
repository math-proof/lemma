/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part85
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_adaptiveConnectorEvent_measurableSet {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    MeasurableSet (rlc_adaptiveConnectorEvent gamma gamma') := by
  unfold rlc_adaptiveConnectorEvent
  split
  · exact MeasurableSet.univ
  · exact rlc_axisGapConnectorEvent_measurableSet _

theorem rlc_adaptiveConnectorEvent_eq_univ_of_not_disjoint {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hdisj : ¬ Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
    rlc_adaptiveConnectorEvent gamma gamma' = Set.univ := by
  rw [rlc_adaptiveConnectorEvent,
    rlc_axisBarrierGap?_eq_none_of_not_disjoint gamma gamma' hdisj]

theorem rlc_adaptiveConnectorEvent_eq_gap_of_some {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (G : RlcAxisBarrierGap gamma gamma')
    (hG : rlc_axisBarrierGap? gamma gamma' = some G) :
    rlc_adaptiveConnectorEvent gamma gamma' = rlc_axisGapConnectorEvent G := by
  rw [rlc_adaptiveConnectorEvent, hG]

theorem rlc_axisGapRegion_not_barrier {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'} {z : Site 2}
    (hz : z ∈ rlc_axisGapRegion G) :
    z ∉ rlc_connectorBarrier gamma gamma' := by
  have hzset : z ∈ rlc_axisGapRegionSet G := by
    simpa [rlc_axisGapRegion] using hz
  obtain ⟨hzAllowed, _hs, _hreach⟩ := hzset
  exact (Finset.mem_sdiff.mp hzAllowed).2

theorem RlcAxisBarrierGap.seedVertex_not_right_of_disjoint {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
    G.seedVertex ∉ rlc_pathVertices gamma.1 := by
  intro hseed
  have hab := G.lower_lt_upper
  have hle : G.lower + 1 ≤ G.upper := by omega
  rcases hle.eq_or_lt with heq | hlt
  · have hseedLeft : G.seedVertex ∈ rlc_pathVertices gamma'.1 := by
      have hu := (rlc_mem_axisHeights_iff
        (rlc_pathVertices gamma'.1) G.upper).mp G.upper_mem
      simpa [RlcAxisBarrierGap.seedVertex, heq] using hu
    exact (Finset.disjoint_left.mp hdisj) hseed hseedLeft
  · have hnotBarrier := G.seedVertex_not_barrier_of_lt hlt
    apply hnotBarrier
    simp [rlc_connectorBarrier, hseed]

theorem RlcAxisBarrierGap.firstEdge_not_mem_rightPath_of_disjoint {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
    G.firstEdge ∉ rlc_pathEdges gamma.1 := by
  intro he
  have he' : s(G.lowerVertex, G.seedVertex) ∈ rlc_pathEdges gamma.1 := by
    simpa [RlcAxisBarrierGap.firstEdge] using he
  exact G.seedVertex_not_right_of_disjoint hdisj
    (rlc_pathEdge_endpoints_mem_vertices gamma.1 he').2

theorem RlcAxisBarrierGap.firstEdge_not_mem_leftPath_of_disjoint {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
    G.firstEdge ∉ rlc_pathEdges gamma'.1 := by
  intro he
  have he' : s(G.lowerVertex, G.seedVertex) ∈ rlc_pathEdges gamma'.1 := by
    simpa [RlcAxisBarrierGap.firstEdge] using he
  exact (Finset.disjoint_left.mp hdisj) G.lowerVertex_mem_right
    (rlc_pathEdge_endpoints_mem_vertices gamma'.1 he').1

theorem rlc_rightPathEdges_disjoint_axisGapEdges {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
    Disjoint (rlc_pathEdges gamma.1) (rlc_axisGapEdges G) := by
  rw [Finset.disjoint_left]
  intro e hePath heGap
  rw [rlc_axisGapEdges, Finset.mem_union] at heGap
  rcases heGap with heRegion | heFirst
  · simp only [Finset.mem_filter] at heRegion
    obtain ⟨_ebox, z, hzRegion, hze⟩ := heRegion
    induction e using Sym2.inductionOn with
    | _ x y =>
      have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 hePath
      rw [Sym2.mem_iff] at hze
      rcases hze with rfl | rfl
      · exact rlc_axisGapRegion_not_barrier hzRegion (by
          simp [rlc_connectorBarrier, hends.1])
      · exact rlc_axisGapRegion_not_barrier hzRegion (by
          simp [rlc_connectorBarrier, hends.2])
  · have heEq : e = G.firstEdge := by simpa using heFirst
    exact G.firstEdge_not_mem_rightPath_of_disjoint hdisj (heEq ▸ hePath)

theorem rlc_leftPathEdges_disjoint_axisGapEdges {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
    Disjoint (rlc_pathEdges gamma'.1) (rlc_axisGapEdges G) := by
  rw [Finset.disjoint_left]
  intro e hePath heGap
  rw [rlc_axisGapEdges, Finset.mem_union] at heGap
  rcases heGap with heRegion | heFirst
  · simp only [Finset.mem_filter] at heRegion
    obtain ⟨_ebox, z, hzRegion, hze⟩ := heRegion
    induction e using Sym2.inductionOn with
    | _ x y =>
      have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 hePath
      rw [Sym2.mem_iff] at hze
      rcases hze with rfl | rfl
      · exact rlc_axisGapRegion_not_barrier hzRegion (by
          simp [rlc_connectorBarrier, hends.1])
      · exact rlc_axisGapRegion_not_barrier hzRegion (by
          simp [rlc_connectorBarrier, hends.2])
  · have heEq : e = G.firstEdge := by simpa using heFirst
    exact G.firstEdge_not_mem_leftPath_of_disjoint hdisj (heEq ▸ hePath)


theorem rlc_mem_axisGapConnectorEvent_of_firstEdge_open {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (hadjGap : G.lower + 1 = G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hopen : omega G.firstEdge = true) :
    omega ∈ rlc_axisGapConnectorEvent G := by
  have hLowerR := rlc_rightPathVertex_mem_connectorBox gamma G.lowerVertex_mem_right
  have hUpperR := rlc_leftPathVertex_mem_connectorBox gamma' G.upperVertex_mem_left
  refine ⟨G.lowerVertex, G.lowerVertex_mem_right,
    G.upperVertex, G.upperVertex_mem_left, hLowerR, hUpperR, ?_⟩
  have hlat : (hypercubicLattice 2).Adj G.lowerVertex G.upperVertex := by
    simp [RlcAxisBarrierGap.lowerVertex, RlcAxisBarrierGap.upperVertex,
      hypercubicLattice_adj, Fin.sum_univ_two, ← hadjGap]
  have hfirst : s(G.lowerVertex, G.upperVertex) = G.firstEdge := by
    simp [RlcAxisBarrierGap.firstEdge, RlcAxisBarrierGap.seedVertex,
      RlcAxisBarrierGap.upperVertex, hadjGap]
  have hfirstMem : G.firstEdge ∈ rlc_axisGapEdges G := by
    simp [rlc_axisGapEdges]
  have hmask : rlc_maskConfig (rlc_axisGapEdges G) omega
      s(G.lowerVertex, G.upperVertex) = true := by
    rw [hfirst, rlc_maskConfig, if_pos hfirstMem]
    exact hopen
  have hstep :
      (openSubgraphInduce 2 (rlc_maskConfig (rlc_axisGapEdges G) omega)
        (rect (-2 * n) (2 * n) (-n) n)).Adj
        ⟨G.lowerVertex, hLowerR⟩ ⟨G.upperVertex, hUpperR⟩ := by
    rw [openSubgraphInduce_adj]
    exact ⟨hlat, hmask⟩
  exact hstep.reachable


theorem rlc_axisGapConnector_half_of_adjacent {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (hadjGap : G.lower + 1 = G.upper) :
    (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (rlc_axisGapConnectorEvent G) := by
  let Open : Set (ConfigSpace (Sym2 (Site 2))) := {omega | omega G.firstEdge = true}
  have hsub : Open ⊆ rlc_axisGapConnectorEvent G := by
    intro omega homega
    exact rlc_mem_axisGapConnectorEvent_of_firstEdge_open G hadjGap omega homega
  have hprob : rba_selfDualMeasure.real Open = (1 : ℝ) / 2 := by
    simpa [Open, rba_selfDualMeasure] using
      (coord_true_prob (E := Sym2 (Site 2)) (2⁻¹ : ℝ≥0) half_le_one G.firstEdge)
  rw [← hprob]
  exact measureReal_mono hsub


theorem rlc_adaptiveConnector_half_of_nonadjacent {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hnonadj : ∀ G : RlcAxisBarrierGap gamma gamma',
      G.lower + 1 < G.upper →
      (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (rlc_axisGapConnectorEvent G)) :
    (1 : ℝ) / 2 ≤
      rba_selfDualMeasure.real (rlc_adaptiveConnectorEvent gamma gamma') := by
  by_cases hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)
  · obtain ⟨G, hG⟩ := rlc_axisBarrierGap?_eq_some_of_disjoint gamma gamma' hdisj
    rw [rlc_adaptiveConnectorEvent_eq_gap_of_some gamma gamma' G hG]
    have hle : G.lower + 1 ≤ G.upper := by
      have := G.lower_lt_upper
      omega
    rcases hle.eq_or_lt with hadj | hlt
    · exact rlc_axisGapConnector_half_of_adjacent G hadj
    · exact hnonadj G hlt
  · rw [rlc_adaptiveConnectorEvent_eq_univ_of_not_disjoint gamma gamma' hdisj,
      probReal_univ]
    norm_num

theorem rlc_exists_axis_barrier_gap_of_not_connector {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_connectorEvent gamma gamma') :
    ∃ a b : ℤ,
      a ∈ rlc_axisHeights (rlc_pathVertices gamma.1) ∧
      b ∈ rlc_axisHeights (rlc_pathVertices gamma'.1) ∧
      (gamma.1.1 : Site 2) 1 ≤ a ∧ a < b ∧
      b ≤ (gamma'.1.2.1 : Site 2) 1 ∧
      ∀ t : ℤ, a < t → t < b →
        ![0, t] ∉ rlc_connectorBarrier gamma gamma' :=
  rlc_exists_axis_barrier_gap_of_disjoint gamma gamma'
    (rlc_pathVertices_disjoint_of_not_connector gamma gamma' omega hno)


end Universality
end StatMech
