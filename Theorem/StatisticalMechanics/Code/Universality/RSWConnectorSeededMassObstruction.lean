/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededMassObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassCapstone.Part2
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Theorem.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDualityObstruction.Part6
import Def.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassObstruction
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem scaleTwoGapNorthEdge_mem :
    scaleTwoGapNorthEdge ∈
      (rlc_axisGapFiniteGraph rlc_scaleTwoDoubleFailureGap).edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset]
  refine ⟨by
    simp [scaleTwoGapCenter, scaleTwoGapNorth, hypercubicLattice_adj,
      Fin.sum_univ_two], ?_⟩
  simpa [scaleTwoGapNorthEdge, scaleTwoGapCenter, scaleTwoGapNorth,
    Sym2.map_mk] using rlc_scaleTwoAxisGap_leftEdge_mem

theorem scaleTwoGapSouthEdge_mem :
    scaleTwoGapSouthEdge ∈
      (rlc_axisGapFiniteGraph rlc_scaleTwoDoubleFailureGap).edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset]
  simpa [scaleTwoGapSouthEdge, scaleTwoGapSouth, scaleTwoGapCenter] using
    rlc_scaleTwoDoubleFailureGap.firstEdge_mem_axisGapFiniteGraph

theorem scaleTwoGapEastEdge_mem :
    scaleTwoGapEastEdge ∈
      (rlc_axisGapFiniteGraph rlc_scaleTwoDoubleFailureGap).edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset]
  refine ⟨by
    simp [scaleTwoGapEast, scaleTwoGapCenter, hypercubicLattice_adj,
      Fin.sum_univ_two], ?_⟩
  rw [rlc_axisGapEdges, Finset.mem_union]
  left
  rw [Finset.mem_filter]
  refine ⟨?_, ⟨![0, -1], ?_, ?_⟩⟩
  · rw [mem_edgesWithinFinset]
    exact ⟨![1, -1], by simp [rlc_connectorBox, mem_rect],
      ![0, -1], by simp [rlc_connectorBox, mem_rect], rfl⟩
  · rw [rlc_scaleTwoAxisGapRegion_eq_singleton]
    simp
  · simp [scaleTwoGapEastEdge, scaleTwoGapEast, scaleTwoGapCenter,
      Sym2.map_mk]

theorem scaleTwoGapWestEdge_mem :
    scaleTwoGapWestEdge ∈
      (rlc_axisGapFiniteGraph rlc_scaleTwoDoubleFailureGap).edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset]
  refine ⟨by
    simp [scaleTwoGapWest, scaleTwoGapCenter, hypercubicLattice_adj,
      Fin.sum_univ_two], ?_⟩
  simpa [scaleTwoGapWestEdge, scaleTwoGapWest, scaleTwoGapCenter,
    Sym2.map_mk] using rlc_scaleTwoAxisGap_westEdge_mem

theorem scaleTwoGap_source_event_iff
    (rho : ConfigSpace (Sym2 ScaleTwoConnectorVertex)) :
    rho ∈ rlc_finiteAxisGapConnectorEvent rlc_scaleTwoDoubleFailureGap ↔
      rho scaleTwoGapNorthEdge = true ∧
        (rho scaleTwoGapSouthEdge = true ∨
          rho scaleTwoGapEastEdge = true) := by
  constructor
  · rintro ⟨x, y, hx, hy, hreach⟩
    obtain ⟨w⟩ := hreach
    have hnorth : rho scaleTwoGapNorthEdge = true := by
      cases w.reverse with
      | nil =>
          exact False.elim
            (Finset.disjoint_left.mp
              rlc_scaleTwoDoubleFailure_exposedPaths_disjoint hx hy)
      | @cons _ z _ hyz _ =>
          rw [FK.openSub_adj] at hyz
          obtain ⟨hyN, hzC⟩ :=
            rlc_scaleTwoAxisGap_left_neighbor hy hyz.1
          have hedge : s(y, z) = scaleTwoGapNorthEdge := by
            apply Sym2.map.injective Subtype.val_injective
            simp only [Sym2.map_mk]
            rw [hyN, hzC, Sym2.eq_swap]
            rfl
          rw [hedge] at hyz
          exact hyz.2
    refine ⟨hnorth, ?_⟩
    cases w with
    | nil =>
        exact False.elim
          (Finset.disjoint_left.mp
            rlc_scaleTwoDoubleFailure_exposedPaths_disjoint hx hy)
    | @cons _ z _ hxz _ =>
        rw [FK.openSub_adj] at hxz
        obtain ⟨hxSE, hzC⟩ :=
          rlc_scaleTwoAxisGap_right_neighbor hx hxz.1
        rcases hxSE with hxS | hxE
        · left
          have hedge : s(x, z) = scaleTwoGapSouthEdge := by
            apply Sym2.map.injective Subtype.val_injective
            simp only [Sym2.map_mk]
            rw [hxS, hzC]
            rfl
          rw [hedge] at hxz
          exact hxz.2
        · right
          have hedge : s(x, z) = scaleTwoGapEastEdge := by
            apply Sym2.map.injective Subtype.val_injective
            simp only [Sym2.map_mk]
            rw [hxE, hzC]
            rfl
          rw [hedge] at hxz
          exact hxz.2
  · rintro ⟨hnorth, hsouth | heast⟩
    · refine ⟨scaleTwoGapSouth, scaleTwoGapNorth, ?_, ?_, ?_⟩
      · rw [rlc_connectorOnRight,
          rlc_scaleTwoDoubleFailure_right_vertices]
        simp [scaleTwoGapSouth]
      · rw [rlc_connectorOnLeft,
          rlc_scaleTwoDoubleFailure_left_vertices]
        simp [scaleTwoGapNorth]
      · exact (show (FK.openSub (rlc_axisGapFiniteGraph
            rlc_scaleTwoDoubleFailureGap) rho).Adj
              scaleTwoGapSouth scaleTwoGapCenter from
            ⟨SimpleGraph.mem_edgeFinset.mp scaleTwoGapSouthEdge_mem,
              hsouth⟩).reachable.trans
          (show (FK.openSub (rlc_axisGapFiniteGraph
            rlc_scaleTwoDoubleFailureGap) rho).Adj
              scaleTwoGapCenter scaleTwoGapNorth from
            ⟨SimpleGraph.mem_edgeFinset.mp scaleTwoGapNorthEdge_mem,
              hnorth⟩).reachable
    · refine ⟨scaleTwoGapEast, scaleTwoGapNorth, ?_, ?_, ?_⟩
      · rw [rlc_connectorOnRight,
          rlc_scaleTwoDoubleFailure_right_vertices]
        simp [scaleTwoGapEast]
      · rw [rlc_connectorOnLeft,
          rlc_scaleTwoDoubleFailure_left_vertices]
        simp [scaleTwoGapNorth]
      · exact (show (FK.openSub (rlc_axisGapFiniteGraph
            rlc_scaleTwoDoubleFailureGap) rho).Adj
              scaleTwoGapEast scaleTwoGapCenter from
            ⟨SimpleGraph.mem_edgeFinset.mp scaleTwoGapEastEdge_mem,
              heast⟩).reachable.trans
          (show (FK.openSub (rlc_axisGapFiniteGraph
            rlc_scaleTwoDoubleFailureGap) rho).Adj
              scaleTwoGapCenter scaleTwoGapNorth from
            ⟨SimpleGraph.mem_edgeFinset.mp scaleTwoGapNorthEdge_mem,
              hnorth⟩).reachable

end
end StatMech.Universality
