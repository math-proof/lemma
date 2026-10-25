/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFacePositionedObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceScaleOneAudit.Part2
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFacePositionedObstruction
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_axisReturnCounterexample_source_failure :
    rlc_axisReturnCounterexampleClosedConfig ∉
      rlc_finiteCentralFaceRandomConnectorEvent
        rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft := by
  intro h
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  have hopen : FK.openSub
      (rlc_connectorCentralFaceFiniteGraph
        rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft)
      rlc_axisReturnCounterexampleClosedConfig = ⊥ := by
    ext u v
    simp [FK.openSub_adj, rlc_axisReturnCounterexampleClosedConfig]
  rw [hopen] at hxy
  have hxyEq : x = y := SimpleGraph.reachable_bot.mp hxy
  subst y
  rw [rlc_connectorOnRight] at hx
  rw [rlc_connectorOnLeft] at hy
  exact Finset.disjoint_left.mp
    rlc_axisReturnCounterexample_bookPositioned.exposed_disjoint hx hy

theorem not_fourTrace
    {e : Sym2 (Site 2)}
    (he : e = s((![0, -1] : Site 2), ![0, 0]) ∨
      e = s((![1, -1] : Site 2), ![1, 0]) ∨
      e = s((![1, 0] : Site 2), ![2, 0])) :
    e ∉ rlc_connectorFourTraceEdges rlc_traceSplitCounterexampleRight
      rlc_axisReturnCounterexampleLeft := by
  rcases he with rfl | rfl | rfl
  all_goals
    rw [rlc_connectorFourTraceEdges, rlc_connectorReflectedTraceEdges,
      rlc_reflectedPathEdges,
      rlc_traceSplitCounterexample_right_edges,
      rlc_axisReturnCounterexample_left_edges]
    simp [rlc_reflectedPathEdges, rlc_flipX, rlc_flipXFun,
      Sym2.map_mk]
    all_goals
      intro x hx
      have hx' : x ∈
          ({s((![-2, 0] : Site 2), ![-2, 1]),
            s((![-2, 1] : Site 2), ![-1, 1]),
            s((![-1, 1] : Site 2), ![-1, 0]),
            s((![-1, 0] : Site 2), ![0, 0]),
            s((![0, 0] : Site 2), ![0, 1])} : Finset (Sym2 (Site 2))) := by
        simpa only [rlc_axisReturnCounterexample_left_edges] using hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
      rcases hx' with rfl | rfl | rfl | rfl | rfl <;>
        simp [Sym2.map_mk]

theorem not_closure
    {x y : Site 2} (hxy : (hypercubicLattice 2).Adj x y)
    (hface : rlc_connectorCentralFace ∉ flankFaces x y) :
    s(x, y) ∉ rlc_connectorCentralFaceClosureEdges
      rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft := by
  intro he
  rw [rlc_connectorCentralFaceClosureEdges, Finset.mem_filter] at he
  obtain ⟨_hebox, f, hf, hfe⟩ := he
  rw [rlc_axisReturnCounterexample_centralFaceRegion_eq_singleton] at hf
  simp only [Finset.mem_singleton] at hf
  subst f
  rw [StatMech.FrontierD.fci_faceEdgeEquiv_symm_mk_of_adj hxy] at hfe
  exact hface hfe

theorem bad_c_not_planar :
    s((![0, -1] : Site 2), ![0, 0]) ∉
      rlc_connectorCentralFacePlanarEdges
        rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft := by
  rw [rlc_connectorCentralFacePlanarEdges, Finset.mem_union]
  push Not
  constructor
  · apply not_closure
    · simp [hypercubicLattice_adj, Fin.sum_univ_two]
    · simp [rlc_connectorCentralFace, flankFaces]
  · exact not_fourTrace (Or.inl rfl)

theorem bad_d_not_planar :
    s((![1, -1] : Site 2), ![1, 0]) ∉
      rlc_connectorCentralFacePlanarEdges
        rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft := by
  rw [rlc_connectorCentralFacePlanarEdges, Finset.mem_union]
  push Not
  constructor
  · apply not_closure
    · simp [hypercubicLattice_adj, Fin.sum_univ_two]
    · simp [rlc_connectorCentralFace, flankFaces]
  · exact not_fourTrace (Or.inr (Or.inl rfl))

theorem bad_e_not_planar :
    s((![1, 0] : Site 2), ![2, 0]) ∉
      rlc_connectorCentralFacePlanarEdges
        rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft := by
  rw [rlc_connectorCentralFacePlanarEdges, Finset.mem_union]
  push Not
  constructor
  · apply not_closure
    · simp [hypercubicLattice_adj, Fin.sum_univ_two]
    · simp [rlc_connectorCentralFace, flankFaces]
  · exact not_fourTrace (Or.inr (Or.inr rfl))

end
end StatMech.Universality
