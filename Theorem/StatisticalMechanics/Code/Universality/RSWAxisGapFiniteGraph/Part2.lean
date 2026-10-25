/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapFiniteGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part75
import Def.StatisticalMechanics.Code.Universality.RSWAxisGapFiniteGraph.Part3
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_axisGapConnectorEvent_iff_finite {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) :
    omega ∈ rlc_axisGapConnectorEvent G ↔
      rlc_connectorRestrictConfig omega ∈
        rlc_finiteAxisGapConnectorEvent G := by
  rw [rlc_axisGapConnectorEvent, rlc_finiteAxisGapConnectorEvent]
  constructor
  · rintro ⟨x, hx, y, hy, hxR, hyR, hxy⟩
    refine ⟨⟨x, hxR⟩, ⟨y, hyR⟩, hx, hy, ?_⟩
    rw [rlc_openSub_axisGapFiniteGraph_restrict_eq]
    exact hxy
  · rintro ⟨x, y, hx, hy, hxy⟩
    refine ⟨x, hx, y, hy, x.2, y.2, ?_⟩
    rw [rlc_openSub_axisGapFiniteGraph_restrict_eq] at hxy
    exact hxy


theorem RlcAxisBarrierGap.lowerVertex_mem_connectorBox {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    G.lowerVertex ∈ rlc_connectorBox n := by
  simpa [rlc_connectorBox] using
    (rlc_rightPathVertex_mem_connectorBox gamma G.lowerVertex_mem_right)


theorem RlcAxisBarrierGap.upperVertex_mem_connectorBox {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    G.upperVertex ∈ rlc_connectorBox n := by
  simpa [rlc_connectorBox] using
    (rlc_leftPathVertex_mem_connectorBox gamma' G.upperVertex_mem_left)


theorem RlcAxisBarrierGap.seedVertex_mem_connectorBox {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    G.seedVertex ∈ rlc_connectorBox n := by
  have hlower := G.lowerVertex_mem_connectorBox
  have hupper := G.upperVertex_mem_connectorBox
  simp only [rlc_connectorBox, Set.Finite.mem_toFinset, mem_rect,
    RlcAxisBarrierGap.lowerVertex, RlcAxisBarrierGap.upperVertex,
    RlcAxisBarrierGap.seedVertex, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hlower hupper ⊢
  have hgap := G.lower_lt_upper
  omega


theorem RlcAxisBarrierGap.firstEdge_mem_axisGapFiniteGraph {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    (rlc_axisGapFiniteGraph G).Adj
      ⟨G.lowerVertex, by
        simpa [rlc_connectorBox] using G.lowerVertex_mem_connectorBox⟩
      ⟨G.seedVertex, by
        simpa [rlc_connectorBox] using G.seedVertex_mem_connectorBox⟩ := by
  constructor
  · simpa [RlcAxisBarrierGap.firstEdge] using G.firstEdge_lattice
  · simp [rlc_axisGapEdges, RlcAxisBarrierGap.firstEdge]


theorem rlc_axisGapEdges_endpoints_mem_connectorBox {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') {v w : Site 2}
    (he : s(v, w) ∈ rlc_axisGapEdges G) :
    v ∈ rlc_connectorBox n ∧ w ∈ rlc_connectorBox n := by
  rw [rlc_axisGapEdges, Finset.mem_union] at he
  rcases he with hinterior | hfirst
  · rw [Finset.mem_filter, mem_edgesWithinFinset] at hinterior
    obtain ⟨⟨x, hx, y, hy, hxy⟩, _⟩ := hinterior
    rw [Sym2.eq_iff] at hxy
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hx, hy⟩
    · exact ⟨hy, hx⟩
  · have heq : s(v, w) = s(G.lowerVertex, G.seedVertex) := by
      simpa [RlcAxisBarrierGap.firstEdge] using hfirst
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨G.lowerVertex_mem_connectorBox,
        G.seedVertex_mem_connectorBox⟩
    · exact ⟨G.seedVertex_mem_connectorBox,
        G.lowerVertex_mem_connectorBox⟩


theorem rlc_axisGapEdge_exists_lift {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') {e : Sym2 (Site 2)}
    (he : e ∈ rlc_axisGapEdges G) :
    ∃ f : Sym2 (RlcConnectorVertex n), f.map Subtype.val = e := by
  induction e using Sym2.inductionOn with
  | _ v w =>
      obtain ⟨hv, hw⟩ :=
        rlc_axisGapEdges_endpoints_mem_connectorBox G he
      let vf : RlcConnectorVertex n := ⟨v, by
        simpa [rlc_connectorBox] using hv⟩
      let wf : RlcConnectorVertex n := ⟨w, by
        simpa [rlc_connectorBox] using hw⟩
      exact ⟨s(vf, wf), by simp [Sym2.map_mk, vf, wf]⟩

end
end StatMech.Universality
