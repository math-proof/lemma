/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapFiniteGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part75
import Def.StatisticalMechanics.Code.Universality.RSWAxisGapFiniteGraph.Part5
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_axisGapAmbientConfig_supportEdge {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (Site 2)} (he : e ∈ rlc_axisGapEdges G) :
    rlc_axisGapAmbientConfig G tau e =
      tau (rlc_axisGapEdgeLift G e he) := by
  simp [rlc_axisGapAmbientConfig, he]


theorem rlc_axisGapAmbientConfig_graphEdge {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {x y : RlcConnectorVertex n}
    (hxy : (rlc_axisGapFiniteGraph G).Adj x y) :
    rlc_connectorRestrictConfig (rlc_axisGapAmbientConfig G tau) s(x, y) =
      tau s(x, y) := by
  have he : s((x : Site 2), (y : Site 2)) ∈ rlc_axisGapEdges G := hxy.2
  rw [rlc_connectorRestrictConfig, Sym2.map_mk,
    rlc_axisGapAmbientConfig_supportEdge G tau he]
  congr 1
  apply Sym2.map.injective Subtype.val_injective
  rw [rlc_axisGapEdgeLift_map]
  rfl


theorem rlc_openSub_restrict_axisGapAmbientConfig_eq {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.openSub (rlc_axisGapFiniteGraph G)
        (rlc_connectorRestrictConfig (rlc_axisGapAmbientConfig G tau)) =
      FK.openSub (rlc_axisGapFiniteGraph G) tau := by
  ext x y
  simp only [FK.openSub_adj]
  constructor
  · rintro ⟨hxy, hopen⟩
    exact ⟨hxy, by
      rw [rlc_axisGapAmbientConfig_graphEdge G tau hxy] at hopen
      exact hopen⟩
  · rintro ⟨hxy, hopen⟩
    exact ⟨hxy, by
      rw [rlc_axisGapAmbientConfig_graphEdge G tau hxy]
      exact hopen⟩


theorem rlc_axisGapAmbientConfig_mem_connectorEvent_iff {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_axisGapAmbientConfig G tau ∈ rlc_axisGapConnectorEvent G ↔
      tau ∈ rlc_finiteAxisGapConnectorEvent G := by
  rw [rlc_axisGapConnectorEvent_iff_finite]
  unfold rlc_finiteAxisGapConnectorEvent
  simp only [Set.mem_setOf_eq]
  rw [rlc_openSub_restrict_axisGapAmbientConfig_eq]


theorem rlc_finiteAxisGapConnectorFailure_reflectedOpenDualCircuit {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
    ∃ (p q f g u : Site 2)
      (c : (openSubgraph 2 (rlc_dualReflectConfig
        (rlc_maskConfig (rlc_axisGapEdges G)
          (rlc_axisGapAmbientConfig G tau)))).Walk
          (rlc_dualReflect u) (rlc_dualReflect u)),
      p 0 = 0 ∧ q 0 = 0 ∧
      sharedPrimalEdge f g = s(p, q) ∧
      c.IsCycle ∧
      s(rlc_dualReflect f, rlc_dualReflect g) ∈ c.edges := by
  apply rlc_axisGapReachSet_reflectedOpenDualCircuit G hn hlt
    (rlc_axisGapAmbientConfig G tau)
  intro hconn
  exact hno ((rlc_axisGapAmbientConfig_mem_connectorEvent_iff G tau).mp hconn)


theorem rlc_axisGapRegionSet_eq_connectorOriginRegionSet_of_origin_mem
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (ho : origin 2 ∈ rlc_axisGapRegionSet G) :
    rlc_axisGapRegionSet G =
      rlc_connectorOriginRegionSet gamma gamma' := by
  ext z
  constructor
  · rintro ⟨hzAllowed, _hseedAllowed, hseedz⟩
    obtain ⟨hoAllowed, _hseedAllowed, hseedOrigin⟩ := ho
    exact ⟨hzAllowed, hoAllowed, hseedOrigin.symm.trans hseedz⟩
  · rintro ⟨hzAllowed, _hoAllowed, horiginz⟩
    obtain ⟨_hoAllowed, hseedAllowed, hseedOrigin⟩ := ho
    exact ⟨hzAllowed, hseedAllowed, hseedOrigin.trans horiginz⟩


theorem rlc_axisGapRegion_eq_connectorOriginRegion_of_origin_mem
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (ho : origin 2 ∈ rlc_axisGapRegionSet G) :
    rlc_axisGapRegion G =
      rlc_connectorOriginRegion gamma gamma' := by
  ext z
  simpa [rlc_axisGapRegion, rlc_connectorOriginRegion] using
    Set.ext_iff.mp
      (rlc_axisGapRegionSet_eq_connectorOriginRegionSet_of_origin_mem G ho) z


theorem rlc_axisGapEdges_eq_connectorEdges_of_origin_mem
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (ho : origin 2 ∈ rlc_axisGapRegionSet G) :
    rlc_axisGapEdges G = rlc_connectorEdges gamma gamma' := by
  have hregion :=
    rlc_axisGapRegion_eq_connectorOriginRegion_of_origin_mem G ho
  obtain ⟨_hoAllowed, hseedAllowed, _hseedOrigin⟩ := ho
  have hseedSet : G.seedVertex ∈ rlc_axisGapRegionSet G :=
    ⟨hseedAllowed, hseedAllowed, SimpleGraph.Reachable.refl _⟩
  have hseed : G.seedVertex ∈ rlc_connectorOriginRegion gamma gamma' := by
    rw [← hregion]
    simpa [rlc_axisGapRegion] using hseedSet
  have hfirst : G.firstEdge ∈ rlc_connectorEdges gamma gamma' := by
    rw [rlc_connectorEdges, Finset.mem_filter]
    constructor
    · rw [mem_edgesWithinFinset]
      exact ⟨G.lowerVertex, G.lowerVertex_mem_connectorBox,
        G.seedVertex, G.seedVertex_mem_connectorBox,
        by simp [RlcAxisBarrierGap.firstEdge]⟩
    · exact ⟨G.seedVertex, hseed, by
        simp [RlcAxisBarrierGap.firstEdge]⟩
  rw [rlc_axisGapEdges, rlc_connectorEdges, hregion]
  apply Finset.union_eq_left.mpr
  simpa [rlc_connectorEdges] using hfirst


theorem rlc_axisGapFiniteGraph_eq_connectorFiniteGraph_of_origin_mem
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (ho : origin 2 ∈ rlc_axisGapRegionSet G) :
    rlc_axisGapFiniteGraph G = rlc_connectorFiniteGraph gamma gamma' := by
  ext x y
  simp only [rlc_axisGapFiniteGraph, rlc_connectorFiniteGraph]
  rw [rlc_axisGapEdges_eq_connectorEdges_of_origin_mem G ho]


theorem rlc_axisGapConnectorEvent_eq_connectorEvent_of_origin_mem
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (ho : origin 2 ∈ rlc_axisGapRegionSet G) :
    rlc_axisGapConnectorEvent G = rlc_connectorEvent gamma gamma' := by
  unfold rlc_axisGapConnectorEvent rlc_connectorEvent
  rw [rlc_axisGapEdges_eq_connectorEdges_of_origin_mem G ho]

end
end StatMech.Universality
