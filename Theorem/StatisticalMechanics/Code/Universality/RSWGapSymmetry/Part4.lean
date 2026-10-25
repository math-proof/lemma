/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Def.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part3
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

theorem rlc_mixedWired_reflected_faceBoundaryEdge_support_of_local
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Adj f g)
    (htarget : rlc_reflectedTargetLocallySupported G
      s(rlc_dualReflect f, rlc_dualReflect g))
    (hsource : rlc_boundarySourceLocallySupported G
      (sharedPrimalEdge f g)) :
    s(rlc_dualReflect f, rlc_dualReflect g) ∈
        (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∪
          rlc_mixedAxisGapEdges G ∧
      rlc_pimsEdgeEquiv s(rlc_dualReflect f, rlc_dualReflect g) ∈
        rlc_mixedAxisGapEdges G := by
  constructor
  · rw [rlc_mem_exposed_union_mixedAxisGapEdges_iff G]
    rcases htarget with hexposed | hgap | hright | hleft
    · exact Or.inl hexposed
    · exact Or.inr (Or.inl
        (rlc_mem_axisGapEdges_of_flipX_edgeBoxIncidentGap G hgap))
    · exact Or.inr (Or.inr (Or.inl hright))
    · exact Or.inr (Or.inr (Or.inr hleft))
  · rw [rlc_mixedWired_faceBoundary_preimage_mem_mixedAxisGapEdges_iff
      G hn hlt omega hfg]
    rcases hsource with hgap | hright | hleft
    · exact Or.inl (rlc_mem_axisGapEdges_of_edgeBoxIncidentGap G hgap)
    · exact Or.inr (Or.inl hright)
    · exact Or.inr (Or.inr hleft)


theorem rlc_dualReflect_wired_faceBoundaryWalk_of_local_support {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk x y)
    (hlocal : ∀ {f g : Site 2}, s(f, g) ∈ c.edges →
      rlc_reflectedTargetLocallySupported G
          s(rlc_dualReflect f, rlc_dualReflect g) ∧
        rlc_boundarySourceLocallySupported G (sharedPrimalEdge f g)) :
    ∃ q : (openSubgraph 2
      (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G)
        (rlc_dualReflectConfig omega))).Walk
        (rlc_dualReflect x) (rlc_dualReflect y),
      q.edges = (rlc_dualReflectOpenWalk
        (rlc_wiredConnectorConfig gamma gamma'
          (rlc_mixedAxisGapEdges G) omega)
        (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
          G hn hlt omega))).edges ∧
      q.support = (rlc_dualReflectOpenWalk
        (rlc_wiredConnectorConfig gamma gamma'
          (rlc_mixedAxisGapEdges G) omega)
        (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
          G hn hlt omega))).support := by
  let eta := rlc_wiredConnectorConfig gamma gamma'
    (rlc_mixedAxisGapEdges G) omega
  let hle := rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual
    G hn hlt omega
  let p := rlc_dualReflectOpenWalk eta (c.mapLe hle)
  apply rlc_dualReflect_wired_walk_of_support G omega p
  intro e he
  have hEdges : p.edges =
      (c.mapLe hle).edges.map
        (Sym2.map (rlc_dualReflectOpenHom eta)) :=
    SimpleGraph.Walk.edges_map (rlc_dualReflectOpenHom eta) (c.mapLe hle)
  rw [hEdges] at he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
  induction e0 using Sym2.inductionOn with
  | _ f g =>
      have hfgEdge : s(f, g) ∈ c.edges := by
        rw [c.edges_mapLe_eq_edges hle] at he0
        exact he0
      exact rlc_mixedWired_reflected_faceBoundaryEdge_support_of_local
        G hn hlt omega (c.adj_of_mem_edges hfgEdge)
          (hlocal hfgEdge).1 (hlocal hfgEdge).2

end Universality
end StatMech
