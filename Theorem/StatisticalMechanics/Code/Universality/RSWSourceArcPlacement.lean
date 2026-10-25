/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWContactFreeSourceArc
import Theorem.StatisticalMechanics.Code.Universality.RSWAxisOrContactObstruction.Part2
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_mem_axisGapEdges_iff_edgeBoxIncidentGap
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper) (e : Sym2 (Site 2)) :
    e ∈ rlc_axisGapEdges G ↔ rlc_edgeBoxIncidentGap G e := by
  induction e using Sym2.inductionOn with
  | _ v w =>
      constructor
      · intro he
        have hbox := rlc_axisGapEdges_endpoints_mem_box G hn hlt he
        refine ⟨?_, ?_⟩
        · intro z hz
          rw [Sym2.mem_iff] at hz
          rcases hz with rfl | rfl
          · exact hbox.1
          · exact hbox.2
        · rw [rlc_axisGapEdges, Finset.mem_union] at he
          rcases he with he | he
          · exact (Finset.mem_filter.mp he).2
          · have heq : s(v, w) = s(G.lowerVertex, G.seedVertex) := by
              simpa [RlcAxisBarrierGap.firstEdge] using he
            refine ⟨G.seedVertex, G.seedVertex_mem_region_of_lt hn hlt, ?_⟩
            rw [heq, Sym2.mem_iff]
            simp
      · exact rlc_mem_axisGapEdges_of_edgeBoxIncidentGap G


theorem rlc_mixedWired_faceBoundary_sourceSupported_iff_sourceLocal
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Adj f g) :
    sharedPrimalEdge f g ∈ rlc_mixedAxisGapEdges G ↔
      rlc_boundarySourceLocallySupported G (sharedPrimalEdge f g) := by
  have hpims : rlc_pimsEdgeEquiv
      s(rlc_dualReflect f, rlc_dualReflect g) = sharedPrimalEdge f g :=
    rlc_pimsEdgeEquiv_reflected_faceBoundaryEdge
      (rlc_mixedWiredReachSet G omega) hfg
  calc
    sharedPrimalEdge f g ∈ rlc_mixedAxisGapEdges G ↔
        rlc_pimsEdgeEquiv s(rlc_dualReflect f, rlc_dualReflect g) ∈
          rlc_mixedAxisGapEdges G := by rw [hpims]
    _ ↔ sharedPrimalEdge f g ∈ rlc_axisGapEdges G ∨
          sharedPrimalEdge f g ∈ rlc_reflectedPathEdges gamma.1 ∨
          sharedPrimalEdge f g ∈ rlc_reflectedPathEdges gamma'.1 :=
      rlc_mixedWired_faceBoundary_preimage_mem_mixedAxisGapEdges_iff
        G hn hlt omega hfg
    _ ↔ rlc_boundarySourceLocallySupported G
          (sharedPrimalEdge f g) := by
      unfold rlc_boundarySourceLocallySupported
      rw [← rlc_mem_axisGapEdges_iff_edgeBoxIncidentGap G hn hlt]


theorem rlc_faceBoundaryWalk_sourceSupported_iff_sourceLocal
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk x y) :
    RlcFaceBoundaryWalkSourceSupported G omega c ↔
      ∀ {f g : Site 2}, s(f, g) ∈ c.edges →
        rlc_boundarySourceLocallySupported G (sharedPrimalEdge f g) := by
  constructor
  · intro hsource f g hfg
    exact (rlc_mixedWired_faceBoundary_sourceSupported_iff_sourceLocal
      G hn hlt omega (c.adj_of_mem_edges hfg)).mp (hsource hfg)
  · intro hlocal f g hfg
    exact (rlc_mixedWired_faceBoundary_sourceSupported_iff_sourceLocal
      G hn hlt omega (c.adj_of_mem_edges hfg)).mpr (hlocal hfg)


theorem rlc_contourEdgeRelaxedLocal_iff_targetLocal_of_sourceSupported
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Adj f g)
    (hsource : sharedPrimalEdge f g ∈ rlc_mixedAxisGapEdges G) :
    rlc_contourEdgeRelaxedLocal G f g ↔
      rlc_reflectedTargetLocallySupported G
        s(rlc_dualReflect f, rlc_dualReflect g) := by
  have hsourceLocal :=
    (rlc_mixedWired_faceBoundary_sourceSupported_iff_sourceLocal
      G hn hlt omega hfg).mp hsource
  constructor
  · rintro (hexposed | ⟨htarget, _hsource⟩)
    · exact Or.inl hexposed
    · exact htarget
  · intro htarget
    exact Or.inr ⟨htarget, hsourceLocal⟩


theorem rlc_contourEdgeRelaxedLocal_comm_of_adj
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') {f g : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g) :
    rlc_contourEdgeRelaxedLocal G f g ↔
      rlc_contourEdgeRelaxedLocal G g f := by
  unfold rlc_contourEdgeRelaxedLocal
  rw [show s(rlc_dualReflect g, rlc_dualReflect f) =
      s(rlc_dualReflect f, rlc_dualReflect g) from Sym2.eq_swap]
  rw [sharedPrimalEdge_comm_of_adj hfg]


theorem rlc_contourEdgeRelaxedLocal_of_mk_eq
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    {f g a b : Site 2} (hab : (hypercubicLattice 2).Adj a b)
    (he : s(f, g) = s(a, b))
    (hlocal : rlc_contourEdgeRelaxedLocal G a b) :
    rlc_contourEdgeRelaxedLocal G f g := by
  rw [Sym2.eq_iff] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hlocal
  · exact (rlc_contourEdgeRelaxedLocal_comm_of_adj G hab).mp hlocal


theorem rlc_faceBoundaryWalk_relaxedLocal_iff_targetLocal_of_sourceSupported
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk x y)
    (hsource : RlcFaceBoundaryWalkSourceSupported G omega c) :
    (∀ {f g : Site 2}, s(f, g) ∈ c.edges →
        rlc_contourEdgeRelaxedLocal G f g) ↔
      ∀ {f g : Site 2}, s(f, g) ∈ c.edges →
        rlc_reflectedTargetLocallySupported G
          s(rlc_dualReflect f, rlc_dualReflect g) := by
  constructor <;> intro h f g hfg
  · exact (rlc_contourEdgeRelaxedLocal_iff_targetLocal_of_sourceSupported
      G hn hlt omega (c.adj_of_mem_edges hfg) (hsource hfg)).mp (h hfg)
  · exact (rlc_contourEdgeRelaxedLocal_iff_targetLocal_of_sourceSupported
      G hn hlt omega (c.adj_of_mem_edges hfg) (hsource hfg)).mpr (h hfg)


theorem rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalWalk_meets_paths
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {u v : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u v)
    (hlocal : ∀ {f g : Site 2}, s(f, g) ∈ c.edges →
      rlc_contourEdgeRelaxedLocal G f g)
    (hright : ∃ x ∈ c.support,
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hleft : ∃ y ∈ c.support,
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  obtain ⟨x, hx, hxPath⟩ := hright
  obtain ⟨y, hy, hyPath⟩ := hleft
  let a : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk x y :=
    (c.takeUntil x hx).reverse.append (c.takeUntil y hy)
  have haLocal : ∀ {f g : Site 2}, s(f, g) ∈ a.edges →
      rlc_contourEdgeRelaxedLocal G f g := by
    intro f g hfg
    dsimp only [a] at hfg
    rw [SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_reverse, List.mem_append,
      List.mem_reverse] at hfg
    rcases hfg with hfg | hfg
    · exact hlocal (c.edges_takeUntil_subset hx hfg)
    · exact hlocal (c.edges_takeUntil_subset hy hfg)
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalArc
    G hn hlt omega a hxPath hyPath haLocal


theorem rlc_mixedWiredConnectorEvent_dualReflect_of_sourceSupportedWalk_meets_paths
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {u v : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u v)
    (hsource : RlcFaceBoundaryWalkSourceSupported G omega c)
    (htarget : ∀ {f g : Site 2}, s(f, g) ∈ c.edges →
      rlc_reflectedTargetLocallySupported G
        s(rlc_dualReflect f, rlc_dualReflect g))
    (hright : ∃ x ∈ c.support,
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hleft : ∃ y ∈ c.support,
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  apply rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalWalk_meets_paths
    G hn hlt omega c
  · exact (rlc_faceBoundaryWalk_relaxedLocal_iff_targetLocal_of_sourceSupported
      G hn hlt omega c hsource).mpr htarget
  · exact hright
  · exact hleft


theorem rlc_sourceSupportedWalk_targetDefect_of_dualReflect_failure
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : rlc_dualReflectConfig omega ∉ rlc_mixedWiredConnectorEvent G)
    {u v : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u v)
    (hsource : RlcFaceBoundaryWalkSourceSupported G omega c)
    (hright : ∃ x ∈ c.support,
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hleft : ∃ y ∈ c.support,
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
    ∃ f g : Site 2, s(f, g) ∈ c.edges ∧
      ¬ rlc_reflectedTargetLocallySupported G
        s(rlc_dualReflect f, rlc_dualReflect g) := by
  by_contra hdefect
  have htarget : ∀ {f g : Site 2}, s(f, g) ∈ c.edges →
      rlc_reflectedTargetLocallySupported G
        s(rlc_dualReflect f, rlc_dualReflect g) := by
    intro f g hfg
    by_contra hbad
    exact hdefect ⟨f, g, hfg, hbad⟩
  exact hno
    (rlc_mixedWiredConnectorEvent_dualReflect_of_sourceSupportedWalk_meets_paths
      G hn hlt omega c hsource htarget hright hleft)


end Universality
end StatMech
