import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part4
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_flipX_mem_image_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean)
-/
@[path]
private lemma rlc_flipX_mem_image_iff_eq
  {P : Finset (Site 2)}
  {z : Site 2} :
-- imply
  rlc_flipX z ∈ P.image rlc_flipX ↔ z ∈ P := by
-- proof
  apply StatMech.Universality.rlc_flipX_mem_image_iff P z

/--
[rlc_mem_flipX_image_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean)
-/
@[path]
private lemma rlc_mem_flipX_image_iff_eq
  {P : Finset (Site 2)}
  {z : Site 2} :
-- imply
  z ∈ P.image rlc_flipX ↔ rlc_flipX z ∈ P := by
-- proof
  apply StatMech.Universality.rlc_mem_flipX_image_iff P z

/--
[rlc_connectorBarrier_mem_flipX_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean)
-/
@[path]
private lemma rlc_connectorBarrier_mem_flipX_iff_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2} :
-- imply
  z ∈ rlc_connectorBarrier gamma gamma' ↔ rlc_flipX z ∈ rlc_connectorBarrier gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorBarrier_mem_flipX_iff gamma gamma' z

/--
[rlc_connectorBox_mem_flipX_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean)
-/
@[path]
private lemma rlc_connectorBox_mem_flipX_iff_eq
  {n : ℤ}
  {z : Site 2} :
-- imply
  z ∈ rlc_connectorBox n ↔ rlc_flipX z ∈ rlc_connectorBox n := by
-- proof
  apply StatMech.Universality.rlc_connectorBox_mem_flipX_iff z

/--
[rlc_connectorAllowed_mem_flipX_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean)
-/
@[path]
private lemma rlc_connectorAllowed_mem_flipX_iff_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2} :
-- imply
  z ∈ rlc_connectorAllowed gamma gamma' ↔ rlc_flipX z ∈ rlc_connectorAllowed gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorAllowed_mem_flipX_iff gamma gamma' z

/--
[rlc_adj_flipX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean)
-/
@[path]
private lemma rlc_adj_flipX_eq
  {x y : Site 2} :
-- imply
  (hypercubicLattice 2).Adj x y ↔ (hypercubicLattice 2).Adj (rlc_flipX x) (rlc_flipX y) := by
-- proof
  apply StatMech.Universality.rlc_adj_flipX x y

/--
[rlc_axisGapRegionSet_mem_flipX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean)
-/
@[path]
private lemma rlc_axisGapRegionSet_mem_flipX_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {z : Site 2}
-- given
  (hz : z ∈ rlc_axisGapRegionSet G) :
-- imply
  rlc_flipX z ∈ rlc_axisGapRegionSet G := by
-- proof
  apply StatMech.Universality.rlc_axisGapRegionSet_mem_flipX G hz

/--
[rlc_axisGapRegionSet_mem_flipX_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean)
-/
@[path]
private lemma rlc_axisGapRegionSet_mem_flipX_iff_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {z : Site 2} :
-- imply
  z ∈ rlc_axisGapRegionSet G ↔ rlc_flipX z ∈ rlc_axisGapRegionSet G := by
-- proof
  apply StatMech.Universality.rlc_axisGapRegionSet_mem_flipX_iff G z

/--
[rlc_axisGapRegion_mem_flipX_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean)
-/
@[path]
private lemma rlc_axisGapRegion_mem_flipX_iff_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {z : Site 2} :
-- imply
  z ∈ rlc_axisGapRegion G ↔ rlc_flipX z ∈ rlc_axisGapRegion G := by
-- proof
  apply StatMech.Universality.rlc_axisGapRegion_mem_flipX_iff G z

/--
[RlcAxisBarrierGap.firstEdge_map_flipX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean)
-/
@[path]
private lemma firstEdge_map_flipX_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'} :
-- imply
  G.firstEdge.map rlc_flipX = G.firstEdge := by
-- proof
  apply StatMech.Universality.RlcAxisBarrierGap.firstEdge_map_flipX G

/--
[rlc_edge_map_flipX_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean)
-/
@[path]
private lemma rlc_edge_map_flipX_involutive_eq
  {e : Sym2 (Site 2)} :
-- imply
  (e.map rlc_flipX).map rlc_flipX = e := by
-- proof
  apply StatMech.Universality.rlc_edge_map_flipX_involutive e

/--
[rlc_axisGapEdges_mem_map_flipX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean)
-/
@[path]
private lemma rlc_axisGapEdges_mem_map_flipX_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ rlc_axisGapEdges G) :
-- imply
  e.map rlc_flipX ∈ rlc_axisGapEdges G := by
-- proof
  apply StatMech.Universality.rlc_axisGapEdges_mem_map_flipX G he

/--
[rlc_axisGapEdges_mem_map_flipX_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean)
-/
@[path]
private lemma rlc_axisGapEdges_mem_map_flipX_iff_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {e : Sym2 (Site 2)} :
-- imply
  e ∈ rlc_axisGapEdges G ↔ e.map rlc_flipX ∈ rlc_axisGapEdges G := by
-- proof
  apply StatMech.Universality.rlc_axisGapEdges_mem_map_flipX_iff G e

/--
[rlc_mem_axisGapEdges_of_edgeBoxIncidentGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean)
-/
@[path]
private lemma rlc_mem_axisGapEdges_of_edgeBoxIncidentGap_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {e : Sym2 (Site 2)}
-- given
  (he : rlc_edgeBoxIncidentGap G e) :
-- imply
  e ∈ rlc_axisGapEdges G := by
-- proof
  apply StatMech.Universality.rlc_mem_axisGapEdges_of_edgeBoxIncidentGap G he

/--
[rlc_mem_axisGapEdges_of_flipX_edgeBoxIncidentGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean)
-/
@[path]
private lemma rlc_mem_axisGapEdges_of_flipX_edgeBoxIncidentGap_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {e : Sym2 (Site 2)}
-- given
  (he : rlc_edgeBoxIncidentGap G (e.map rlc_flipX)) :
-- imply
  e ∈ rlc_axisGapEdges G := by
-- proof
  apply StatMech.Universality.rlc_mem_axisGapEdges_of_flipX_edgeBoxIncidentGap G he

/--
[rlc_mem_exposed_union_mixedAxisGapEdges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean)
-/
@[path]
private lemma rlc_mem_exposed_union_mixedAxisGapEdges_iff_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {e : Sym2 (Site 2)} :
-- imply
  e ∈ (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∪ rlc_mixedAxisGapEdges G ↔ e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 ∨ e ∈ rlc_axisGapEdges G ∨ e ∈ rlc_reflectedPathEdges gamma.1 ∨ e ∈ rlc_reflectedPathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_mem_exposed_union_mixedAxisGapEdges_iff G e

/--
[rlc_axisGapEdge_mem_exposed_union_mixedAxisGapEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean)
-/
@[path]
private lemma rlc_axisGapEdge_mem_exposed_union_mixedAxisGapEdges_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ rlc_axisGapEdges G) :
-- imply
  e ∈ (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∪ rlc_mixedAxisGapEdges G := by
-- proof
  apply StatMech.Universality.rlc_axisGapEdge_mem_exposed_union_mixedAxisGapEdges G he

/--
[rlc_axisGapEdge_mem_mixedAxisGapEdges_of_not_exposed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean)
-/
@[path]
private lemma rlc_axisGapEdge_mem_mixedAxisGapEdges_of_not_exposed_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ rlc_axisGapEdges G)
  (hnot : e ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
-- imply
  e ∈ rlc_mixedAxisGapEdges G := by
-- proof
  apply StatMech.Universality.rlc_axisGapEdge_mem_mixedAxisGapEdges_of_not_exposed G he hnot

/--
[rlc_gapSymmetry_pimsEdgeEquiv_reflected_faceBoundaryEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean)
-/
@[path]
private lemma rlc_gapSymmetry_pimsEdgeEquiv_reflected_faceBoundaryEdge_eq
  {S : Set (Site 2)}
  {f g : Site 2}
-- given
  (hfg : (faceBoundaryGraph S).Adj f g) :
-- imply
  rlc_pimsEdgeEquiv s(rlc_dualReflect f, rlc_dualReflect g) = sharedPrimalEdge f g := by
-- proof
  apply StatMech.Universality.rlc_gapSymmetry_pimsEdgeEquiv_reflected_faceBoundaryEdge S hfg

/--
[rlc_gapSymmetry_faceBoundary_preimage_not_exposed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean)
-/
@[path]
private lemma rlc_gapSymmetry_faceBoundary_preimage_not_exposed_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {f g : Site 2}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hfg : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Adj f g) :
-- imply
  rlc_pimsEdgeEquiv s(rlc_dualReflect f, rlc_dualReflect g) ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_gapSymmetry_faceBoundary_preimage_not_exposed G hn hlt omega hfg

/--
[rlc_mixedWired_faceBoundary_preimage_mem_mixedAxisGapEdges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean)
-/
@[path]
private lemma rlc_mixedWired_faceBoundary_preimage_mem_mixedAxisGapEdges_iff_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {f g : Site 2}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hfg : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Adj f g) :
-- imply
  rlc_pimsEdgeEquiv s(rlc_dualReflect f, rlc_dualReflect g) ∈ rlc_mixedAxisGapEdges G ↔ sharedPrimalEdge f g ∈ rlc_axisGapEdges G ∨ sharedPrimalEdge f g ∈ rlc_reflectedPathEdges gamma.1 ∨ sharedPrimalEdge f g ∈ rlc_reflectedPathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_mixedWired_faceBoundary_preimage_mem_mixedAxisGapEdges_iff G hn hlt omega hfg

/--
[rlc_mixedWired_reflected_faceBoundaryEdge_support_of_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean)
-/
@[path]
private lemma rlc_mixedWired_reflected_faceBoundaryEdge_support_of_local_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {f g : Site 2}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hfg : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Adj f g)
  (htarget : rlc_reflectedTargetLocallySupported G s(rlc_dualReflect f, rlc_dualReflect g))
  (hsource : rlc_boundarySourceLocallySupported G (sharedPrimalEdge f g)) :
-- imply
  s(rlc_dualReflect f, rlc_dualReflect g) ∈ (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∪ rlc_mixedAxisGapEdges G ∧ rlc_pimsEdgeEquiv s(rlc_dualReflect f, rlc_dualReflect g) ∈ rlc_mixedAxisGapEdges G := by
-- proof
  apply StatMech.Universality.rlc_mixedWired_reflected_faceBoundaryEdge_support_of_local G hn hlt omega hfg htarget hsource

/--
[rlc_dualReflect_wired_faceBoundaryWalk_of_local_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean)
-/
@[path]
private lemma rlc_dualReflect_wired_faceBoundaryWalk_of_local_support_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2}
  {c : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Walk x y}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hlocal : ∀ {f g : Site 2}, s(f, g) ∈ c.edges → rlc_reflectedTargetLocallySupported G s(rlc_dualReflect f, rlc_dualReflect g) ∧ rlc_boundarySourceLocallySupported G (sharedPrimalEdge f g)) :
-- imply
  ∃ q : (openSubgraph 2 (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) (rlc_dualReflectConfig omega))).Walk (rlc_dualReflect x) (rlc_dualReflect y), q.edges = (rlc_dualReflectOpenWalk (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega) (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega))).edges ∧ q.support = (rlc_dualReflectOpenWalk (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega) (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega))).support := by
-- proof
  apply StatMech.Universality.rlc_dualReflect_wired_faceBoundaryWalk_of_local_support G hn hlt omega c hlocal


-- created on 2026-10-23
