import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.RSWArcSupport
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_mixedWiredConnectorEvent_of_openWalk_meets_paths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcSupport.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_of_openWalk_meets_paths_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {a b : Site 2}
  {q : (openSubgraph 2 (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega)).Walk a b}
-- given
  (hbox : ∀ z ∈ q.support, z ∈ rlc_connectorBox n)
  (hright : ∃ x ∈ q.support, x ∈ rlc_pathVertices gamma.1)
  (hleft : ∃ y ∈ q.support, y ∈ rlc_pathVertices gamma'.1) :
-- imply
  omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_of_openWalk_meets_paths G omega q hbox hright hleft

/--
[rlc_dualReflect_wired_open_of_relaxed_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcSupport.lean)
-/
@[path]
private lemma rlc_dualReflect_wired_open_of_relaxed_support_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)}
-- given
  (hsupport : e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 ∨ (e ∈ rlc_mixedAxisGapEdges G ∧ rlc_pimsEdgeEquiv e ∈ rlc_mixedAxisGapEdges G))
  (hopen : rlc_dualReflectConfig (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega) e = true) :
-- imply
  rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) (rlc_dualReflectConfig omega) e = true := by
-- proof
  apply StatMech.Universality.rlc_dualReflect_wired_open_of_relaxed_support G omega hsupport hopen

/--
[rlc_dualReflect_wired_walk_of_relaxed_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcSupport.lean)
-/
@[path]
private lemma rlc_dualReflect_wired_walk_of_relaxed_support_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2}
  {p : (openSubgraph 2 (rlc_dualReflectConfig (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega))).Walk x y}
-- given
  (hsupport : ∀ e ∈ p.edges, e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 ∨ (e ∈ rlc_mixedAxisGapEdges G ∧ rlc_pimsEdgeEquiv e ∈ rlc_mixedAxisGapEdges G)) :
-- imply
  ∃ q : (openSubgraph 2 (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) (rlc_dualReflectConfig omega))).Walk x y, q.edges = p.edges ∧ q.support = p.support := by
-- proof
  apply StatMech.Universality.rlc_dualReflect_wired_walk_of_relaxed_support G omega p hsupport

/--
[rlc_pimsEdgeEquiv_reflected_faceBoundaryEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcSupport.lean)
-/
@[path]
private lemma rlc_pimsEdgeEquiv_reflected_faceBoundaryEdge_eq
  {S : Set (Site 2)}
  {f g : Site 2}
-- given
  (hfg : (faceBoundaryGraph S).Adj f g) :
-- imply
  rlc_pimsEdgeEquiv s(rlc_dualReflect f, rlc_dualReflect g) = sharedPrimalEdge f g := by
-- proof
  apply StatMech.Universality.rlc_pimsEdgeEquiv_reflected_faceBoundaryEdge S hfg

/--
[rlc_mixedWired_faceBoundary_preimage_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcSupport.lean)
-/
@[path]
private lemma rlc_mixedWired_faceBoundary_preimage_closed_eq
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
  rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega (rlc_pimsEdgeEquiv s(rlc_dualReflect f, rlc_dualReflect g)) = false := by
-- proof
  apply StatMech.Universality.rlc_mixedWired_faceBoundary_preimage_closed G hn hlt omega hfg

/--
[rlc_mixedWired_faceBoundary_preimage_not_exposed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcSupport.lean)
-/
@[path]
private lemma rlc_mixedWired_faceBoundary_preimage_not_exposed_eq
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
  apply StatMech.Universality.rlc_mixedWired_faceBoundary_preimage_not_exposed G hn hlt omega hfg

/--
[rlc_mixedWired_faceBoundary_preimage_mem_mixedSupport_of_region_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcSupport.lean)
-/
@[path]
private lemma rlc_mixedWired_faceBoundary_preimage_mem_mixedSupport_of_region_incident_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {f g p q : Site 2}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hfg : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Adj f g)
  (hshared : sharedPrimalEdge f g = s(p, q))
  (hpR : p ∈ rect (-2 * n) (2 * n) (-n) n)
  (hqR : q ∈ rect (-2 * n) (2 * n) (-n) n)
  (hincident : p ∈ rlc_axisGapRegion G ∨ q ∈ rlc_axisGapRegion G) :
-- imply
  rlc_pimsEdgeEquiv s(rlc_dualReflect f, rlc_dualReflect g) ∈ rlc_mixedAxisGapEdges G := by
-- proof
  apply StatMech.Universality.rlc_mixedWired_faceBoundary_preimage_mem_mixedSupport_of_region_incident G hn hlt omega hfg hshared hpR hqR hincident

/--
[rlc_mixedWired_exists_faceBoundary_outside_transportSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcSupport.lean)
-/
@[path]
private lemma rlc_mixedWired_exists_faceBoundary_outside_transportSupport_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper) :
-- imply
  ∃ f g : Site 2, (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Adj f g ∧ s(rlc_dualReflect f, rlc_dualReflect g) ∉ (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∪ rlc_mixedAxisGapEdges G ∧ rlc_pimsEdgeEquiv s(rlc_dualReflect f, rlc_dualReflect g) ∉ rlc_mixedAxisGapEdges G := by
-- proof
  apply StatMech.Universality.rlc_mixedWired_exists_faceBoundary_outside_transportSupport G hn hlt omega

/--
[rlc_mixedWiredReachSet_faceBoundaryComplementaryArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcSupport.lean)
-/
@[path]
private lemma rlc_mixedWiredReachSet_faceBoundaryComplementaryArc_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
-- imply
  ∃ (t : ℤ) (f g : Site 2), G.lower ≤ t ∧ t < G.upper ∧ ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧ ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧ sharedPrimalEdge f g = s(![0, t], ![0, t + 1]) ∧ ∃ p : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Walk f g, s(f, g) ∉ p.edges := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredReachSet_faceBoundaryComplementaryArc G omega hno

/--
[rlc_dualReflect_wired_faceBoundaryWalk_of_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcSupport.lean)
-/
@[path]
private lemma rlc_dualReflect_wired_faceBoundaryWalk_of_support_eq
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
  (htarget : ∀ {f g : Site 2}, s(f, g) ∈ c.edges → s(rlc_dualReflect f, rlc_dualReflect g) ∈ (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∪ rlc_mixedAxisGapEdges G)
  (hsource : ∀ {f g : Site 2}, s(f, g) ∈ c.edges → sharedPrimalEdge f g ∈ rlc_mixedAxisGapEdges G) :
-- imply
  ∃ q : (openSubgraph 2 (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) (rlc_dualReflectConfig omega))).Walk (rlc_dualReflect x) (rlc_dualReflect y), q.edges = (rlc_dualReflectOpenWalk (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega) (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega))).edges ∧ q.support = (rlc_dualReflectOpenWalk (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega) (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega))).support := by
-- proof
  apply StatMech.Universality.rlc_dualReflect_wired_faceBoundaryWalk_of_support G hn hlt omega c htarget hsource

/--
[rlc_dualReflect_wired_faceBoundaryWalk_of_relaxed_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcSupport.lean)
-/
@[path]
private lemma rlc_dualReflect_wired_faceBoundaryWalk_of_relaxed_support_eq
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
  (hsupport : ∀ {f g : Site 2}, s(f, g) ∈ c.edges → s(rlc_dualReflect f, rlc_dualReflect g) ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 ∨ (s(rlc_dualReflect f, rlc_dualReflect g) ∈ rlc_mixedAxisGapEdges G ∧ sharedPrimalEdge f g ∈ rlc_mixedAxisGapEdges G)) :
-- imply
  ∃ q : (openSubgraph 2 (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) (rlc_dualReflectConfig omega))).Walk (rlc_dualReflect x) (rlc_dualReflect y), q.edges = (rlc_dualReflectOpenWalk (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega) (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega))).edges ∧ q.support = (rlc_dualReflectOpenWalk (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega) (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega))).support := by
-- proof
  apply StatMech.Universality.rlc_dualReflect_wired_faceBoundaryWalk_of_relaxed_support G hn hlt omega c hsupport

/--
[rlc_dualReflect_wired_faceBoundaryWalk_of_relaxed_region_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcSupport.lean)
-/
@[path]
private lemma rlc_dualReflect_wired_faceBoundaryWalk_of_relaxed_region_incident_eq
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
  (hloc : ∀ {f g : Site 2}, s(f, g) ∈ c.edges → s(rlc_dualReflect f, rlc_dualReflect g) ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 ∨ (s(rlc_dualReflect f, rlc_dualReflect g) ∈ rlc_mixedAxisGapEdges G ∧ ∃ p q : Site 2, sharedPrimalEdge f g = s(p, q) ∧ p ∈ rect (-2 * n) (2 * n) (-n) n ∧ q ∈ rect (-2 * n) (2 * n) (-n) n ∧ (p ∈ rlc_axisGapRegion G ∨ q ∈ rlc_axisGapRegion G))) :
-- imply
  ∃ q : (openSubgraph 2 (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) (rlc_dualReflectConfig omega))).Walk (rlc_dualReflect x) (rlc_dualReflect y), q.edges = (rlc_dualReflectOpenWalk (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega) (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega))).edges ∧ q.support = (rlc_dualReflectOpenWalk (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega) (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega))).support := by
-- proof
  apply StatMech.Universality.rlc_dualReflect_wired_faceBoundaryWalk_of_relaxed_region_incident G hn hlt omega c hloc

/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_faceBoundaryArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcSupport.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_faceBoundaryArc_eq
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
  (hloc : ∀ {f g : Site 2}, s(f, g) ∈ c.edges → s(rlc_dualReflect f, rlc_dualReflect g) ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 ∨ (s(rlc_dualReflect f, rlc_dualReflect g) ∈ rlc_mixedAxisGapEdges G ∧ ∃ p q : Site 2, sharedPrimalEdge f g = s(p, q) ∧ p ∈ rect (-2 * n) (2 * n) (-n) n ∧ q ∈ rect (-2 * n) (2 * n) (-n) n ∧ (p ∈ rlc_axisGapRegion G ∨ q ∈ rlc_axisGapRegion G)))
  (hbox : ∀ z ∈ (rlc_dualReflectOpenWalk (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega) (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega))).support, z ∈ rlc_connectorBox n)
  (hright : ∃ z ∈ (rlc_dualReflectOpenWalk (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega) (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega))).support, z ∈ rlc_pathVertices gamma.1)
  (hleft : ∃ z ∈ (rlc_dualReflectOpenWalk (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega) (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega))).support, z ∈ rlc_pathVertices gamma'.1) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_faceBoundaryArc G hn hlt omega c hloc hbox hright hleft

/--
[rlc_dualReflect_wired_faceBoundaryWalk_of_region_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcSupport.lean)
-/
@[path]
private lemma rlc_dualReflect_wired_faceBoundaryWalk_of_region_incident_eq
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
  (htarget : ∀ {f g : Site 2}, s(f, g) ∈ c.edges → s(rlc_dualReflect f, rlc_dualReflect g) ∈ (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∪ rlc_mixedAxisGapEdges G)
  (hloc : ∀ {f g : Site 2}, s(f, g) ∈ c.edges → ∃ p q : Site 2, sharedPrimalEdge f g = s(p, q) ∧ p ∈ rect (-2 * n) (2 * n) (-n) n ∧ q ∈ rect (-2 * n) (2 * n) (-n) n ∧ (p ∈ rlc_axisGapRegion G ∨ q ∈ rlc_axisGapRegion G)) :
-- imply
  ∃ q : (openSubgraph 2 (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) (rlc_dualReflectConfig omega))).Walk (rlc_dualReflect x) (rlc_dualReflect y), q.edges = (rlc_dualReflectOpenWalk (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega) (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega))).edges ∧ q.support = (rlc_dualReflectOpenWalk (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega) (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega))).support := by
-- proof
  apply StatMech.Universality.rlc_dualReflect_wired_faceBoundaryWalk_of_region_incident G hn hlt omega c htarget hloc


-- created on 2026-10-23
