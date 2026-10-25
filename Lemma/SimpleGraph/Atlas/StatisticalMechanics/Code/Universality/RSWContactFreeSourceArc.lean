import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWContactFreeSourceArc
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_mixedWired_reflected_faceBoundaryEdge_open_raw_of_sourceSupported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWContactFreeSourceArc.lean)
-/
@[path]
private lemma rlc_mixedWired_reflected_faceBoundaryEdge_open_raw_of_sourceSupported_eq
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
  (hsource : sharedPrimalEdge f g ∈ rlc_mixedAxisGapEdges G) :
-- imply
  rlc_dualReflectConfig omega s(rlc_dualReflect f, rlc_dualReflect g) = true := by
-- proof
  apply StatMech.Universality.rlc_mixedWired_reflected_faceBoundaryEdge_open_raw_of_sourceSupported G hn hlt omega hfg hsource

/--
[rlc_mixedWired_reflected_faceBoundaryEdge_open_raw_or_sourceDefect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWContactFreeSourceArc.lean)
-/
@[path]
private lemma rlc_mixedWired_reflected_faceBoundaryEdge_open_raw_or_sourceDefect_eq
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
  rlc_dualReflectConfig omega s(rlc_dualReflect f, rlc_dualReflect g) = true ∨ sharedPrimalEdge f g ∉ rlc_mixedAxisGapEdges G := by
-- proof
  apply StatMech.Universality.rlc_mixedWired_reflected_faceBoundaryEdge_open_raw_or_sourceDefect G hn hlt omega hfg

/--
[rlc_dualReflect_raw_faceBoundaryWalk_of_sourceSupported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWContactFreeSourceArc.lean)
-/
@[path]
private lemma rlc_dualReflect_raw_faceBoundaryWalk_of_sourceSupported_eq
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
  (hsource : RlcFaceBoundaryWalkSourceSupported G omega c) :
-- imply
  ∃ q : (openSubgraph 2 (rlc_dualReflectConfig omega)).Walk (rlc_dualReflect x) (rlc_dualReflect y), q.edges = (rlc_dualReflectOpenWalk (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega) (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega))).edges ∧ q.support = (rlc_dualReflectOpenWalk (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega) (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega))).support := by
-- proof
  apply StatMech.Universality.rlc_dualReflect_raw_faceBoundaryWalk_of_sourceSupported G hn hlt omega c hsource

/--
[rlc_dualReflectOpenWalk_edge_not_mem_of_edge_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWContactFreeSourceArc.lean)
-/
@[path]
private lemma rlc_dualReflectOpenWalk_edge_not_mem_of_edge_not_mem_eq
  {S : Set (Site 2)}
  {eta : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2}
  {c : (faceBoundaryGraph S).Walk x y}
  {e : Sym2 (Site 2)}
-- given
  (hle : faceBoundaryGraph S ≤ openSubgraph 2 (fci_faceDualConfig eta))
  (he : e ∉ c.edges) :
-- imply
  rlc_dualReflectEdge e ∉ (rlc_dualReflectOpenWalk eta (c.mapLe hle)).edges := by
-- proof
  apply StatMech.Universality.rlc_dualReflectOpenWalk_edge_not_mem_of_edge_not_mem S eta c hle he

/--
[rlc_mixedWiredReachSet_faceBoundaryComplementaryArc_with_anchorAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWContactFreeSourceArc.lean)
-/
@[path]
private lemma rlc_mixedWiredReachSet_faceBoundaryComplementaryArc_with_anchorAdj_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
-- imply
  ∃ (t : ℤ) (f g : Site 2), G.lower ≤ t ∧ t < G.upper ∧ ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧ ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧ (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Adj f g ∧ sharedPrimalEdge f g = s(![0, t], ![0, t + 1]) ∧ ∃ p : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Walk f g, s(f, g) ∉ p.edges := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredReachSet_faceBoundaryComplementaryArc_with_anchorAdj G omega hno

/--
[rlc_mixedWiredFailure_faceBoundaryArc_sourceNormalForm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWContactFreeSourceArc.lean)
-/
@[path]
private lemma rlc_mixedWiredFailure_faceBoundaryArc_sourceNormalForm_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
-- imply
  ∃ (t : ℤ) (f g : Site 2) (p : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Walk f g), G.lower ≤ t ∧ t < G.upper ∧ ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧ ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧ (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Adj f g ∧ sharedPrimalEdge f g = s(![0, t], ![0, t + 1]) ∧ s(f, g) ∉ p.edges ∧ s(![0, t], ![0, t + 1]) ∈ rlc_mixedAxisGapEdges G ∧ omega s(![0, t], ![0, t + 1]) = false ∧ rlc_dualReflectConfig omega s(![-1, t + 1], ![0, t + 1]) = true ∧ ∀ {a b : Site 2}, s(a, b) ∈ p.edges → rlc_pimsEdgeEquiv s(rlc_dualReflect a, rlc_dualReflect b) = sharedPrimalEdge a b ∧ rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega (rlc_pimsEdgeEquiv s(rlc_dualReflect a, rlc_dualReflect b)) = false ∧ rlc_pimsEdgeEquiv s(rlc_dualReflect a, rlc_dualReflect b) ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 ∧ (rlc_pimsEdgeEquiv s(rlc_dualReflect a, rlc_dualReflect b) ∈ rlc_mixedAxisGapEdges G ↔ sharedPrimalEdge a b ∈ rlc_axisGapEdges G ∨ sharedPrimalEdge a b ∈ rlc_reflectedPathEdges gamma.1 ∨ sharedPrimalEdge a b ∈ rlc_reflectedPathEdges gamma'.1) := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredFailure_faceBoundaryArc_sourceNormalForm G hn hlt omega hno

/--
[rlc_mixedWiredFailure_faceBoundaryArc_rawOpen_or_sourceDefect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWContactFreeSourceArc.lean)
-/
@[path]
private lemma rlc_mixedWiredFailure_faceBoundaryArc_rawOpen_or_sourceDefect_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
-- imply
  ∃ (t : ℤ) (f g : Site 2) (p : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Walk f g), G.lower ≤ t ∧ t < G.upper ∧ ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧ ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧ (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Adj f g ∧ sharedPrimalEdge f g = s(![0, t], ![0, t + 1]) ∧ s(f, g) ∉ p.edges ∧ ∀ {a b : Site 2}, s(a, b) ∈ p.edges → rlc_dualReflectConfig omega s(rlc_dualReflect a, rlc_dualReflect b) = true ∨ sharedPrimalEdge a b ∉ rlc_mixedAxisGapEdges G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredFailure_faceBoundaryArc_rawOpen_or_sourceDefect G hn hlt omega hno

/--
[rlc_mixedWiredFailure_rawComplementaryArc_or_sourceDefect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWContactFreeSourceArc.lean)
-/
@[path]
private lemma rlc_mixedWiredFailure_rawComplementaryArc_or_sourceDefect_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
-- imply
  ∃ (t : ℤ) (f g : Site 2) (p : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Walk f g), G.lower ≤ t ∧ t < G.upper ∧ ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧ ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧ (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Adj f g ∧ sharedPrimalEdge f g = s(![0, t], ![0, t + 1]) ∧ s(f, g) ∉ p.edges ∧ ((∃ q : (openSubgraph 2 (rlc_dualReflectConfig omega)).Walk (rlc_dualReflect f) (rlc_dualReflect g), q.edges = (rlc_dualReflectOpenWalk (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega) (p.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega))).edges ∧ q.support = (rlc_dualReflectOpenWalk (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega) (p.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega))).support ∧ s(rlc_dualReflect f, rlc_dualReflect g) ∉ q.edges) ∨ ∃ a b : Site 2, s(a, b) ∈ p.edges ∧ sharedPrimalEdge a b ∉ rlc_mixedAxisGapEdges G) := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredFailure_rawComplementaryArc_or_sourceDefect G hn hlt omega hno

/--
[rlc_dualReflect_wired_faceBoundaryWalk_of_relaxedLocal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWContactFreeSourceArc.lean)
-/
@[path]
private lemma rlc_dualReflect_wired_faceBoundaryWalk_of_relaxedLocal_eq
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
  (hlocal : ∀ {f g : Site 2}, s(f, g) ∈ c.edges → rlc_contourEdgeRelaxedLocal G f g) :
-- imply
  ∃ q : (openSubgraph 2 (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) (rlc_dualReflectConfig omega))).Walk (rlc_dualReflect x) (rlc_dualReflect y), q.edges = (rlc_dualReflectOpenWalk (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega) (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega))).edges ∧ q.support = (rlc_dualReflectOpenWalk (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega) (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega))).support := by
-- proof
  apply StatMech.Universality.rlc_dualReflect_wired_faceBoundaryWalk_of_relaxedLocal G hn hlt omega c hlocal

/--
[rlc_mixedWiredFailure_wiredComplementaryArc_or_relaxedLocalDefect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWContactFreeSourceArc.lean)
-/
@[path]
private lemma rlc_mixedWiredFailure_wiredComplementaryArc_or_relaxedLocalDefect_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
-- imply
  ∃ (t : ℤ) (f g : Site 2) (p : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Walk f g), G.lower ≤ t ∧ t < G.upper ∧ ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧ ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧ (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Adj f g ∧ sharedPrimalEdge f g = s(![0, t], ![0, t + 1]) ∧ s(f, g) ∉ p.edges ∧ ((∃ q : (openSubgraph 2 (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) (rlc_dualReflectConfig omega))).Walk (rlc_dualReflect f) (rlc_dualReflect g), q.edges = (rlc_dualReflectOpenWalk (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega) (p.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega))).edges ∧ q.support = (rlc_dualReflectOpenWalk (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega) (p.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega))).support ∧ s(rlc_dualReflect f, rlc_dualReflect g) ∉ q.edges) ∨ ∃ a b : Site 2, s(a, b) ∈ p.edges ∧ ¬ rlc_contourEdgeRelaxedLocal G a b) := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredFailure_wiredComplementaryArc_or_relaxedLocalDefect G hn hlt omega hno


-- created on 2026-10-23
