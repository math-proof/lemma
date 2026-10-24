import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.RSWSourceArcPlacement
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_mem_axisGapEdges_iff_edgeBoxIncidentGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma rlc_mem_axisGapEdges_iff_edgeBoxIncidentGap_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {e : Sym2 (Site 2)}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper) :
-- imply
  e ∈ rlc_axisGapEdges G ↔ rlc_edgeBoxIncidentGap G e := by
-- proof
  apply StatMech.Universality.rlc_mem_axisGapEdges_iff_edgeBoxIncidentGap G hn hlt e

/--
[rlc_mixedWired_faceBoundary_sourceSupported_iff_sourceLocal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma rlc_mixedWired_faceBoundary_sourceSupported_iff_sourceLocal_eq
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
  sharedPrimalEdge f g ∈ rlc_mixedAxisGapEdges G ↔ rlc_boundarySourceLocallySupported G (sharedPrimalEdge f g) := by
-- proof
  apply StatMech.Universality.rlc_mixedWired_faceBoundary_sourceSupported_iff_sourceLocal G hn hlt omega hfg

/--
[rlc_faceBoundaryWalk_sourceSupported_iff_sourceLocal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma rlc_faceBoundaryWalk_sourceSupported_iff_sourceLocal_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2}
  {c : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Walk x y}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper) :
-- imply
  RlcFaceBoundaryWalkSourceSupported G omega c ↔ ∀ {f g : Site 2}, s(f, g) ∈ c.edges → rlc_boundarySourceLocallySupported G (sharedPrimalEdge f g) := by
-- proof
  apply StatMech.Universality.rlc_faceBoundaryWalk_sourceSupported_iff_sourceLocal G hn hlt omega c

/--
[rlc_contourEdgeRelaxedLocal_iff_targetLocal_of_sourceSupported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma rlc_contourEdgeRelaxedLocal_iff_targetLocal_of_sourceSupported_eq
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
  rlc_contourEdgeRelaxedLocal G f g ↔ rlc_reflectedTargetLocallySupported G s(rlc_dualReflect f, rlc_dualReflect g) := by
-- proof
  apply StatMech.Universality.rlc_contourEdgeRelaxedLocal_iff_targetLocal_of_sourceSupported G hn hlt omega hfg hsource

/--
[rlc_contourEdgeRelaxedLocal_comm_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma rlc_contourEdgeRelaxedLocal_comm_of_adj_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {f g : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f g) :
-- imply
  rlc_contourEdgeRelaxedLocal G f g ↔ rlc_contourEdgeRelaxedLocal G g f := by
-- proof
  apply StatMech.Universality.rlc_contourEdgeRelaxedLocal_comm_of_adj G hfg

/--
[rlc_contourEdgeRelaxedLocal_of_mk_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma rlc_contourEdgeRelaxedLocal_of_mk_eq_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {f g a b : Site 2}
-- given
  (hab : (hypercubicLattice 2).Adj a b)
  (he : s(f, g) = s(a, b))
  (hlocal : rlc_contourEdgeRelaxedLocal G a b) :
-- imply
  rlc_contourEdgeRelaxedLocal G f g := by
-- proof
  apply StatMech.Universality.rlc_contourEdgeRelaxedLocal_of_mk_eq G hab he hlocal

/--
[rlc_faceBoundaryWalk_relaxedLocal_iff_targetLocal_of_sourceSupported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma rlc_faceBoundaryWalk_relaxedLocal_iff_targetLocal_of_sourceSupported_eq
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
  (∀ {f g : Site 2}, s(f, g) ∈ c.edges → rlc_contourEdgeRelaxedLocal G f g) ↔ ∀ {f g : Site 2}, s(f, g) ∈ c.edges → rlc_reflectedTargetLocallySupported G s(rlc_dualReflect f, rlc_dualReflect g) := by
-- proof
  apply StatMech.Universality.rlc_faceBoundaryWalk_relaxedLocal_iff_targetLocal_of_sourceSupported G hn hlt omega c hsource

/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalWalk_meets_paths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalWalk_meets_paths_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {u v : Site 2}
  {c : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Walk u v}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hlocal : ∀ {f g : Site 2}, s(f, g) ∈ c.edges → rlc_contourEdgeRelaxedLocal G f g)
  (hright : ∃ x ∈ c.support, rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hleft : ∃ y ∈ c.support, rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalWalk_meets_paths G hn hlt omega c hlocal hright hleft

/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_sourceSupportedWalk_meets_paths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_sourceSupportedWalk_meets_paths_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {u v : Site 2}
  {c : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Walk u v}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hsource : RlcFaceBoundaryWalkSourceSupported G omega c)
  (htarget : ∀ {f g : Site 2}, s(f, g) ∈ c.edges → rlc_reflectedTargetLocallySupported G s(rlc_dualReflect f, rlc_dualReflect g))
  (hright : ∃ x ∈ c.support, rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hleft : ∃ y ∈ c.support, rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_sourceSupportedWalk_meets_paths G hn hlt omega c hsource htarget hright hleft

/--
[rlc_sourceSupportedWalk_targetDefect_of_dualReflect_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma rlc_sourceSupportedWalk_targetDefect_of_dualReflect_failure_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {u v : Site 2}
  {c : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Walk u v}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hno : rlc_dualReflectConfig omega ∉ rlc_mixedWiredConnectorEvent G)
  (hsource : RlcFaceBoundaryWalkSourceSupported G omega c)
  (hright : ∃ x ∈ c.support, rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hleft : ∃ y ∈ c.support, rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
-- imply
  ∃ f g : Site 2, s(f, g) ∈ c.edges ∧ ¬ rlc_reflectedTargetLocallySupported G s(rlc_dualReflect f, rlc_dualReflect g) := by
-- proof
  apply StatMech.Universality.rlc_sourceSupportedWalk_targetDefect_of_dualReflect_failure G hn hlt omega hno c hsource hright hleft

/--
[rlc_relaxedLocalTraceArcExists_iff_not_defectCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma rlc_relaxedLocalTraceArcExists_iff_not_defectCut_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  RlcRelaxedLocalTraceArcExists G omega ↔ ¬ RlcRelaxedLocalDefectsSeparateTraces G omega := by
-- proof
  apply StatMech.Universality.rlc_relaxedLocalTraceArcExists_iff_not_defectCut G omega

/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalTraceArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalTraceArc_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (h : RlcRelaxedLocalTraceArcExists G omega) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalTraceArc G hn hlt omega h

/--
[rlc_relaxedLocalDefectsSeparateTraces_of_dualReflect_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma rlc_relaxedLocalDefectsSeparateTraces_of_dualReflect_failure_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hno : rlc_dualReflectConfig omega ∉ rlc_mixedWiredConnectorEvent G) :
-- imply
  RlcRelaxedLocalDefectsSeparateTraces G omega := by
-- proof
  apply StatMech.Universality.rlc_relaxedLocalDefectsSeparateTraces_of_dualReflect_failure G hn hlt omega hno

/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_not_defectCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_not_defectCut_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hcut : ¬ RlcRelaxedLocalDefectsSeparateTraces G omega) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_not_defectCut G hn hlt omega hcut

/--
[rlc_carriesRelaxedTraceArc_iff_not_defectsHitTraceSubwalksOf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma rlc_carriesRelaxedTraceArc_iff_not_defectsHitTraceSubwalksOf_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {u v : Site 2}
  {p : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Walk u v} :
-- imply
  RlcFaceBoundaryWalkCarriesRelaxedTraceArc G omega p ↔ ¬ RlcRelaxedLocalDefectsHitTraceSubwalksOf G omega p := by
-- proof
  apply StatMech.Universality.rlc_carriesRelaxedTraceArc_iff_not_defectsHitTraceSubwalksOf G omega p

/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_carriesRelaxedTraceArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_carriesRelaxedTraceArc_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {u v : Site 2}
  {p : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Walk u v}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hcarry : RlcFaceBoundaryWalkCarriesRelaxedTraceArc G omega p) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_carriesRelaxedTraceArc G hn hlt omega p hcarry

/--
[RlcRelaxedLocalDefectsSeparateTraces.hitTraceSubwalksOf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma hitTraceSubwalksOf_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {u v : Site 2}
  {p : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Walk u v}
-- given
  (hcut : RlcRelaxedLocalDefectsSeparateTraces G omega) :
-- imply
  RlcRelaxedLocalDefectsHitTraceSubwalksOf G omega p := by
-- proof
  apply StatMech.Universality.RlcRelaxedLocalDefectsSeparateTraces.hitTraceSubwalksOf hcut p

/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_failureComplementaryArcEscapes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_failureComplementaryArcEscapes_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hplace : RlcFailureComplementaryArcEscapesDefectCut G omega) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_failureComplementaryArcEscapes G hn hlt omega hplace

/--
[not_failureComplementaryArcEscapes_of_dualReflect_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma not_failureComplementaryArcEscapes_of_dualReflect_failure_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hno : rlc_dualReflectConfig omega ∉ rlc_mixedWiredConnectorEvent G) :
-- imply
  ¬ RlcFailureComplementaryArcEscapesDefectCut G omega := by
-- proof
  apply StatMech.Universality.not_failureComplementaryArcEscapes_of_dualReflect_failure G hn hlt omega hno

/--
[rlc_doubleFailure_complementaryArc_trace_or_relaxedLocalDefect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma rlc_doubleFailure_complementaryArc_trace_or_relaxedLocalDefect_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
  (hnoReflect : rlc_dualReflectConfig omega ∉ rlc_mixedWiredConnectorEvent G) :
-- imply
  ∃ (t : ℤ) (f g : Site 2) (p : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Walk f g), G.lower ≤ t ∧ t < G.upper ∧ ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧ ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧ (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Adj f g ∧ sharedPrimalEdge f g = s(![0, t], ![0, t + 1]) ∧ s(f, g) ∉ p.edges ∧ ((∀ x ∈ p.support, rlc_dualReflect x ∉ rlc_pathVertices gamma.1) ∨ (∀ y ∈ p.support, rlc_dualReflect y ∉ rlc_pathVertices gamma'.1) ∨ ∃ a b : Site 2, s(a, b) ∈ p.edges ∧ ¬ rlc_contourEdgeRelaxedLocal G a b) := by
-- proof
  apply StatMech.Universality.rlc_doubleFailure_complementaryArc_trace_or_relaxedLocalDefect G hn hlt omega hno hnoReflect

/--
[rlc_doubleFailure_complementaryArc_defectCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma rlc_doubleFailure_complementaryArc_defectCut_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
  (hnoReflect : rlc_dualReflectConfig omega ∉ rlc_mixedWiredConnectorEvent G) :
-- imply
  ∃ (t : ℤ) (f g : Site 2) (p : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Walk f g), G.lower ≤ t ∧ t < G.upper ∧ ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧ ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧ (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Adj f g ∧ sharedPrimalEdge f g = s(![0, t], ![0, t + 1]) ∧ s(f, g) ∉ p.edges ∧ RlcRelaxedLocalDefectsHitTraceSubwalksOf G omega p := by
-- proof
  apply StatMech.Universality.rlc_doubleFailure_complementaryArc_defectCut G hn hlt omega hno hnoReflect

/--
[rlc_traceSplitCounterexample_boundaryArc_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma rlc_traceSplitCounterexample_boundaryArc_edges_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hK : rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega = (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2))) :
-- imply
  (rlc_traceSplitCounterexample_boundaryArc omega hK).edges = [s((![-1, -2] : Site 2), ![-1, -1]), s((![-1, -1] : Site 2), ![0, -1]), s((![0, -1] : Site 2), ![1, -1])] := by
-- proof
  apply StatMech.Universality.rlc_traceSplitCounterexample_boundaryArc_edges omega hK

/--
[rlc_traceSplitCounterexample_boundaryArc_rightContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma rlc_traceSplitCounterexample_boundaryArc_rightContact_eq :
-- imply
  rlc_dualReflect (![-1, -2] : Site 2) ∈ rlc_pathVertices rlc_traceSplitCounterexampleRight.1 := by
-- proof
  apply StatMech.Universality.rlc_traceSplitCounterexample_boundaryArc_rightContact

/--
[rlc_traceSplitCounterexample_boundaryArc_leftContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma rlc_traceSplitCounterexample_boundaryArc_leftContact_eq :
-- imply
  rlc_dualReflect (![1, -1] : Site 2) ∈ rlc_pathVertices rlc_traceSplitCounterexampleLeft.1 := by
-- proof
  apply StatMech.Universality.rlc_traceSplitCounterexample_boundaryArc_leftContact

/--
[rlc_traceSplitCounterexample_boundaryArc_relaxed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma rlc_traceSplitCounterexample_boundaryArc_relaxed_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hK : rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega = (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2))) :
-- imply
  ∀ {f g : Site 2}, s(f, g) ∈ (rlc_traceSplitCounterexample_boundaryArc omega hK).edges → rlc_contourEdgeRelaxedLocal rlc_windingSideCounterexampleGap f g := by
-- proof
  apply StatMech.Universality.rlc_traceSplitCounterexample_boundaryArc_relaxed omega hK

/--
[rlc_traceSplitCounterexample_not_defectCut_of_reachSet_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma rlc_traceSplitCounterexample_not_defectCut_of_reachSet_eq_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hK : rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega = (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2))) :
-- imply
  ¬ RlcRelaxedLocalDefectsSeparateTraces rlc_windingSideCounterexampleGap omega := by
-- proof
  apply StatMech.Universality.rlc_traceSplitCounterexample_not_defectCut_of_reachSet_eq omega hK

/--
[rlc_windingSideCounterexample_not_defectCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma rlc_windingSideCounterexample_not_defectCut_eq :
-- imply
  ¬ RlcRelaxedLocalDefectsSeparateTraces rlc_windingSideCounterexampleGap rlc_windingSideCounterexampleConfig := by
-- proof
  apply StatMech.Universality.rlc_windingSideCounterexample_not_defectCut

/--
[rlc_axisOrContactCounterexample_not_defectCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma rlc_axisOrContactCounterexample_not_defectCut_eq :
-- imply
  ¬ RlcRelaxedLocalDefectsSeparateTraces rlc_windingSideCounterexampleGap rlc_axisOrContactCounterexampleConfig := by
-- proof
  apply StatMech.Universality.rlc_axisOrContactCounterexample_not_defectCut

/--
[rlc_axisOrContactCounterexample_dual_success](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean)
-/
@[path]
private lemma rlc_axisOrContactCounterexample_dual_success_eq :
-- imply
  rlc_dualReflectConfig rlc_axisOrContactCounterexampleConfig ∈ rlc_mixedWiredConnectorEvent rlc_windingSideCounterexampleGap := by
-- proof
  apply StatMech.Universality.rlc_axisOrContactCounterexample_dual_success


-- created on 2026-10-23
