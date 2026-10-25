import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWArcBadPlacement.Part6
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_contourArc_edges_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcBadPlacement.lean)
-/
@[path]
private lemma rlc_contourArc_edges_cover_eq
  {H : SimpleGraph (Site 2)}
  {u x y : Site 2}
  {c : H.Walk u u}
  {e : Sym2 (Site 2)}
-- given
  (hx : x ∈ c.support)
  (hy : y ∈ c.support) :
-- imply
  e ∈ c.edges ↔ e ∈ (rlc_orderedContourArc c hx hy).edges ∨ e ∈ (rlc_complementaryContourArc c hx hy).edges := by
-- proof
  apply StatMech.Universality.rlc_contourArc_edges_cover c hx hy

/--
[rlc_contourArcLocalSide_iff_badEdgesOnOneArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcBadPlacement.lean)
-/
@[path]
private lemma rlc_contourArcLocalSide_iff_badEdgesOnOneArc_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Walk u u}
-- given
  (hc : c.IsTrail)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support) :
-- imply
  RlcContourArcLocalSide G omega c hx hy ↔ RlcContourBadEdgesOnOneArcAt G omega c hx hy := by
-- proof
  apply StatMech.Universality.rlc_contourArcLocalSide_iff_badEdgesOnOneArc G omega c hc hx hy

/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_traceContactsCutOffBadEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcBadPlacement.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_traceContactsCutOffBadEdges_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {u : Site 2}
  {c : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Walk u u}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hc : c.IsTrail)
  (hcut : RlcTraceContactsCutOffBadEdges G omega c) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_traceContactsCutOffBadEdges G hn hlt omega c hc hcut

/--
[rlc_contourEdgeRelaxedLocal_not_strict_of_exposed_not_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcBadPlacement.lean)
-/
@[path]
private lemma rlc_contourEdgeRelaxedLocal_not_strict_of_exposed_not_source_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {f g : Site 2}
-- given
  (hexposed : s(rlc_dualReflect f, rlc_dualReflect g) ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1)
  (hsource : ¬ rlc_boundarySourceLocallySupported G (sharedPrimalEdge f g)) :
-- imply
  rlc_contourEdgeRelaxedLocal G f g ∧ ¬ rlc_contourEdgeLocal G f g := by
-- proof
  apply StatMech.Universality.rlc_contourEdgeRelaxedLocal_not_strict_of_exposed_not_source G hexposed hsource

/--
[rlc_contourArcRelaxedLocalSide_iff_badEdgesOnOneArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcBadPlacement.lean)
-/
@[path]
private lemma rlc_contourArcRelaxedLocalSide_iff_badEdgesOnOneArc_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Walk u u}
-- given
  (hc : c.IsTrail)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support) :
-- imply
  RlcContourArcRelaxedLocalSide G omega c hx hy ↔ RlcContourRelaxedBadEdgesOnOneArcAt G omega c hx hy := by
-- proof
  apply StatMech.Universality.rlc_contourArcRelaxedLocalSide_iff_badEdgesOnOneArc G omega c hc hx hy

/--
[rlc_contourArcRelaxedLocalSide_of_localSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcBadPlacement.lean)
-/
@[path]
private lemma rlc_contourArcRelaxedLocalSide_of_localSide_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Walk u u}
-- given
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hside : RlcContourArcLocalSide G omega c hx hy) :
-- imply
  RlcContourArcRelaxedLocalSide G omega c hx hy := by
-- proof
  apply StatMech.Universality.rlc_contourArcRelaxedLocalSide_of_localSide G omega c hx hy hside

/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcBadPlacement.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalArc_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2}
  {a : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Walk x y}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hlocal : ∀ {f g : Site 2}, s(f, g) ∈ a.edges → rlc_contourEdgeRelaxedLocal G f g) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalArc G hn hlt omega a hxPath hyPath hlocal

/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcBadPlacement.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalSide_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Walk u u}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hside : RlcContourArcRelaxedLocalSide G omega c hx hy) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalSide G hn hlt omega c hx hy hxPath hyPath hside

/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_traceContactsCutOffRelaxedBadEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcBadPlacement.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_traceContactsCutOffRelaxedBadEdges_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {u : Site 2}
  {c : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Walk u u}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hc : c.IsTrail)
  (hcut : RlcTraceContactsCutOffRelaxedBadEdges G omega c) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_traceContactsCutOffRelaxedBadEdges G hn hlt omega c hc hcut


-- created on 2026-10-23
