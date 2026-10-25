import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWArcJordan.Part2
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_reflectedTargetLocallySupported_endpoint_mem_connectorBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcJordan.lean)
-/
@[path]
private lemma rlc_reflectedTargetLocallySupported_endpoint_mem_connectorBox_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {e : Sym2 (Site 2)}
  {z : Site 2}
-- given
  (he : rlc_reflectedTargetLocallySupported G e)
  (hz : z ∈ e) :
-- imply
  z ∈ rlc_connectorBox n := by
-- proof
  apply StatMech.Universality.rlc_reflectedTargetLocallySupported_endpoint_mem_connectorBox G he hz

/--
[rlc_walk_support_mem_connectorBox_of_targetLocal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcJordan.lean)
-/
@[path]
private lemma rlc_walk_support_mem_connectorBox_of_targetLocal_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {x y : Site 2}
  {H : SimpleGraph (Site 2)}
  {a : H.Walk x y}
-- given
  (hy : y ∈ rlc_connectorBox n)
  (hlocal : ∀ {f g : Site 2}, s(f, g) ∈ a.edges → rlc_reflectedTargetLocallySupported G s(f, g)) :
-- imply
  ∀ z ∈ a.support, z ∈ rlc_connectorBox n := by
-- proof
  apply StatMech.Universality.rlc_walk_support_mem_connectorBox_of_targetLocal G a hy hlocal

/--
[rlc_faceBoundaryArc_reflected_support_mem_connectorBox_of_targetLocal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcJordan.lean)
-/
@[path]
private lemma rlc_faceBoundaryArc_reflected_support_mem_connectorBox_of_targetLocal_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {x y : Site 2}
  {H : SimpleGraph (Site 2)}
  {a : H.Walk x y}
-- given
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hlocal : ∀ {f g : Site 2}, s(f, g) ∈ a.edges → rlc_reflectedTargetLocallySupported G s(rlc_dualReflect f, rlc_dualReflect g)) :
-- imply
  ∀ z ∈ a.support, rlc_dualReflect z ∈ rlc_connectorBox n := by
-- proof
  apply StatMech.Universality.rlc_faceBoundaryArc_reflected_support_mem_connectorBox_of_targetLocal G a hyPath hlocal

/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_contourArcLocalSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcJordan.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_contourArcLocalSide_eq
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
  (hside : RlcContourArcLocalSide G omega c hx hy) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_contourArcLocalSide G hn hlt omega c hx hy hxPath hyPath hside

/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_straddles_of_arcLocalSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcJordan.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_straddles_of_arcLocalSide_eq
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
  (hright : rlc_TraceStraddlesLoop ((rlc_dualReflectOpenWalk (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega) (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega))).mapLe (rlc_openSubgraph_le_lattice _)) gamma.1)
  (hleft : rlc_TraceStraddlesLoop ((rlc_dualReflectOpenWalk (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega) (c.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega))).mapLe (rlc_openSubgraph_le_lattice _)) gamma'.1)
  (hJordan : ∀ {x y : Site 2} (hx : x ∈ c.support) (hy : y ∈ c.support), rlc_dualReflect x ∈ rlc_pathVertices gamma.1 → rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 → RlcContourArcLocalSide G omega c hx hy) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_straddles_of_arcLocalSide G hn hlt omega c hright hleft hJordan


-- created on 2026-10-23
