import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWOuterArc
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_orderedContourArc_support_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterArc.lean)
-/
@[path]
private lemma rlc_orderedContourArc_support_subset_eq
  {H : SimpleGraph (Site 2)}
  {u x y : Site 2}
  {c : H.Walk u u}
-- given
  (hx : x ∈ c.support)
  (hy : y ∈ c.support) :
-- imply
  (rlc_orderedContourArc c hx hy).support ⊆ c.support := by
-- proof
  apply StatMech.Universality.rlc_orderedContourArc_support_subset c hx hy

/--
[rlc_orderedContourArc_edges_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterArc.lean)
-/
@[path]
private lemma rlc_orderedContourArc_edges_subset_eq
  {H : SimpleGraph (Site 2)}
  {u x y : Site 2}
  {c : H.Walk u u}
-- given
  (hx : x ∈ c.support)
  (hy : y ∈ c.support) :
-- imply
  (rlc_orderedContourArc c hx hy).edges ⊆ c.edges := by
-- proof
  apply StatMech.Universality.rlc_orderedContourArc_edges_subset c hx hy

/--
[rlc_complementaryContourArc_support_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterArc.lean)
-/
@[path]
private lemma rlc_complementaryContourArc_support_subset_eq
  {H : SimpleGraph (Site 2)}
  {u x y : Site 2}
  {c : H.Walk u u}
-- given
  (hx : x ∈ c.support)
  (hy : y ∈ c.support) :
-- imply
  (rlc_complementaryContourArc c hx hy).support ⊆ c.support := by
-- proof
  apply StatMech.Universality.rlc_complementaryContourArc_support_subset c hx hy

/--
[rlc_complementaryContourArc_edges_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterArc.lean)
-/
@[path]
private lemma rlc_complementaryContourArc_edges_subset_eq
  {H : SimpleGraph (Site 2)}
  {u x y : Site 2}
  {c : H.Walk u u}
-- given
  (hx : x ∈ c.support)
  (hy : y ∈ c.support) :
-- imply
  (rlc_complementaryContourArc c hx hy).edges ⊆ c.edges := by
-- proof
  apply StatMech.Universality.rlc_complementaryContourArc_edges_subset c hx hy

/--
[rlc_select_complementaryContourArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterArc.lean)
-/
@[path]
private lemma rlc_select_complementaryContourArc_eq
  {H : SimpleGraph (Site 2)}
  {u x y : Site 2}
  {c : H.Walk u u}
-- given
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (Pv : Site 2 → Prop)
  (Pe : Sym2 (Site 2) → Prop)
  (hside : ((∀ z ∈ (rlc_orderedContourArc c hx hy).support, Pv z) ∧ (∀ e ∈ (rlc_orderedContourArc c hx hy).edges, Pe e)) ∨ ((∀ z ∈ (rlc_complementaryContourArc c hx hy).support, Pv z) ∧ (∀ e ∈ (rlc_complementaryContourArc c hx hy).edges, Pe e))) :
-- imply
  ∃ a : H.Walk x y, (∀ z ∈ a.support, Pv z) ∧ (∀ e ∈ a.edges, Pe e) ∧ a.support ⊆ c.support ∧ a.edges ⊆ c.edges := by
-- proof
  apply StatMech.Universality.rlc_select_complementaryContourArc c hx hy Pv Pe hside

/--
[rlc_orderedContourArc_vertex_property](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterArc.lean)
-/
@[path]
private lemma rlc_orderedContourArc_vertex_property_eq
  {H : SimpleGraph (Site 2)}
  {u x y : Site 2}
  {c : H.Walk u u}
-- given
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (P : Site 2 → Prop)
  (hP : ∀ z ∈ c.support, P z) :
-- imply
  ∀ z ∈ (rlc_orderedContourArc c hx hy).support, P z := by
-- proof
  apply StatMech.Universality.rlc_orderedContourArc_vertex_property c hx hy P hP

/--
[rlc_orderedContourArc_edge_property](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterArc.lean)
-/
@[path]
private lemma rlc_orderedContourArc_edge_property_eq
  {H : SimpleGraph (Site 2)}
  {u x y : Site 2}
  {c : H.Walk u u}
-- given
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (P : Sym2 (Site 2) → Prop)
  (hP : ∀ e ∈ c.edges, P e) :
-- imply
  ∀ e ∈ (rlc_orderedContourArc c hx hy).edges, P e := by
-- proof
  apply StatMech.Universality.rlc_orderedContourArc_edge_property c hx hy P hP

/--
[rlc_faceBoundaryWalk_reflected_support_mem_connectorBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterArc.lean)
-/
@[path]
private lemma rlc_faceBoundaryWalk_reflected_support_mem_connectorBox_eq
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
  (hbox : ∀ z ∈ a.support, rlc_dualReflect z ∈ rlc_connectorBox n) :
-- imply
  ∀ z ∈ (rlc_dualReflectOpenWalk (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega) (a.mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega))).support, z ∈ rlc_connectorBox n := by
-- proof
  apply StatMech.Universality.rlc_faceBoundaryWalk_reflected_support_mem_connectorBox G hn hlt omega a hbox

/--
[rlc_orderedFaceBoundaryArc_reflected_support_mem_connectorBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterArc.lean)
-/
@[path]
private lemma rlc_orderedFaceBoundaryArc_reflected_support_mem_connectorBox_eq
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
  (hbox : ∀ z ∈ c.support, rlc_dualReflect z ∈ rlc_connectorBox n) :
-- imply
  ∀ z ∈ (rlc_dualReflectOpenWalk (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G) omega) ((rlc_orderedContourArc c hx hy).mapLe (rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega))).support, z ∈ rlc_connectorBox n := by
-- proof
  apply StatMech.Universality.rlc_orderedFaceBoundaryArc_reflected_support_mem_connectorBox G hn hlt omega c hx hy hbox

/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_orderedContourContacts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterArc.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_orderedContourContacts_eq
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
  (hbox : ∀ z ∈ c.support, rlc_dualReflect z ∈ rlc_connectorBox n)
  (hlocal : ∀ {f g : Site 2}, s(f, g) ∈ c.edges → rlc_reflectedTargetLocallySupported G s(rlc_dualReflect f, rlc_dualReflect g) ∧ rlc_boundarySourceLocallySupported G (sharedPrimalEdge f g)) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_orderedContourContacts G hn hlt omega c hx hy hxPath hyPath hbox hlocal

/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_contourArcSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterArc.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_contourArcSide_eq
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
  (hside : ((∀ z ∈ (rlc_orderedContourArc c hx hy).support, rlc_dualReflect z ∈ rlc_connectorBox n) ∧ (∀ {f g : Site 2}, s(f, g) ∈ (rlc_orderedContourArc c hx hy).edges → rlc_reflectedTargetLocallySupported G s(rlc_dualReflect f, rlc_dualReflect g) ∧ rlc_boundarySourceLocallySupported G (sharedPrimalEdge f g))) ∨ ((∀ z ∈ (rlc_complementaryContourArc c hx hy).support, rlc_dualReflect z ∈ rlc_connectorBox n) ∧ (∀ {f g : Site 2}, s(f, g) ∈ (rlc_complementaryContourArc c hx hy).edges → rlc_reflectedTargetLocallySupported G s(rlc_dualReflect f, rlc_dualReflect g) ∧ rlc_boundarySourceLocallySupported G (sharedPrimalEdge f g)))) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_contourArcSide G hn hlt omega c hx hy hxPath hyPath hside


-- created on 2026-10-23
