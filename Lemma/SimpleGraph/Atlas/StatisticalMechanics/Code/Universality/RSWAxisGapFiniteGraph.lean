import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapFiniteGraph.Part4
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_openSub_axisGapFiniteGraph_restrict_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapFiniteGraph.lean)
-/
@[path]
private lemma rlc_openSub_axisGapFiniteGraph_restrict_eq_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  FK.openSub (rlc_axisGapFiniteGraph G) (rlc_connectorRestrictConfig omega) = openSubgraphInduce 2 (rlc_maskConfig (rlc_axisGapEdges G) omega) (rect (-2 * n) (2 * n) (-n) n) := by
-- proof
  apply StatMech.Universality.rlc_openSub_axisGapFiniteGraph_restrict_eq G omega

/--
[rlc_axisGapConnectorEvent_iff_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapFiniteGraph.lean)
-/
@[path]
private lemma rlc_axisGapConnectorEvent_iff_finite_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  omega ∈ rlc_axisGapConnectorEvent G ↔ rlc_connectorRestrictConfig omega ∈ rlc_finiteAxisGapConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_axisGapConnectorEvent_iff_finite G omega

/--
[RlcAxisBarrierGap.lowerVertex_mem_connectorBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapFiniteGraph.lean)
-/
@[path]
private lemma lowerVertex_mem_connectorBox_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'} :
-- imply
  G.lowerVertex ∈ rlc_connectorBox n := by
-- proof
  apply StatMech.Universality.RlcAxisBarrierGap.lowerVertex_mem_connectorBox G

/--
[RlcAxisBarrierGap.upperVertex_mem_connectorBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapFiniteGraph.lean)
-/
@[path]
private lemma upperVertex_mem_connectorBox_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'} :
-- imply
  G.upperVertex ∈ rlc_connectorBox n := by
-- proof
  apply StatMech.Universality.RlcAxisBarrierGap.upperVertex_mem_connectorBox G

/--
[RlcAxisBarrierGap.seedVertex_mem_connectorBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapFiniteGraph.lean)
-/
@[path]
private lemma seedVertex_mem_connectorBox_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'} :
-- imply
  G.seedVertex ∈ rlc_connectorBox n := by
-- proof
  apply StatMech.Universality.RlcAxisBarrierGap.seedVertex_mem_connectorBox G

/--
[RlcAxisBarrierGap.firstEdge_mem_axisGapFiniteGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapFiniteGraph.lean)
-/
@[path]
private lemma firstEdge_mem_axisGapFiniteGraph_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'} :
-- imply
  (rlc_axisGapFiniteGraph G).Adj ⟨G.lowerVertex, by simpa [rlc_connectorBox] using G.lowerVertex_mem_connectorBox⟩ ⟨G.seedVertex, by simpa [rlc_connectorBox] using G.seedVertex_mem_connectorBox⟩ := by
-- proof
  apply StatMech.Universality.RlcAxisBarrierGap.firstEdge_mem_axisGapFiniteGraph G

/--
[rlc_axisGapEdges_endpoints_mem_connectorBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapFiniteGraph.lean)
-/
@[path]
private lemma rlc_axisGapEdges_endpoints_mem_connectorBox_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {v w : Site 2}
-- given
  (he : s(v, w) ∈ rlc_axisGapEdges G) :
-- imply
  v ∈ rlc_connectorBox n ∧ w ∈ rlc_connectorBox n := by
-- proof
  apply StatMech.Universality.rlc_axisGapEdges_endpoints_mem_connectorBox G he

/--
[rlc_axisGapEdge_exists_lift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapFiniteGraph.lean)
-/
@[path]
private lemma rlc_axisGapEdge_exists_lift_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ rlc_axisGapEdges G) :
-- imply
  ∃ f : Sym2 (RlcConnectorVertex n), f.map Subtype.val = e := by
-- proof
  apply StatMech.Universality.rlc_axisGapEdge_exists_lift G he

/--
[rlc_axisGapEdgeLift_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapFiniteGraph.lean)
-/
@[path]
private lemma rlc_axisGapEdgeLift_map_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ rlc_axisGapEdges G) :
-- imply
  (rlc_axisGapEdgeLift G e he).map Subtype.val = e := by
-- proof
  apply StatMech.Universality.rlc_axisGapEdgeLift_map G e he

/--
[rlc_axisGapAmbientConfig_supportEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapFiniteGraph.lean)
-/
@[path]
private lemma rlc_axisGapAmbientConfig_supportEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ rlc_axisGapEdges G) :
-- imply
  rlc_axisGapAmbientConfig G tau e = tau (rlc_axisGapEdgeLift G e he) := by
-- proof
  apply StatMech.Universality.rlc_axisGapAmbientConfig_supportEdge G tau he

/--
[rlc_axisGapAmbientConfig_graphEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapFiniteGraph.lean)
-/
@[path]
private lemma rlc_axisGapAmbientConfig_graphEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {x y : RlcConnectorVertex n}
-- given
  (hxy : (rlc_axisGapFiniteGraph G).Adj x y) :
-- imply
  rlc_connectorRestrictConfig (rlc_axisGapAmbientConfig G tau) s(x, y) = tau s(x, y) := by
-- proof
  apply StatMech.Universality.rlc_axisGapAmbientConfig_graphEdge G tau hxy

/--
[rlc_openSub_restrict_axisGapAmbientConfig_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapFiniteGraph.lean)
-/
@[path]
private lemma rlc_openSub_restrict_axisGapAmbientConfig_eq_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.openSub (rlc_axisGapFiniteGraph G) (rlc_connectorRestrictConfig (rlc_axisGapAmbientConfig G tau)) = FK.openSub (rlc_axisGapFiniteGraph G) tau := by
-- proof
  apply StatMech.Universality.rlc_openSub_restrict_axisGapAmbientConfig_eq G tau

/--
[rlc_axisGapAmbientConfig_mem_connectorEvent_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapFiniteGraph.lean)
-/
@[path]
private lemma rlc_axisGapAmbientConfig_mem_connectorEvent_iff_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  rlc_axisGapAmbientConfig G tau ∈ rlc_axisGapConnectorEvent G ↔ tau ∈ rlc_finiteAxisGapConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_axisGapAmbientConfig_mem_connectorEvent_iff G tau

/--
[rlc_finiteAxisGapConnectorFailure_reflectedOpenDualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapFiniteGraph.lean)
-/
@[path]
private lemma rlc_finiteAxisGapConnectorFailure_reflectedOpenDualCircuit_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
-- imply
  ∃ (p q f g u : Site 2) (c : (openSubgraph 2 (rlc_dualReflectConfig (rlc_maskConfig (rlc_axisGapEdges G) (rlc_axisGapAmbientConfig G tau)))).Walk (rlc_dualReflect u) (rlc_dualReflect u)), p 0 = 0 ∧ q 0 = 0 ∧ sharedPrimalEdge f g = s(p, q) ∧ c.IsCycle ∧ s(rlc_dualReflect f, rlc_dualReflect g) ∈ c.edges := by
-- proof
  apply StatMech.Universality.rlc_finiteAxisGapConnectorFailure_reflectedOpenDualCircuit G hn hlt tau hno

/--
[rlc_axisGapRegionSet_eq_connectorOriginRegionSet_of_origin_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapFiniteGraph.lean)
-/
@[path]
private lemma rlc_axisGapRegionSet_eq_connectorOriginRegionSet_of_origin_mem_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
-- given
  (ho : origin 2 ∈ rlc_axisGapRegionSet G) :
-- imply
  rlc_axisGapRegionSet G = rlc_connectorOriginRegionSet gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_axisGapRegionSet_eq_connectorOriginRegionSet_of_origin_mem G ho

/--
[rlc_axisGapRegion_eq_connectorOriginRegion_of_origin_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapFiniteGraph.lean)
-/
@[path]
private lemma rlc_axisGapRegion_eq_connectorOriginRegion_of_origin_mem_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
-- given
  (ho : origin 2 ∈ rlc_axisGapRegionSet G) :
-- imply
  rlc_axisGapRegion G = rlc_connectorOriginRegion gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_axisGapRegion_eq_connectorOriginRegion_of_origin_mem G ho

/--
[rlc_axisGapEdges_eq_connectorEdges_of_origin_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapFiniteGraph.lean)
-/
@[path]
private lemma rlc_axisGapEdges_eq_connectorEdges_of_origin_mem_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
-- given
  (ho : origin 2 ∈ rlc_axisGapRegionSet G) :
-- imply
  rlc_axisGapEdges G = rlc_connectorEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_axisGapEdges_eq_connectorEdges_of_origin_mem G ho

/--
[rlc_axisGapFiniteGraph_eq_connectorFiniteGraph_of_origin_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapFiniteGraph.lean)
-/
@[path]
private lemma rlc_axisGapFiniteGraph_eq_connectorFiniteGraph_of_origin_mem_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
-- given
  (ho : origin 2 ∈ rlc_axisGapRegionSet G) :
-- imply
  rlc_axisGapFiniteGraph G = rlc_connectorFiniteGraph gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_axisGapFiniteGraph_eq_connectorFiniteGraph_of_origin_mem G ho

/--
[rlc_axisGapConnectorEvent_eq_connectorEvent_of_origin_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapFiniteGraph.lean)
-/
@[path]
private lemma rlc_axisGapConnectorEvent_eq_connectorEvent_of_origin_mem_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
-- given
  (ho : origin 2 ∈ rlc_axisGapRegionSet G) :
-- imply
  rlc_axisGapConnectorEvent G = rlc_connectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_axisGapConnectorEvent_eq_connectorEvent_of_origin_mem G ho


-- created on 2026-10-23
