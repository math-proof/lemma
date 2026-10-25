import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part75
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_connectorOriginRegionSet_mem_flipX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOriginRegionSet_mem_flipX_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hz : z ∈ rlc_connectorOriginRegionSet gamma gamma') :
-- imply
  rlc_flipX z ∈ rlc_connectorOriginRegionSet gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorOriginRegionSet_mem_flipX gamma gamma' hz

/--
[rlc_connectorOriginRegionSet_mem_flipX_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOriginRegionSet_mem_flipX_iff_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2} :
-- imply
  z ∈ rlc_connectorOriginRegionSet gamma gamma' ↔ rlc_flipX z ∈ rlc_connectorOriginRegionSet gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorOriginRegionSet_mem_flipX_iff gamma gamma' z

/--
[rlc_connectorOriginRegion_mem_flipX_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOriginRegion_mem_flipX_iff_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2} :
-- imply
  z ∈ rlc_connectorOriginRegion gamma gamma' ↔ rlc_flipX z ∈ rlc_connectorOriginRegion gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorOriginRegion_mem_flipX_iff gamma gamma' z

/--
[rlc_connectorEdges_mem_map_flipX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorEdges_mem_map_flipX_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ rlc_connectorEdges gamma gamma') :
-- imply
  e.map rlc_flipX ∈ rlc_connectorEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorEdges_mem_map_flipX gamma gamma' he

/--
[rlc_connectorEdges_mem_map_flipX_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorEdges_mem_map_flipX_iff_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)} :
-- imply
  e ∈ rlc_connectorEdges gamma gamma' ↔ e.map rlc_flipX ∈ rlc_connectorEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorEdges_mem_map_flipX_iff gamma gamma' e

/--
[rlc_connectorReachSet_reflectedOpenDualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorReachSet_reflectedOpenDualCircuit_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hno : omega ∉ rlc_connectorEvent gamma gamma') :
-- imply
  ∃ (u : Site 2) (c : (openSubgraph 2 (rlc_dualReflectConfig (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega))).Walk (rlc_dualReflect u) (rlc_dualReflect u)), c.IsCycle := by
-- proof
  apply StatMech.Universality.rlc_connectorReachSet_reflectedOpenDualCircuit gamma gamma' omega hno

/--
[rlc_openSub_connectorFiniteGraph_restrict_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_openSub_connectorFiniteGraph_restrict_eq_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  FK.openSub (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorRestrictConfig omega) = openSubgraphInduce 2 (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega) (rect (-2 * n) (2 * n) (-n) n) := by
-- proof
  apply StatMech.Universality.rlc_openSub_connectorFiniteGraph_restrict_eq gamma gamma' omega

/--
[rlc_connectorTraceWiring_le_separateWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorTraceWiring_le_separateWiring_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  rlc_connectorTraceWiring gamma gamma' ≤ rlc_connectorSeparateWiring gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorTraceWiring_le_separateWiring gamma gamma'

/--
[rlc_connectorTraceWiring_reachable_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorTraceWiring_reachable_right_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x y : RlcConnectorVertex n}
-- given
  (hx : rlc_connectorOnRight gamma x)
  (hy : rlc_connectorOnRight gamma y) :
-- imply
  (rlc_connectorTraceWiring gamma gamma').Reachable x y := by
-- proof
  apply StatMech.Universality.rlc_connectorTraceWiring_reachable_right gamma gamma' hx hy

/--
[rlc_connectorTraceWiring_reachable_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorTraceWiring_reachable_left_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x y : RlcConnectorVertex n}
-- given
  (hx : rlc_connectorOnLeft gamma' x)
  (hy : rlc_connectorOnLeft gamma' y) :
-- imply
  (rlc_connectorTraceWiring gamma gamma').Reachable x y := by
-- proof
  apply StatMech.Universality.rlc_connectorTraceWiring_reachable_left gamma gamma' hx hy

/--
[rlc_connectorTraceWiring_reachable_iff_separateWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorTraceWiring_reachable_iff_separateWiring_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H : SimpleGraph (RlcConnectorVertex n)}
  {x y : RlcConnectorVertex n} :
-- imply
  (H ⊔ rlc_connectorTraceWiring gamma gamma').Reachable x y ↔ (H ⊔ rlc_connectorSeparateWiring gamma gamma').Reachable x y := by
-- proof
  apply StatMech.Universality.rlc_connectorTraceWiring_reachable_iff_separateWiring gamma gamma' H x y

/--
[rlc_numClustersBC_traceWiring_eq_separateWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_numClustersBC_traceWiring_eq_separateWiring_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.numClustersBC (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorTraceWiring gamma gamma') tau = FK.numClustersBC (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') tau := by
-- proof
  apply StatMech.Universality.rlc_numClustersBC_traceWiring_eq_separateWiring gamma gamma' tau

/--
[rlc_bcWeight_traceWiring_eq_separateWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_bcWeight_traceWiring_eq_separateWiring_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.bcWeight (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorTraceWiring gamma gamma') p q tau = FK.bcWeight (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') p q tau := by
-- proof
  apply StatMech.Universality.rlc_bcWeight_traceWiring_eq_separateWiring gamma gamma' p q tau

/--
[rlc_bcZ_traceWiring_eq_separateWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_bcZ_traceWiring_eq_separateWiring_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real} :
-- imply
  FK.bcZ (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorTraceWiring gamma gamma') p q = FK.bcZ (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') p q := by
-- proof
  apply StatMech.Universality.rlc_bcZ_traceWiring_eq_separateWiring gamma gamma' p q

/--
[rlc_bcProb_traceWiring_eq_separateWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_bcProb_traceWiring_eq_separateWiring_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.bcProb (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorTraceWiring gamma gamma') p q tau = FK.bcProb (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') p q tau := by
-- proof
  apply StatMech.Universality.rlc_bcProb_traceWiring_eq_separateWiring gamma gamma' p q tau

/--
[rlc_bcEventMass_traceWiring_eq_separateWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_bcEventMass_traceWiring_eq_separateWiring_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {A : Set (ConfigSpace (Sym2 (RlcConnectorVertex n)))} :
-- imply
  FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorTraceWiring gamma gamma') p q A = FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') p q A := by
-- proof
  apply StatMech.Universality.rlc_bcEventMass_traceWiring_eq_separateWiring gamma gamma' p q A

/--
[rlc_connectorFiniteGraph_adj_not_traceWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorFiniteGraph_adj_not_traceWiring_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x y : RlcConnectorVertex n}
-- given
  (hxy : (rlc_connectorFiniteGraph gamma gamma').Adj x y) :
-- imply
  ¬ (rlc_connectorTraceWiring gamma gamma').Adj x y := by
-- proof
  apply StatMech.Universality.rlc_connectorFiniteGraph_adj_not_traceWiring gamma gamma' hxy

/--
[rlc_openSub_augmented_forceTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_openSub_augmented_forceTrace_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' tau) = FK.openSub (rlc_connectorFiniteGraph gamma gamma') tau ⊔ rlc_connectorTraceWiring gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_openSub_augmented_forceTrace gamma gamma' tau

/--
[rlc_numClusters_augmented_forceTrace_eq_traceBC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_numClusters_augmented_forceTrace_eq_traceBC_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.numClusters (rlc_connectorAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' tau) = FK.numClustersBC (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorTraceWiring gamma gamma') tau := by
-- proof
  apply StatMech.Universality.rlc_numClusters_augmented_forceTrace_eq_traceBC gamma gamma' tau

/--
[rlc_connectorForced_clusterEuler](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorForced_clusterEuler_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  let P := rlc_connectorAugmentedPlanarDomain gamma gamma' let K := FK.openSub P.G (rlc_connectorForceTraceConfig gamma gamma' tau) Nat.card P.V + Nat.card (BeffaraDC.pfdClosedDual P K).ConnectedComponent = K.edgeSet.ncard + FK.numClustersBC (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') tau + 1 := by
-- proof
  apply StatMech.Universality.rlc_connectorForced_clusterEuler gamma gamma' tau

/--
[rlc_edgeProduct_augmented_forceTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_edgeProduct_augmented_forceTrace_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p : Real}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.edgeProduct (rlc_connectorAugmentedPlanarDomain gamma gamma').G p (rlc_connectorForceTraceConfig gamma gamma' tau) = p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card * FK.edgeProduct (rlc_connectorFiniteGraph gamma gamma') p tau := by
-- proof
  apply StatMech.Universality.rlc_edgeProduct_augmented_forceTrace gamma gamma' p tau

/--
[rlc_fkWeight_augmented_forceTrace_eq_separateBC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_fkWeight_augmented_forceTrace_eq_separateBC_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.fkWeight (rlc_connectorAugmentedPlanarDomain gamma gamma').G p q (rlc_connectorForceTraceConfig gamma gamma' tau) = p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card * FK.bcWeight (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') p q tau := by
-- proof
  apply StatMech.Universality.rlc_fkWeight_augmented_forceTrace_eq_separateBC gamma gamma' p q tau

/--
[rlc_connectorForced_weight_duality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorForced_weight_duality_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  let P := rlc_connectorAugmentedPlanarDomain gamma gamma' let forced := rlc_connectorForceTraceConfig gamma gamma' tau p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card * FK.bcWeight (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') p q tau * q ^ (P.G.edgeFinset.card + 1) = (p / (1 - BeffaraDC.dualParam p q)) ^ P.G.edgeFinset.card * q ^ Nat.card P.V * BeffaraDC.pfdDualWeight P (BeffaraDC.dualParam p q) q (FK.openSub P.G forced) := by
-- proof
  apply StatMech.Universality.rlc_connectorForced_weight_duality gamma gamma' tau hp hp1 hq

/--
[rlc_connectorForcedDualZ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorForcedDualZ_pos_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < rlc_connectorForcedDualZ gamma gamma' p q := by
-- proof
  apply StatMech.Universality.rlc_connectorForcedDualZ_pos gamma gamma' hp hp1 hq

/--
[rlc_connectorForced_partition_duality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorForced_partition_duality_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  let P := rlc_connectorAugmentedPlanarDomain gamma gamma' p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card * FK.bcZ (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') p q * q ^ (P.G.edgeFinset.card + 1) = (p / (1 - BeffaraDC.dualParam p q)) ^ P.G.edgeFinset.card * q ^ Nat.card P.V * rlc_connectorForcedDualZ gamma gamma' (BeffaraDC.dualParam p q) q := by
-- proof
  apply StatMech.Universality.rlc_connectorForced_partition_duality gamma gamma' hp hp1 hq

/--
[rlc_bcProb_separate_eq_forcedDualProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_bcProb_separate_eq_forcedDualProb_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  FK.bcProb (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') p q tau = rlc_connectorForcedDualProb gamma gamma' (BeffaraDC.dualParam p q) q tau := by
-- proof
  apply StatMech.Universality.rlc_bcProb_separate_eq_forcedDualProb gamma gamma' tau hp hp1 hq

/--
[rlc_connectorEdge_exists_lift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorEdge_exists_lift_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ rlc_connectorEdges gamma gamma') :
-- imply
  ∃ f : Sym2 (RlcConnectorVertex n), f.map Subtype.val = e := by
-- proof
  apply StatMech.Universality.rlc_connectorEdge_exists_lift gamma gamma' he

/--
[rlc_connectorEdgeLift_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorEdgeLift_map_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ rlc_connectorEdges gamma gamma') :
-- imply
  (rlc_connectorEdgeLift gamma gamma' e he).map Subtype.val = e := by
-- proof
  apply StatMech.Universality.rlc_connectorEdgeLift_map gamma gamma' e he

/--
[rlc_connectorAmbientMixedConfig_connectorEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorAmbientMixedConfig_connectorEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ rlc_connectorEdges gamma gamma') :
-- imply
  rlc_connectorAmbientMixedConfig gamma gamma' tau e = tau (rlc_connectorEdgeLift gamma gamma' e he) := by
-- proof
  apply StatMech.Universality.rlc_connectorAmbientMixedConfig_connectorEdge gamma gamma' tau he

/--
[rlc_connectorAmbientMixedConfig_traceEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorAmbientMixedConfig_traceEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
-- imply
  rlc_connectorAmbientMixedConfig gamma gamma' tau e = true := by
-- proof
  apply StatMech.Universality.rlc_connectorAmbientMixedConfig_traceEdge gamma gamma' tau he

/--
[rlc_pimsEdgeEquiv_mem_connectorPIMSExteriorPreimages](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_pimsEdgeEquiv_mem_connectorPIMSExteriorPreimages_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)}
-- given
  (htarget : e ∈ rlc_connectorEdges gamma gamma')
  (hsource : rlc_pimsEdgeEquiv e ∉ rlc_connectorEdges gamma gamma')
  (htrace : rlc_pimsEdgeEquiv e ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
-- imply
  rlc_pimsEdgeEquiv e ∈ rlc_connectorPIMSExteriorPreimages gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_pimsEdgeEquiv_mem_connectorPIMSExteriorPreimages gamma gamma' htarget hsource htrace

/--
[rlc_connectorAmbientCollaredConfig_connectorEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorAmbientCollaredConfig_connectorEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ rlc_connectorEdges gamma gamma') :
-- imply
  rlc_connectorAmbientCollaredConfig gamma gamma' tau e = tau (rlc_connectorEdgeLift gamma gamma' e he) := by
-- proof
  apply StatMech.Universality.rlc_connectorAmbientCollaredConfig_connectorEdge gamma gamma' tau he

/--
[rlc_connectorAmbientCollaredConfig_traceEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorAmbientCollaredConfig_traceEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
-- imply
  rlc_connectorAmbientCollaredConfig gamma gamma' tau e = true := by
-- proof
  apply StatMech.Universality.rlc_connectorAmbientCollaredConfig_traceEdge gamma gamma' tau he

/--
[rlc_connectorAmbientCollaredConfig_collarEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorAmbientCollaredConfig_collarEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ rlc_connectorPIMSExteriorPreimages gamma gamma') :
-- imply
  rlc_connectorAmbientCollaredConfig gamma gamma' tau e = true := by
-- proof
  apply StatMech.Universality.rlc_connectorAmbientCollaredConfig_collarEdge gamma gamma' tau he

/--
[rlc_connectorAmbientMixedConfig_graphEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorAmbientMixedConfig_graphEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {x y : RlcConnectorVertex n}
-- given
  (hxy : (rlc_connectorFiniteGraph gamma gamma').Adj x y) :
-- imply
  rlc_connectorRestrictConfig (rlc_connectorAmbientMixedConfig gamma gamma' tau) s(x, y) = tau s(x, y) := by
-- proof
  apply StatMech.Universality.rlc_connectorAmbientMixedConfig_graphEdge gamma gamma' tau hxy

/--
[rlc_openSub_restrict_ambientMixed_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_openSub_restrict_ambientMixed_eq_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.openSub (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorRestrictConfig (rlc_connectorAmbientMixedConfig gamma gamma' tau)) = FK.openSub (rlc_connectorFiniteGraph gamma gamma') tau := by
-- proof
  apply StatMech.Universality.rlc_openSub_restrict_ambientMixed_eq gamma gamma' tau

/--
[rlc_connectorPIMSReflectedConfig_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSReflectedConfig_apply_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (RlcConnectorVertex n)} :
-- imply
  rlc_connectorPIMSReflectedConfig gamma gamma' tau e = !(rlc_connectorAmbientMixedConfig gamma gamma' tau (rlc_pimsEdgeEquiv (e.map Subtype.val))) := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSReflectedConfig_apply gamma gamma' tau e

/--
[rlc_connectorPIMSReflectedConfig_of_preimage_connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSReflectedConfig_of_preimage_connector_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (RlcConnectorVertex n)}
-- given
  (he : rlc_pimsEdgeEquiv (e.map Subtype.val) ∈ rlc_connectorEdges gamma gamma') :
-- imply
  rlc_connectorPIMSReflectedConfig gamma gamma' tau e = !(tau (rlc_connectorEdgeLift gamma gamma' (rlc_pimsEdgeEquiv (e.map Subtype.val)) he)) := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSReflectedConfig_of_preimage_connector gamma gamma' tau e he

/--
[rlc_connectorPIMSReflectedConfig_of_preimage_trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSReflectedConfig_of_preimage_trace_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (RlcConnectorVertex n)}
-- given
  (he : rlc_pimsEdgeEquiv (e.map Subtype.val) ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
-- imply
  rlc_connectorPIMSReflectedConfig gamma gamma' tau e = false := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSReflectedConfig_of_preimage_trace gamma gamma' tau e he

/--
[rlc_connectorPIMSReflectedConfig_of_preimage_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSReflectedConfig_of_preimage_exterior_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (RlcConnectorVertex n)}
-- given
  (hG : rlc_pimsEdgeEquiv (e.map Subtype.val) ∉ rlc_connectorEdges gamma gamma')
  (htrace : rlc_pimsEdgeEquiv (e.map Subtype.val) ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
-- imply
  rlc_connectorPIMSReflectedConfig gamma gamma' tau e = true := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSReflectedConfig_of_preimage_exterior gamma gamma' tau e hG htrace

/--
[rlc_connectorPIMSCollaredReflectedConfig_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSCollaredReflectedConfig_apply_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (RlcConnectorVertex n)} :
-- imply
  rlc_connectorPIMSCollaredReflectedConfig gamma gamma' tau e = !(rlc_connectorAmbientCollaredConfig gamma gamma' tau (rlc_pimsEdgeEquiv (e.map Subtype.val))) := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSCollaredReflectedConfig_apply gamma gamma' tau e

/--
[rlc_connectorPIMSCollaredReflectedConfig_of_preimage_connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSCollaredReflectedConfig_of_preimage_connector_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (RlcConnectorVertex n)}
-- given
  (he : rlc_pimsEdgeEquiv (e.map Subtype.val) ∈ rlc_connectorEdges gamma gamma') :
-- imply
  rlc_connectorPIMSCollaredReflectedConfig gamma gamma' tau e = !(tau (rlc_connectorEdgeLift gamma gamma' (rlc_pimsEdgeEquiv (e.map Subtype.val)) he)) := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSCollaredReflectedConfig_of_preimage_connector gamma gamma' tau e he

/--
[rlc_connectorPIMSCollaredReflectedConfig_of_preimage_trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSCollaredReflectedConfig_of_preimage_trace_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (RlcConnectorVertex n)}
-- given
  (he : rlc_pimsEdgeEquiv (e.map Subtype.val) ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
-- imply
  rlc_connectorPIMSCollaredReflectedConfig gamma gamma' tau e = false := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSCollaredReflectedConfig_of_preimage_trace gamma gamma' tau e he

/--
[rlc_connectorPIMSCollaredReflectedConfig_of_preimage_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSCollaredReflectedConfig_of_preimage_exterior_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (RlcConnectorVertex n)}
-- given
  (htarget : e.map Subtype.val ∈ rlc_connectorEdges gamma gamma')
  (hG : rlc_pimsEdgeEquiv (e.map Subtype.val) ∉ rlc_connectorEdges gamma gamma')
  (htrace : rlc_pimsEdgeEquiv (e.map Subtype.val) ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
-- imply
  rlc_connectorPIMSCollaredReflectedConfig gamma gamma' tau e = false := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSCollaredReflectedConfig_of_preimage_exterior gamma gamma' tau e htarget hG htrace

/--
[rlc_connectorPIMSCollaredParameter_of_preimage_connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSCollaredParameter_of_preimage_connector_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p : Real}
  {e : Sym2 (RlcConnectorVertex n)}
-- given
  (he : rlc_pimsEdgeEquiv (e.map Subtype.val) ∈ rlc_connectorEdges gamma gamma') :
-- imply
  rlc_connectorPIMSCollaredParameter gamma gamma' p e = p := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSCollaredParameter_of_preimage_connector gamma gamma' p e he

/--
[rlc_connectorPIMSCollaredParameter_of_preimage_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSCollaredParameter_of_preimage_exterior_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p : Real}
  {e : Sym2 (RlcConnectorVertex n)}
-- given
  (he : rlc_pimsEdgeEquiv (e.map Subtype.val) ∉ rlc_connectorEdges gamma gamma') :
-- imply
  rlc_connectorPIMSCollaredParameter gamma gamma' p e = 0 := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSCollaredParameter_of_preimage_exterior gamma gamma' p e he

/--
[rlc_connectorPIMSCollaredParameter_of_preimage_trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSCollaredParameter_of_preimage_trace_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p : Real}
  {e : Sym2 (RlcConnectorVertex n)}
-- given
  (he : rlc_pimsEdgeEquiv (e.map Subtype.val) ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
-- imply
  rlc_connectorPIMSCollaredParameter gamma gamma' p e = 0 := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSCollaredParameter_of_preimage_trace gamma gamma' p e he

/--
[rlc_connectorPIMSExteriorTraceLocal_iff_le_separateWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSExteriorTraceLocal_iff_le_separateWiring_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  RlcConnectorPIMSExteriorTraceLocal gamma gamma' ↔ rlc_connectorPIMSExteriorGraph gamma gamma' ≤ rlc_connectorSeparateWiring gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSExteriorTraceLocal_iff_le_separateWiring gamma gamma'

/--
[rlc_connectorPIMSExteriorTraceLocal_or_badEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSExteriorTraceLocal_or_badEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  RlcConnectorPIMSExteriorTraceLocal gamma gamma' ∨ ∃ x y : RlcConnectorVertex n, (rlc_connectorPIMSExteriorGraph gamma gamma').Adj x y ∧ ¬ ((rlc_connectorOnRight gamma x ∧ rlc_connectorOnRight gamma y) ∨ (rlc_connectorOnLeft gamma' x ∧ rlc_connectorOnLeft gamma' y)) := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSExteriorTraceLocal_or_badEdge gamma gamma'

/--
[not_rlc_connectorPIMSExtremalSelectionExteriorLocality_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma not_rlc_connectorPIMSExtremalSelectionExteriorLocality_iff_eq
  {n : Int} :
-- imply
  ¬ RlcConnectorPIMSExtremalSelectionExteriorLocality n ↔ ∃ (pair : RlcDiagonalPathPair n) (omega : ConfigSpace (Sym2 (Site 2))) (x y : RlcConnectorVertex n), omega ∈ rlc_extremalPairCandidate pair ∧ (rlc_connectorPIMSExteriorGraph pair.1 pair.2).Adj x y ∧ ¬ ((rlc_connectorOnRight pair.1 x ∧ rlc_connectorOnRight pair.1 y) ∨ (rlc_connectorOnLeft pair.2 x ∧ rlc_connectorOnLeft pair.2 y)) := by
-- proof
  apply StatMech.Universality.not_rlc_connectorPIMSExtremalSelectionExteriorLocality_iff

/--
[rlc_extremalSelection_exterior_badEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_extremalSelection_exterior_badEdge_eq :
-- imply
  (rlc_connectorPIMSExteriorGraph rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft).Adj rlc_extremalSelectionExteriorBadX rlc_extremalSelectionExteriorBadY ∧ ¬ ((rlc_connectorOnRight rlc_traceSplitCounterexampleRight rlc_extremalSelectionExteriorBadX ∧ rlc_connectorOnRight rlc_traceSplitCounterexampleRight rlc_extremalSelectionExteriorBadY) ∨ (rlc_connectorOnLeft rlc_traceSplitCounterexampleLeft rlc_extremalSelectionExteriorBadX ∧ rlc_connectorOnLeft rlc_traceSplitCounterexampleLeft rlc_extremalSelectionExteriorBadY)) := by
-- proof
  apply StatMech.Universality.rlc_extremalSelection_exterior_badEdge

/--
[not_rlc_connectorPIMSExtremalSelectionExteriorLocality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma not_rlc_connectorPIMSExtremalSelectionExteriorLocality_eq :
-- imply
  ¬ RlcConnectorPIMSExtremalSelectionExteriorLocality 1 := by
-- proof
  apply StatMech.Universality.not_rlc_connectorPIMSExtremalSelectionExteriorLocality

/--
[rlc_connectorPIMSExteriorGraph_le_separateWiring_of_extremalSelection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSExteriorGraph_le_separateWiring_of_extremalSelection_eq
  {n : Int}
  {pair : RlcDiagonalPathPair n}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hselection : RlcConnectorPIMSExtremalSelectionExteriorLocality n)
  (hpair : omega ∈ rlc_extremalPairCandidate pair) :
-- imply
  rlc_connectorPIMSExteriorGraph pair.1 pair.2 ≤ rlc_connectorSeparateWiring pair.1 pair.2 := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSExteriorGraph_le_separateWiring_of_extremalSelection hselection pair hpair

/--
[rlc_connectorPIMSExterior_reachable_iff_wiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSExterior_reachable_iff_wiring_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x y : RlcConnectorVertex n} :
-- imply
  (rlc_connectorPIMSExteriorGraph gamma gamma').Reachable x y ↔ (rlc_connectorPIMSExteriorWiring gamma gamma').Reachable x y := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSExterior_reachable_iff_wiring gamma gamma' x y

/--
[rlc_connectorPIMSExterior_sup_reachable_iff_wiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSExterior_sup_reachable_iff_wiring_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H : SimpleGraph (RlcConnectorVertex n)}
  {x y : RlcConnectorVertex n} :
-- imply
  (H ⊔ rlc_connectorPIMSExteriorGraph gamma gamma').Reachable x y ↔ (H ⊔ rlc_connectorPIMSExteriorWiring gamma gamma').Reachable x y := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSExterior_sup_reachable_iff_wiring gamma gamma' H x y

/--
[rlc_connectorFiniteGraph_eq_PIMS_preimage_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorFiniteGraph_eq_PIMS_preimage_partition_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  rlc_connectorFiniteGraph gamma gamma' = (rlc_connectorPIMSVariableGraph gamma gamma' ⊔ rlc_connectorPIMSTraceGraph gamma gamma') ⊔ rlc_connectorPIMSExteriorGraph gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorFiniteGraph_eq_PIMS_preimage_partition gamma gamma'

/--
[rlc_openSub_PIMS_trace_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_openSub_PIMS_trace_eq_bot_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.openSub (rlc_connectorPIMSTraceGraph gamma gamma') (rlc_connectorPIMSReflectedConfig gamma gamma' tau) = ⊥ := by
-- proof
  apply StatMech.Universality.rlc_openSub_PIMS_trace_eq_bot gamma gamma' tau

/--
[rlc_openSub_PIMS_eq_variable_sup_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_openSub_PIMS_eq_variable_sup_exterior_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.openSub (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorPIMSReflectedConfig gamma gamma' tau) = FK.openSub (rlc_connectorPIMSVariableGraph gamma gamma') (rlc_connectorPIMSReflectedConfig gamma gamma' tau) ⊔ rlc_connectorPIMSExteriorGraph gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_openSub_PIMS_eq_variable_sup_exterior gamma gamma' tau

/--
[rlc_openSub_PIMSCollared_eq_variable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_openSub_PIMSCollared_eq_variable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.openSub (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' tau) = FK.openSub (rlc_connectorPIMSVariableGraph gamma gamma') (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' tau) := by
-- proof
  apply StatMech.Universality.rlc_openSub_PIMSCollared_eq_variable gamma gamma' tau

/--
[rlc_connectorComponentWiring_eq_bot_of_oneAttachment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorComponentWiring_eq_bot_of_oneAttachment_eq
  {n : Int}
  {H : SimpleGraph (RlcConnectorVertex n)}
-- given
  (hattach : RlcConnectorExteriorOneAttachment H) :
-- imply
  rlc_connectorComponentWiring H = ⊥ := by
-- proof
  apply StatMech.Universality.rlc_connectorComponentWiring_eq_bot_of_oneAttachment H hattach

/--
[rlc_connectorPIMSCollaredExteriorOpenGraph_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSCollaredExteriorOpenGraph_eq_bot_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  rlc_connectorPIMSCollaredExteriorOpenGraph gamma gamma' tau = ⊥ := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSCollaredExteriorOpenGraph_eq_bot gamma gamma' tau

/--
[rlc_connectorPIMSCollaredExterior_oneAttachment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSCollaredExterior_oneAttachment_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  RlcConnectorExteriorOneAttachment (rlc_connectorPIMSCollaredExteriorOpenGraph gamma gamma' tau) := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSCollaredExterior_oneAttachment gamma gamma' tau

/--
[rlc_connectorPIMSCollaredInducedWiring_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSCollaredInducedWiring_eq_bot_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  rlc_connectorComponentWiring (rlc_connectorPIMSCollaredExteriorOpenGraph gamma gamma' tau) = ⊥ := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSCollaredInducedWiring_eq_bot gamma gamma' tau

/--
[rlc_openSub_PIMSVariableConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_openSub_PIMSVariableConfig_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.openSub (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorPIMSVariableConfig gamma gamma' rho) = FK.openSub (rlc_connectorPIMSVariableGraph gamma gamma') rho := by
-- proof
  apply StatMech.Universality.rlc_openSub_PIMSVariableConfig gamma gamma' rho

/--
[rlc_openSub_PIMSAssembleConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_openSub_PIMSAssembleConfig_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.openSub (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorPIMSAssembleConfig gamma gamma' rho) = FK.openSub (rlc_connectorPIMSVariableGraph gamma gamma') rho ⊔ rlc_connectorPIMSExteriorGraph gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_openSub_PIMSAssembleConfig gamma gamma' rho

/--
[rlc_connectorPIMSReflectedConfig_open_of_masked_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSReflectedConfig_open_of_masked_open_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (RlcConnectorVertex n)}
-- given
  (hnotTrace : rlc_pimsEdgeEquiv (e.map Subtype.val) ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1)
  (hopen : rlc_dualReflectConfig (rlc_maskConfig (rlc_connectorEdges gamma gamma') (rlc_connectorAmbientMixedConfig gamma gamma' tau)) (e.map Subtype.val) = true) :
-- imply
  rlc_connectorPIMSReflectedConfig gamma gamma' tau e = true := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSReflectedConfig_open_of_masked_open gamma gamma' tau e hnotTrace hopen

/--
[rlc_pimsEdgeEquiv_connectorReflectedDualEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_pimsEdgeEquiv_connectorReflectedDualEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f : Ising.kwg_Edge (rlc_connectorAugmentedPlanarDomain gamma gamma')} :
-- imply
  rlc_pimsEdgeEquiv (rlc_connectorReflectedDualEdge gamma gamma' f) = Ising.kwg_embeddedEdge (rlc_connectorAugmentedPlanarDomain gamma gamma') f := by
-- proof
  apply StatMech.Universality.rlc_pimsEdgeEquiv_connectorReflectedDualEdge gamma gamma' f

/--
[rlc_connectorReflectedDualEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorReflectedDualEdge_injective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Function.Injective (rlc_connectorReflectedDualEdge gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorReflectedDualEdge_injective gamma gamma'

/--
[rlc_connectorOuterTargetVertex_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterTargetVertex_injective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Function.Injective (rlc_connectorOuterTargetVertex gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterTargetVertex_injective gamma gamma'

/--
[rlc_connectorOuterDualEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterDualEdge_injective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Function.Injective (rlc_connectorOuterDualEdge gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterDualEdge_injective gamma gamma'

/--
[rlc_connectorOuterFaceProjection_face](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterFaceProjection_face_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {C : Ising.kwg_Face (rlc_connectorAugmentedPlanarDomain gamma gamma')} :
-- imply
  rlc_connectorOuterFaceProjection gamma gamma' (rlc_connectorOuterFace gamma gamma' C) = C := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterFaceProjection_face gamma gamma' C

/--
[rlc_connectorOuterSpoke_adj_face](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterSpoke_adj_face_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x : RlcConnectorOuterDualVertex gamma gamma'}
-- given
  (hx : ¬RlcConnectorOuterIsFace gamma gamma' x) :
-- imply
  (rlc_connectorOuterSpokeGraph gamma gamma').Adj x (rlc_connectorOuterFace gamma gamma' (rlc_connectorOuterFaceProjection gamma gamma' x)) := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterSpoke_adj_face gamma gamma' x hx

/--
[rlc_connectorOuterDualEdge_ne_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterDualEdge_ne_diag_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f : Ising.kwg_Edge (rlc_connectorAugmentedPlanarDomain gamma gamma')}
  {x : RlcConnectorOuterDualVertex gamma gamma'} :
-- imply
  rlc_connectorOuterDualEdge gamma gamma' f ≠ s(x, x) := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterDualEdge_ne_diag gamma gamma' f x

/--
[rlc_connectorOuterDualEdge_mem_random](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterDualEdge_mem_random_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f : Ising.kwg_Edge (rlc_connectorAugmentedPlanarDomain gamma gamma')} :
-- imply
  rlc_connectorOuterDualEdge gamma gamma' f ∈ (rlc_connectorOuterRandomGraph gamma gamma').edgeSet := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterDualEdge_mem_random gamma gamma' f

/--
[rlc_connectorOuterRandom_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterRandom_edgeFinset_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  (rlc_connectorOuterRandomGraph gamma gamma').edgeFinset = Finset.univ.image (rlc_connectorOuterDualEdge gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterRandom_edgeFinset gamma gamma'

/--
[rlc_pimsEdgeEquiv_mem_latticeEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_pimsEdgeEquiv_mem_latticeEdge_eq
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ (hypercubicLattice 2).edgeSet) :
-- imply
  rlc_pimsEdgeEquiv e ∈ (hypercubicLattice 2).edgeSet := by
-- proof
  apply StatMech.Universality.rlc_pimsEdgeEquiv_mem_latticeEdge he

/--
[rlc_connectorForceFourTraceConfig_exposed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorForceFourTraceConfig_exposed_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (RlcConnectorVertex n)}
-- given
  (he : e ∈ (rlc_connectorTraceWiring gamma gamma').edgeFinset) :
-- imply
  rlc_connectorForceFourTraceConfig gamma gamma' tau e = true := by
-- proof
  apply StatMech.Universality.rlc_connectorForceFourTraceConfig_exposed gamma gamma' tau he

/--
[rlc_connectorForceFourTraceConfig_reflected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorForceFourTraceConfig_reflected_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (RlcConnectorVertex n)}
-- given
  (he : e ∈ (rlc_connectorReflectedTraceWiring gamma gamma').edgeFinset)
  (hnot : e ∉ (rlc_connectorTraceWiring gamma gamma').edgeFinset) :
-- imply
  rlc_connectorForceFourTraceConfig gamma gamma' tau e = false := by
-- proof
  apply StatMech.Universality.rlc_connectorForceFourTraceConfig_reflected gamma gamma' tau he hnot

/--
[rlc_connectorForceFourTraceConfig_corridor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorForceFourTraceConfig_corridor_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {x y : RlcConnectorVertex n}
-- given
  (hxy : (rlc_connectorFiniteGraph gamma gamma').Adj x y) :
-- imply
  rlc_connectorForceFourTraceConfig gamma gamma' tau s(x, y) = tau s(x, y) := by
-- proof
  apply StatMech.Universality.rlc_connectorForceFourTraceConfig_corridor gamma gamma' tau hxy

/--
[rlc_openSub_fourTrace_force](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_openSub_fourTrace_force_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.openSub (rlc_connectorFourTracePlanarDomain gamma gamma').G (rlc_connectorForceFourTraceConfig gamma gamma' tau) = FK.openSub (rlc_connectorFiniteGraph gamma gamma') tau ⊔ rlc_connectorTraceWiring gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_openSub_fourTrace_force gamma gamma' tau

/--
[rlc_connectorCollaredWallEdges_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollaredWallEdges_preimage_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)}
-- given
  (htarget : e ∈ rlc_connectorEdges gamma gamma')
  (hsource : rlc_pimsEdgeEquiv e ∉ rlc_connectorEdges gamma gamma')
  (htrace : rlc_pimsEdgeEquiv e ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
-- imply
  rlc_pimsEdgeEquiv e ∈ rlc_connectorCollaredWallEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorCollaredWallEdges_preimage gamma gamma' htarget hsource htrace

/--
[rlc_connectorCollaredWall_endpoint_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollaredWall_endpoint_mem_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)}
  {x : Site 2}
-- given
  (he : e ∈ rlc_connectorCollaredWallEdges gamma gamma')
  (hx : x ∈ e) :
-- imply
  x ∈ rlc_connectorCollaredSites gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorCollaredWall_endpoint_mem gamma gamma' he hx

/--
[rlc_connectorCollaredWallGraph_has_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollaredWallGraph_has_preimage_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)}
-- given
  (htarget : e ∈ rlc_connectorEdges gamma gamma')
  (htargetLat : e ∈ (hypercubicLattice 2).edgeSet)
  (hsource : rlc_pimsEdgeEquiv e ∉ rlc_connectorEdges gamma gamma')
  (htrace : rlc_pimsEdgeEquiv e ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
-- imply
  ∃ x y : RlcConnectorCollaredVertex gamma gamma', s(x.1, y.1) = rlc_pimsEdgeEquiv e ∧ (rlc_connectorCollaredWallGraph gamma gamma').Adj x y := by
-- proof
  apply StatMech.Universality.rlc_connectorCollaredWallGraph_has_preimage gamma gamma' htarget htargetLat hsource htrace

/--
[rlc_extremalSelection_bad_preimage_is_collaredWall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_extremalSelection_bad_preimage_is_collaredWall_eq :
-- imply
  ∃ x y : RlcConnectorCollaredVertex rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft, s(x.1, y.1) = rlc_pimsEdgeEquiv s(rlc_extremalSelectionExteriorBadX.1, rlc_extremalSelectionExteriorBadY.1) ∧ (rlc_connectorCollaredWallGraph rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft).Adj x y := by
-- proof
  apply StatMech.Universality.rlc_extremalSelection_bad_preimage_is_collaredWall

/--
[rlc_connectorVertexToCollared_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorVertexToCollared_injective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Function.Injective (rlc_connectorVertexToCollared gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorVertexToCollared_injective gamma gamma'

/--
[rlc_extremalSelection_badCollar_inside_not_augmented](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_extremalSelection_badCollar_inside_not_augmented_eq :
-- imply
  (rlc_connectorCollaredWallGraph rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft).Adj (rlc_connectorVertexToCollared rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft rlc_extremalSelectionBadCollarX) (rlc_connectorVertexToCollared rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft rlc_extremalSelectionBadCollarY) ∧ ¬(rlc_connectorAugmentedPlanarDomain rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft).G.Adj rlc_extremalSelectionBadCollarX rlc_extremalSelectionBadCollarY := by
-- proof
  apply StatMech.Universality.rlc_extremalSelection_badCollar_inside_not_augmented

/--
[rlc_connectorAugmented_adj_collared](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorAugmented_adj_collared_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x y : RlcConnectorVertex n}
-- given
  (hxy : (rlc_connectorAugmentedPlanarDomain gamma gamma').G.Adj x y) :
-- imply
  (rlc_connectorCollaredPlanarDomain gamma gamma').G.Adj (rlc_connectorVertexToCollared gamma gamma' x) (rlc_connectorVertexToCollared gamma gamma' y) := by
-- proof
  apply StatMech.Universality.rlc_connectorAugmented_adj_collared gamma gamma' hxy

/--
[rlc_connectorAugmentedEdgeToCollared_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorAugmentedEdgeToCollared_injective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Function.Injective (rlc_connectorAugmentedEdgeToCollared gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorAugmentedEdgeToCollared_injective gamma gamma'

/--
[rlc_connectorCollaredWall_mem_imageGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollaredWall_mem_imageGraph_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ rlc_connectorCollaredWallEdges gamma gamma')
  (hlat : e ∈ (hypercubicLattice 2).edgeSet) :
-- imply
  e ∈ (Lattice.imageGraph (rlc_connectorCollaredPlanarDomain gamma gamma')).edgeSet := by
-- proof
  apply StatMech.Universality.rlc_connectorCollaredWall_mem_imageGraph gamma gamma' he hlat

/--
[rlc_connectorCollaredWall_blocks_faceStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollaredWall_blocks_faceStep_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)}
  {f g : Site 2}
-- given
  (he : e ∈ rlc_connectorCollaredWallEdges gamma gamma')
  (hlat : e ∈ (hypercubicLattice 2).edgeSet)
  (hshared : sharedPrimalEdge f g = e) :
-- imply
  ¬ (whb_faceRegion (Lattice.imageGraph (rlc_connectorCollaredPlanarDomain gamma gamma'))).Adj f g := by
-- proof
  apply StatMech.Universality.rlc_connectorCollaredWall_blocks_faceStep gamma gamma' he hlat hshared

/--
[rlc_connectorCollared_preimage_blocks_faceStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollared_preimage_blocks_faceStep_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)}
  {f g : Site 2}
-- given
  (htarget : e ∈ rlc_connectorEdges gamma gamma')
  (htargetLat : e ∈ (hypercubicLattice 2).edgeSet)
  (hsource : rlc_pimsEdgeEquiv e ∉ rlc_connectorEdges gamma gamma')
  (htrace : rlc_pimsEdgeEquiv e ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1)
  (hshared : sharedPrimalEdge f g = rlc_pimsEdgeEquiv e) :
-- imply
  ¬ (whb_faceRegion (Lattice.imageGraph (rlc_connectorCollaredPlanarDomain gamma gamma'))).Adj f g := by
-- proof
  apply StatMech.Universality.rlc_connectorCollared_preimage_blocks_faceStep gamma gamma' htarget htargetLat hsource htrace hshared

/--
[rlc_connectorEdgeLift_mem_finiteGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorEdgeLift_mem_finiteGraph_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ rlc_connectorEdges gamma gamma')
  (hlat : e ∈ (hypercubicLattice 2).edgeSet) :
-- imply
  rlc_connectorEdgeLift gamma gamma' e he ∈ (rlc_connectorFiniteGraph gamma gamma').edgeSet := by
-- proof
  apply StatMech.Universality.rlc_connectorEdgeLift_mem_finiteGraph gamma gamma' e he hlat

/--
[rlc_connectorOuterRandomGraph_adj_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterRandomGraph_adj_target_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x y : RlcConnectorVertex n} :
-- imply
  (rlc_connectorOuterRandomGraph gamma gamma').Adj (rlc_connectorOuterTargetVertex gamma gamma' x) (rlc_connectorOuterTargetVertex gamma gamma' y) ↔ (rlc_connectorPIMSVariableGraph gamma gamma').Adj x y := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterRandomGraph_adj_target gamma gamma' x y

/--
[rlc_connectorOuterSpokeGraph_not_adj_targets](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterSpokeGraph_not_adj_targets_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x y : RlcConnectorVertex n} :
-- imply
  ¬(rlc_connectorOuterSpokeGraph gamma gamma').Adj (rlc_connectorOuterTargetVertex gamma gamma' x) (rlc_connectorOuterTargetVertex gamma gamma' y) := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterSpokeGraph_not_adj_targets gamma gamma' x y

/--
[rlc_connectorOuterDualGraph_adjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterDualGraph_adjMatch_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  FK.ocd_AdjMatch (rlc_connectorPIMSVariableGraph gamma gamma') (rlc_connectorOuterDualGraph gamma gamma') (rlc_connectorOuterTargetVertex gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterDualGraph_adjMatch gamma gamma'

/--
[rlc_connectorOuterFaceTag_eq_true_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterFaceTag_eq_true_iff_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x : RlcConnectorOuterDualVertex gamma gamma'} :
-- imply
  rlc_connectorOuterFaceTag gamma gamma' x = true ↔ RlcConnectorOuterIsFace gamma gamma' x := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterFaceTag_eq_true_iff gamma gamma' x

/--
[rlc_connectorOuterFaceTag_outerDualEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterFaceTag_outerDualEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f : Ising.kwg_Edge (rlc_connectorAugmentedPlanarDomain gamma gamma')} :
-- imply
  (rlc_connectorOuterDualEdge gamma gamma' f).map (rlc_connectorOuterFaceTag gamma gamma') = s(false, false) := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterFaceTag_outerDualEdge gamma gamma' f

/--
[rlc_connectorOuterSpoke_faceTag_ne_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterSpoke_faceTag_ne_false_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x y : RlcConnectorOuterDualVertex gamma gamma'}
-- given
  (hxy : (rlc_connectorOuterSpokeGraph gamma gamma').Adj x y) :
-- imply
  s(x, y).map (rlc_connectorOuterFaceTag gamma gamma') ≠ s(false, false) := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterSpoke_faceTag_ne_false gamma gamma' hxy

/--
[rlc_connectorOuterDualEdge_not_mem_spoke](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterDualEdge_not_mem_spoke_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f : Ising.kwg_Edge (rlc_connectorAugmentedPlanarDomain gamma gamma')} :
-- imply
  rlc_connectorOuterDualEdge gamma gamma' f ∉ (rlc_connectorOuterSpokeGraph gamma gamma').edgeSet := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterDualEdge_not_mem_spoke gamma gamma' f

/--
[rlc_connectorOuterDualConfig_randomEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterDualConfig_randomEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {f : Ising.kwg_Edge (rlc_connectorAugmentedPlanarDomain gamma gamma')} :
-- imply
  rlc_connectorOuterDualConfig gamma gamma' tau (rlc_connectorOuterDualEdge gamma gamma' f) = !(rlc_connectorForceTraceConfig gamma gamma' tau f.1) := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterDualConfig_randomEdge gamma gamma' tau f

/--
[rlc_connectorOuterDualConfig_spoke](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterDualConfig_spoke_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (RlcConnectorOuterDualVertex gamma gamma')}
-- given
  (he : e ∈ (rlc_connectorOuterSpokeGraph gamma gamma').edgeSet) :
-- imply
  rlc_connectorOuterDualConfig gamma gamma' tau e = true := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterDualConfig_spoke gamma gamma' tau he

/--
[rlc_connectorOuterFaceProjection_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterFaceProjection_edge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f : Ising.kwg_Edge (rlc_connectorAugmentedPlanarDomain gamma gamma')} :
-- imply
  (rlc_connectorOuterDualEdge gamma gamma' f).map (rlc_connectorOuterFaceProjection gamma gamma') = Ising.kwg_dualEnds (rlc_connectorAugmentedPlanarDomain gamma gamma') f := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterFaceProjection_edge gamma gamma' f

/--
[rlc_connectorOuterSpoke_le_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterSpoke_le_open_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  rlc_connectorOuterSpokeGraph gamma gamma' ≤ rlc_connectorOuterOpenGraph gamma gamma' tau := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterSpoke_le_open gamma gamma' tau

/--
[rlc_connectorOuterDualEdge_open_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterDualEdge_open_iff_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {f : Ising.kwg_Edge (rlc_connectorAugmentedPlanarDomain gamma gamma')} :
-- imply
  rlc_connectorOuterDualEdge gamma gamma' f ∈ (rlc_connectorOuterOpenGraph gamma gamma' tau).edgeSet ↔ f.1 ∉ (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' tau)).edgeSet := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterDualEdge_open_iff gamma gamma' tau f

/--
[rlc_connectorOuterFaceProjection_reachable_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterFaceProjection_reachable_of_adj_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {x y : RlcConnectorOuterDualVertex gamma gamma'}
-- given
  (hxy : (rlc_connectorOuterOpenGraph gamma gamma' tau).Adj x y) :
-- imply
  (BeffaraDC.pfdClosedDual (rlc_connectorAugmentedPlanarDomain gamma gamma') (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' tau))).Reachable (rlc_connectorOuterFaceProjection gamma gamma' x) (rlc_connectorOuterFaceProjection gamma gamma' y) := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterFaceProjection_reachable_of_adj gamma gamma' tau hxy

/--
[rlc_connectorOuterFaceProjection_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterFaceProjection_reachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {x y : RlcConnectorOuterDualVertex gamma gamma'}
-- given
  (hxy : (rlc_connectorOuterOpenGraph gamma gamma' tau).Reachable x y) :
-- imply
  (BeffaraDC.pfdClosedDual (rlc_connectorAugmentedPlanarDomain gamma gamma') (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' tau))).Reachable (rlc_connectorOuterFaceProjection gamma gamma' x) (rlc_connectorOuterFaceProjection gamma gamma' y) := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterFaceProjection_reachable gamma gamma' tau hxy

/--
[rlc_connectorOuterDualEdge_endpoints_not_face](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterDualEdge_endpoints_not_face_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f : Ising.kwg_Edge (rlc_connectorAugmentedPlanarDomain gamma gamma')}
  {x y : RlcConnectorOuterDualVertex gamma gamma'}
-- given
  (hxy : rlc_connectorOuterDualEdge gamma gamma' f = s(x, y)) :
-- imply
  ¬RlcConnectorOuterIsFace gamma gamma' x ∧ ¬RlcConnectorOuterIsFace gamma gamma' y := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterDualEdge_endpoints_not_face gamma gamma' f hxy

/--
[rlc_connectorOuterFace_reachable_of_pfd_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterFace_reachable_of_pfd_adj_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {C D : Ising.kwg_Face (rlc_connectorAugmentedPlanarDomain gamma gamma')}
-- given
  (hCD : (BeffaraDC.pfdClosedDual (rlc_connectorAugmentedPlanarDomain gamma gamma') (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' tau))).Adj C D) :
-- imply
  (rlc_connectorOuterOpenGraph gamma gamma' tau).Reachable (rlc_connectorOuterFace gamma gamma' C) (rlc_connectorOuterFace gamma gamma' D) := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterFace_reachable_of_pfd_adj gamma gamma' tau hCD

/--
[rlc_connectorOuterFace_reachable_of_pfd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterFace_reachable_of_pfd_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {C D : Ising.kwg_Face (rlc_connectorAugmentedPlanarDomain gamma gamma')}
-- given
  (hCD : (BeffaraDC.pfdClosedDual (rlc_connectorAugmentedPlanarDomain gamma gamma') (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' tau))).Reachable C D) :
-- imply
  (rlc_connectorOuterOpenGraph gamma gamma' tau).Reachable (rlc_connectorOuterFace gamma gamma' C) (rlc_connectorOuterFace gamma gamma' D) := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterFace_reachable_of_pfd gamma gamma' tau hCD

/--
[rlc_connectorOuter_reachable_face](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuter_reachable_face_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {x : RlcConnectorOuterDualVertex gamma gamma'} :
-- imply
  (rlc_connectorOuterOpenGraph gamma gamma' tau).Reachable x (rlc_connectorOuterFace gamma gamma' (rlc_connectorOuterFaceProjection gamma gamma' x)) := by
-- proof
  apply StatMech.Universality.rlc_connectorOuter_reachable_face gamma gamma' tau x

/--
[rlc_connectorOuter_reachable_iff_pfd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuter_reachable_iff_pfd_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {x y : RlcConnectorOuterDualVertex gamma gamma'} :
-- imply
  (rlc_connectorOuterOpenGraph gamma gamma' tau).Reachable x y ↔ (BeffaraDC.pfdClosedDual (rlc_connectorAugmentedPlanarDomain gamma gamma') (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' tau))).Reachable (rlc_connectorOuterFaceProjection gamma gamma' x) (rlc_connectorOuterFaceProjection gamma gamma' y) := by
-- proof
  apply StatMech.Universality.rlc_connectorOuter_reachable_iff_pfd gamma gamma' tau x y

/--
[rlc_connectorOuterComponentMap_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterComponentMap_mk_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {x : RlcConnectorOuterDualVertex gamma gamma'} :
-- imply
  rlc_connectorOuterComponentMap gamma gamma' tau ((rlc_connectorOuterOpenGraph gamma gamma' tau).connectedComponentMk x) = (BeffaraDC.pfdClosedDual (rlc_connectorAugmentedPlanarDomain gamma gamma') (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' tau))).connectedComponentMk (rlc_connectorOuterFaceProjection gamma gamma' x) := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterComponentMap_mk gamma gamma' tau x

/--
[rlc_connectorOuterComponentMap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterComponentMap_injective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  Function.Injective (rlc_connectorOuterComponentMap gamma gamma' tau) := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterComponentMap_injective gamma gamma' tau

/--
[rlc_connectorOuterComponentMap_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterComponentMap_surjective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  Function.Surjective (rlc_connectorOuterComponentMap gamma gamma' tau) := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterComponentMap_surjective gamma gamma' tau

/--
[rlc_connectorOuter_numClusters_eq_pfd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuter_numClusters_eq_pfd_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.numClustersBC (rlc_connectorOuterDualGraph gamma gamma') ⊥ (rlc_connectorOuterDualConfig gamma gamma' tau) = Nat.card (BeffaraDC.pfdClosedDual (rlc_connectorAugmentedPlanarDomain gamma gamma') (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' tau))).ConnectedComponent := by
-- proof
  apply StatMech.Universality.rlc_connectorOuter_numClusters_eq_pfd gamma gamma' tau

/--
[rlc_connectorOuterRandom_spoke_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterRandom_spoke_disjoint_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Disjoint (rlc_connectorOuterRandomGraph gamma gamma').edgeFinset (rlc_connectorOuterSpokeGraph gamma gamma').edgeFinset := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterRandom_spoke_disjoint gamma gamma'

/--
[rlc_openCount_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_openCount_complement_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  FK.openCount G (fun e => !(omega e)) = G.edgeFinset.card - FK.openCount G omega := by
-- proof
  apply StatMech.Universality.rlc_openCount_complement G omega

/--
[rlc_connector_pfdDualEdgeFactor_eq_randomProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connector_pfdDualEdgeFactor_eq_randomProduct_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {p : Real} :
-- imply
  BeffaraDC.edgeProductCount p (rlc_connectorAugmentedPlanarDomain gamma gamma').G.edgeFinset.card ((rlc_connectorAugmentedPlanarDomain gamma gamma').G.edgeFinset.card - (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' tau)).edgeSet.ncard) = ∏ f : Ising.kwg_Edge (rlc_connectorAugmentedPlanarDomain gamma gamma'), if !(rlc_connectorForceTraceConfig gamma gamma' tau f.1) then p else 1 - p := by
-- proof
  apply StatMech.Universality.rlc_connector_pfdDualEdgeFactor_eq_randomProduct gamma gamma' tau p

/--
[rlc_connectorOuter_randomEdgeProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuter_randomEdgeProduct_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {p : Real} :
-- imply
  (∏ e ∈ (rlc_connectorOuterRandomGraph gamma gamma').edgeFinset, if rlc_connectorOuterDualConfig gamma gamma' tau e then p else 1 - p) = ∏ f : Ising.kwg_Edge (rlc_connectorAugmentedPlanarDomain gamma gamma'), if !(rlc_connectorForceTraceConfig gamma gamma' tau f.1) then p else 1 - p := by
-- proof
  apply StatMech.Universality.rlc_connectorOuter_randomEdgeProduct gamma gamma' tau p

/--
[rlc_connectorOuter_spokeEdgeProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuter_spokeEdgeProduct_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {p : Real} :
-- imply
  (∏ e ∈ (rlc_connectorOuterSpokeGraph gamma gamma').edgeFinset, if rlc_connectorOuterDualConfig gamma gamma' tau e then p else 1 - p) = p ^ (rlc_connectorOuterSpokeGraph gamma gamma').edgeFinset.card := by
-- proof
  apply StatMech.Universality.rlc_connectorOuter_spokeEdgeProduct gamma gamma' tau p

/--
[rlc_connectorOuter_edgeProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuter_edgeProduct_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {p : Real} :
-- imply
  FK.edgeProduct (rlc_connectorOuterDualGraph gamma gamma') p (rlc_connectorOuterDualConfig gamma gamma' tau) = p ^ (rlc_connectorOuterSpokeGraph gamma gamma').edgeFinset.card * BeffaraDC.edgeProductCount p (rlc_connectorAugmentedPlanarDomain gamma gamma').G.edgeFinset.card ((rlc_connectorAugmentedPlanarDomain gamma gamma').G.edgeFinset.card - (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' tau)).edgeSet.ncard) := by
-- proof
  apply StatMech.Universality.rlc_connectorOuter_edgeProduct gamma gamma' tau p

/--
[rlc_connectorOuter_bcWeight_eq_pfdDualWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuter_bcWeight_eq_pfdDualWeight_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {p q : Real} :
-- imply
  FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q (rlc_connectorOuterDualConfig gamma gamma' tau) = p ^ (rlc_connectorOuterSpokeGraph gamma gamma').edgeFinset.card * BeffaraDC.pfdDualWeight (rlc_connectorAugmentedPlanarDomain gamma gamma') p q (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' tau)) := by
-- proof
  apply StatMech.Universality.rlc_connectorOuter_bcWeight_eq_pfdDualWeight gamma gamma' tau p q

/--
[rlc_connectorOuterRestrictedZ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterRestrictedZ_eq_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real} :
-- imply
  rlc_connectorOuterRestrictedZ gamma gamma' p q = p ^ (rlc_connectorOuterSpokeGraph gamma gamma').edgeFinset.card * rlc_connectorForcedDualZ gamma gamma' p q := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterRestrictedZ_eq gamma gamma' p q

/--
[rlc_connectorOuterRestrictedProb_eq_forcedDualProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterRestrictedProb_eq_forcedDualProb_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {p q : Real}
-- given
  (hp : 0 < p) :
-- imply
  rlc_connectorOuterRestrictedProb gamma gamma' p q tau = rlc_connectorForcedDualProb gamma gamma' p q tau := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterRestrictedProb_eq_forcedDualProb gamma gamma' tau hp

/--
[rlc_connector_path_end_mem_vertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connector_path_end_mem_vertices_eq
  {a b c d : Int}
  {gamma : RlcCrossingPath a b c d} :
-- imply
  (gamma.2.1 : Site 2) ∈ rlc_pathVertices gamma := by
-- proof
  apply StatMech.Universality.rlc_connector_path_end_mem_vertices gamma

/--
[rlc_connectorRightAnchor_onRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorRightAnchor_onRight_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n} :
-- imply
  rlc_connectorOnRight gamma (rlc_connectorRightAnchor gamma) := by
-- proof
  apply StatMech.Universality.rlc_connectorRightAnchor_onRight gamma

/--
[rlc_connectorLeftAnchor_onLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorLeftAnchor_onLeft_eq
  {n : Int}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  rlc_connectorOnLeft gamma' (rlc_connectorLeftAnchor gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorLeftAnchor_onLeft gamma'

/--
[rlc_connectorInnerOuterVertex_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorInnerOuterVertex_injective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Function.Injective (rlc_connectorInnerOuterVertex gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorInnerOuterVertex_injective gamma gamma'

/--
[rlc_connectorInnerOuter_adjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorInnerOuter_adjMatch_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  FK.ocd_AdjMatch (rlc_connectorInnerGraph gamma gamma') (rlc_connectorOuterDualGraph gamma gamma') (rlc_connectorInnerOuterVertex gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorInnerOuter_adjMatch gamma gamma'

/--
[rlc_connectorInner_outerWeight_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorInner_outerWeight_factorization_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {psi : ConfigSpace (Sym2 (RlcConnectorOuterDualVertex gamma gamma'))}
  {omega : ConfigSpace (Sym2 (RlcConnectorInnerVertex gamma gamma'))}
  {p q : Real} :
-- imply
  FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') (Lattice.boundaryCliqueGraph (fun _ => False)) p q (FK.ocd_psiExt (rlc_connectorInnerOuterVertex gamma gamma') psi omega) = FK.bcWeight (rlc_connectorInnerGraph gamma gamma') (rlc_connectorInnerInducedWiring gamma gamma' psi) p q omega * FK.ocd_psiShift (rlc_connectorOuterDualGraph gamma gamma') (rlc_connectorInnerOuterVertex gamma gamma') (fun _ => False) psi p q := by
-- proof
  apply StatMech.Universality.rlc_connectorInner_outerWeight_factorization gamma gamma' psi omega p q

/--
[rlc_connectorInner_condProb_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorInner_condProb_eq_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {psi : ConfigSpace (Sym2 (RlcConnectorOuterDualVertex gamma gamma'))}
  {omega : ConfigSpace (Sym2 (RlcConnectorInnerVertex gamma gamma'))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  FK.condBcProb (rlc_connectorOuterDualGraph gamma gamma') (Lattice.boundaryCliqueGraph (fun _ => False)) p q (FK.ocd_innerEdgeFinset (rlc_connectorInnerOuterVertex gamma gamma')) psi (FK.ocd_psiExt (rlc_connectorInnerOuterVertex gamma gamma') psi omega) = FK.bcProb (rlc_connectorInnerGraph gamma gamma') (rlc_connectorInnerInducedWiring gamma gamma' psi) p q omega := by
-- proof
  apply StatMech.Universality.rlc_connectorInner_condProb_eq gamma gamma' hp hp1 hq psi omega

/--
[rlc_connectorInnerEdgeToVariable_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorInnerEdgeToVariable_injective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Function.Injective (rlc_connectorInnerEdgeToVariable gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorInnerEdgeToVariable_injective gamma gamma'

/--
[rlc_connectorInnerEdgeToVariable_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorInnerEdgeToVariable_surjective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Function.Surjective (rlc_connectorInnerEdgeToVariable gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorInnerEdgeToVariable_surjective gamma gamma'

/--
[rlc_connectorVariableEdge_preimage_mem_connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorVariableEdge_preimage_mem_connector_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : (rlc_connectorPIMSVariableGraph gamma gamma').edgeSet} :
-- imply
  rlc_pimsEdgeEquiv (e.1.map Subtype.val) ∈ rlc_connectorEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorVariableEdge_preimage_mem_connector gamma gamma' e

/--
[rlc_connectorVariableEdge_map_mem_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorVariableEdge_map_mem_lattice_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : (rlc_connectorPIMSVariableGraph gamma gamma').edgeSet} :
-- imply
  e.1.map Subtype.val ∈ (hypercubicLattice 2).edgeSet := by
-- proof
  apply StatMech.Universality.rlc_connectorVariableEdge_map_mem_lattice gamma gamma' e

/--
[rlc_connectorVariableSourceEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorVariableSourceEdge_injective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Function.Injective (rlc_connectorVariableSourceEdge gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorVariableSourceEdge_injective gamma gamma'

/--
[rlc_connectorInnerSourceEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorInnerSourceEdge_injective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Function.Injective (rlc_connectorInnerSourceEdge gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorInnerSourceEdge_injective gamma gamma'

/--
[rlc_connectorSourceActiveAssemble_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorSourceActiveAssemble_inner_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet}
  {xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')}
  {e : (rlc_connectorInnerGraph gamma gamma').edgeSet} :
-- imply
  rlc_connectorSourceActiveAssemble gamma gamma' (eta, xi) (rlc_connectorInnerSourceEdge gamma gamma' e) = !(eta e) := by
-- proof
  apply StatMech.Universality.rlc_connectorSourceActiveAssemble_inner gamma gamma' eta xi e

/--
[rlc_connectorSourceActiveAssemble_outer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorSourceActiveAssemble_outer_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet}
  {xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')}
  {e : RlcConnectorOuterSourceEdge gamma gamma'} :
-- imply
  rlc_connectorSourceActiveAssemble gamma gamma' (eta, xi) e.1 = xi e := by
-- proof
  apply StatMech.Universality.rlc_connectorSourceActiveAssemble_outer gamma gamma' eta xi e

/--
[rlc_connectorForceTraceConfig_finiteEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorForceTraceConfig_finiteEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : (rlc_connectorFiniteGraph gamma gamma').edgeSet} :
-- imply
  rlc_connectorForceTraceConfig gamma gamma' tau e.1 = tau e.1 := by
-- proof
  apply StatMech.Universality.rlc_connectorForceTraceConfig_finiteEdge gamma gamma' tau e

/--
[rlc_connectorVariableSourceEdge_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorVariableSourceEdge_map_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : (rlc_connectorPIMSVariableGraph gamma gamma').edgeSet} :
-- imply
  (rlc_connectorVariableSourceEdge gamma gamma' e).1.map Subtype.val = rlc_pimsEdgeEquiv (e.1.map Subtype.val) := by
-- proof
  apply StatMech.Universality.rlc_connectorVariableSourceEdge_map gamma gamma' e

/--
[rlc_connectorInnerSourceEdge_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorInnerSourceEdge_map_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : (rlc_connectorInnerGraph gamma gamma').edgeSet} :
-- imply
  (rlc_connectorInnerSourceEdge gamma gamma' e).1.map Subtype.val = rlc_pimsEdgeEquiv ((rlc_connectorInnerEdgeToVariable gamma gamma' e).1.map Subtype.val) := by
-- proof
  apply StatMech.Universality.rlc_connectorInnerSourceEdge_map gamma gamma' e

/--
[rlc_connectorOuterDualEdge_innerAugmented](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterDualEdge_innerAugmented_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : (rlc_connectorInnerGraph gamma gamma').edgeSet} :
-- imply
  rlc_connectorOuterDualEdge gamma gamma' (rlc_connectorInnerAugmentedEdge gamma gamma' e) = e.1.map (rlc_connectorInnerOuterVertex gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterDualEdge_innerAugmented gamma gamma' e

/--
[rlc_connectorReflectedDualEdge_innerAugmented](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorReflectedDualEdge_innerAugmented_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : (rlc_connectorInnerGraph gamma gamma').edgeSet} :
-- imply
  rlc_connectorReflectedDualEdge gamma gamma' (rlc_connectorInnerAugmentedEdge gamma gamma' e) = (rlc_connectorInnerEdgeToVariable gamma gamma' e).1.map Subtype.val := by
-- proof
  apply StatMech.Universality.rlc_connectorReflectedDualEdge_innerAugmented gamma gamma' e

/--
[rlc_connectorOuterDualEdge_mem_innerRange_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterDualEdge_mem_innerRange_iff_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f : Ising.kwg_Edge (rlc_connectorAugmentedPlanarDomain gamma gamma')} :
-- imply
  rlc_connectorOuterDualEdge gamma gamma' f ∈ Set.range (FK.ocd_innerEdge (rlc_connectorInnerOuterVertex gamma gamma')) ↔ ∃ e : (rlc_connectorInnerGraph gamma gamma').edgeSet, f.1 = (rlc_connectorInnerSourceEdge gamma gamma' e).1 := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterDualEdge_mem_innerRange_iff gamma gamma' f

/--
[rlc_connectorOuterConfig_innerActive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterConfig_innerActive_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : (rlc_connectorInnerGraph gamma gamma').edgeSet} :
-- imply
  FK.restrictActive (rlc_connectorInnerGraph gamma gamma') (FK.ocd_innerRestrict (rlc_connectorInnerOuterVertex gamma gamma') (rlc_connectorOuterDualConfig gamma gamma' tau)) e = rlc_connectorInnerActiveOfSource gamma gamma' (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') tau) e := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterConfig_innerActive gamma gamma' tau e

/--
[rlc_connectorOuterConfig_agreesOff_of_outerActive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterConfig_agreesOff_of_outerActive_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau sigma : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (houter : rlc_connectorOuterActiveOfSource gamma gamma' (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') tau) = rlc_connectorOuterActiveOfSource gamma gamma' (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') sigma)) :
-- imply
  FK.AgreesOff (FK.ocd_innerEdgeFinset (rlc_connectorInnerOuterVertex gamma gamma')) (rlc_connectorOuterDualConfig gamma gamma' tau) (rlc_connectorOuterDualConfig gamma gamma' sigma) := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterConfig_agreesOff_of_outerActive gamma gamma' tau sigma houter

/--
[rlc_connectorSplitSource_outProj_independent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorSplitSource_outProj_independent_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {eta eta' : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet}
  {xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')} :
-- imply
  FK.ocd_outProj (rlc_connectorInnerOuterVertex gamma gamma') (rlc_connectorOuterDualConfig gamma gamma' (rlc_connectorSplitSourceConfig gamma gamma' eta xi)) = FK.ocd_outProj (rlc_connectorInnerOuterVertex gamma gamma') (rlc_connectorOuterDualConfig gamma gamma' (rlc_connectorSplitSourceConfig gamma gamma' eta' xi)) := by
-- proof
  apply StatMech.Universality.rlc_connectorSplitSource_outProj_independent gamma gamma' eta eta' xi

/--
[rlc_connectorEmptyBoundary_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorEmptyBoundary_eq_bot_eq
  [Fintype V]
  [DecidableEq V] :
-- imply
  Lattice.boundaryCliqueGraph (fun _ : V => False) = (⊥ : SimpleGraph V) := by
-- proof
  apply StatMech.Universality.rlc_connectorEmptyBoundary_eq_bot

/--
[rlc_connector_bcWeight_emptyBoundary_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connector_bcWeight_emptyBoundary_eq_bot_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : Real}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  FK.bcWeight G (Lattice.boundaryCliqueGraph (fun _ : V => False)) p q omega = FK.bcWeight G ⊥ p q omega := by
-- proof
  apply StatMech.Universality.rlc_connector_bcWeight_emptyBoundary_eq_bot G p q omega

/--
[rlc_connectorSplitSource_outProj_eq_state](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorSplitSource_outProj_eq_state_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet}
  {xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')} :
-- imply
  FK.ocd_outProj (rlc_connectorInnerOuterVertex gamma gamma') (rlc_connectorOuterDualConfig gamma gamma' (rlc_connectorSplitSourceConfig gamma gamma' eta xi)) = rlc_connectorOuterStateOfSource gamma gamma' xi := by
-- proof
  apply StatMech.Universality.rlc_connectorSplitSource_outProj_eq_state gamma gamma' eta xi

/--
[rlc_connectorOuterState_reconstruct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterState_reconstruct_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet}
  {xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')} :
-- imply
  FK.ocd_psiExt (rlc_connectorInnerOuterVertex gamma gamma') (rlc_connectorOuterStateOfSource gamma gamma' xi) (FK.ocd_innerRestrict (rlc_connectorInnerOuterVertex gamma gamma') (rlc_connectorOuterDualConfig gamma gamma' (rlc_connectorSplitSourceConfig gamma gamma' eta xi))) = rlc_connectorOuterDualConfig gamma gamma' (rlc_connectorSplitSourceConfig gamma gamma' eta xi) := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterState_reconstruct gamma gamma' eta xi

/--
[rlc_connectorSplitSource_innerActive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorSplitSource_innerActive_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet}
  {xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')} :
-- imply
  FK.restrictActive (rlc_connectorInnerGraph gamma gamma') (FK.ocd_innerRestrict (rlc_connectorInnerOuterVertex gamma gamma') (rlc_connectorOuterDualConfig gamma gamma' (rlc_connectorSplitSourceConfig gamma gamma' eta xi))) = eta := by
-- proof
  apply StatMech.Universality.rlc_connectorSplitSource_innerActive gamma gamma' eta xi

/--
[rlc_connectorSplitSource_outerWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorSplitSource_outerWeight_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet}
  {xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')}
  {p q : Real} :
-- imply
  FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q (rlc_connectorOuterDualConfig gamma gamma' (rlc_connectorSplitSourceConfig gamma gamma' eta xi)) = FK.activeBCWeight (rlc_connectorInnerGraph gamma gamma') (rlc_connectorInnerInducedWiring gamma gamma' (rlc_connectorOuterStateOfSource gamma gamma' xi)) (fun _ => p) q eta * FK.ocd_psiShift (rlc_connectorOuterDualGraph gamma gamma') (rlc_connectorInnerOuterVertex gamma gamma') (fun _ => False) (rlc_connectorOuterStateOfSource gamma gamma' xi) p q := by
-- proof
  apply StatMech.Universality.rlc_connectorSplitSource_outerWeight gamma gamma' eta xi p q

/--
[rlc_connectorFibreMixtureZ_eq_sum_outerWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorFibreMixtureZ_eq_sum_outerWeight_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real} :
-- imply
  rlc_connectorFibreMixtureZ gamma gamma' p q = ∑ xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'), ∑ eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet, FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q (rlc_connectorOuterDualConfig gamma gamma' (rlc_connectorSplitSourceConfig gamma gamma' eta xi)) := by
-- proof
  apply StatMech.Universality.rlc_connectorFibreMixtureZ_eq_sum_outerWeight gamma gamma' p q

/--
[rlc_connectorFibreMixtureZ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorFibreMixtureZ_pos_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < rlc_connectorFibreMixtureZ gamma gamma' p q := by
-- proof
  apply StatMech.Universality.rlc_connectorFibreMixtureZ_pos gamma gamma' hp hp1 hq

/--
[rlc_connectorFibreWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorFibreWeight_nonneg_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 ≤ rlc_connectorFibreWeight gamma gamma' p q xi := by
-- proof
  apply StatMech.Universality.rlc_connectorFibreWeight_nonneg gamma gamma' hp hp1 hq xi

/--
[rlc_connectorFibreWeight_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorFibreWeight_sum_eq_one_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ∑ xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'), rlc_connectorFibreWeight gamma gamma' p q xi = 1 := by
-- proof
  apply StatMech.Universality.rlc_connectorFibreWeight_sum_eq_one gamma gamma' hp hp1 hq

/--
[rlc_connectorSplitOuterEventMass_eq_fibreMixture](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorSplitOuterEventMass_eq_fibreMixture_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {A : Set (ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  rlc_connectorSplitOuterEventMass gamma gamma' p q A = ∑ xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'), rlc_connectorFibreWeight gamma gamma' p q xi * FK.activeBCProbOf (rlc_connectorInnerGraph gamma gamma') (rlc_connectorInnerInducedWiring gamma gamma' (rlc_connectorOuterStateOfSource gamma gamma' xi)) (fun _ => p) q A := by
-- proof
  apply StatMech.Universality.rlc_connectorSplitOuterEventMass_eq_fibreMixture gamma gamma' hp hp1 hq A

/--
[rlc_connectorForceTraceConfig_activeCanonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorForceTraceConfig_activeCanonical_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {f : Ising.kwg_Edge (rlc_connectorAugmentedPlanarDomain gamma gamma')} :
-- imply
  rlc_connectorForceTraceConfig gamma gamma' tau f.1 = rlc_connectorForceTraceConfig gamma gamma' (FK.extendActive (rlc_connectorFiniteGraph gamma gamma') (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') tau)) f.1 := by
-- proof
  apply StatMech.Universality.rlc_connectorForceTraceConfig_activeCanonical gamma gamma' tau f

/--
[rlc_connectorOuterDualConfig_activeCanonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterDualConfig_activeCanonical_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  rlc_connectorOuterDualConfig gamma gamma' tau = rlc_connectorOuterDualConfig gamma gamma' (FK.extendActive (rlc_connectorFiniteGraph gamma gamma') (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') tau)) := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterDualConfig_activeCanonical gamma gamma' tau

/--
[rlc_connectorOuterRestrictedZ_eq_inactive_mul_fibreMixture](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterRestrictedZ_eq_inactive_mul_fibreMixture_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real} :
-- imply
  rlc_connectorOuterRestrictedZ gamma gamma' p q = 2 ^ FK.ecz_NE (rlc_connectorFiniteGraph gamma gamma') * rlc_connectorFibreMixtureZ gamma gamma' p q := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterRestrictedZ_eq_inactive_mul_fibreMixture gamma gamma' p q

/--
[rlc_connectorOuterReducedNumer_eq_inactive_mul_splitNumer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterReducedNumer_eq_inactive_mul_splitNumer_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {A : Set (ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet)} :
-- imply
  (∑ tau : ConfigSpace (Sym2 (RlcConnectorVertex n)), (rlc_connectorReducedStateOfConfig gamma gamma' ⁻¹' A).indicator (fun _ => (1 : Real)) tau * FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q (rlc_connectorOuterDualConfig gamma gamma' tau)) = 2 ^ FK.ecz_NE (rlc_connectorFiniteGraph gamma gamma') * (∑ xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'), ∑ eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet, A.indicator (fun _ => (1 : Real)) eta * FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q (rlc_connectorOuterDualConfig gamma gamma' (rlc_connectorSplitSourceConfig gamma gamma' eta xi))) := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterReducedNumer_eq_inactive_mul_splitNumer gamma gamma' p q A

/--
[rlc_connectorForcedDualReducedEventMass_eq_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorForcedDualReducedEventMass_eq_split_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {A : Set (ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet)}
-- given
  (hp : 0 < p) :
-- imply
  rlc_connectorForcedDualEventMass gamma gamma' p q (rlc_connectorReducedStateOfConfig gamma gamma' ⁻¹' A) = rlc_connectorSplitOuterEventMass gamma gamma' p q A := by
-- proof
  apply StatMech.Universality.rlc_connectorForcedDualReducedEventMass_eq_split gamma gamma' hp A

/--
[rlc_connectorOuterDualConfig_le_max](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorOuterDualConfig_le_max_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  rlc_connectorOuterDualConfig gamma gamma' tau ≤ rlc_connectorOuterMaxConfig gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorOuterDualConfig_le_max gamma gamma' tau

/--
[rlc_connectorInnerInducedWiring_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorInnerInducedWiring_mono_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {psi phi : ConfigSpace (Sym2 (RlcConnectorOuterDualVertex gamma gamma'))}
-- given
  (hpsi : psi ≤ phi) :
-- imply
  rlc_connectorInnerInducedWiring gamma gamma' psi ≤ rlc_connectorInnerInducedWiring gamma gamma' phi := by
-- proof
  apply StatMech.Universality.rlc_connectorInnerInducedWiring_mono gamma gamma' hpsi

/--
[rlc_connectorInnerInducedWiring_le_max](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorInnerInducedWiring_le_max_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  rlc_connectorInnerInducedWiring gamma gamma' (rlc_connectorOuterDualConfig gamma gamma' tau) ≤ rlc_connectorInnerMaxInducedWiring gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorInnerInducedWiring_le_max gamma gamma' tau

/--
[rlc_connectorCollaredOuterTargetVertex_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollaredOuterTargetVertex_injective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Function.Injective (rlc_connectorCollaredOuterTargetVertex gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorCollaredOuterTargetVertex_injective gamma gamma'

/--
[rlc_connectorCollaredOuterDualEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollaredOuterDualEdge_injective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Function.Injective (rlc_connectorCollaredOuterDualEdge gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorCollaredOuterDualEdge_injective gamma gamma'

/--
[rlc_connectorCollaredOuterFaceProjection_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollaredOuterFaceProjection_edge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f : Ising.kwg_Edge (rlc_connectorAugmentedPlanarDomain gamma gamma')} :
-- imply
  (rlc_connectorCollaredOuterDualEdge gamma gamma' f).map (rlc_connectorCollaredOuterFaceProjection gamma gamma') = rlc_connectorCollaredDualEnds gamma gamma' f := by
-- proof
  apply StatMech.Universality.rlc_connectorCollaredOuterFaceProjection_edge gamma gamma' f

/--
[rlc_connectorCollaredOuterRandomGraph_adj_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollaredOuterRandomGraph_adj_target_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x y : RlcConnectorVertex n} :
-- imply
  (rlc_connectorCollaredOuterRandomGraph gamma gamma').Adj (rlc_connectorCollaredOuterTargetVertex gamma gamma' x) (rlc_connectorCollaredOuterTargetVertex gamma gamma' y) ↔ (rlc_connectorPIMSVariableGraph gamma gamma').Adj x y := by
-- proof
  apply StatMech.Universality.rlc_connectorCollaredOuterRandomGraph_adj_target gamma gamma' x y

/--
[rlc_connectorCollaredOuterSpokeGraph_not_adj_targets](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollaredOuterSpokeGraph_not_adj_targets_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x y : RlcConnectorVertex n} :
-- imply
  ¬(rlc_connectorCollaredOuterSpokeGraph gamma gamma').Adj (rlc_connectorCollaredOuterTargetVertex gamma gamma' x) (rlc_connectorCollaredOuterTargetVertex gamma gamma' y) := by
-- proof
  apply StatMech.Universality.rlc_connectorCollaredOuterSpokeGraph_not_adj_targets gamma gamma' x y

/--
[rlc_connectorCollaredOuterDualGraph_adjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollaredOuterDualGraph_adjMatch_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  FK.ocd_AdjMatch (rlc_connectorPIMSVariableGraph gamma gamma') (rlc_connectorCollaredOuterDualGraph gamma gamma') (rlc_connectorCollaredOuterTargetVertex gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorCollaredOuterDualGraph_adjMatch gamma gamma'

/--
[rlc_connectorInnerCollaredOuterVertex_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorInnerCollaredOuterVertex_injective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Function.Injective (rlc_connectorInnerCollaredOuterVertex gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorInnerCollaredOuterVertex_injective gamma gamma'

/--
[rlc_connectorInnerCollaredOuter_adjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorInnerCollaredOuter_adjMatch_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  FK.ocd_AdjMatch (rlc_connectorInnerGraph gamma gamma') (rlc_connectorCollaredOuterDualGraph gamma gamma') (rlc_connectorInnerCollaredOuterVertex gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorInnerCollaredOuter_adjMatch gamma gamma'

/--
[rlc_connectorInnerCollared_outerWeight_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorInnerCollared_outerWeight_factorization_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {psi : ConfigSpace (Sym2 (RlcConnectorCollaredOuterVertex gamma gamma'))}
  {omega : ConfigSpace (Sym2 (RlcConnectorInnerVertex gamma gamma'))}
  {p q : Real} :
-- imply
  FK.bcWeight (rlc_connectorCollaredOuterDualGraph gamma gamma') (Lattice.boundaryCliqueGraph (fun _ => False)) p q (FK.ocd_psiExt (rlc_connectorInnerCollaredOuterVertex gamma gamma') psi omega) = FK.bcWeight (rlc_connectorInnerGraph gamma gamma') (rlc_connectorInnerCollaredInducedWiring gamma gamma' psi) p q omega * FK.ocd_psiShift (rlc_connectorCollaredOuterDualGraph gamma gamma') (rlc_connectorInnerCollaredOuterVertex gamma gamma') (fun _ => False) psi p q := by
-- proof
  apply StatMech.Universality.rlc_connectorInnerCollared_outerWeight_factorization gamma gamma' psi omega p q

/--
[rlc_connectorInnerCollared_condProb_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorInnerCollared_condProb_eq_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {psi : ConfigSpace (Sym2 (RlcConnectorCollaredOuterVertex gamma gamma'))}
  {omega : ConfigSpace (Sym2 (RlcConnectorInnerVertex gamma gamma'))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  FK.condBcProb (rlc_connectorCollaredOuterDualGraph gamma gamma') (Lattice.boundaryCliqueGraph (fun _ => False)) p q (FK.ocd_innerEdgeFinset (rlc_connectorInnerCollaredOuterVertex gamma gamma')) psi (FK.ocd_psiExt (rlc_connectorInnerCollaredOuterVertex gamma gamma') psi omega) = FK.bcProb (rlc_connectorInnerGraph gamma gamma') (rlc_connectorInnerCollaredInducedWiring gamma gamma' psi) p q omega := by
-- proof
  apply StatMech.Universality.rlc_connectorInnerCollared_condProb_eq gamma gamma' hp hp1 hq psi omega

/--
[rlc_connectorCollaredOuterDualEdge_innerAugmented](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollaredOuterDualEdge_innerAugmented_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : (rlc_connectorInnerGraph gamma gamma').edgeSet} :
-- imply
  rlc_connectorCollaredOuterDualEdge gamma gamma' (rlc_connectorInnerAugmentedEdge gamma gamma' e) = e.1.map (rlc_connectorInnerCollaredOuterVertex gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorCollaredOuterDualEdge_innerAugmented gamma gamma' e

/--
[rlc_connectorCollaredOuterDualConfig_randomEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollaredOuterDualConfig_randomEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {f : Ising.kwg_Edge (rlc_connectorAugmentedPlanarDomain gamma gamma')} :
-- imply
  rlc_connectorCollaredOuterDualConfig gamma gamma' tau (rlc_connectorCollaredOuterDualEdge gamma gamma' f) = !(rlc_connectorForceTraceConfig gamma gamma' tau f.1) := by
-- proof
  apply StatMech.Universality.rlc_connectorCollaredOuterDualConfig_randomEdge gamma gamma' tau f

/--
[rlc_connectorCollaredOuterConfig_innerActive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollaredOuterConfig_innerActive_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : (rlc_connectorInnerGraph gamma gamma').edgeSet} :
-- imply
  FK.restrictActive (rlc_connectorInnerGraph gamma gamma') (FK.ocd_innerRestrict (rlc_connectorInnerCollaredOuterVertex gamma gamma') (rlc_connectorCollaredOuterDualConfig gamma gamma' tau)) e = rlc_connectorInnerActiveOfSource gamma gamma' (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') tau) e := by
-- proof
  apply StatMech.Universality.rlc_connectorCollaredOuterConfig_innerActive gamma gamma' tau e

/--
[rlc_connectorCollaredOuterDualEdge_mem_innerRange_of_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollaredOuterDualEdge_mem_innerRange_of_source_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f : Ising.kwg_Edge (rlc_connectorAugmentedPlanarDomain gamma gamma')}
  {e : (rlc_connectorInnerGraph gamma gamma').edgeSet}
-- given
  (he : f.1 = (rlc_connectorInnerSourceEdge gamma gamma' e).1) :
-- imply
  rlc_connectorCollaredOuterDualEdge gamma gamma' f ∈ Set.range (FK.ocd_innerEdge (rlc_connectorInnerCollaredOuterVertex gamma gamma')) := by
-- proof
  apply StatMech.Universality.rlc_connectorCollaredOuterDualEdge_mem_innerRange_of_source gamma gamma' f e he

/--
[rlc_connectorCollaredOuterConfig_agreesOff_of_outerActive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollaredOuterConfig_agreesOff_of_outerActive_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau sigma : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (houter : rlc_connectorOuterActiveOfSource gamma gamma' (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') tau) = rlc_connectorOuterActiveOfSource gamma gamma' (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') sigma)) :
-- imply
  FK.AgreesOff (FK.ocd_innerEdgeFinset (rlc_connectorInnerCollaredOuterVertex gamma gamma')) (rlc_connectorCollaredOuterDualConfig gamma gamma' tau) (rlc_connectorCollaredOuterDualConfig gamma gamma' sigma) := by
-- proof
  apply StatMech.Universality.rlc_connectorCollaredOuterConfig_agreesOff_of_outerActive gamma gamma' tau sigma houter

/--
[rlc_connectorCollaredSplitSource_outProj_independent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollaredSplitSource_outProj_independent_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {eta eta' : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet}
  {xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')} :
-- imply
  FK.ocd_outProj (rlc_connectorInnerCollaredOuterVertex gamma gamma') (rlc_connectorCollaredOuterDualConfig gamma gamma' (rlc_connectorSplitSourceConfig gamma gamma' eta xi)) = FK.ocd_outProj (rlc_connectorInnerCollaredOuterVertex gamma gamma') (rlc_connectorCollaredOuterDualConfig gamma gamma' (rlc_connectorSplitSourceConfig gamma gamma' eta' xi)) := by
-- proof
  apply StatMech.Universality.rlc_connectorCollaredSplitSource_outProj_independent gamma gamma' eta eta' xi

/--
[rlc_connectorCollaredSplitSource_outProj_eq_state](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollaredSplitSource_outProj_eq_state_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet}
  {xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')} :
-- imply
  FK.ocd_outProj (rlc_connectorInnerCollaredOuterVertex gamma gamma') (rlc_connectorCollaredOuterDualConfig gamma gamma' (rlc_connectorSplitSourceConfig gamma gamma' eta xi)) = rlc_connectorCollaredOuterStateOfSource gamma gamma' xi := by
-- proof
  apply StatMech.Universality.rlc_connectorCollaredSplitSource_outProj_eq_state gamma gamma' eta xi

/--
[rlc_connectorCollaredOuterState_reconstruct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollaredOuterState_reconstruct_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet}
  {xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')} :
-- imply
  FK.ocd_psiExt (rlc_connectorInnerCollaredOuterVertex gamma gamma') (rlc_connectorCollaredOuterStateOfSource gamma gamma' xi) (FK.ocd_innerRestrict (rlc_connectorInnerCollaredOuterVertex gamma gamma') (rlc_connectorCollaredOuterDualConfig gamma gamma' (rlc_connectorSplitSourceConfig gamma gamma' eta xi))) = rlc_connectorCollaredOuterDualConfig gamma gamma' (rlc_connectorSplitSourceConfig gamma gamma' eta xi) := by
-- proof
  apply StatMech.Universality.rlc_connectorCollaredOuterState_reconstruct gamma gamma' eta xi

/--
[rlc_connectorCollaredSplitSource_innerActive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollaredSplitSource_innerActive_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet}
  {xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')} :
-- imply
  FK.restrictActive (rlc_connectorInnerGraph gamma gamma') (FK.ocd_innerRestrict (rlc_connectorInnerCollaredOuterVertex gamma gamma') (rlc_connectorCollaredOuterDualConfig gamma gamma' (rlc_connectorSplitSourceConfig gamma gamma' eta xi))) = eta := by
-- proof
  apply StatMech.Universality.rlc_connectorCollaredSplitSource_innerActive gamma gamma' eta xi

/--
[rlc_connectorCollaredSplitSource_outerWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollaredSplitSource_outerWeight_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet}
  {xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')}
  {p q : Real} :
-- imply
  FK.bcWeight (rlc_connectorCollaredOuterDualGraph gamma gamma') ⊥ p q (rlc_connectorCollaredOuterDualConfig gamma gamma' (rlc_connectorSplitSourceConfig gamma gamma' eta xi)) = FK.activeBCWeight (rlc_connectorInnerGraph gamma gamma') (rlc_connectorInnerCollaredInducedWiring gamma gamma' (rlc_connectorCollaredOuterStateOfSource gamma gamma' xi)) (fun _ => p) q eta * FK.ocd_psiShift (rlc_connectorCollaredOuterDualGraph gamma gamma') (rlc_connectorInnerCollaredOuterVertex gamma gamma') (fun _ => False) (rlc_connectorCollaredOuterStateOfSource gamma gamma' xi) p q := by
-- proof
  apply StatMech.Universality.rlc_connectorCollaredSplitSource_outerWeight gamma gamma' eta xi p q

/--
[rlc_connectorCollaredFibreMixtureZ_eq_sum_outerWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollaredFibreMixtureZ_eq_sum_outerWeight_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real} :
-- imply
  rlc_connectorCollaredFibreMixtureZ gamma gamma' p q = ∑ xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'), ∑ eta : ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet, FK.bcWeight (rlc_connectorCollaredOuterDualGraph gamma gamma') ⊥ p q (rlc_connectorCollaredOuterDualConfig gamma gamma' (rlc_connectorSplitSourceConfig gamma gamma' eta xi)) := by
-- proof
  apply StatMech.Universality.rlc_connectorCollaredFibreMixtureZ_eq_sum_outerWeight gamma gamma' p q

/--
[rlc_connectorCollaredFibreMixtureZ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollaredFibreMixtureZ_pos_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < rlc_connectorCollaredFibreMixtureZ gamma gamma' p q := by
-- proof
  apply StatMech.Universality.rlc_connectorCollaredFibreMixtureZ_pos gamma gamma' hp hp1 hq

/--
[rlc_connectorCollaredFibreWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollaredFibreWeight_nonneg_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 ≤ rlc_connectorCollaredFibreWeight gamma gamma' p q xi := by
-- proof
  apply StatMech.Universality.rlc_connectorCollaredFibreWeight_nonneg gamma gamma' hp hp1 hq xi

/--
[rlc_connectorCollaredFibreWeight_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollaredFibreWeight_sum_eq_one_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ∑ xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'), rlc_connectorCollaredFibreWeight gamma gamma' p q xi = 1 := by
-- proof
  apply StatMech.Universality.rlc_connectorCollaredFibreWeight_sum_eq_one gamma gamma' hp hp1 hq

/--
[rlc_connectorCollaredSplitOuterEventMass_eq_fibreMixture](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollaredSplitOuterEventMass_eq_fibreMixture_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {A : Set (ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  rlc_connectorCollaredSplitOuterEventMass gamma gamma' p q A = ∑ xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'), rlc_connectorCollaredFibreWeight gamma gamma' p q xi * FK.activeBCProbOf (rlc_connectorInnerGraph gamma gamma') (rlc_connectorInnerCollaredInducedWiring gamma gamma' (rlc_connectorCollaredOuterStateOfSource gamma gamma' xi)) (fun _ => p) q A := by
-- proof
  apply StatMech.Universality.rlc_connectorCollaredSplitOuterEventMass_eq_fibreMixture gamma gamma' hp hp1 hq A

/--
[rlc_connectorCollaredOuterDualConfig_le_max](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollaredOuterDualConfig_le_max_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  rlc_connectorCollaredOuterDualConfig gamma gamma' tau ≤ rlc_connectorCollaredOuterMaxConfig gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorCollaredOuterDualConfig_le_max gamma gamma' tau

/--
[rlc_connectorInnerCollaredInducedWiring_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorInnerCollaredInducedWiring_mono_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {psi phi : ConfigSpace (Sym2 (RlcConnectorCollaredOuterVertex gamma gamma'))}
-- given
  (hpsi : psi ≤ phi) :
-- imply
  rlc_connectorInnerCollaredInducedWiring gamma gamma' psi ≤ rlc_connectorInnerCollaredInducedWiring gamma gamma' phi := by
-- proof
  apply StatMech.Universality.rlc_connectorInnerCollaredInducedWiring_mono gamma gamma' hpsi

/--
[rlc_connectorInnerCollaredInducedWiring_le_max](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorInnerCollaredInducedWiring_le_max_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  rlc_connectorInnerCollaredInducedWiring gamma gamma' (rlc_connectorCollaredOuterDualConfig gamma gamma' tau) ≤ rlc_connectorInnerCollaredMaxInducedWiring gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorInnerCollaredInducedWiring_le_max gamma gamma' tau

/--
[rlc_connector_activeBCProbOf_q_one_independent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connector_activeBCProbOf_q_one_independent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C D : SimpleGraph V}
  [DecidableRel C.Adj]
  [DecidableRel D.Adj]
  {pf : Sym2 V → Real}
  {A : Set (ConfigSpace G.edgeSet)} :
-- imply
  FK.activeBCProbOf G C pf 1 A = FK.activeBCProbOf G D pf 1 A := by
-- proof
  apply StatMech.Universality.rlc_connector_activeBCProbOf_q_one_independent G C D pf A

/--
[rlc_connectorSplitOuterEventMass_q_one_eq_innerMerged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorSplitOuterEventMass_q_one_eq_innerMerged_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p : Real}
  {A : Set (ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  rlc_connectorSplitOuterEventMass gamma gamma' p 1 A = FK.activeBCProbOf (rlc_connectorInnerGraph gamma gamma') (rlc_connectorInnerMergedWiring gamma gamma') (fun _ => p) 1 A := by
-- proof
  apply StatMech.Universality.rlc_connectorSplitOuterEventMass_q_one_eq_innerMerged gamma gamma' hp hp1 A

/--
[rlc_connectorCollaredSplitOuterEventMass_q_one_eq_innerMerged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCollaredSplitOuterEventMass_q_one_eq_innerMerged_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p : Real}
  {A : Set (ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  rlc_connectorCollaredSplitOuterEventMass gamma gamma' p 1 A = FK.activeBCProbOf (rlc_connectorInnerGraph gamma gamma') (rlc_connectorInnerMergedWiring gamma gamma') (fun _ => p) 1 A := by
-- proof
  apply StatMech.Universality.rlc_connectorCollaredSplitOuterEventMass_q_one_eq_innerMerged gamma gamma' hp hp1 A

/--
[rlc_connectorForcedDualReducedEventMass_q_one_eq_innerMerged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorForcedDualReducedEventMass_q_one_eq_innerMerged_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p : Real}
  {A : Set (ConfigSpace (rlc_connectorInnerGraph gamma gamma').edgeSet)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  rlc_connectorForcedDualEventMass gamma gamma' p 1 (rlc_connectorReducedStateOfConfig gamma gamma' ⁻¹' A) = FK.activeBCProbOf (rlc_connectorInnerGraph gamma gamma') (rlc_connectorInnerMergedWiring gamma gamma') (fun _ => p) 1 A := by
-- proof
  apply StatMech.Universality.rlc_connectorForcedDualReducedEventMass_q_one_eq_innerMerged gamma gamma' hp hp1 A

/--
[rlc_connectorReflectedDualConfig_eq_true_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorReflectedDualConfig_eq_true_iff_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (RlcConnectorVertex n)} :
-- imply
  rlc_connectorReflectedDualConfig gamma gamma' tau e = true ↔ ∃ f : Ising.kwg_Edge (rlc_connectorAugmentedPlanarDomain gamma gamma'), f.1 ∉ (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' tau)).edgeSet ∧ e.map Subtype.val = s(rlc_dualReflect (Ising.kwg_flankLeft (rlc_connectorAugmentedPlanarDomain gamma gamma') f), rlc_dualReflect (Ising.kwg_flankRight (rlc_connectorAugmentedPlanarDomain gamma gamma') f)) := by
-- proof
  apply StatMech.Universality.rlc_connectorReflectedDualConfig_eq_true_iff gamma gamma' tau e

/--
[rlc_connectorReflectedDualConfig_open_preimage_mem_connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorReflectedDualConfig_open_preimage_mem_connector_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (RlcConnectorVertex n)}
-- given
  (hopen : rlc_connectorReflectedDualConfig gamma gamma' tau e = true) :
-- imply
  rlc_pimsEdgeEquiv (e.map Subtype.val) ∈ rlc_connectorEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorReflectedDualConfig_open_preimage_mem_connector gamma gamma' tau e hopen

/--
[rlc_connectorReflectedDualConfig_le_PIMS](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorReflectedDualConfig_le_PIMS_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  rlc_connectorReflectedDualConfig gamma gamma' tau <= rlc_connectorPIMSReflectedConfig gamma gamma' tau := by
-- proof
  apply StatMech.Universality.rlc_connectorReflectedDualConfig_le_PIMS gamma gamma' tau

/--
[rlc_connectorReflectedDualConfig_le_PIMSCollared](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorReflectedDualConfig_le_PIMSCollared_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  rlc_connectorReflectedDualConfig gamma gamma' tau <= rlc_connectorPIMSCollaredReflectedConfig gamma gamma' tau := by
-- proof
  apply StatMech.Universality.rlc_connectorReflectedDualConfig_le_PIMSCollared gamma gamma' tau

/--
[rlc_connectorForcedDualProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorForcedDualProb_nonneg_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 <= rlc_connectorForcedDualProb gamma gamma' p q tau := by
-- proof
  apply StatMech.Universality.rlc_connectorForcedDualProb_nonneg gamma gamma' hp hp1 hq tau

/--
[rlc_connectorForcedDualEventMass_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorForcedDualEventMass_mono_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {A B : Set (ConfigSpace (Sym2 (RlcConnectorVertex n)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hAB : A ⊆ B) :
-- imply
  rlc_connectorForcedDualEventMass gamma gamma' p q A <= rlc_connectorForcedDualEventMass gamma gamma' p q B := by
-- proof
  apply StatMech.Universality.rlc_connectorForcedDualEventMass_mono gamma gamma' hp hp1 hq hAB

/--
[rlc_bcEventMass_separate_eq_forcedDualEventMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_bcEventMass_separate_eq_forcedDualEventMass_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (ConfigSpace (Sym2 (RlcConnectorVertex n)))}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') p q A = rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.dualParam p q) q A := by
-- proof
  apply StatMech.Universality.rlc_bcEventMass_separate_eq_forcedDualEventMass gamma gamma' A hp hp1 hq

/--
[rlc_bcProb_separate_selfDual_eq_forcedDualProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_bcProb_separate_selfDual_eq_forcedDualProb_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  FK.bcProb (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q tau = rlc_connectorForcedDualProb gamma gamma' (BeffaraDC.selfDualPoint q) q tau := by
-- proof
  apply StatMech.Universality.rlc_bcProb_separate_selfDual_eq_forcedDualProb gamma gamma' tau hq

/--
[rlc_bcEventMass_separate_selfDual_eq_forcedDualEventMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_bcEventMass_separate_selfDual_eq_forcedDualEventMass_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (ConfigSpace (Sym2 (RlcConnectorVertex n)))}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q A = rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q A := by
-- proof
  apply StatMech.Universality.rlc_bcEventMass_separate_selfDual_eq_forcedDualEventMass gamma gamma' A hq

/--
[rlc_connectorComponentWiring_le_merged_of_oneAttachment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorComponentWiring_le_merged_of_oneAttachment_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H : SimpleGraph (RlcConnectorVertex n)}
-- given
  (hattach : RlcConnectorExteriorOneAttachment H) :
-- imply
  rlc_connectorComponentWiring H ≤ rlc_connectorMergedWiring gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorComponentWiring_le_merged_of_oneAttachment gamma gamma' H hattach

/--
[rlc_connectorPIMSCollaredInducedWiring_le_merged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSCollaredInducedWiring_le_merged_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  rlc_connectorComponentWiring (rlc_connectorPIMSCollaredExteriorOpenGraph gamma gamma' tau) ≤ rlc_connectorMergedWiring gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSCollaredInducedWiring_le_merged gamma gamma' tau

/--
[rlc_connectorMergedWiring_le_mergedClique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorMergedWiring_le_mergedClique_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  rlc_connectorMergedWiring gamma gamma' ≤ rlc_connectorMergedClique gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorMergedWiring_le_mergedClique gamma gamma'

/--
[rlc_connectorMergedWiring_reachable_onEither](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorMergedWiring_reachable_onEither_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x y : RlcConnectorVertex n}
-- given
  (hx : rlc_connectorOnEither gamma gamma' x)
  (hy : rlc_connectorOnEither gamma gamma' y) :
-- imply
  (rlc_connectorMergedWiring gamma gamma').Reachable x y := by
-- proof
  apply StatMech.Universality.rlc_connectorMergedWiring_reachable_onEither gamma gamma' hx hy

/--
[rlc_connectorMergedWiring_reachable_iff_mergedClique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorMergedWiring_reachable_iff_mergedClique_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H : SimpleGraph (RlcConnectorVertex n)}
  {x y : RlcConnectorVertex n} :
-- imply
  (H ⊔ rlc_connectorMergedWiring gamma gamma').Reachable x y ↔ (H ⊔ rlc_connectorMergedClique gamma gamma').Reachable x y := by
-- proof
  apply StatMech.Universality.rlc_connectorMergedWiring_reachable_iff_mergedClique gamma gamma' H x y

/--
[rlc_numClustersBC_mergedWiring_eq_mergedClique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_numClustersBC_mergedWiring_eq_mergedClique_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.numClustersBC (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') tau = FK.numClustersBC (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorMergedClique gamma gamma') tau := by
-- proof
  apply StatMech.Universality.rlc_numClustersBC_mergedWiring_eq_mergedClique gamma gamma' tau

/--
[rlc_bcProb_mergedWiring_eq_mergedClique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_bcProb_mergedWiring_eq_mergedClique_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.bcProb (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') p q tau = FK.bcProb (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorMergedClique gamma gamma') p q tau := by
-- proof
  apply StatMech.Universality.rlc_bcProb_mergedWiring_eq_mergedClique gamma gamma' p q tau

/--
[rlc_bcEventMass_mergedWiring_eq_mergedClique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_bcEventMass_mergedWiring_eq_mergedClique_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {A : Set (ConfigSpace (Sym2 (RlcConnectorVertex n)))} :
-- imply
  FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') p q A = FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorMergedClique gamma gamma') p q A := by
-- proof
  apply StatMech.Universality.rlc_bcEventMass_mergedWiring_eq_mergedClique gamma gamma' p q A

/--
[rlc_connectorForcedDualEventMass_compl_le_merged_of_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorForcedDualEventMass_compl_le_merged_of_equiv_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  {A : Set (ConfigSpace (Sym2 (RlcConnectorVertex n)))}
  {D : ConfigSpace (Sym2 (RlcConnectorVertex n)) ≃ ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hq : 1 <= q)
  (hfailure : ∀ tau, tau ∉ A → D tau ∈ A)
  (hprob : ∀ tau, rlc_connectorForcedDualProb gamma gamma' (BeffaraDC.selfDualPoint q) q tau <= FK.bcProb (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (D tau)) :
-- imply
  rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q Aᶜ <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q A := by
-- proof
  apply StatMech.Universality.rlc_connectorForcedDualEventMass_compl_le_merged_of_equiv gamma gamma' hq A D hfailure hprob

/--
[rlc_connectorEvent_iff_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorEvent_iff_finite_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  omega ∈ rlc_connectorEvent gamma gamma' ↔ rlc_connectorRestrictConfig omega ∈ rlc_finiteConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorEvent_iff_finite gamma gamma' omega

/--
[rlc_connectorAmbientMixedConfig_mem_connectorEvent_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorAmbientMixedConfig_mem_connectorEvent_iff_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  rlc_connectorAmbientMixedConfig gamma gamma' tau ∈ rlc_connectorEvent gamma gamma' ↔ tau ∈ rlc_finiteConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorAmbientMixedConfig_mem_connectorEvent_iff gamma gamma' tau

/--
[rlc_finiteConnectorFailure_reflectedOpenDualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_finiteConnectorFailure_reflectedOpenDualCircuit_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hno : tau ∉ rlc_finiteConnectorEvent gamma gamma') :
-- imply
  ∃ (u : Site 2) (c : (openSubgraph 2 (rlc_dualReflectConfig (rlc_maskConfig (rlc_connectorEdges gamma gamma') (rlc_connectorAmbientMixedConfig gamma gamma' tau)))).Walk (rlc_dualReflect u) (rlc_dualReflect u)), c.IsCycle := by
-- proof
  apply StatMech.Universality.rlc_finiteConnectorFailure_reflectedOpenDualCircuit gamma gamma' tau hno

/--
[rlc_connectorReachSet_openWalk_lift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorReachSet_openWalk_lift_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {u v : RlcConnectorVertex n}
  {w : (openSubgraphInduce 2 (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega) (rect (-2 * n) (2 * n) (-n) n)).Walk u v}
-- given
  (hu : (u : Site 2) ∈ rlc_connectorReachSet gamma gamma' omega) :
-- imply
  ∃ hv : (v : Site 2) ∈ rlc_connectorReachSet gamma gamma' omega, ((hypercubicLattice 2).induce (rlc_connectorReachSet gamma gamma' omega)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
-- proof
  apply StatMech.Universality.rlc_connectorReachSet_openWalk_lift gamma gamma' omega hu w

/--
[rlc_connectorReachSet_rightPath_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorReachSet_rightPath_reachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2}
-- given
  (hx : x ∈ rlc_pathVertices gamma.1)
  (hy : y ∈ rlc_pathVertices gamma.1) :
-- imply
  ((hypercubicLattice 2).induce (rlc_connectorReachSet gamma gamma' omega)).Reachable ⟨x, rlc_rightPathVertex_mem_connectorReachSet gamma gamma' omega hx⟩ ⟨y, rlc_rightPathVertex_mem_connectorReachSet gamma gamma' omega hy⟩ := by
-- proof
  apply StatMech.Universality.rlc_connectorReachSet_rightPath_reachable gamma gamma' omega hx hy

/--
[rlc_connectorReachSet_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorReachSet_reachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {u v : Site 2}
-- given
  (hu : u ∈ rlc_connectorReachSet gamma gamma' omega)
  (hv : v ∈ rlc_connectorReachSet gamma gamma' omega) :
-- imply
  ((hypercubicLattice 2).induce (rlc_connectorReachSet gamma gamma' omega)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
-- proof
  apply StatMech.Universality.rlc_connectorReachSet_reachable gamma gamma' omega hu hv

/--
[rlc_connectorReachSet_reachable_in_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorReachSet_reachable_in_barrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {u v : Site 2}
-- given
  (hu : u ∈ rlc_connectorReachSet gamma gamma' omega)
  (hv : v ∈ rlc_connectorReachSet gamma gamma' omega) :
-- imply
  (latticeMinusBarrier (rlc_connectorReachSet gamma gamma' omega)).Reachable u v := by
-- proof
  apply StatMech.Universality.rlc_connectorReachSet_reachable_in_barrier gamma gamma' omega hu hv

/--
[rlc_connectorExteriorComponent_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorExteriorComponent_infinite_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  (rlc_connectorExteriorComponent gamma gamma' omega).supp.Infinite := by
-- proof
  apply StatMech.Universality.rlc_connectorExteriorComponent_infinite gamma gamma' omega

/--
[rlc_connectorReachSet_subset_filled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorReachSet_subset_filled_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  rlc_connectorReachSet gamma gamma' omega ⊆ rlc_connectorFilledReachSet gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_connectorReachSet_subset_filled gamma gamma' omega

/--
[rlc_connectorExteriorSet_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorExteriorSet_reachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {u v : Site 2}
-- given
  (hu : u ∈ rlc_connectorExteriorSet gamma gamma' omega)
  (hv : v ∈ rlc_connectorExteriorSet gamma gamma' omega) :
-- imply
  ((hypercubicLattice 2).induce (rlc_connectorExteriorSet gamma gamma' omega)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
-- proof
  apply StatMech.Universality.rlc_connectorExteriorSet_reachable gamma gamma' omega hu hv

/--
[rlc_connectorFilledReachSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorFilledReachSet_finite_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  (rlc_connectorFilledReachSet gamma gamma' omega).Finite := by
-- proof
  apply StatMech.Universality.rlc_connectorFilledReachSet_finite gamma gamma' omega

/--
[rlc_connectorExteriorSet_reachable_in_filledBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorExteriorSet_reachable_in_filledBarrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {u v : Site 2}
-- given
  (hu : u ∈ rlc_connectorExteriorSet gamma gamma' omega)
  (hv : v ∈ rlc_connectorExteriorSet gamma gamma' omega) :
-- imply
  (latticeMinusBarrier (rlc_connectorFilledReachSet gamma gamma' omega)).Reachable u v := by
-- proof
  apply StatMech.Universality.rlc_connectorExteriorSet_reachable_in_filledBarrier gamma gamma' omega hu hv

/--
[rlc_connectorFilledReachSet_reaches_reachSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorFilledReachSet_reaches_reachSet_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {u : Site 2}
-- given
  (hu : u ∈ rlc_connectorFilledReachSet gamma gamma' omega) :
-- imply
  ∃ z : Site 2, ∃ hz : z ∈ rlc_connectorReachSet gamma gamma' omega, ((hypercubicLattice 2).induce (rlc_connectorFilledReachSet gamma gamma' omega)).Reachable ⟨u, hu⟩ ⟨z, rlc_connectorReachSet_subset_filled gamma gamma' omega hz⟩ := by
-- proof
  apply StatMech.Universality.rlc_connectorFilledReachSet_reaches_reachSet gamma gamma' omega hu

/--
[rlc_connectorFilledReachSet_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorFilledReachSet_reachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {u v : Site 2}
-- given
  (hu : u ∈ rlc_connectorFilledReachSet gamma gamma' omega)
  (hv : v ∈ rlc_connectorFilledReachSet gamma gamma' omega) :
-- imply
  ((hypercubicLattice 2).induce (rlc_connectorFilledReachSet gamma gamma' omega)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
-- proof
  apply StatMech.Universality.rlc_connectorFilledReachSet_reachable gamma gamma' omega hu hv

/--
[rlc_connectorFilledReachSet_reachable_in_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorFilledReachSet_reachable_in_barrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {u v : Site 2}
-- given
  (hu : u ∈ rlc_connectorFilledReachSet gamma gamma' omega)
  (hv : v ∈ rlc_connectorFilledReachSet gamma gamma' omega) :
-- imply
  (latticeMinusBarrier (rlc_connectorFilledReachSet gamma gamma' omega)).Reachable u v := by
-- proof
  apply StatMech.Universality.rlc_connectorFilledReachSet_reachable_in_barrier gamma gamma' omega hu hv

/--
[rlc_connectorFilledReachSet_faceBoundaryConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorFilledReachSet_faceBoundaryConnected_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  FaceBoundaryConnected (rlc_connectorFilledReachSet gamma gamma' omega) (phb_boundarySupport (rlc_connectorFilledReachSet gamma gamma' omega) (rlc_connectorFilledReachSet_finite gamma gamma' omega)) := by
-- proof
  apply StatMech.Universality.rlc_connectorFilledReachSet_faceBoundaryConnected gamma gamma' omega

/--
[rlc_connectorFilledBoundary_inside_mem_reachSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorFilledBoundary_inside_mem_reachSet_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {p q : Site 2}
-- given
  (hp : p ∈ rlc_connectorFilledReachSet gamma gamma' omega)
  (hq : q ∉ rlc_connectorFilledReachSet gamma gamma' omega)
  (hpq : (hypercubicLattice 2).Adj p q) :
-- imply
  p ∈ rlc_connectorReachSet gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_connectorFilledBoundary_inside_mem_reachSet gamma gamma' omega hp hq hpq

/--
[rlc_connectorFilled_edgeBoundary_subset_reachSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorFilled_edgeBoundary_subset_reachSet_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {p q : Site 2}
-- given
  (hpq : (p, q) ∈ edgeBoundary 2 (rlc_connectorFilledReachSet gamma gamma' omega)) :
-- imply
  (p, q) ∈ edgeBoundary 2 (rlc_connectorReachSet gamma gamma' omega) := by
-- proof
  apply StatMech.Universality.rlc_connectorFilled_edgeBoundary_subset_reachSet gamma gamma' omega hpq

/--
[rlc_connectorFilledFaceBoundaryGraph_le_reachFaceBoundaryGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorFilledFaceBoundaryGraph_le_reachFaceBoundaryGraph_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  faceBoundaryGraph (rlc_connectorFilledReachSet gamma gamma' omega) ≤ faceBoundaryGraph (rlc_connectorReachSet gamma gamma' omega) := by
-- proof
  apply StatMech.Universality.rlc_connectorFilledFaceBoundaryGraph_le_reachFaceBoundaryGraph gamma gamma' omega

/--
[rlc_connectorFilledFaceBoundary_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorFilledFaceBoundary_reachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {f g : Site 2}
-- given
  (hf : f ∈ (faceBoundaryGraph (rlc_connectorFilledReachSet gamma gamma' omega)).support)
  (hg : g ∈ (faceBoundaryGraph (rlc_connectorFilledReachSet gamma gamma' omega)).support) :
-- imply
  (faceBoundaryGraph (rlc_connectorFilledReachSet gamma gamma' omega)).Reachable f g := by
-- proof
  apply StatMech.Universality.rlc_connectorFilledFaceBoundary_reachable gamma gamma' omega hf hg

/--
[rlc_connector_faceBoundary_preimage_not_trace_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connector_faceBoundary_preimage_not_trace_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {f g : Site 2}
-- given
  (hno : tau ∉ rlc_finiteConnectorEvent gamma gamma')
  (hfg : (faceBoundaryGraph (rlc_connectorReachSet gamma gamma' (rlc_connectorAmbientMixedConfig gamma gamma' tau))).Adj f g) :
-- imply
  sharedPrimalEdge f g ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_connector_faceBoundary_preimage_not_trace_of_failure gamma gamma' tau hno hfg

/--
[rlc_connector_reflectedFaceBoundary_preimage_not_trace_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connector_reflectedFaceBoundary_preimage_not_trace_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {f g : Site 2}
-- given
  (hno : tau ∉ rlc_finiteConnectorEvent gamma gamma')
  (hfg : (faceBoundaryGraph (rlc_connectorReachSet gamma gamma' (rlc_connectorAmbientMixedConfig gamma gamma' tau))).Adj f g) :
-- imply
  rlc_pimsEdgeEquiv s(rlc_dualReflect f, rlc_dualReflect g) ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_connector_reflectedFaceBoundary_preimage_not_trace_of_failure gamma gamma' tau hno hfg

/--
[rlc_connector_reflectedFaceBoundaryWalk_preimage_not_trace_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connector_reflectedFaceBoundaryWalk_preimage_not_trace_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {x y : Site 2}
  {a : (faceBoundaryGraph (rlc_connectorReachSet gamma gamma' (rlc_connectorAmbientMixedConfig gamma gamma' tau))).Walk x y}
-- given
  (hno : tau ∉ rlc_finiteConnectorEvent gamma gamma') :
-- imply
  let eta := rlc_maskConfig (rlc_connectorEdges gamma gamma') (rlc_connectorAmbientMixedConfig gamma gamma' tau) let hle := rlc_faceBoundaryGraph_le_openFaceDual gamma gamma' (rlc_connectorAmbientMixedConfig gamma gamma' tau) ∀ e ∈ (rlc_dualReflectOpenWalk eta (a.mapLe hle)).edges, rlc_pimsEdgeEquiv e ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_connector_reflectedFaceBoundaryWalk_preimage_not_trace_of_failure gamma gamma' tau hno a

/--
[rlc_connectorEdge_endpoint_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorEdge_endpoint_mem_box_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)}
  {z : Site 2}
-- given
  (he : e ∈ rlc_connectorEdges gamma gamma')
  (hz : z ∈ e) :
-- imply
  z ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)) := by
-- proof
  apply StatMech.Universality.rlc_connectorEdge_endpoint_mem_box gamma gamma' he hz

/--
[rlc_walk_support_mem_connectorBox_of_connectorEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_walk_support_mem_connectorBox_of_connectorEdges_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H : SimpleGraph (Site 2)}
  {x y : Site 2}
  {a : H.Walk x y}
-- given
  (hy : y ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)))
  (hedges : ∀ e ∈ a.edges, e ∈ rlc_connectorEdges gamma gamma') :
-- imply
  ∀ z ∈ a.support, z ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)) := by
-- proof
  apply StatMech.Universality.rlc_walk_support_mem_connectorBox_of_connectorEdges gamma gamma' a hy hedges

/--
[rlc_traceSplitCounterexample_not_filledBoundaryTargetSupported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_traceSplitCounterexample_not_filledBoundaryTargetSupported_eq :
-- imply
  ¬ RlcConnectorPIMSFilledBoundaryTargetSupported rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft rlc_traceSplitCounterexampleFiniteAllClosed := by
-- proof
  apply StatMech.Universality.rlc_traceSplitCounterexample_not_filledBoundaryTargetSupported

/--
[rlc_traceSplitCounterexample_finiteAllClosed_reachSet_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_traceSplitCounterexample_finiteAllClosed_reachSet_eq_eq :
-- imply
  rlc_connectorReachSet rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft (rlc_connectorAmbientMixedConfig rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft rlc_traceSplitCounterexampleFiniteAllClosed) = (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2)) := by
-- proof
  apply StatMech.Universality.rlc_traceSplitCounterexample_finiteAllClosed_reachSet_eq

/--
[rlc_traceSplitCounterexample_finiteAllClosed_boundaryArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_traceSplitCounterexample_finiteAllClosed_boundaryArc_eq :
-- imply
  RlcConnectorPIMSBoundaryArc rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft rlc_traceSplitCounterexampleFiniteAllClosed := by
-- proof
  apply StatMech.Universality.rlc_traceSplitCounterexample_finiteAllClosed_boundaryArc

/--
[rlc_traceSplitCounterexample_finiteAllClosed_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_traceSplitCounterexample_finiteAllClosed_failure_eq :
-- imply
  rlc_traceSplitCounterexampleFiniteAllClosed ∉ rlc_finiteConnectorEvent rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
-- proof
  apply StatMech.Universality.rlc_traceSplitCounterexample_finiteAllClosed_failure

/--
[rlc_traceSplitCounterexample_reflectedDual_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_traceSplitCounterexample_reflectedDual_failure_eq :
-- imply
  rlc_connectorReflectedDualConfig rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft rlc_traceSplitCounterexampleFiniteAllClosed ∉ rlc_finiteConnectorEvent rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
-- proof
  apply StatMech.Universality.rlc_traceSplitCounterexample_reflectedDual_failure

/--
[rlc_connectorPIMSBoundaryArc_of_filledBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSBoundaryArc_of_filledBoundary_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hcontacts : RlcConnectorPIMSFilledBoundaryContacts gamma gamma' tau)
  (htarget : RlcConnectorPIMSFilledBoundaryTargetSupported gamma gamma' tau) :
-- imply
  RlcConnectorPIMSBoundaryArc gamma gamma' tau := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSBoundaryArc_of_filledBoundary gamma gamma' tau hcontacts htarget

/--
[rlc_connectorPIMSBoundaryArc_of_contourContacts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSBoundaryArc_of_contourContacts_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_connectorReachSet gamma gamma' (rlc_connectorAmbientMixedConfig gamma gamma' tau))).Walk u u}
-- given
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hside : RlcConnectorPIMSContourArcSide gamma gamma' tau c hx hy) :
-- imply
  RlcConnectorPIMSBoundaryArc gamma gamma' tau := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSBoundaryArc_of_contourContacts gamma gamma' tau c hx hy hxPath hyPath hside

/--
[rlc_connectorPIMSBoundaryArc_of_contourCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSBoundaryArc_of_contourCertificate_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (h : RlcConnectorPIMSContourCertificate gamma gamma' tau) :
-- imply
  RlcConnectorPIMSBoundaryArc gamma gamma' tau := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSBoundaryArc_of_contourCertificate gamma gamma' tau h

/--
[rlc_connectorPIMSSourceOpenCase_not_trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSSourceOpenCase_not_trace_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (Site 2)}
-- given
  (hcase : RlcConnectorPIMSSourceOpenCase gamma gamma' tau e) :
-- imply
  rlc_pimsEdgeEquiv e ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSSourceOpenCase_not_trace gamma gamma' tau hcase

/--
[rlc_connectorPIMSSourceOpenCase_of_maskedDual_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSSourceOpenCase_of_maskedDual_open_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (Site 2)}
-- given
  (hnotTrace : rlc_pimsEdgeEquiv e ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1)
  (hopen : rlc_dualReflectConfig (rlc_maskConfig (rlc_connectorEdges gamma gamma') (rlc_connectorAmbientMixedConfig gamma gamma' tau)) e = true) :
-- imply
  RlcConnectorPIMSSourceOpenCase gamma gamma' tau e := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSSourceOpenCase_of_maskedDual_open gamma gamma' tau e hnotTrace hopen

/--
[rlc_connectorPIMSReflectedConfig_open_of_sourceOpenCase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSReflectedConfig_open_of_sourceOpenCase_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (Site 2)}
-- given
  (htarget : e ∈ rlc_connectorEdges gamma gamma')
  (hcase : RlcConnectorPIMSSourceOpenCase gamma gamma' tau e) :
-- imply
  rlc_connectorPIMSReflectedConfig gamma gamma' tau (rlc_connectorEdgeLift gamma gamma' e htarget) = true := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSReflectedConfig_open_of_sourceOpenCase gamma gamma' tau e htarget hcase

/--
[rlc_connectorPIMSSupportedArc_of_boundaryArc_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSSupportedArc_of_boundaryArc_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hno : tau ∉ rlc_finiteConnectorEvent gamma gamma')
  (harc : RlcConnectorPIMSBoundaryArc gamma gamma' tau) :
-- imply
  RlcConnectorPIMSSupportedArc gamma gamma' tau := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSSupportedArc_of_boundaryArc_of_failure gamma gamma' tau hno harc

/--
[rlc_connectorPIMSActualSelectedArc_of_boundaryArc_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSActualSelectedArc_of_boundaryArc_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hno : tau ∉ rlc_finiteConnectorEvent gamma gamma')
  (harc : RlcConnectorPIMSBoundaryArc gamma gamma' tau) :
-- imply
  RlcConnectorPIMSActualSelectedArc gamma gamma' tau := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSActualSelectedArc_of_boundaryArc_of_failure gamma gamma' tau hno harc

/--
[rlc_connectorPIMSSupportedArc_of_actualSelectedArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSSupportedArc_of_actualSelectedArc_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (harc : RlcConnectorPIMSActualSelectedArc gamma gamma' tau) :
-- imply
  RlcConnectorPIMSSupportedArc gamma gamma' tau := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSSupportedArc_of_actualSelectedArc gamma gamma' tau harc

/--
[rlc_connectorPIMS_openWalk_of_maskedDual_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMS_openWalk_of_maskedDual_walk_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {x y : Site 2}
  {c : (openSubgraph 2 (rlc_dualReflectConfig (rlc_maskConfig (rlc_connectorEdges gamma gamma') (rlc_connectorAmbientMixedConfig gamma gamma' tau)))).Walk x y}
-- given
  (hsupport : ∀ z ∈ c.support, z ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2)))
  (htarget : ∀ e ∈ c.edges, e ∈ rlc_connectorEdges gamma gamma')
  (hnotTrace : ∀ e ∈ c.edges, rlc_pimsEdgeEquiv e ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
-- imply
  Nonempty ((FK.openSub (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorPIMSReflectedConfig gamma gamma' tau)).Walk ⟨x, hsupport x c.start_mem_support⟩ ⟨y, hsupport y c.end_mem_support⟩) := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMS_openWalk_of_maskedDual_walk gamma gamma' tau c hsupport htarget hnotTrace

/--
[rlc_connectorPIMSReflectedConfig_mem_event_of_supportedArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSReflectedConfig_mem_event_of_supportedArc_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (harc : RlcConnectorPIMSSupportedArc gamma gamma' tau) :
-- imply
  rlc_connectorPIMSReflectedConfig gamma gamma' tau ∈ rlc_finiteConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSReflectedConfig_mem_event_of_supportedArc gamma gamma' tau harc

/--
[rlc_connectorPIMSReflectedConfig_mem_event_of_actualSelectedArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSReflectedConfig_mem_event_of_actualSelectedArc_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (harc : RlcConnectorPIMSActualSelectedArc gamma gamma' tau) :
-- imply
  rlc_connectorPIMSReflectedConfig gamma gamma' tau ∈ rlc_finiteConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSReflectedConfig_mem_event_of_actualSelectedArc gamma gamma' tau harc

/--
[rlc_traceSplitCounterexample_PIMS_actualSelectedArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_traceSplitCounterexample_PIMS_actualSelectedArc_eq :
-- imply
  RlcConnectorPIMSActualSelectedArc rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft rlc_traceSplitCounterexampleFiniteAllClosed := by
-- proof
  apply StatMech.Universality.rlc_traceSplitCounterexample_PIMS_actualSelectedArc

/--
[rlc_traceSplitCounterexample_PIMS_firstEdge_source_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_traceSplitCounterexample_PIMS_firstEdge_source_exterior_eq :
-- imply
  let e := s((![0, -1] : Site 2), ![0, 0]) rlc_pimsEdgeEquiv e ∉ rlc_connectorEdges rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft ∧ rlc_pimsEdgeEquiv e ∉ rlc_pathEdges rlc_traceSplitCounterexampleRight.1 ∪ rlc_pathEdges rlc_traceSplitCounterexampleLeft.1 := by
-- proof
  apply StatMech.Universality.rlc_traceSplitCounterexample_PIMS_firstEdge_source_exterior

/--
[rlc_traceSplitCounterexample_PIMS_success_via_boundaryArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_traceSplitCounterexample_PIMS_success_via_boundaryArc_eq :
-- imply
  rlc_connectorPIMSReflectedConfig rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft rlc_traceSplitCounterexampleFiniteAllClosed ∈ rlc_finiteConnectorEvent rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
-- proof
  apply StatMech.Universality.rlc_traceSplitCounterexample_PIMS_success_via_boundaryArc

/--
[rlc_connectorPIMSReflectedConfig_mem_event_of_filledBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSReflectedConfig_mem_event_of_filledBoundary_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hno : tau ∉ rlc_finiteConnectorEvent gamma gamma')
  (hcontacts : RlcConnectorPIMSFilledBoundaryContacts gamma gamma' tau)
  (htarget : RlcConnectorPIMSFilledBoundaryTargetSupported gamma gamma' tau) :
-- imply
  rlc_connectorPIMSReflectedConfig gamma gamma' tau ∈ rlc_finiteConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSReflectedConfig_mem_event_of_filledBoundary gamma gamma' tau hno hcontacts htarget

/--
[rlc_finiteConnectorEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_finiteConnectorEvent_isIncreasing_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  IsIncreasing (rlc_finiteConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteConnectorEvent_isIncreasing gamma gamma'

/--
[rlc_connectorPIMSVariableExteriorEvent_iff_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSVariableExteriorEvent_iff_wired_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  rho ∈ rlc_connectorPIMSVariableExteriorEvent gamma gamma' ↔ rho ∈ rlc_connectorPIMSVariableWiredEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSVariableExteriorEvent_iff_wired gamma gamma' rho

/--
[rlc_connectorPIMSVariableExteriorEvent_iff_assemble](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSVariableExteriorEvent_iff_assemble_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  rho ∈ rlc_connectorPIMSVariableExteriorEvent gamma gamma' ↔ rlc_connectorPIMSAssembleConfig gamma gamma' rho ∈ rlc_finiteConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSVariableExteriorEvent_iff_assemble gamma gamma' rho

/--
[rlc_PIMS_mem_finiteConnectorEvent_iff_variableExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_PIMS_mem_finiteConnectorEvent_iff_variableExterior_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  rlc_connectorPIMSReflectedConfig gamma gamma' tau ∈ rlc_finiteConnectorEvent gamma gamma' ↔ rlc_connectorPIMSReflectedConfig gamma gamma' tau ∈ rlc_connectorPIMSVariableExteriorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_PIMS_mem_finiteConnectorEvent_iff_variableExterior gamma gamma' tau

/--
[rlc_connectorPIMSVariableExteriorEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSVariableExteriorEvent_isIncreasing_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  IsIncreasing (rlc_connectorPIMSVariableExteriorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSVariableExteriorEvent_isIncreasing gamma gamma'

/--
[rlc_connectorPIMSVariableWiredEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSVariableWiredEvent_isIncreasing_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  IsIncreasing (rlc_connectorPIMSVariableWiredEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSVariableWiredEvent_isIncreasing gamma gamma'

/--
[rlc_connectorPIMSReflectedConfig_mem_event_of_reflectedDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSReflectedConfig_mem_event_of_reflectedDual_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hdual : rlc_connectorReflectedDualConfig gamma gamma' tau ∈ rlc_finiteConnectorEvent gamma gamma') :
-- imply
  rlc_connectorPIMSReflectedConfig gamma gamma' tau ∈ rlc_finiteConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSReflectedConfig_mem_event_of_reflectedDual gamma gamma' tau hdual

/--
[rlc_connectorForcedDualEventMass_reflected_le_PIMS](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorForcedDualEventMass_reflected_le_PIMS_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  rlc_connectorForcedDualEventMass gamma gamma' p q (rlc_connectorReflectedDualConfig gamma gamma' ⁻¹' rlc_finiteConnectorEvent gamma gamma') <= rlc_connectorForcedDualEventMass gamma gamma' p q (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹' rlc_finiteConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorForcedDualEventMass_reflected_le_PIMS gamma gamma' hp hp1 hq

/--
[rlc_connectorPIMSCollaredReflectedConfig_mem_event_of_reflectedDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSCollaredReflectedConfig_mem_event_of_reflectedDual_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hdual : rlc_connectorReflectedDualConfig gamma gamma' tau ∈ rlc_finiteConnectorEvent gamma gamma') :
-- imply
  rlc_connectorPIMSCollaredReflectedConfig gamma gamma' tau ∈ rlc_finiteConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSCollaredReflectedConfig_mem_event_of_reflectedDual gamma gamma' tau hdual

/--
[rlc_connectorForcedDualEventMass_reflected_le_PIMSCollared](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorForcedDualEventMass_reflected_le_PIMSCollared_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  rlc_connectorForcedDualEventMass gamma gamma' p q (rlc_connectorReflectedDualConfig gamma gamma' ⁻¹' rlc_finiteConnectorEvent gamma gamma') <= rlc_connectorForcedDualEventMass gamma gamma' p q (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' ⁻¹' rlc_finiteConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorForcedDualEventMass_reflected_le_PIMSCollared gamma gamma' hp hp1 hq

/--
[rlc_connectorPIMS_pushforward_le_merged_of_inducedWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMS_pushforward_le_merged_of_inducedWiring_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  {C : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel C.Adj]
-- given
  (hq : 1 <= q)
  (hC : C <= rlc_connectorMergedWiring gamma gamma')
  (hpush : rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹' rlc_finiteConnectorEvent gamma gamma') = FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') C (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma')) :
-- imply
  rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹' rlc_finiteConnectorEvent gamma gamma') <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMS_pushforward_le_merged_of_inducedWiring gamma gamma' hq C hC hpush

/--
[rlc_connectorPIMS_pushforward_le_merged_of_inducedMixture](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMS_pushforward_le_merged_of_inducedMixture_eq
  {n : Int}
  [Fintype I]
  [DecidableEq I]
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  {w : I → Real}
  {C : I → SimpleGraph (RlcConnectorVertex n)}
  [∀ i, DecidableRel (C i).Adj]
-- given
  (hq : 1 <= q)
  (hw : ∀ i, 0 <= w i)
  (hwSum : ∑ i, w i = 1)
  (hC : ∀ i, C i <= rlc_connectorMergedWiring gamma gamma')
  (hpush : rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹' rlc_finiteConnectorEvent gamma gamma') = ∑ i, w i * FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (C i) (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma')) :
-- imply
  rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹' rlc_finiteConnectorEvent gamma gamma') <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMS_pushforward_le_merged_of_inducedMixture gamma gamma' hq w C hw hwSum hC hpush

/--
[rlc_connectorPIMS_pushforward_le_merged_of_weightedMixture](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMS_pushforward_le_merged_of_weightedMixture_eq
  {n : Int}
  [Fintype I]
  [DecidableEq I]
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  {w : I → Real}
  {C : I → SimpleGraph (RlcConnectorVertex n)}
  [∀ i, DecidableRel (C i).Adj]
  {pf : I → Sym2 (RlcConnectorVertex n) → Real}
-- given
  (hq : 1 <= q)
  (hw : ∀ i, 0 <= w i)
  (hwSum : ∑ i, w i = 1)
  (hC : ∀ i, C i <= rlc_connectorMergedWiring gamma gamma')
  (hpf0 : ∀ i e, 0 <= pf i e)
  (hpf1 : ∀ i e, pf i e < 1)
  (hpfle : ∀ i e, pf i e <= BeffaraDC.selfDualPoint q)
  (hpush : rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹' rlc_finiteConnectorEvent gamma gamma') = ∑ i, w i * (∑ omega, (rlc_finiteConnectorEvent gamma gamma').indicator (fun _ => (1 : Real)) omega * FK.bcProbW (rlc_connectorFiniteGraph gamma gamma') (C i) (pf i) q omega)) :
-- imply
  rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹' rlc_finiteConnectorEvent gamma gamma') <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMS_pushforward_le_merged_of_weightedMixture gamma gamma' hq w C pf hw hwSum hC hpf0 hpf1 hpfle hpush

/--
[rlc_connectorPIMSCollared_pushforward_le_merged_of_weightedMixture](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSCollared_pushforward_le_merged_of_weightedMixture_eq
  {n : Int}
  [Fintype I]
  [DecidableEq I]
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  {w : I → Real}
  {C : I → SimpleGraph (RlcConnectorVertex n)}
  [∀ i, DecidableRel (C i).Adj]
-- given
  (hq : 1 <= q)
  (hw : ∀ i, 0 <= w i)
  (hwSum : ∑ i, w i = 1)
  (hC : ∀ i, C i <= rlc_connectorMergedWiring gamma gamma')
  (hpush : rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' ⁻¹' rlc_finiteConnectorEvent gamma gamma') = ∑ i, w i * (∑ omega, (rlc_finiteConnectorEvent gamma gamma').indicator (fun _ => (1 : Real)) omega * FK.bcProbW (rlc_connectorFiniteGraph gamma gamma') (C i) (rlc_connectorPIMSCollaredParameter gamma gamma' (BeffaraDC.selfDualPoint q)) q omega)) :
-- imply
  rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' ⁻¹' rlc_finiteConnectorEvent gamma gamma') <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSCollared_pushforward_le_merged_of_weightedMixture gamma gamma' hq w C hw hwSum hC hpush

/--
[rlc_connectorPIMSCollared_pushforward_le_merged_of_componentMixture](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSCollared_pushforward_le_merged_of_componentMixture_eq
  {n : Int}
  [Fintype I]
  [DecidableEq I]
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  {w : I → Real}
  {tauExt : I → ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hq : 1 <= q)
  (hw : ∀ i, 0 <= w i)
  (hwSum : ∑ i, w i = 1)
  (hpush : rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' ⁻¹' rlc_finiteConnectorEvent gamma gamma') = ∑ i, w i * (∑ omega, (rlc_finiteConnectorEvent gamma gamma').indicator (fun _ => (1 : Real)) omega * FK.bcProbW (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorComponentWiring (rlc_connectorPIMSCollaredExteriorOpenGraph gamma gamma' (tauExt i))) (rlc_connectorPIMSCollaredParameter gamma gamma' (BeffaraDC.selfDualPoint q)) q omega)) :
-- imply
  rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' ⁻¹' rlc_finiteConnectorEvent gamma gamma') <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSCollared_pushforward_le_merged_of_componentMixture gamma gamma' hq w tauExt hw hwSum hpush

/--
[rlc_finiteConnectorEvent_iff_traceAnchors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_finiteConnectorEvent_iff_traceAnchors_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  tau ∈ rlc_finiteConnectorEvent gamma gamma' ↔ (FK.openSub (rlc_connectorFiniteGraph gamma gamma') tau ⊔ rlc_connectorTraceWiring gamma gamma').Reachable (rlc_connectorRightAnchor gamma) (rlc_connectorLeftAnchor gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteConnectorEvent_iff_traceAnchors gamma gamma' tau

/--
[rlc_connectorPIMSVariableExteriorEvent_iff_variable_of_exterior_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSVariableExteriorEvent_iff_variable_of_exterior_le_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hext : rlc_connectorPIMSExteriorGraph gamma gamma' ≤ rlc_connectorSeparateWiring gamma gamma') :
-- imply
  rho ∈ rlc_connectorPIMSVariableExteriorEvent gamma gamma' ↔ rlc_connectorPIMSVariableConfig gamma gamma' rho ∈ rlc_finiteConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSVariableExteriorEvent_iff_variable_of_exterior_le gamma gamma' rho hext

/--
[rlc_connectorPIMSVariableExteriorEvent_iff_variable_of_wiring_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSVariableExteriorEvent_iff_variable_of_wiring_le_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hwire : rlc_connectorPIMSExteriorWiring gamma gamma' ≤ rlc_connectorSeparateWiring gamma gamma') :
-- imply
  rho ∈ rlc_connectorPIMSVariableExteriorEvent gamma gamma' ↔ rlc_connectorPIMSVariableConfig gamma gamma' rho ∈ rlc_finiteConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSVariableExteriorEvent_iff_variable_of_wiring_le gamma gamma' rho hwire

/--
[rlc_connectorPIMSVariableExteriorEvent_iff_variable_of_traceLocal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorPIMSVariableExteriorEvent_iff_variable_of_traceLocal_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hlocal : RlcConnectorPIMSExteriorTraceLocal gamma gamma') :
-- imply
  rho ∈ rlc_connectorPIMSVariableExteriorEvent gamma gamma' ↔ rlc_connectorPIMSVariableConfig gamma gamma' rho ∈ rlc_finiteConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorPIMSVariableExteriorEvent_iff_variable_of_traceLocal gamma gamma' rho hlocal

/--
[rlc_PIMS_mem_finiteConnectorEvent_iff_variable_of_traceLocal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_PIMS_mem_finiteConnectorEvent_iff_variable_of_traceLocal_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hlocal : RlcConnectorPIMSExteriorTraceLocal gamma gamma') :
-- imply
  rlc_connectorPIMSReflectedConfig gamma gamma' tau ∈ rlc_finiteConnectorEvent gamma gamma' ↔ rlc_connectorPIMSVariableConfig gamma gamma' (rlc_connectorPIMSReflectedConfig gamma gamma' tau) ∈ rlc_finiteConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_PIMS_mem_finiteConnectorEvent_iff_variable_of_traceLocal gamma gamma' tau hlocal

/--
[rlc_PIMS_mem_finiteConnectorEvent_iff_variable_of_extremalSelection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_PIMS_mem_finiteConnectorEvent_iff_variable_of_extremalSelection_eq
  {n : Int}
  {pair : RlcDiagonalPathPair n}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hselection : RlcConnectorPIMSExtremalSelectionExteriorLocality n)
  (hpair : omega ∈ rlc_extremalPairCandidate pair) :
-- imply
  rlc_connectorPIMSReflectedConfig pair.1 pair.2 tau ∈ rlc_finiteConnectorEvent pair.1 pair.2 ↔ rlc_connectorPIMSVariableConfig pair.1 pair.2 (rlc_connectorPIMSReflectedConfig pair.1 pair.2 tau) ∈ rlc_finiteConnectorEvent pair.1 pair.2 := by
-- proof
  apply StatMech.Universality.rlc_PIMS_mem_finiteConnectorEvent_iff_variable_of_extremalSelection hselection pair hpair tau

/--
[rlc_finiteConnectorEvent_iff_augmented_forceTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_finiteConnectorEvent_iff_augmented_forceTrace_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  tau ∈ rlc_finiteConnectorEvent gamma gamma' ↔ (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G (rlc_connectorForceTraceConfig gamma gamma' tau)).Reachable (rlc_connectorRightAnchor gamma) (rlc_connectorLeftAnchor gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteConnectorEvent_iff_augmented_forceTrace gamma gamma' tau

/--
[rlc_finiteConnectorMass_ge_one_div_one_add_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_finiteConnectorMass_ge_one_div_one_add_q_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hdual : FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') p q (rlc_finiteConnectorEvent gamma gamma')ᶜ <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') p q (rlc_finiteConnectorEvent gamma gamma')) :
-- imply
  1 / (1 + q) <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') p q (rlc_finiteConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteConnectorMass_ge_one_div_one_add_q gamma gamma' hp hp1 hq hdual

/--
[rlc_finiteConnectorMass_selfDual_ge_one_div_one_add_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_finiteConnectorMass_selfDual_ge_one_div_one_add_q_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
-- given
  (hq : 1 <= q)
  (hdual : rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma')ᶜ <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma')) :
-- imply
  1 / (1 + q) <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteConnectorMass_selfDual_ge_one_div_one_add_q gamma gamma' hq hdual

/--
[rlc_finiteConnectorMass_selfDual_ge_of_reflected_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_finiteConnectorMass_selfDual_ge_of_reflected_equiv_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  {D : ConfigSpace (Sym2 (RlcConnectorVertex n)) ≃ ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hq : 1 <= q)
  (hfailure : ∀ tau, tau ∉ rlc_finiteConnectorEvent gamma gamma' → D tau ∈ rlc_finiteConnectorEvent gamma gamma')
  (hprob : ∀ tau, rlc_connectorForcedDualProb gamma gamma' (BeffaraDC.selfDualPoint q) q tau <= FK.bcProb (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (D tau)) :
-- imply
  1 / (1 + q) <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteConnectorMass_selfDual_ge_of_reflected_equiv gamma gamma' hq D hfailure hprob

/--
[rlc_finiteConnectorMass_selfDual_ge_of_reflected_map_domination](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_finiteConnectorMass_selfDual_ge_of_reflected_map_domination_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  {F : ConfigSpace (Sym2 (RlcConnectorVertex n)) → ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hq : 1 <= q)
  (hfailure : ∀ tau, tau ∉ rlc_finiteConnectorEvent gamma gamma' → F tau ∈ rlc_finiteConnectorEvent gamma gamma')
  (hdom : rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (F ⁻¹' rlc_finiteConnectorEvent gamma gamma') <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma')) :
-- imply
  1 / (1 + q) <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteConnectorMass_selfDual_ge_of_reflected_map_domination gamma gamma' hq F hfailure hdom

/--
[rlc_finiteConnectorMass_selfDual_ge_of_reflectedDual_domination](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_finiteConnectorMass_selfDual_ge_of_reflectedDual_domination_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
-- given
  (hq : 1 <= q)
  (hfailure : ∀ tau, tau ∉ rlc_finiteConnectorEvent gamma gamma' → rlc_connectorReflectedDualConfig gamma gamma' tau ∈ rlc_finiteConnectorEvent gamma gamma')
  (hdom : rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_connectorReflectedDualConfig gamma gamma' ⁻¹' rlc_finiteConnectorEvent gamma gamma') <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma')) :
-- imply
  1 / (1 + q) <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteConnectorMass_selfDual_ge_of_reflectedDual_domination gamma gamma' hq hfailure hdom

/--
[rlc_finiteConnectorMass_selfDual_ge_of_PIMSReflected_domination](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_finiteConnectorMass_selfDual_ge_of_PIMSReflected_domination_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
-- given
  (hq : 1 <= q)
  (hfailure : ∀ tau, tau ∉ rlc_finiteConnectorEvent gamma gamma' → rlc_connectorPIMSReflectedConfig gamma gamma' tau ∈ rlc_finiteConnectorEvent gamma gamma')
  (hdom : rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹' rlc_finiteConnectorEvent gamma gamma') <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma')) :
-- imply
  1 / (1 + q) <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteConnectorMass_selfDual_ge_of_PIMSReflected_domination gamma gamma' hq hfailure hdom

/--
[rlc_finiteConnectorMass_selfDual_ge_of_PIMSArc_domination](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_finiteConnectorMass_selfDual_ge_of_PIMSArc_domination_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
-- given
  (hq : 1 <= q)
  (harc : ∀ tau, tau ∉ rlc_finiteConnectorEvent gamma gamma' → RlcConnectorPIMSSupportedArc gamma gamma' tau)
  (hdom : rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹' rlc_finiteConnectorEvent gamma gamma') <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma')) :
-- imply
  1 / (1 + q) <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteConnectorMass_selfDual_ge_of_PIMSArc_domination gamma gamma' hq harc hdom

/--
[rlc_finiteConnectorMass_selfDual_ge_of_PIMSActualSelectedArc_domination](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_finiteConnectorMass_selfDual_ge_of_PIMSActualSelectedArc_domination_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
-- given
  (hq : 1 <= q)
  (harc : ∀ tau, tau ∉ rlc_finiteConnectorEvent gamma gamma' → RlcConnectorPIMSActualSelectedArc gamma gamma' tau)
  (hdom : rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹' rlc_finiteConnectorEvent gamma gamma') <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma')) :
-- imply
  1 / (1 + q) <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteConnectorMass_selfDual_ge_of_PIMSActualSelectedArc_domination gamma gamma' hq harc hdom

/--
[rlc_finiteConnectorMass_selfDual_ge_of_PIMSBoundaryArc_domination](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_finiteConnectorMass_selfDual_ge_of_PIMSBoundaryArc_domination_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
-- given
  (hq : 1 <= q)
  (harc : ∀ tau, tau ∉ rlc_finiteConnectorEvent gamma gamma' → RlcConnectorPIMSBoundaryArc gamma gamma' tau)
  (hdom : rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹' rlc_finiteConnectorEvent gamma gamma') <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma')) :
-- imply
  1 / (1 + q) <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteConnectorMass_selfDual_ge_of_PIMSBoundaryArc_domination gamma gamma' hq harc hdom

/--
[rlc_finiteConnectorMass_selfDual_ge_of_PIMSBoundaryArc_inducedWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_finiteConnectorMass_selfDual_ge_of_PIMSBoundaryArc_inducedWiring_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  {C : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel C.Adj]
-- given
  (hq : 1 <= q)
  (hC : C <= rlc_connectorMergedWiring gamma gamma')
  (hpush : rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹' rlc_finiteConnectorEvent gamma gamma') = FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') C (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma'))
  (harc : ∀ tau, tau ∉ rlc_finiteConnectorEvent gamma gamma' → RlcConnectorPIMSBoundaryArc gamma gamma' tau) :
-- imply
  1 / (1 + q) <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteConnectorMass_selfDual_ge_of_PIMSBoundaryArc_inducedWiring gamma gamma' hq C hC hpush harc

/--
[rlc_finiteConnectorMass_selfDual_ge_of_PIMSBoundaryArc_inducedMixture](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_finiteConnectorMass_selfDual_ge_of_PIMSBoundaryArc_inducedMixture_eq
  {n : Int}
  [Fintype I]
  [DecidableEq I]
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  {w : I → Real}
  {C : I → SimpleGraph (RlcConnectorVertex n)}
  [∀ i, DecidableRel (C i).Adj]
-- given
  (hq : 1 <= q)
  (hw : ∀ i, 0 <= w i)
  (hwSum : ∑ i, w i = 1)
  (hC : ∀ i, C i <= rlc_connectorMergedWiring gamma gamma')
  (hpush : rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹' rlc_finiteConnectorEvent gamma gamma') = ∑ i, w i * FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (C i) (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma'))
  (harc : ∀ tau, tau ∉ rlc_finiteConnectorEvent gamma gamma' → RlcConnectorPIMSBoundaryArc gamma gamma' tau) :
-- imply
  1 / (1 + q) <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteConnectorMass_selfDual_ge_of_PIMSBoundaryArc_inducedMixture gamma gamma' hq w C hw hwSum hC hpush harc

/--
[rlc_finiteConnectorMass_selfDual_ge_of_PIMSFilledBoundary_inducedMixture](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_finiteConnectorMass_selfDual_ge_of_PIMSFilledBoundary_inducedMixture_eq
  {n : Int}
  [Fintype I]
  [DecidableEq I]
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  {w : I → Real}
  {C : I → SimpleGraph (RlcConnectorVertex n)}
  [∀ i, DecidableRel (C i).Adj]
-- given
  (hq : 1 <= q)
  (hw : ∀ i, 0 <= w i)
  (hwSum : ∑ i, w i = 1)
  (hC : ∀ i, C i <= rlc_connectorMergedWiring gamma gamma')
  (hpush : rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹' rlc_finiteConnectorEvent gamma gamma') = ∑ i, w i * FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (C i) (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma'))
  (hgeom : ∀ tau, tau ∉ rlc_finiteConnectorEvent gamma gamma' → RlcConnectorPIMSFilledBoundaryContacts gamma gamma' tau ∧ RlcConnectorPIMSFilledBoundaryTargetSupported gamma gamma' tau) :
-- imply
  1 / (1 + q) <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteConnectorMass_selfDual_ge_of_PIMSFilledBoundary_inducedMixture gamma gamma' hq w C hw hwSum hC hpush hgeom

/--
[rlc_finiteConnectorMass_selfDual_ge_of_PIMSCollared_componentMixture](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean)
-/
@[path]
private lemma rlc_finiteConnectorMass_selfDual_ge_of_PIMSCollared_componentMixture_eq
  {n : Int}
  [Fintype I]
  [DecidableEq I]
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  {w : I → Real}
  {tauExt : I → ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hq : 1 <= q)
  (hw : ∀ i, 0 <= w i)
  (hwSum : ∑ i, w i = 1)
  (hfailure : ∀ tau, tau ∉ rlc_finiteConnectorEvent gamma gamma' → rlc_connectorReflectedDualConfig gamma gamma' tau ∈ rlc_finiteConnectorEvent gamma gamma')
  (hpush : rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' ⁻¹' rlc_finiteConnectorEvent gamma gamma') = ∑ i, w i * (∑ omega, (rlc_finiteConnectorEvent gamma gamma').indicator (fun _ => (1 : Real)) omega * FK.bcProbW (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorComponentWiring (rlc_connectorPIMSCollaredExteriorOpenGraph gamma gamma' (tauExt i))) (rlc_connectorPIMSCollaredParameter gamma gamma' (BeffaraDC.selfDualPoint q)) q omega)) :
-- imply
  1 / (1 + q) <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteConnectorMass_selfDual_ge_of_PIMSCollared_componentMixture gamma gamma' hq w tauExt hw hwSum hfailure hpush


-- created on 2026-10-23
