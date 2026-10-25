import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededOrdinaryAmbient.Part2
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_axisGapAmbientMixedConfig_supportEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededOrdinaryAmbient.lean)
-/
@[path]
private lemma rlc_axisGapAmbientMixedConfig_supportEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ rlc_axisGapEdges G) :
-- imply
  rlc_axisGapAmbientMixedConfig G tau e = tau (rlc_axisGapEdgeLift G e he) := by
-- proof
  apply StatMech.Universality.rlc_axisGapAmbientMixedConfig_supportEdge G tau he

/--
[rlc_axisGapAmbientMixedConfig_traceEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededOrdinaryAmbient.lean)
-/
@[path]
private lemma rlc_axisGapAmbientMixedConfig_traceEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (Site 2)}
-- given
  (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1))
  (he : e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
-- imply
  rlc_axisGapAmbientMixedConfig G tau e = true := by
-- proof
  apply StatMech.Universality.rlc_axisGapAmbientMixedConfig_traceEdge G tau hdisj he

/--
[rlc_axisGapAmbientMixedConfig_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededOrdinaryAmbient.lean)
-/
@[path]
private lemma rlc_axisGapAmbientMixedConfig_exterior_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (Site 2)}
-- given
  (hG : e ∉ rlc_axisGapEdges G)
  (htrace : e ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
-- imply
  rlc_axisGapAmbientMixedConfig G tau e = false := by
-- proof
  apply StatMech.Universality.rlc_axisGapAmbientMixedConfig_exterior G tau hG htrace

/--
[rlc_axisGapPIMSMixedReflectedConfig_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededOrdinaryAmbient.lean)
-/
@[path]
private lemma rlc_axisGapPIMSMixedReflectedConfig_apply_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (RlcConnectorVertex n)} :
-- imply
  rlc_axisGapPIMSMixedReflectedConfig G tau e = !(rlc_axisGapAmbientMixedConfig G tau (rlc_pimsEdgeEquiv (e.map Subtype.val))) := by
-- proof
  apply StatMech.Universality.rlc_axisGapPIMSMixedReflectedConfig_apply G tau e

/--
[rlc_axisGap_seed_mem_allowed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededOrdinaryAmbient.lean)
-/
@[path]
private lemma rlc_axisGap_seed_mem_allowed_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper) :
-- imply
  G.seedVertex ∈ rlc_connectorAllowed gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_axisGap_seed_mem_allowed G hn hlt

/--
[rlc_axisGap_seed_not_mem_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededOrdinaryAmbient.lean)
-/
@[path]
private lemma rlc_axisGap_seed_not_mem_barrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper) :
-- imply
  G.seedVertex ∉ rlc_connectorBarrier gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_axisGap_seed_not_mem_barrier G hn hlt

/--
[rlc_axisGapEdges_ne_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededOrdinaryAmbient.lean)
-/
@[path]
private lemma rlc_axisGapEdges_ne_empty_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'} :
-- imply
  rlc_axisGapEdges G ≠ ∅ := by
-- proof
  apply StatMech.Universality.rlc_axisGapEdges_ne_empty G

/--
[rlc_axisGapFiniteGraph_ne_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededOrdinaryAmbient.lean)
-/
@[path]
private lemma rlc_axisGapFiniteGraph_ne_bot_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'} :
-- imply
  rlc_axisGapFiniteGraph G ≠ ⊥ := by
-- proof
  apply StatMech.Universality.rlc_axisGapFiniteGraph_ne_bot G

/--
[rlc_axisGapAmbientMixedConfig_eq_connectorAmbient_of_origin_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededOrdinaryAmbient.lean)
-/
@[path]
private lemma rlc_axisGapAmbientMixedConfig_eq_connectorAmbient_of_origin_mem_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (ho : origin 2 ∈ rlc_axisGapRegionSet G) :
-- imply
  rlc_axisGapAmbientMixedConfig G tau = rlc_connectorAmbientMixedConfig gamma gamma' tau := by
-- proof
  apply StatMech.Universality.rlc_axisGapAmbientMixedConfig_eq_connectorAmbient_of_origin_mem G ho tau

/--
[rlc_axisGapPIMSMixed_eq_connectorPIMS_of_origin_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededOrdinaryAmbient.lean)
-/
@[path]
private lemma rlc_axisGapPIMSMixed_eq_connectorPIMS_of_origin_mem_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (ho : origin 2 ∈ rlc_axisGapRegionSet G) :
-- imply
  rlc_axisGapPIMSMixedReflectedConfig G tau = rlc_connectorPIMSReflectedConfig gamma gamma' tau := by
-- proof
  apply StatMech.Universality.rlc_axisGapPIMSMixed_eq_connectorPIMS_of_origin_mem G ho tau

/--
[rlc_scaleTwo_seededOrdinary_graph_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededOrdinaryAmbient.lean)
-/
@[path]
private lemma rlc_scaleTwo_seededOrdinary_graph_nonempty_eq :
-- imply
  rlc_axisGapFiniteGraph rlc_scaleTwoDoubleFailureGap ≠ ⊥ := by
-- proof
  apply StatMech.Universality.rlc_scaleTwo_seededOrdinary_graph_nonempty

/--
[rlc_scaleOne_seededOrdinary_success_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededOrdinaryAmbient.lean)
-/
@[path]
private lemma rlc_scaleOne_seededOrdinary_success_nonempty_eq :
-- imply
  (rlc_axisGapPIMSMixedReflectedConfig rlc_windingSideCounterexampleGap ⁻¹' rlc_finiteAxisGapConnectorEvent rlc_windingSideCounterexampleGap).Nonempty := by
-- proof
  apply StatMech.Universality.rlc_scaleOne_seededOrdinary_success_nonempty


-- created on 2026-10-23
