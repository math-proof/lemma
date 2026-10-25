import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFiniteGraph.Part5
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_connectorCentralFaceFiniteGraph_le_closureGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceFiniteGraph_le_closureGraph_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  rlc_connectorCentralFaceFiniteGraph gamma gamma' ≤ rlc_connectorCentralFaceClosureGraph gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceFiniteGraph_le_closureGraph gamma gamma'

/--
[rlc_exists_connector_iff_traceAnchors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFiniteGraph.lean)
-/
@[path]
private lemma rlc_exists_connector_iff_traceAnchors_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H : SimpleGraph (RlcConnectorVertex n)} :
-- imply
  (∃ x y : RlcConnectorVertex n, rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧ H.Reachable x y) ↔ (H ⊔ rlc_connectorTraceWiring gamma gamma').Reachable (rlc_connectorRightAnchor gamma) (rlc_connectorLeftAnchor gamma') := by
-- proof
  apply StatMech.Universality.rlc_exists_connector_iff_traceAnchors gamma gamma' H

/--
[rlc_connectorCentralFaceEdgeLift_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceEdgeLift_map_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ rlc_connectorCentralFaceEdges gamma gamma') :
-- imply
  (rlc_connectorCentralFaceEdgeLift e he).map Subtype.val = e := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceEdgeLift_map e he

/--
[rlc_connectorCentralFaceAmbientConfig_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceAmbientConfig_support_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ rlc_connectorCentralFaceEdges gamma gamma') :
-- imply
  rlc_connectorCentralFaceAmbientConfig gamma gamma' rho e = rho (rlc_connectorCentralFaceEdgeLift e he) := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceAmbientConfig_support gamma gamma' rho he

/--
[rlc_connectorCentralFaceAmbientConfig_trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceAmbientConfig_trace_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
-- imply
  rlc_connectorCentralFaceAmbientConfig gamma gamma' rho e = true := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceAmbientConfig_trace gamma gamma' rho he

/--
[rlc_connectorCentralFaceAmbientConfig_eq_false_of_lifts_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceAmbientConfig_eq_false_of_lifts_closed_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (Site 2)}
-- given
  (htrace : e ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1)
  (hclosed : ∀ f : Sym2 (RlcConnectorVertex n), f.map Subtype.val = e → rho f = false) :
-- imply
  rlc_connectorCentralFaceAmbientConfig gamma gamma' rho e = false := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceAmbientConfig_eq_false_of_lifts_closed gamma gamma' rho htrace hclosed

/--
[rlc_connectorCentralFacePIMSConfig_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFiniteGraph.lean)
-/
@[path]
private lemma rlc_connectorCentralFacePIMSConfig_apply_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (RlcConnectorVertex n)} :
-- imply
  rlc_connectorCentralFacePIMSConfig gamma gamma' rho e = !(rlc_connectorCentralFaceAmbientConfig gamma gamma' rho (rlc_pimsEdgeEquiv (e.map Subtype.val))) := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFacePIMSConfig_apply gamma gamma' rho e

/--
[rlc_openSub_centralFaceClosure_ambient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFiniteGraph.lean)
-/
@[path]
private lemma rlc_openSub_centralFaceClosure_ambient_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FK.openSub (rlc_connectorCentralFaceClosureGraph gamma gamma') (rlc_connectorRestrictConfig (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho)) = FK.openSub (rlc_connectorCentralFaceFiniteGraph gamma gamma') rho ⊔ rlc_connectorTraceWiring gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_openSub_centralFaceClosure_ambient gamma gamma' rho

/--
[rlc_mem_randomConnectorEvent_iff_ambientClosureConnectorEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFiniteGraph.lean)
-/
@[path]
private lemma rlc_mem_randomConnectorEvent_iff_ambientClosureConnectorEvent_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  rho ∈ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma' ↔ rlc_connectorRestrictConfig (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho) ∈ rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_mem_randomConnectorEvent_iff_ambientClosureConnectorEvent gamma gamma' rho


-- created on 2026-10-23
