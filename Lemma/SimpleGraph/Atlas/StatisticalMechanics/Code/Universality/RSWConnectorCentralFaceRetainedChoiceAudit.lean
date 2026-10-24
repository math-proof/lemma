import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceRetainedChoiceAudit
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_retainedChoiceAudit_right_vertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceRetainedChoiceAudit.lean)
-/
@[path]
private lemma rlc_retainedChoiceAudit_right_vertices_eq :
-- imply
  rlc_pathVertices rlc_retainedChoiceAuditRight.1 = {![0, -2], ![1, -2], ![2, -2], ![2, -1], ![2, 0], ![1, 0], ![1, 1], ![2, 1], ![3, 1], ![4, 1]} := by
-- proof
  apply StatMech.Universality.rlc_retainedChoiceAudit_right_vertices

/--
[rlc_retainedChoiceAudit_left_vertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceRetainedChoiceAudit.lean)
-/
@[path]
private lemma rlc_retainedChoiceAudit_left_vertices_eq :
-- imply
  rlc_pathVertices rlc_retainedChoiceAuditLeft.1 = {![-4, -2], ![-3, -2], ![-2, -2], ![-1, -2], ![-1, -1], ![-1, 0], ![-1, 1], ![-2, 1], ![-2, 2], ![-1, 2], ![0, 2]} := by
-- proof
  apply StatMech.Universality.rlc_retainedChoiceAudit_left_vertices

/--
[rlc_retainedChoiceAudit_right_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceRetainedChoiceAudit.lean)
-/
@[path]
private lemma rlc_retainedChoiceAudit_right_edges_eq :
-- imply
  rlc_pathEdges rlc_retainedChoiceAuditRight.1 = rlc_rca_rightEdges := by
-- proof
  apply StatMech.Universality.rlc_retainedChoiceAudit_right_edges

/--
[rlc_retainedChoiceAudit_left_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceRetainedChoiceAudit.lean)
-/
@[path]
private lemma rlc_retainedChoiceAudit_left_edges_eq :
-- imply
  rlc_pathEdges rlc_retainedChoiceAuditLeft.1 = rlc_rca_leftEdges := by
-- proof
  apply StatMech.Universality.rlc_retainedChoiceAudit_left_edges

/--
[rlc_retainedChoiceAudit_faithful](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceRetainedChoiceAudit.lean)
-/
@[path]
private lemma rlc_retainedChoiceAudit_faithful_eq :
-- imply
  RlcBookFaithfulTracePair rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft := by
-- proof
  apply StatMech.Universality.rlc_retainedChoiceAudit_faithful

/--
[rlc_retainedChoiceAuditConfig_eq_true_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceRetainedChoiceAudit.lean)
-/
@[path]
private lemma rlc_retainedChoiceAuditConfig_eq_true_iff_eq
  {e : Sym2 (RlcConnectorVertex 2)} :
-- imply
  rlc_retainedChoiceAuditConfig e = true ↔ e.map Subtype.val ∈ rlc_retainedChoiceAuditOpenEdges := by
-- proof
  apply StatMech.Universality.rlc_retainedChoiceAuditConfig_eq_true_iff e

/--
[rlc_retainedChoiceAudit_source_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceRetainedChoiceAudit.lean)
-/
@[path]
private lemma rlc_retainedChoiceAudit_source_failure_eq :
-- imply
  rlc_retainedChoiceAuditConfig ∉ rlc_finiteCentralFaceRandomConnectorEvent rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft := by
-- proof
  apply StatMech.Universality.rlc_retainedChoiceAudit_source_failure

/--
[rlc_retainedChoiceAudit_upperComponent_no_right_contact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceRetainedChoiceAudit.lean)
-/
@[path]
private lemma rlc_retainedChoiceAudit_upperComponent_no_right_contact_eq
  {z : Site 2}
-- given
  (hz : (rlc_connectorCentralFaceGoodBoundaryGraph rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft rlc_retainedChoiceAuditConfig).Reachable (![-1, 0] : Site 2) z) :
-- imply
  rlc_dualReflect z ∉ rlc_pathVertices rlc_retainedChoiceAuditRight.1 := by
-- proof
  apply StatMech.Universality.rlc_retainedChoiceAudit_upperComponent_no_right_contact hz

/--
[rlc_retainedChoiceAudit_topWall_endpoint_not_mem_filled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceRetainedChoiceAudit.lean)
-/
@[path]
private lemma rlc_retainedChoiceAudit_topWall_endpoint_not_mem_filled_eq :
-- imply
  (![-3, 2] : Site 2) ∉ rlc_connectorCentralFaceFilledReachSet rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft rlc_retainedChoiceAuditConfig := by
-- proof
  apply StatMech.Universality.rlc_retainedChoiceAudit_topWall_endpoint_not_mem_filled

/--
[rlc_retainedChoiceAudit_reflectedRight_endpoint_not_mem_filled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceRetainedChoiceAudit.lean)
-/
@[path]
private lemma rlc_retainedChoiceAudit_reflectedRight_endpoint_not_mem_filled_eq :
-- imply
  (![-2, -1] : Site 2) ∉ rlc_connectorCentralFaceFilledReachSet rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft rlc_retainedChoiceAuditConfig := by
-- proof
  apply StatMech.Universality.rlc_retainedChoiceAudit_reflectedRight_endpoint_not_mem_filled


-- created on 2026-10-23
