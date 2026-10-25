import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorActualSelectedObstruction
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_scaleTwoDoubleFailure_origin_mem_leftPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorActualSelectedObstruction.lean)
-/
@[path]
private lemma rlc_scaleTwoDoubleFailure_origin_mem_leftPath_eq :
-- imply
  origin 2 ∈ rlc_pathVertices rlc_scaleTwoDoubleFailureLeft.1 := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoDoubleFailure_origin_mem_leftPath

/--
[rlc_scaleTwoDoubleFailure_origin_not_connectorAllowed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorActualSelectedObstruction.lean)
-/
@[path]
private lemma rlc_scaleTwoDoubleFailure_origin_not_connectorAllowed_eq :
-- imply
  origin 2 ∉ rlc_connectorAllowed rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoDoubleFailure_origin_not_connectorAllowed

/--
[rlc_scaleTwoDoubleFailure_originRegion_eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorActualSelectedObstruction.lean)
-/
@[path]
private lemma rlc_scaleTwoDoubleFailure_originRegion_eq_empty_eq :
-- imply
  rlc_connectorOriginRegion rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft = ∅ := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoDoubleFailure_originRegion_eq_empty

/--
[rlc_scaleTwoDoubleFailure_connectorEdges_eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorActualSelectedObstruction.lean)
-/
@[path]
private lemma rlc_scaleTwoDoubleFailure_connectorEdges_eq_empty_eq :
-- imply
  rlc_connectorEdges rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft = ∅ := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoDoubleFailure_connectorEdges_eq_empty

/--
[rlc_scaleTwoDoubleFailure_exposedPaths_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorActualSelectedObstruction.lean)
-/
@[path]
private lemma rlc_scaleTwoDoubleFailure_exposedPaths_disjoint_eq :
-- imply
  Disjoint (rlc_pathVertices rlc_scaleTwoDoubleFailureRight.1) (rlc_pathVertices rlc_scaleTwoDoubleFailureLeft.1) := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoDoubleFailure_exposedPaths_disjoint

/--
[rlc_scaleTwoDoubleFailure_finiteConnector_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorActualSelectedObstruction.lean)
-/
@[path]
private lemma rlc_scaleTwoDoubleFailure_finiteConnector_failure_eq
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex 2))} :
-- imply
  tau ∉ rlc_finiteConnectorEvent rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoDoubleFailure_finiteConnector_failure tau

/--
[rlc_scaleTwoDoubleFailure_PIMS_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorActualSelectedObstruction.lean)
-/
@[path]
private lemma rlc_scaleTwoDoubleFailure_PIMS_failure_eq
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex 2))} :
-- imply
  rlc_connectorPIMSReflectedConfig rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft tau ∉ rlc_finiteConnectorEvent rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoDoubleFailure_PIMS_failure tau

/--
[rlc_scaleTwoDoubleFailure_not_actualSelectedArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorActualSelectedObstruction.lean)
-/
@[path]
private lemma rlc_scaleTwoDoubleFailure_not_actualSelectedArc_eq
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex 2))} :
-- imply
  ¬ RlcConnectorPIMSActualSelectedArc rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft tau := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoDoubleFailure_not_actualSelectedArc tau

/--
[rlc_failure_not_imply_actualSelectedArc_scaleTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorActualSelectedObstruction.lean)
-/
@[path]
private lemma rlc_failure_not_imply_actualSelectedArc_scaleTwo_eq :
-- imply
  ¬ (∀ tau : ConfigSpace (Sym2 (RlcConnectorVertex 2)), tau ∉ rlc_finiteConnectorEvent rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft → RlcConnectorPIMSActualSelectedArc rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft tau) := by
-- proof
  apply StatMech.Universality.rlc_failure_not_imply_actualSelectedArc_scaleTwo


-- created on 2026-10-23
