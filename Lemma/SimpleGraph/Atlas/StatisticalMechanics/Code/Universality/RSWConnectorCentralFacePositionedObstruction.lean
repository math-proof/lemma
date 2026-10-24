import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.RSWConnectorCentralFacePositionedObstruction
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_axisReturnCounterexample_centralFaceRegion_eq_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFacePositionedObstruction.lean)
-/
@[path]
private lemma rlc_axisReturnCounterexample_centralFaceRegion_eq_singleton_eq :
-- imply
  rlc_connectorCentralFaceRegion rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft = {rlc_connectorCentralFace} := by
-- proof
  apply StatMech.Universality.rlc_axisReturnCounterexample_centralFaceRegion_eq_singleton

/--
[rlc_axisReturnCounterexample_source_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFacePositionedObstruction.lean)
-/
@[path]
private lemma rlc_axisReturnCounterexample_source_failure_eq :
-- imply
  rlc_axisReturnCounterexampleClosedConfig ∉ rlc_finiteCentralFaceRandomConnectorEvent rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft := by
-- proof
  apply StatMech.Universality.rlc_axisReturnCounterexample_source_failure

/--
[rlc_axisReturnCounterexample_PIMS_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFacePositionedObstruction.lean)
-/
@[path]
private lemma rlc_axisReturnCounterexample_PIMS_failure_eq :
-- imply
  rlc_connectorCentralFacePIMSConfig rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft rlc_axisReturnCounterexampleClosedConfig ∉ rlc_finiteCentralFaceClosureConnectorEvent rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft := by
-- proof
  apply StatMech.Universality.rlc_axisReturnCounterexample_PIMS_failure

/--
[rlc_axisReturnCounterexample_positioned_doubleFailure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFacePositionedObstruction.lean)
-/
@[path]
private lemma rlc_axisReturnCounterexample_positioned_doubleFailure_eq :
-- imply
  RlcBookPositionedTracePair rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft ∧ rlc_axisReturnCounterexampleClosedConfig ∉ rlc_finiteCentralFaceRandomConnectorEvent rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft ∧ rlc_connectorCentralFacePIMSConfig rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft rlc_axisReturnCounterexampleClosedConfig ∉ rlc_finiteCentralFaceClosureConnectorEvent rlc_traceSplitCounterexampleRight rlc_axisReturnCounterexampleLeft := by
-- proof
  apply StatMech.Universality.rlc_axisReturnCounterexample_positioned_doubleFailure


-- created on 2026-10-23
