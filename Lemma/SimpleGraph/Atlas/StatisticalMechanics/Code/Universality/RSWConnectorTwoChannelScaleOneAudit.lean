import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelScaleOneAudit
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_activeDoubleFailure_twoChannel_openSub_le_connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelScaleOneAudit.lean)
-/
@[path]
private lemma rlc_activeDoubleFailure_twoChannel_openSub_le_connector_eq :
-- imply
  FK.openSub (rlc_connectorTwoChannelGraph rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft) rlc_activeGapDoubleFailureConfig ≤ FK.openSub (rlc_connectorFiniteGraph rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft) rlc_activeGapDoubleFailureConfig := by
-- proof
  apply StatMech.Universality.rlc_activeDoubleFailure_twoChannel_openSub_le_connector

/--
[rlc_activeDoubleFailure_twoChannel_source_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelScaleOneAudit.lean)
-/
@[path]
private lemma rlc_activeDoubleFailure_twoChannel_source_failure_eq :
-- imply
  rlc_activeGapDoubleFailureConfig ∉ rlc_finiteTwoChannelConnectorEvent rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
-- proof
  apply StatMech.Universality.rlc_activeDoubleFailure_twoChannel_source_failure

/--
[rlc_activeDoubleFailure_twoChannel_PIMS_success](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelScaleOneAudit.lean)
-/
@[path]
private lemma rlc_activeDoubleFailure_twoChannel_PIMS_success_eq :
-- imply
  rlc_connectorCentralFacePIMSConfig rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft rlc_activeGapDoubleFailureConfig ∈ rlc_finiteTwoChannelConnectorEvent rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
-- proof
  apply StatMech.Universality.rlc_activeDoubleFailure_twoChannel_PIMS_success

/--
[rlc_activeDoubleFailure_twoChannel_repaired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelScaleOneAudit.lean)
-/
@[path]
private lemma rlc_activeDoubleFailure_twoChannel_repaired_eq :
-- imply
  rlc_activeGapDoubleFailureConfig ∉ rlc_finiteTwoChannelConnectorEvent rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft ∧ rlc_connectorCentralFacePIMSConfig rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft rlc_activeGapDoubleFailureConfig ∈ rlc_finiteTwoChannelConnectorEvent rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
-- proof
  apply StatMech.Universality.rlc_activeDoubleFailure_twoChannel_repaired

/--
[rlc_activeDoubleFailure_twoChannel_singletonMass_le_mergedSuccess](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelScaleOneAudit.lean)
-/
@[path]
private lemma rlc_activeDoubleFailure_twoChannel_singletonMass_le_mergedSuccess_eq :
-- imply
  rlc_twoChannelForcedDualEventMass rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft (1 / 2) 1 {rlc_activeGapDoubleFailureConfig} ≤ FK.bcEventMass (rlc_connectorTwoChannelGraph rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft) (rlc_connectorMergedWiring rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft) (1 / 2) 1 (rlc_finiteTwoChannelConnectorEvent rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft) := by
-- proof
  apply StatMech.Universality.rlc_activeDoubleFailure_twoChannel_singletonMass_le_mergedSuccess


-- created on 2026-10-23
