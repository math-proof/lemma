import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.RSWStoppedPathPIMSActiveObstruction
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_activeGap_sourceA_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedPathPIMSActiveObstruction.lean)
-/
@[path]
private lemma rlc_activeGap_sourceA_mem_eq :
-- imply
  s((![1, -1] : Site 2), ![1, 0]) ∈ rlc_axisGapEdges rlc_windingSideCounterexampleGap := by
-- proof
  apply StatMech.Universality.rlc_activeGap_sourceA_mem

/--
[rlc_activeGap_sourceB_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedPathPIMSActiveObstruction.lean)
-/
@[path]
private lemma rlc_activeGap_sourceB_mem_eq :
-- imply
  s((![0, 0] : Site 2), ![1, 0]) ∈ rlc_axisGapEdges rlc_windingSideCounterexampleGap := by
-- proof
  apply StatMech.Universality.rlc_activeGap_sourceB_mem

/--
[rlc_activeGap_sourceC_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedPathPIMSActiveObstruction.lean)
-/
@[path]
private lemma rlc_activeGap_sourceC_mem_eq :
-- imply
  s((![-1, 0] : Site 2), ![0, 0]) ∈ rlc_axisGapEdges rlc_windingSideCounterexampleGap := by
-- proof
  apply StatMech.Universality.rlc_activeGap_sourceC_mem

/--
[rlc_activeGapDoubleFailureConfig_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedPathPIMSActiveObstruction.lean)
-/
@[path]
private lemma rlc_activeGapDoubleFailureConfig_failure_eq :
-- imply
  rlc_activeGapDoubleFailureConfig ∉ rlc_finiteAxisGapConnectorEvent rlc_windingSideCounterexampleGap := by
-- proof
  apply StatMech.Universality.rlc_activeGapDoubleFailureConfig_failure

/--
[rlc_activeGapDoubleFailureConfig_PIMS_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedPathPIMSActiveObstruction.lean)
-/
@[path]
private lemma rlc_activeGapDoubleFailureConfig_PIMS_failure_eq :
-- imply
  rlc_axisGapPIMSReflectedConfig rlc_windingSideCounterexampleGap rlc_activeGapDoubleFailureConfig ∉ rlc_finiteAxisGapConnectorEvent rlc_windingSideCounterexampleGap := by
-- proof
  apply StatMech.Universality.rlc_activeGapDoubleFailureConfig_PIMS_failure

/--
[rlc_activeExtremalGap_doubleFailure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedPathPIMSActiveObstruction.lean)
-/
@[path]
private lemma rlc_activeExtremalGap_doubleFailure_eq :
-- imply
  (rlc_extremalPairCandidate (rlc_traceSplitCounterexampleRight, rlc_traceSplitCounterexampleLeft)).Nonempty ∧ rlc_activeGapDoubleFailureConfig ∉ rlc_finiteAxisGapConnectorEvent rlc_windingSideCounterexampleGap ∧ rlc_axisGapPIMSReflectedConfig rlc_windingSideCounterexampleGap rlc_activeGapDoubleFailureConfig ∉ rlc_finiteAxisGapConnectorEvent rlc_windingSideCounterexampleGap := by
-- proof
  apply StatMech.Universality.rlc_activeExtremalGap_doubleFailure

/--
[rlc_activeExtremalGap_not_stoppedProvenance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedPathPIMSActiveObstruction.lean)
-/
@[path]
private lemma rlc_activeExtremalGap_not_stoppedProvenance_eq :
-- imply
  ¬ Nonempty (RlcStoppedExtremalAxisGapProvenance rlc_windingSideCounterexampleGap (by norm_num) (by norm_num [rlc_windingSideCounterexampleGap])) := by
-- proof
  apply StatMech.Universality.rlc_activeExtremalGap_not_stoppedProvenance

/--
[not_rlc_extremalStrataCarryStoppedPIMSProvenance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedPathPIMSActiveObstruction.lean)
-/
@[path]
private lemma not_rlc_extremalStrataCarryStoppedPIMSProvenance_eq :
-- imply
  ¬ RlcExtremalStrataCarryStoppedPIMSProvenance 1 := by
-- proof
  apply StatMech.Universality.not_rlc_extremalStrataCarryStoppedPIMSProvenance


-- created on 2026-10-23
