import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorMassDualityScaleOneAudit
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_scaleOne_origin_mem_gapRegionSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorMassDualityScaleOneAudit.lean)
-/
@[path]
private lemma rlc_scaleOne_origin_mem_gapRegionSet_eq :
-- imply
  origin 2 ∈ rlc_axisGapRegionSet rlc_windingSideCounterexampleGap := by
-- proof
  apply StatMech.Universality.rlc_scaleOne_origin_mem_gapRegionSet

/--
[rlc_activeFullConnector_doubleFailure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorMassDualityScaleOneAudit.lean)
-/
@[path]
private lemma rlc_activeFullConnector_doubleFailure_eq :
-- imply
  rlc_activeGapDoubleFailureConfig ∉ rlc_finiteConnectorEvent rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft ∧ rlc_connectorPIMSReflectedConfig rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft rlc_activeGapDoubleFailureConfig ∉ rlc_finiteConnectorEvent rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
-- proof
  apply StatMech.Universality.rlc_activeFullConnector_doubleFailure

/--
[rlc_traceSplitCounterexample_PIMSCollared_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorMassDualityScaleOneAudit.lean)
-/
@[path]
private lemma rlc_traceSplitCounterexample_PIMSCollared_failure_eq
  {tau : ConfigSpace (Sym2 (RlcConnectorVertex 1))} :
-- imply
  rlc_connectorPIMSCollaredReflectedConfig rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft tau ∉ rlc_finiteConnectorEvent rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
-- proof
  apply StatMech.Universality.rlc_traceSplitCounterexample_PIMSCollared_failure tau

/--
[rlc_traceSplitCounterexample_PIMSCollared_preimage_eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorMassDualityScaleOneAudit.lean)
-/
@[path]
private lemma rlc_traceSplitCounterexample_PIMSCollared_preimage_eq_empty_eq :
-- imply
  rlc_connectorPIMSCollaredReflectedConfig rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft ⁻¹' rlc_finiteConnectorEvent rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft = ∅ := by
-- proof
  apply StatMech.Universality.rlc_traceSplitCounterexample_PIMSCollared_preimage_eq_empty

/--
[rlc_traceSplitCounterexample_not_PIMSCollaredFailureMassTransport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorMassDualityScaleOneAudit.lean)
-/
@[path]
private lemma rlc_traceSplitCounterexample_not_PIMSCollaredFailureMassTransport_eq
  {q : Real}
-- given
  (hq : 1 <= q) :
-- imply
  ¬ RlcConnectorPIMSCollaredFailureMassTransport rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft q := by
-- proof
  apply StatMech.Universality.rlc_traceSplitCounterexample_not_PIMSCollaredFailureMassTransport hq


-- created on 2026-10-23
