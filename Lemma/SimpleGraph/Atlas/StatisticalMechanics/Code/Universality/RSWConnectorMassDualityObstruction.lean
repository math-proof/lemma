import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorMassDualityObstruction
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_scaleTwoDoubleFailure_finiteConnectorEvent_eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorMassDualityObstruction.lean)
-/
@[path]
private lemma rlc_scaleTwoDoubleFailure_finiteConnectorEvent_eq_empty_eq :
-- imply
  rlc_finiteConnectorEvent rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft = ∅ := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoDoubleFailure_finiteConnectorEvent_eq_empty

/--
[rlc_scaleTwoDoubleFailure_not_PIMSFailureMassTransport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorMassDualityObstruction.lean)
-/
@[path]
private lemma rlc_scaleTwoDoubleFailure_not_PIMSFailureMassTransport_eq
  {q : Real}
-- given
  (hq : 1 <= q) :
-- imply
  ¬ RlcConnectorPIMSFailureMassTransport rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft q := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoDoubleFailure_not_PIMSFailureMassTransport hq

/--
[rlc_scaleTwoDoubleFailure_not_PIMSCollaredFailureMassTransport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorMassDualityObstruction.lean)
-/
@[path]
private lemma rlc_scaleTwoDoubleFailure_not_PIMSCollaredFailureMassTransport_eq
  {q : Real}
-- given
  (hq : 1 <= q) :
-- imply
  ¬ RlcConnectorPIMSCollaredFailureMassTransport rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft q := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoDoubleFailure_not_PIMSCollaredFailureMassTransport hq


-- created on 2026-10-23
