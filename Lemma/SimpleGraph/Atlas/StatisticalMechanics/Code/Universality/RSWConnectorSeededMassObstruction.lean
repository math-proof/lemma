import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassObstruction
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_scaleTwoAxisGap_failureMass_q_one_eq_five_eighths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededMassObstruction.lean)
-/
@[path]
private lemma rlc_scaleTwoAxisGap_failureMass_q_one_eq_five_eighths_eq :
-- imply
  FK.bcEventMass (rlc_axisGapFiniteGraph rlc_scaleTwoDoubleFailureGap) (rlc_connectorSeparateWiring rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft) (BeffaraDC.selfDualPoint 1) 1 (rlc_finiteAxisGapConnectorEvent rlc_scaleTwoDoubleFailureGap)ᶜ = 5 / 8 := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoAxisGap_failureMass_q_one_eq_five_eighths

/--
[rlc_scaleTwoAxisGap_PIMSSourceSuccessMass_q_one_le_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededMassObstruction.lean)
-/
@[path]
private lemma rlc_scaleTwoAxisGap_PIMSSourceSuccessMass_q_one_le_half_eq :
-- imply
  rlc_axisGapPIMSSourceSuccessMass rlc_scaleTwoDoubleFailureGap 1 ≤ 1 / 2 := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoAxisGap_PIMSSourceSuccessMass_q_one_le_half

/--
[rlc_scaleTwoAxisGap_not_PIMSFailureMassTransport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededMassObstruction.lean)
-/
@[path]
private lemma rlc_scaleTwoAxisGap_not_PIMSFailureMassTransport_eq :
-- imply
  ¬ RlcAxisGapPIMSFailureMassTransport rlc_scaleTwoDoubleFailureGap 1 := by
-- proof
  apply StatMech.Universality.rlc_scaleTwoAxisGap_not_PIMSFailureMassTransport


-- created on 2026-10-23
