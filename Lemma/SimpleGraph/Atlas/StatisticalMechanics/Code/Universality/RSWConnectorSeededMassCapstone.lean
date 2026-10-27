import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassCapstone.Part2
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_finiteAxisGapConnectorEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededMassCapstone.lean)
-/
@[path]
private lemma rlc_finiteAxisGapConnectorEvent_isIncreasing_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'} :
-- imply
  IsIncreasing (rlc_finiteAxisGapConnectorEvent G) := by
-- proof
  apply StatMech.Universality.rlc_finiteAxisGapConnectorEvent_isIncreasing G

/--
[rlc_axisGapPIMS_pushforward_le_merged_of_inducedWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededMassCapstone.lean)
-/
@[path]
private lemma rlc_axisGapPIMS_pushforward_le_merged_of_inducedWiring_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {q : Real}
  {C : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel C.Adj]
-- given
  (hq : 1 <= q)
  (hC : C <= rlc_connectorMergedWiring gamma gamma')
  (hpush : rlc_axisGapPIMSSourceSuccessMass G q = FK.bcEventMass (rlc_axisGapFiniteGraph G) C (BeffaraDC.selfDualPoint q) q (rlc_finiteAxisGapConnectorEvent G)) :
-- imply
  rlc_axisGapPIMSSourceSuccessMass G q <= FK.bcEventMass (rlc_axisGapFiniteGraph G) (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteAxisGapConnectorEvent G) := by
-- proof
  apply StatMech.Universality.rlc_axisGapPIMS_pushforward_le_merged_of_inducedWiring G hq C hC hpush

/--
[rlc_axisGapPIMS_pushforward_le_merged_of_inducedMixture](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededMassCapstone.lean)
-/
@[path]
private lemma rlc_axisGapPIMS_pushforward_le_merged_of_inducedMixture_eq
  {n : Int}
  [Fintype I]
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {q : Real}
  [forall i, DecidableRel (C i).Adj]
-- given
  (hq : 1 <= q)
  (w : I -> Real)
  (C : I -> SimpleGraph (RlcConnectorVertex n))
  (hw : forall i, 0 <= w i)
  (hwSum : ∑ i, w i = 1)
  (hC : forall i, C i <= rlc_connectorMergedWiring gamma gamma')
  (hpush : rlc_axisGapPIMSSourceSuccessMass G q = ∑ i, w i * FK.bcEventMass (rlc_axisGapFiniteGraph G) (C i) (BeffaraDC.selfDualPoint q) q (rlc_finiteAxisGapConnectorEvent G)) :
-- imply
  rlc_axisGapPIMSSourceSuccessMass G q <= FK.bcEventMass (rlc_axisGapFiniteGraph G) (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteAxisGapConnectorEvent G) := by
-- proof
  apply StatMech.Universality.rlc_axisGapPIMS_pushforward_le_merged_of_inducedMixture G hq w C hw hwSum hC hpush

/--
[rlc_axisGap_G201_of_inducedWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededMassCapstone.lean)
-/
@[path]
private lemma rlc_axisGap_G201_of_inducedWiring_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {q : Real}
  {C : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel C.Adj]
-- given
  (hq : 1 <= q)
  (hC : rlc_connectorSeparateWiring gamma gamma' <= C) :
-- imply
  FK.bcEventMass (rlc_axisGapFiniteGraph G) (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteAxisGapConnectorEvent G) <= FK.bcEventMass (rlc_axisGapFiniteGraph G) C (BeffaraDC.selfDualPoint q) q (rlc_finiteAxisGapConnectorEvent G) := by
-- proof
  apply StatMech.Universality.rlc_axisGap_G201_of_inducedWiring G hq C hC

/--
[rlc_axisGap_G201_of_inducedMixture](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededMassCapstone.lean)
-/
@[path]
private lemma rlc_axisGap_G201_of_inducedMixture_eq
  {n : Int}
  [Fintype I]
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {q : Real}
  {conditionalConnectorMass : Real}
  [forall i, DecidableRel (C i).Adj]
-- given
  (hq : 1 <= q)
  (w : I -> Real)
  (C : I -> SimpleGraph (RlcConnectorVertex n))
  (hw : forall i, 0 <= w i)
  (hwSum : ∑ i, w i = 1)
  (hC : forall i, rlc_connectorSeparateWiring gamma gamma' <= C i)
  (hconditional : conditionalConnectorMass = ∑ i, w i * FK.bcEventMass (rlc_axisGapFiniteGraph G) (C i) (BeffaraDC.selfDualPoint q) q (rlc_finiteAxisGapConnectorEvent G)) :
-- imply
  FK.bcEventMass (rlc_axisGapFiniteGraph G) (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteAxisGapConnectorEvent G) <= conditionalConnectorMass := by
-- proof
  apply StatMech.Universality.rlc_axisGap_G201_of_inducedMixture G hq conditionalConnectorMass w C hw hwSum hC hconditional

/--
[rlc_axisGap_G201_floor_of_inducedMixture](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededMassCapstone.lean)
-/
@[path]
private lemma rlc_axisGap_G201_floor_of_inducedMixture_eq
  {n : Int}
  [Fintype I]
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {q c : Real}
  {conditionalConnectorMass : Real}
  [forall i, DecidableRel (C i).Adj]
-- given
  (hq : 1 <= q)
  (w : I -> Real)
  (C : I -> SimpleGraph (RlcConnectorVertex n))
  (hw : forall i, 0 <= w i)
  (hwSum : ∑ i, w i = 1)
  (hC : forall i, rlc_connectorSeparateWiring gamma gamma' <= C i)
  (hconditional : conditionalConnectorMass = ∑ i, w i * FK.bcEventMass (rlc_axisGapFiniteGraph G) (C i) (BeffaraDC.selfDualPoint q) q (rlc_finiteAxisGapConnectorEvent G))
  (hfloor : c <= FK.bcEventMass (rlc_axisGapFiniteGraph G) (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteAxisGapConnectorEvent G)) :
-- imply
  c <= conditionalConnectorMass := by
-- proof
  apply StatMech.Universality.rlc_axisGap_G201_floor_of_inducedMixture G hq conditionalConnectorMass w C hw hwSum hC hconditional hfloor

/--
[rlc_finiteAxisGapConnectorMass_selfDual_ge_one_div_one_add_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededMassCapstone.lean)
-/
@[path]
private lemma rlc_finiteAxisGapConnectorMass_selfDual_ge_one_div_one_add_q_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {q : Real}
-- given
  (hq : 1 <= q)
  (hdual : FK.bcEventMass (rlc_axisGapFiniteGraph G) (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteAxisGapConnectorEvent G)ᶜ <= FK.bcEventMass (rlc_axisGapFiniteGraph G) (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteAxisGapConnectorEvent G)) :
-- imply
  1 / (1 + q) <= FK.bcEventMass (rlc_axisGapFiniteGraph G) (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteAxisGapConnectorEvent G) := by
-- proof
  apply StatMech.Universality.rlc_finiteAxisGapConnectorMass_selfDual_ge_one_div_one_add_q G hq hdual

/--
[rlc_finiteAxisGapConnectorMass_selfDual_ge_of_failureMass_inducedWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededMassCapstone.lean)
-/
@[path]
private lemma rlc_finiteAxisGapConnectorMass_selfDual_ge_of_failureMass_inducedWiring_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {q : Real}
  {C : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel C.Adj]
-- given
  (hq : 1 <= q)
  (hC : C <= rlc_connectorMergedWiring gamma gamma')
  (htransport : RlcAxisGapPIMSFailureMassTransport G q)
  (hpush : rlc_axisGapPIMSSourceSuccessMass G q = FK.bcEventMass (rlc_axisGapFiniteGraph G) C (BeffaraDC.selfDualPoint q) q (rlc_finiteAxisGapConnectorEvent G)) :
-- imply
  1 / (1 + q) <= FK.bcEventMass (rlc_axisGapFiniteGraph G) (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteAxisGapConnectorEvent G) := by
-- proof
  apply StatMech.Universality.rlc_finiteAxisGapConnectorMass_selfDual_ge_of_failureMass_inducedWiring G hq C hC htransport hpush

/--
[rlc_finiteAxisGapConnectorMass_selfDual_ge_of_failureMass_inducedMixture](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededMassCapstone.lean)
-/
@[path]
private lemma rlc_finiteAxisGapConnectorMass_selfDual_ge_of_failureMass_inducedMixture_eq
  {n : Int}
  [Fintype I]
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {q : Real}
  [forall i, DecidableRel (C i).Adj]
-- given
  (hq : 1 <= q)
  (w : I -> Real)
  (C : I -> SimpleGraph (RlcConnectorVertex n))
  (hw : forall i, 0 <= w i)
  (hwSum : ∑ i, w i = 1)
  (hC : forall i, C i <= rlc_connectorMergedWiring gamma gamma')
  (htransport : RlcAxisGapPIMSFailureMassTransport G q)
  (hpush : rlc_axisGapPIMSSourceSuccessMass G q = ∑ i, w i * FK.bcEventMass (rlc_axisGapFiniteGraph G) (C i) (BeffaraDC.selfDualPoint q) q (rlc_finiteAxisGapConnectorEvent G)) :
-- imply
  1 / (1 + q) <= FK.bcEventMass (rlc_axisGapFiniteGraph G) (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteAxisGapConnectorEvent G) := by
-- proof
  apply StatMech.Universality.rlc_finiteAxisGapConnectorMass_selfDual_ge_of_failureMass_inducedMixture G hq w C hw hwSum hC htransport hpush

/--
[rlc_finiteAxisGapConnectorMass_half_of_failureMass_inducedMixture](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededMassCapstone.lean)
-/
@[path]
private lemma rlc_finiteAxisGapConnectorMass_half_of_failureMass_inducedMixture_eq
  {n : Int}
  [Fintype I]
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  [forall i, DecidableRel (C i).Adj]
-- given
  (w : I -> Real)
  (C : I -> SimpleGraph (RlcConnectorVertex n))
  (hw : forall i, 0 <= w i)
  (hwSum : ∑ i, w i = 1)
  (hC : forall i, C i <= rlc_connectorMergedWiring gamma gamma')
  (htransport : RlcAxisGapPIMSFailureMassTransport G 1)
  (hpush : rlc_axisGapPIMSSourceSuccessMass G 1 = ∑ i, w i * FK.bcEventMass (rlc_axisGapFiniteGraph G) (C i) (BeffaraDC.selfDualPoint 1) 1 (rlc_finiteAxisGapConnectorEvent G)) :
-- imply
  (1 : Real) / 2 <= FK.bcEventMass (rlc_axisGapFiniteGraph G) (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint 1) 1 (rlc_finiteAxisGapConnectorEvent G) := by
-- proof
  apply StatMech.Universality.rlc_finiteAxisGapConnectorMass_half_of_failureMass_inducedMixture G w C hw hwSum hC htransport hpush


-- created on 2026-10-23
