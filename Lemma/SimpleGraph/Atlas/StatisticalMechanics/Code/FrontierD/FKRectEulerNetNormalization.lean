import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerNetNormalization.Part3
open Finset StatMech StatMech.FrontierD


/--
[fkRectRandomClusterWeight_critical_eq_loop_netIndicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerNetNormalization.lean)
-/
@[path]
private lemma fkRectRandomClusterWeight_critical_eq_loop_netIndicator_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration}
-- given
  (hq : 0 < q) :
-- imply
  fkRectRandomClusterWeight R (fkRectCriticalP q) q omega = fkRectCriticalLoopNormalization R q * Real.sqrt q ^ fkRectMedialLoopCount R omega * q ^ fkRectNetIndicator R omega := by
-- proof
  apply StatMech.FrontierD.fkRectRandomClusterWeight_critical_eq_loop_netIndicator R hq omega

/--
[fkRectZeroTurnEulerResidual_eq_netIndicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerNetNormalization.lean)
-/
@[path]
private lemma fkRectZeroTurnEulerResidual_eq_netIndicator_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration}
-- given
  (hq : 4 < q) :
-- imply
  fkRectZeroTurnEulerResidual R q omega = (2 / Real.sqrt q) ^ fkRectZeroTurnLoopCount R omega / q ^ fkRectNetIndicator R omega := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnEulerResidual_eq_netIndicator R hq omega

/--
[fkRectAllOrientedLoopTilt_eq_zeroTurn_netIndicator_fkQgt4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerNetNormalization.lean)
-/
@[path]
private lemma fkRectAllOrientedLoopTilt_eq_zeroTurn_netIndicator_fkQgt4_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration}
-- given
  (hq : 4 < q) :
-- imply
  let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q) fkRectAllOrientedLoopTilt R q lam omega = ((2 / Real.sqrt q) ^ fkRectZeroTurnLoopCount R omega / q ^ fkRectNetIndicator R omega) / Real.sqrt q ^ (R.width * R.height : Nat) := by
-- proof
  apply StatMech.FrontierD.fkRectAllOrientedLoopTilt_eq_zeroTurn_netIndicator_fkQgt4 R hq omega

/--
[fkRectAllSectorNormalization_eq_residualExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerNetNormalization.lean)
-/
@[path]
private lemma fkRectAllSectorNormalization_eq_residualExpectation_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  fkRectAllSectorNormalization R q = ∑ omega : R.Configuration, fkRectCriticalRandomClusterProb R q omega * fkRectZeroTurnEulerResidual R q omega := by
-- proof
  apply StatMech.FrontierD.fkRectAllSectorNormalization_eq_residualExpectation R hq

/--
[fkRectAllSectorNormalization_eq_zeroTurnNetExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerNetNormalization.lean)
-/
@[path]
private lemma fkRectAllSectorNormalization_eq_zeroTurnNetExpectation_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  fkRectAllSectorNormalization R q = ∑ omega : R.Configuration, fkRectCriticalRandomClusterProb R q omega * ((2 / Real.sqrt q) ^ fkRectZeroTurnLoopCount R omega / q ^ fkRectNetIndicator R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectAllSectorNormalization_eq_zeroTurnNetExpectation R hq

/--
[sixVertexTorusFixedCharge_zero_eq_balanced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerNetNormalization.lean)
-/
@[path]
private lemma sixVertexTorusFixedCharge_zero_eq_balanced_eq
  {T : EvenTorus}
  {c : Real} :
-- imply
  sixVertexTorusFixedChargePartitionSum T 0 (Nat.zero_le _) c = svTorusBalancedArrowPartitionSum T c := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusFixedCharge_zero_eq_balanced T c

/--
[sixVertexTorusFixedCharge_zero_le_arrowPartitionSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerNetNormalization.lean)
-/
@[path]
private lemma sixVertexTorusFixedCharge_zero_le_arrowPartitionSum_eq
  {T : EvenTorus}
  {c : Real}
-- given
  (hc : 0 ≤ c) :
-- imply
  sixVertexTorusFixedChargePartitionSum T 0 (Nat.zero_le _) c ≤ sixVertexTorusArrowPartitionSum T c := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusFixedCharge_zero_le_arrowPartitionSum T hc

/--
[fkRectBalancedSectorNormalization_le_allSectorNormalization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerNetNormalization.lean)
-/
@[path]
private lemma fkRectBalancedSectorNormalization_le_allSectorNormalization_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  fkRectBalancedSectorNormalization R q ≤ fkRectAllSectorNormalization R q := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedSectorNormalization_le_allSectorNormalization R hq

/--
[fkRectAllSectorNormalization_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerNetNormalization.lean)
-/
@[path]
private lemma fkRectAllSectorNormalization_pos_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  0 < fkRectAllSectorNormalization R q := by
-- proof
  apply StatMech.FrontierD.fkRectAllSectorNormalization_pos R hq

/--
[fkRectAllSectorNormalization_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerNetNormalization.lean)
-/
@[path]
private lemma fkRectAllSectorNormalization_le_one_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  fkRectAllSectorNormalization R q ≤ 1 := by
-- proof
  apply StatMech.FrontierD.fkRectAllSectorNormalization_le_one R hq

/--
[fkRectBalancedSectorShare_mem_Ioc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerNetNormalization.lean)
-/
@[path]
private lemma fkRectBalancedSectorShare_mem_Ioc_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  fkRectBalancedSectorShare R q ∈ Set.Ioc 0 1 := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedSectorShare_mem_Ioc R hq

/--
[fkRectBalancedSectorNormalization_eq_share_mul_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerNetNormalization.lean)
-/
@[path]
private lemma fkRectBalancedSectorNormalization_eq_share_mul_all_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  fkRectBalancedSectorNormalization R q = fkRectBalancedSectorShare R q * fkRectAllSectorNormalization R q := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedSectorNormalization_eq_share_mul_all R hq

/--
[fkRectBalancedSectorShare_eq_sixVertexRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerNetNormalization.lean)
-/
@[path]
private lemma fkRectBalancedSectorShare_eq_sixVertexRatio_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  fkRectBalancedSectorShare R q = sixVertexTorusFixedChargePartitionSum R.medialTorus 0 (Nat.zero_le _) (fkQgt4SixVertexWeight q) / sixVertexTorusArrowPartitionSum R.medialTorus (fkQgt4SixVertexWeight q) := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedSectorShare_eq_sixVertexRatio R hq

/--
[balancedNormalization_negLog_eq_all_add_share](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerNetNormalization.lean)
-/
@[path]
private lemma balancedNormalization_negLog_eq_all_add_share_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  -Real.log (fkRectBalancedSectorNormalization R q) = -Real.log (fkRectAllSectorNormalization R q) + -Real.log (fkRectBalancedSectorShare R q) := by
-- proof
  apply StatMech.FrontierD.balancedNormalization_negLog_eq_all_add_share R hq


-- created on 2026-10-23
