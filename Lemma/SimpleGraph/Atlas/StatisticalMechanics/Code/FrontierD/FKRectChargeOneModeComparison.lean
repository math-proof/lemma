import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectChargeOneModeComparison
open Finset StatMech StatMech.FrontierD


/--
[fkRectChargeOneModeCost_one_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectChargeOneModeComparison.lean)
-/
@[path]
private lemma fkRectChargeOneModeCost_one_le_eq
  {lam : Real} :
-- imply
  1 <= fkRectChargeOneModeCost lam := by
-- proof
  apply StatMech.FrontierD.fkRectChargeOneModeCost_one_le lam

/--
[componentModeWeight_sum_le_cost_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectChargeOneModeComparison.lean)
-/
@[path]
private lemma componentModeWeight_sum_le_cost_mul_eq
  {R : FKRectTorus}
  {lam : Real}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {C : FKMedialLoop R.medialTorus pairing}
-- given
  (hlam : 0 <= lam)
  (forced : FKMedialLoop R.medialTorus pairing -> Bool) :
-- imply
  fkRectComponentModeWeight lam pairing C false + fkRectComponentModeWeight lam pairing C true <= fkRectChargeOneModeCost lam * fkRectComponentModeWeight lam pairing C (forced C) := by
-- proof
  apply StatMech.FrontierD.componentModeWeight_sum_le_cost_mul R lam hlam pairing forced C

/--
[forcedDownwardModeSum_le_chargeOneFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectChargeOneModeComparison.lean)
-/
@[path]
private lemma forcedDownwardModeSum_le_chargeOneFiber_eq
  {R : FKRectTorus}
  {lam : Real}
  {omega : R.Configuration}
-- given
  (hU : fkRectUnorientedVerticalWindingNumber R omega = 1) :
-- imply
  forcedBoolModeSum (fkMedialVerticallyWindingComponents (fkRectConfigurationToMedialPairing R omega)) (fkMedialDownwardVerticalMode (fkRectConfigurationToMedialPairing R omega)) (fkRectComponentModeWeight lam (fkRectConfigurationToMedialPairing R omega)) <= ∑ arrows : SixVertexArrows R.medialTorus, if fkOrientedLoopVerticalFlux R.medialTorus arrows = -2 then fkRectOrientedLoopWeight R lam omega arrows else 0 := by
-- proof
  apply StatMech.FrontierD.forcedDownwardModeSum_le_chargeOneFiber R lam omega hU

/--
[allOrientedLoopWeight_le_modeCost_sq_mul_chargeOneFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectChargeOneModeComparison.lean)
-/
@[path]
private lemma allOrientedLoopWeight_le_modeCost_sq_mul_chargeOneFiber_eq
  {R : FKRectTorus}
  {lam : Real}
  {omega : R.Configuration}
-- given
  (hlam : 0 <= lam)
  (hU : fkRectUnorientedVerticalWindingNumber R omega = 1) :
-- imply
  (∑ arrows : SixVertexArrows R.medialTorus, fkRectOrientedLoopWeight R lam omega arrows) <= fkRectChargeOneModeCost lam ^ 2 * ∑ arrows : SixVertexArrows R.medialTorus, if fkOrientedLoopVerticalFlux R.medialTorus arrows = -2 then fkRectOrientedLoopWeight R lam omega arrows else 0 := by
-- proof
  apply StatMech.FrontierD.allOrientedLoopWeight_le_modeCost_sq_mul_chargeOneFiber R lam hlam omega hU

/--
[fkRectAllTilt_le_modeCost_sq_mul_chargeOneTilt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectChargeOneModeComparison.lean)
-/
@[path]
private lemma fkRectAllTilt_le_modeCost_sq_mul_chargeOneTilt_eq
  {R : FKRectTorus}
  {q : Real}
  {lam : Real}
  {omega : R.Configuration}
-- given
  (hq : 0 < q)
  (hlam : 0 <= lam)
  (hU : fkRectUnorientedVerticalWindingNumber R omega = 1) :
-- imply
  fkRectAllOrientedLoopTilt R q lam omega <= fkRectChargeOneModeCost lam ^ 2 * fkRectFixedChargeTilt R q lam 1 (one_le_fkRectMedial_halfWidth R) omega := by
-- proof
  apply StatMech.FrontierD.fkRectAllTilt_le_modeCost_sq_mul_chargeOneTilt R hq lam hlam omega hU

/--
[windingOneAllTiltExpectation_le_modeCost_sq_mul_chargeOneExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectChargeOneModeComparison.lean)
-/
@[path]
private lemma windingOneAllTiltExpectation_le_modeCost_sq_mul_chargeOneExpectation_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q) (∑ omega : R.Configuration, fkRectCriticalRandomClusterProb R q omega * (if fkRectUnorientedVerticalWindingNumber R omega = 1 then fkRectAllOrientedLoopTilt R q lam omega else 0)) <= fkRectChargeOneModeCost lam ^ 2 * ∑ omega : R.Configuration, fkRectCriticalRandomClusterProb R q omega * fkRectFixedChargeTilt R q lam 1 (one_le_fkRectMedial_halfWidth R) omega := by
-- proof
  apply StatMech.FrontierD.windingOneAllTiltExpectation_le_modeCost_sq_mul_chargeOneExpectation R hq

/--
[windingOneAllTiltExpectation_le_modeCost_sq_mul_chargeOneRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectChargeOneModeComparison.lean)
-/
@[path]
private lemma windingOneAllTiltExpectation_le_modeCost_sq_mul_chargeOneRatio_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q) (∑ omega : R.Configuration, fkRectCriticalRandomClusterProb R q omega * (if fkRectUnorientedVerticalWindingNumber R omega = 1 then fkRectAllOrientedLoopTilt R q lam omega else 0)) <= fkRectChargeOneModeCost lam ^ 2 * (sixVertexTorusFixedChargePartitionSum R.medialTorus 1 (one_le_fkRectMedial_halfWidth R) (fkQgt4SixVertexWeight q) / fkRectCriticalReducedZ R q) := by
-- proof
  apply StatMech.FrontierD.windingOneAllTiltExpectation_le_modeCost_sq_mul_chargeOneRatio R hq


-- created on 2026-10-23
