import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingCountBridge.Part5
open StatMech StatMech.FrontierD


/--
[fkRectFixedChargeTilt_pos_of_windingNumber_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma fkRectFixedChargeTilt_pos_of_windingNumber_eq_eq
  {R : FKRectTorus}
  {q : Real}
  {lam : Real}
  {omega : R.Configuration}
  {r : Nat}
-- given
  (hq : 0 < q)
  (hr : r ≤ R.medialTorus.width / 2)
  (hU : fkRectUnorientedVerticalWindingNumber R omega = r) :
-- imply
  0 < fkRectFixedChargeTilt R q lam r hr omega := by
-- proof
  apply StatMech.FrontierD.fkRectFixedChargeTilt_pos_of_windingNumber_eq R hq lam omega r hr hU

/--
[fkRectUnorientedVerticalWindingNumber_ge_of_weight_ne_zero_of_flux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma fkRectUnorientedVerticalWindingNumber_ge_of_weight_ne_zero_of_flux_eq
  {R : FKRectTorus}
  {lam : Real}
  {omega : R.Configuration}
  {arrows : SixVertexArrows R.medialTorus}
  {r : Nat}
-- given
  (hweight : fkRectOrientedLoopWeight R lam omega arrows ≠ 0)
  (hflux : fkOrientedLoopVerticalFlux R.medialTorus arrows = -(2 * (r : Int))) :
-- imply
  r ≤ fkRectUnorientedVerticalWindingNumber R omega := by
-- proof
  apply StatMech.FrontierD.fkRectUnorientedVerticalWindingNumber_ge_of_weight_ne_zero_of_flux R lam omega arrows r hweight hflux

/--
[fkRectUnorientedVerticalWindingNumber_ge_of_fixedCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma fkRectUnorientedVerticalWindingNumber_ge_of_fixedCharge_eq
  {R : FKRectTorus}
  {lam : Real}
  {omega : R.Configuration}
  {arrows : SixVertexArrows R.medialTorus}
  {r : Nat}
-- given
  (hr : r ≤ R.medialTorus.width / 2)
  (hweight : fkRectOrientedLoopWeight R lam omega arrows ≠ 0)
  (hsector : sixVertexUpCount (svTorusVerticalRows R.medialTorus arrows (svFinLast R.medialTorus.height_pos)) = R.medialTorus.width / 2 - r) :
-- imply
  r ≤ fkRectUnorientedVerticalWindingNumber R omega := by
-- proof
  apply StatMech.FrontierD.fkRectUnorientedVerticalWindingNumber_ge_of_fixedCharge R lam omega arrows r hr hweight hsector

/--
[fkRectVerticalFluxSummand_ne_zero_imp_windingNumber_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma fkRectVerticalFluxSummand_ne_zero_imp_windingNumber_ge_eq
  {R : FKRectTorus}
  {lam : Real}
  {omega : R.Configuration}
  {arrows : SixVertexArrows R.medialTorus}
  {r : Nat}
-- given
  (hterm : (if fkOrientedLoopVerticalFlux R.medialTorus arrows = -(2 * (r : Int)) then fkRectOrientedLoopWeight R lam omega arrows else 0) ≠ 0) :
-- imply
  r ≤ fkRectUnorientedVerticalWindingNumber R omega := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalFluxSummand_ne_zero_imp_windingNumber_ge R lam omega arrows r hterm

/--
[fkRectFixedChargeSummand_le_windingRestrictedSummand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma fkRectFixedChargeSummand_le_windingRestrictedSummand_eq
  {R : FKRectTorus}
  {lam : Real}
  {omega : R.Configuration}
  {arrows : SixVertexArrows R.medialTorus}
  {r : Nat}
-- given
  (hr : r ≤ R.medialTorus.width / 2) :
-- imply
  (if sixVertexUpCount (svTorusVerticalRows R.medialTorus arrows (svFinLast R.medialTorus.height_pos)) = R.medialTorus.width / 2 - r then fkRectOrientedLoopWeight R lam omega arrows else 0) ≤ if r ≤ fkRectUnorientedVerticalWindingNumber R omega then fkRectOrientedLoopWeight R lam omega arrows else 0 := by
-- proof
  apply StatMech.FrontierD.fkRectFixedChargeSummand_le_windingRestrictedSummand R lam omega arrows r hr

/--
[fkRectOrientedLoopFixedChargePartitionSum_le_windingRestricted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma fkRectOrientedLoopFixedChargePartitionSum_le_windingRestricted_eq
  {R : FKRectTorus}
  {lam : Real}
  {r : Nat}
-- given
  (hr : r ≤ R.medialTorus.width / 2) :
-- imply
  fkRectOrientedLoopSectorPartitionSum R (fkRectFixedChargeSector R r hr) lam ≤ ∑ omega : R.Configuration, if r ≤ fkRectUnorientedVerticalWindingNumber R omega then ∑ arrows : SixVertexArrows R.medialTorus, fkRectOrientedLoopWeight R lam omega arrows else 0 := by
-- proof
  apply StatMech.FrontierD.fkRectOrientedLoopFixedChargePartitionSum_le_windingRestricted R lam r hr

/--
[fkRectZeroTurnLoopCount_add_nonzeroTurnLoopCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma fkRectZeroTurnLoopCount_add_nonzeroTurnLoopCount_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectZeroTurnLoopCount R omega + fkRectNonzeroTurnLoopCount R omega = fkRectMedialLoopCount R omega := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnLoopCount_add_nonzeroTurnLoopCount R omega

/--
[sum_fkRectOrientedLoopWeight_eq_turningProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma sum_fkRectOrientedLoopWeight_eq_turningProduct_eq
  {R : FKRectTorus}
  {lam : Real}
  {omega : R.Configuration} :
-- imply
  (∑ arrows : SixVertexArrows R.medialTorus, fkRectOrientedLoopWeight R lam omega arrows) = ∏ C : FKMedialLoop R.medialTorus (fkRectConfigurationToMedialPairing R omega), (Real.exp ((lam / 4) * FKMedialTurningFiber.canonicalComponentTurn (fkRectConfigurationToMedialPairing R omega) C) + Real.exp (-(lam / 4) * FKMedialTurningFiber.canonicalComponentTurn (fkRectConfigurationToMedialPairing R omega) C)) := by
-- proof
  apply StatMech.FrontierD.sum_fkRectOrientedLoopWeight_eq_turningProduct R lam omega

/--
[fkRectTurningProduct_eq_zero_nonzeroTurnPowers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma fkRectTurningProduct_eq_zero_nonzeroTurnPowers_eq
  {R : FKRectTorus}
  {lam : Real}
  {omega : R.Configuration} :
-- imply
  (∏ C : FKMedialLoop R.medialTorus (fkRectConfigurationToMedialPairing R omega), (Real.exp ((lam / 4) * FKMedialTurningFiber.canonicalComponentTurn (fkRectConfigurationToMedialPairing R omega) C) + Real.exp (-(lam / 4) * FKMedialTurningFiber.canonicalComponentTurn (fkRectConfigurationToMedialPairing R omega) C))) = 2 ^ fkRectZeroTurnLoopCount R omega * (Real.exp lam + Real.exp (-lam)) ^ fkRectNonzeroTurnLoopCount R omega := by
-- proof
  apply StatMech.FrontierD.fkRectTurningProduct_eq_zero_nonzeroTurnPowers R lam omega

/--
[sum_fkRectOrientedLoopWeight_eq_zero_nonzeroTurnPowers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma sum_fkRectOrientedLoopWeight_eq_zero_nonzeroTurnPowers_eq
  {R : FKRectTorus}
  {lam : Real}
  {omega : R.Configuration} :
-- imply
  (∑ arrows : SixVertexArrows R.medialTorus, fkRectOrientedLoopWeight R lam omega arrows) = 2 ^ fkRectZeroTurnLoopCount R omega * (Real.exp lam + Real.exp (-lam)) ^ fkRectNonzeroTurnLoopCount R omega := by
-- proof
  apply StatMech.FrontierD.sum_fkRectOrientedLoopWeight_eq_zero_nonzeroTurnPowers R lam omega

/--
[fkRectAllOrientedLoopTilt_eq_turningProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma fkRectAllOrientedLoopTilt_eq_turningProduct_eq
  {R : FKRectTorus}
  {q lam : Real}
  {omega : R.Configuration} :
-- imply
  fkRectAllOrientedLoopTilt R q lam omega = (∏ C : FKMedialLoop R.medialTorus (fkRectConfigurationToMedialPairing R omega), (Real.exp ((lam / 4) * FKMedialTurningFiber.canonicalComponentTurn (fkRectConfigurationToMedialPairing R omega) C) + Real.exp (-(lam / 4) * FKMedialTurningFiber.canonicalComponentTurn (fkRectConfigurationToMedialPairing R omega) C))) / fkRectCriticalReducedWeight R q omega := by
-- proof
  apply StatMech.FrontierD.fkRectAllOrientedLoopTilt_eq_turningProduct R q lam omega

/--
[fkRectAllOrientedLoopTilt_eq_turningProduct_div_loopDefect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma fkRectAllOrientedLoopTilt_eq_turningProduct_div_loopDefect_eq
  {R : FKRectTorus}
  {q : Real}
  {lam : Real}
  {omega : R.Configuration}
-- given
  (hq : 0 < q) :
-- imply
  fkRectAllOrientedLoopTilt R q lam omega = (∏ C : FKMedialLoop R.medialTorus (fkRectConfigurationToMedialPairing R omega), (Real.exp ((lam / 4) * FKMedialTurningFiber.canonicalComponentTurn (fkRectConfigurationToMedialPairing R omega) C) + Real.exp (-(lam / 4) * FKMedialTurningFiber.canonicalComponentTurn (fkRectConfigurationToMedialPairing R omega) C))) / (Real.sqrt q ^ (R.width * R.height : Nat) * Real.sqrt q ^ fkRectMedialLoopCount R omega * Real.sqrt q ^ fkRectEulerHomologyDefect R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectAllOrientedLoopTilt_eq_turningProduct_div_loopDefect R hq lam omega

/--
[sum_fkRectOrientedLoopWeight_eq_zero_nonzeroTurnPowers_fkQgt4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma sum_fkRectOrientedLoopWeight_eq_zero_nonzeroTurnPowers_fkQgt4_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration}
-- given
  (hq : 4 < q) :
-- imply
  let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q) (∑ arrows : SixVertexArrows R.medialTorus, fkRectOrientedLoopWeight R lam omega arrows) = 2 ^ fkRectZeroTurnLoopCount R omega * Real.sqrt q ^ fkRectNonzeroTurnLoopCount R omega := by
-- proof
  apply StatMech.FrontierD.sum_fkRectOrientedLoopWeight_eq_zero_nonzeroTurnPowers_fkQgt4 R hq omega

/--
[fkRectAllOrientedLoopTilt_eq_zeroTurnLoopCount_fkQgt4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma fkRectAllOrientedLoopTilt_eq_zeroTurnLoopCount_fkQgt4_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration}
-- given
  (hq : 4 < q) :
-- imply
  let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q) fkRectAllOrientedLoopTilt R q lam omega = (2 / Real.sqrt q) ^ fkRectZeroTurnLoopCount R omega / (Real.sqrt q ^ (R.width * R.height : Nat) * Real.sqrt q ^ fkRectEulerHomologyDefect R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectAllOrientedLoopTilt_eq_zeroTurnLoopCount_fkQgt4 R hq omega

/--
[fkRectZeroTurnEulerResidual_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma fkRectZeroTurnEulerResidual_nonneg_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration}
-- given
  (hq : 4 < q) :
-- imply
  0 ≤ fkRectZeroTurnEulerResidual R q omega := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnEulerResidual_nonneg R hq omega

/--
[fkRectZeroTurnEulerResidual_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma fkRectZeroTurnEulerResidual_le_one_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration}
-- given
  (hq : 4 < q) :
-- imply
  fkRectZeroTurnEulerResidual R q omega ≤ 1 := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnEulerResidual_le_one R hq omega

/--
[fkRectCriticalWindingTailMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma fkRectCriticalWindingTailMass_nonneg_eq
  {R : FKRectTorus}
  {q : Real}
  {r : Nat}
-- given
  (hq : 0 < q) :
-- imply
  0 ≤ fkRectCriticalWindingTailMass R q r := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalWindingTailMass_nonneg R hq r

/--
[fkRectCriticalWindingTailMass_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma fkRectCriticalWindingTailMass_le_one_eq
  {R : FKRectTorus}
  {q : Real}
  {r : Nat}
-- given
  (hq : 0 < q) :
-- imply
  fkRectCriticalWindingTailMass R q r ≤ 1 := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalWindingTailMass_le_one R hq r

/--
[fkRectAllOrientedLoopTilt_eq_residual_div_area_fkQgt4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma fkRectAllOrientedLoopTilt_eq_residual_div_area_fkQgt4_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration}
-- given
  (hq : 4 < q) :
-- imply
  let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q) fkRectAllOrientedLoopTilt R q lam omega = fkRectZeroTurnEulerResidual R q omega / Real.sqrt q ^ (R.width * R.height : Nat) := by
-- proof
  apply StatMech.FrontierD.fkRectAllOrientedLoopTilt_eq_residual_div_area_fkQgt4 R hq omega

/--
[sum_rcProb_mul_windingRestrictedAllOrientedLoopTilt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma sum_rcProb_mul_windingRestrictedAllOrientedLoopTilt_eq
  {R : FKRectTorus}
  {q : Real}
  {lam : Real}
  {r : Nat}
-- given
  (hq : 0 < q) :
-- imply
  (∑ omega : R.Configuration, fkRectCriticalRandomClusterProb R q omega * (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then fkRectAllOrientedLoopTilt R q lam omega else 0)) = (∑ omega : R.Configuration, if r ≤ fkRectUnorientedVerticalWindingNumber R omega then ∑ arrows : SixVertexArrows R.medialTorus, fkRectOrientedLoopWeight R lam omega arrows else 0) / fkRectCriticalReducedZ R q := by
-- proof
  apply StatMech.FrontierD.sum_rcProb_mul_windingRestrictedAllOrientedLoopTilt R hq lam r

/--
[sum_rcProb_mul_fixedChargeTilt_le_windingRestrictedAllTilt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma sum_rcProb_mul_fixedChargeTilt_le_windingRestrictedAllTilt_eq
  {R : FKRectTorus}
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : r ≤ R.medialTorus.width / 2) :
-- imply
  let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q) (∑ omega : R.Configuration, fkRectCriticalRandomClusterProb R q omega * fkRectFixedChargeTilt R q lam r hr omega) ≤ ∑ omega : R.Configuration, fkRectCriticalRandomClusterProb R q omega * (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then fkRectAllOrientedLoopTilt R q lam omega else 0) := by
-- proof
  apply StatMech.FrontierD.sum_rcProb_mul_fixedChargeTilt_le_windingRestrictedAllTilt R hq r hr

/--
[sum_rcProb_mul_windingRestrictedAllTilt_eq_residual_div_area](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma sum_rcProb_mul_windingRestrictedAllTilt_eq_residual_div_area_eq
  {R : FKRectTorus}
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q) :
-- imply
  let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q) (∑ omega : R.Configuration, fkRectCriticalRandomClusterProb R q omega * (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then fkRectAllOrientedLoopTilt R q lam omega else 0)) = (∑ omega : R.Configuration, fkRectCriticalRandomClusterProb R q omega * (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then fkRectZeroTurnEulerResidual R q omega else 0)) / Real.sqrt q ^ (R.width * R.height : Nat) := by
-- proof
  apply StatMech.FrontierD.sum_rcProb_mul_windingRestrictedAllTilt_eq_residual_div_area R hq r

/--
[sum_rcProb_mul_windingResidual_le_windingTailMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma sum_rcProb_mul_windingResidual_le_windingTailMass_eq
  {R : FKRectTorus}
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q) :
-- imply
  (∑ omega : R.Configuration, fkRectCriticalRandomClusterProb R q omega * (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then fkRectZeroTurnEulerResidual R q omega else 0)) ≤ fkRectCriticalWindingTailMass R q r := by
-- proof
  apply StatMech.FrontierD.sum_rcProb_mul_windingResidual_le_windingTailMass R hq r

/--
[sum_rcProb_mul_fixedChargeTilt_le_residual_div_area](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma sum_rcProb_mul_fixedChargeTilt_le_residual_div_area_eq
  {R : FKRectTorus}
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : r ≤ R.medialTorus.width / 2) :
-- imply
  let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q) (∑ omega : R.Configuration, fkRectCriticalRandomClusterProb R q omega * fkRectFixedChargeTilt R q lam r hr omega) ≤ (∑ omega : R.Configuration, fkRectCriticalRandomClusterProb R q omega * (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then fkRectZeroTurnEulerResidual R q omega else 0)) / Real.sqrt q ^ (R.width * R.height : Nat) := by
-- proof
  apply StatMech.FrontierD.sum_rcProb_mul_fixedChargeTilt_le_residual_div_area R hq r hr

/--
[sixVertexFixedCharge_div_fkZ_le_residual_div_area](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma sixVertexFixedCharge_div_fkZ_le_residual_div_area_eq
  {R : FKRectTorus}
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : r ≤ R.medialTorus.width / 2) :
-- imply
  sixVertexTorusFixedChargePartitionSum R.medialTorus r hr (fkQgt4SixVertexWeight q) / fkRectCriticalReducedZ R q ≤ (∑ omega : R.Configuration, fkRectCriticalRandomClusterProb R q omega * (if r ≤ fkRectUnorientedVerticalWindingNumber R omega then fkRectZeroTurnEulerResidual R q omega else 0)) / Real.sqrt q ^ (R.width * R.height : Nat) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedCharge_div_fkZ_le_residual_div_area R hq r hr

/--
[sixVertexFixedCharge_div_fkZ_le_windingTail_div_area](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma sixVertexFixedCharge_div_fkZ_le_windingTail_div_area_eq
  {R : FKRectTorus}
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : r ≤ R.medialTorus.width / 2) :
-- imply
  sixVertexTorusFixedChargePartitionSum R.medialTorus r hr (fkQgt4SixVertexWeight q) / fkRectCriticalReducedZ R q ≤ fkRectCriticalWindingTailMass R q r / Real.sqrt q ^ (R.width * R.height : Nat) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedCharge_div_fkZ_le_windingTail_div_area R hq r hr

/--
[sixVertexFixedCharge_div_fkZ_le_invSqrtQ_pow_area](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma sixVertexFixedCharge_div_fkZ_le_invSqrtQ_pow_area_eq
  {R : FKRectTorus}
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : r ≤ R.medialTorus.width / 2) :
-- imply
  sixVertexTorusFixedChargePartitionSum R.medialTorus r hr (fkQgt4SixVertexWeight q) / fkRectCriticalReducedZ R q ≤ (1 / Real.sqrt q) ^ (R.width * R.height : Nat) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedCharge_div_fkZ_le_invSqrtQ_pow_area R hq r hr

/--
[sixVertexFixedCharge_div_fkZ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma sixVertexFixedCharge_div_fkZ_pos_eq
  {R : FKRectTorus}
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : r ≤ R.medialTorus.width / 2) :
-- imply
  0 < sixVertexTorusFixedChargePartitionSum R.medialTorus r hr (fkQgt4SixVertexWeight q) / fkRectCriticalReducedZ R q := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedCharge_div_fkZ_pos R hq r hr

/--
[fkRectBalancedSectorNormalization_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma fkRectBalancedSectorNormalization_pos_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  0 < fkRectBalancedSectorNormalization R q := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedSectorNormalization_pos R hq

/--
[fkRectBalancedSectorNormalization_eq_chargeZeroExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma fkRectBalancedSectorNormalization_eq_chargeZeroExpectation_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q) fkRectBalancedSectorNormalization R q = Real.sqrt q ^ (R.width * R.height : Nat) * ∑ omega : R.Configuration, fkRectCriticalRandomClusterProb R q omega * fkRectFixedChargeTilt R q lam 0 (Nat.zero_le _) omega := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedSectorNormalization_eq_chargeZeroExpectation R hq

/--
[sixVertexFixedCharge_div_chargeZero_eq_areaNormalizedRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma sixVertexFixedCharge_div_chargeZero_eq_areaNormalizedRatio_eq
  {R : FKRectTorus}
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : r ≤ R.medialTorus.width / 2) :
-- imply
  sixVertexTorusFixedChargePartitionSum R.medialTorus r hr (fkQgt4SixVertexWeight q) / sixVertexTorusFixedChargePartitionSum R.medialTorus 0 (Nat.zero_le _) (fkQgt4SixVertexWeight q) = (Real.sqrt q ^ (R.width * R.height : Nat) * (sixVertexTorusFixedChargePartitionSum R.medialTorus r hr (fkQgt4SixVertexWeight q) / fkRectCriticalReducedZ R q)) / fkRectBalancedSectorNormalization R q := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedCharge_div_chargeZero_eq_areaNormalizedRatio R hq r hr

/--
[sixVertexFixedCharge_div_chargeZero_le_windingTail_div_balanced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma sixVertexFixedCharge_div_chargeZero_le_windingTail_div_balanced_eq
  {R : FKRectTorus}
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : r ≤ R.medialTorus.width / 2) :
-- imply
  sixVertexTorusFixedChargePartitionSum R.medialTorus r hr (fkQgt4SixVertexWeight q) / sixVertexTorusFixedChargePartitionSum R.medialTorus 0 (Nat.zero_le _) (fkQgt4SixVertexWeight q) ≤ fkRectCriticalWindingTailMass R q r / fkRectBalancedSectorNormalization R q := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedCharge_div_chargeZero_le_windingTail_div_balanced R hq r hr

/--
[log_sqrtQ_le_fixedCharge_negLogRate_per_area](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma log_sqrtQ_le_fixedCharge_negLogRate_per_area_eq
  {R : FKRectTorus}
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : r ≤ R.medialTorus.width / 2) :
-- imply
  Real.log (Real.sqrt q) ≤ -Real.log (sixVertexTorusFixedChargePartitionSum R.medialTorus r hr (fkQgt4SixVertexWeight q) / fkRectCriticalReducedZ R q) / (R.width * R.height : Nat) := by
-- proof
  apply StatMech.FrontierD.log_sqrtQ_le_fixedCharge_negLogRate_per_area R hq r hr

/--
[sixVertexChargeOne_div_fkZ_le_residual_div_area](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma sixVertexChargeOne_div_fkZ_le_residual_div_area_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  sixVertexTorusFixedChargePartitionSum R.medialTorus 1 (one_le_fkRectMedial_halfWidth R) (fkQgt4SixVertexWeight q) / fkRectCriticalReducedZ R q ≤ (∑ omega : R.Configuration, fkRectCriticalRandomClusterProb R q omega * (if 1 ≤ fkRectUnorientedVerticalWindingNumber R omega then fkRectZeroTurnEulerResidual R q omega else 0)) / Real.sqrt q ^ (R.width * R.height : Nat) := by
-- proof
  apply StatMech.FrontierD.sixVertexChargeOne_div_fkZ_le_residual_div_area R hq

/--
[sixVertexChargeOne_div_fkZ_le_windingTail_div_area](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma sixVertexChargeOne_div_fkZ_le_windingTail_div_area_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  sixVertexTorusFixedChargePartitionSum R.medialTorus 1 (one_le_fkRectMedial_halfWidth R) (fkQgt4SixVertexWeight q) / fkRectCriticalReducedZ R q ≤ fkRectCriticalWindingTailMass R q 1 / Real.sqrt q ^ (R.width * R.height : Nat) := by
-- proof
  apply StatMech.FrontierD.sixVertexChargeOne_div_fkZ_le_windingTail_div_area R hq

/--
[sixVertexChargeOne_div_fkZ_le_invSqrtQ_pow_area](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean)
-/
@[path]
private lemma sixVertexChargeOne_div_fkZ_le_invSqrtQ_pow_area_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  sixVertexTorusFixedChargePartitionSum R.medialTorus 1 (one_le_fkRectMedial_halfWidth R) (fkQgt4SixVertexWeight q) / fkRectCriticalReducedZ R q ≤ (1 / Real.sqrt q) ^ (R.width * R.height : Nat) := by
-- proof
  apply StatMech.FrontierD.sixVertexChargeOne_div_fkZ_le_invSqrtQ_pow_area R hq


-- created on 2026-10-23
