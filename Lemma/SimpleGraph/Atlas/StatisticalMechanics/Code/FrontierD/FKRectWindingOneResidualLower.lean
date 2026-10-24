import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectWindingOneResidualLower
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkMedialLoopCanonicalVerticalFlux_ne_zero_of_turn_eq_zero_of_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneResidualLower.lean)
-/
@[path]
private lemma fkMedialLoopCanonicalVerticalFlux_ne_zero_of_turn_eq_zero_of_exists_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {D : FKMedialLoop R.medialTorus (fkRectConfigurationToMedialPairing R omega)}
-- given
  (hvertical : ∃ C : FKMedialLoop R.medialTorus (fkRectConfigurationToMedialPairing R omega), fkMedialLoopCanonicalVerticalFlux (fkRectConfigurationToMedialPairing R omega) C ≠ 0)
  (hDturn : FKMedialTurningFiber.canonicalComponentTurn (fkRectConfigurationToMedialPairing R omega) D = 0) :
-- imply
  fkMedialLoopCanonicalVerticalFlux (fkRectConfigurationToMedialPairing R omega) D ≠ 0 := by
-- proof
  apply StatMech.FrontierD.fkMedialLoopCanonicalVerticalFlux_ne_zero_of_turn_eq_zero_of_exists R omega hvertical D hDturn

/--
[fkRectZeroTurnLoopCount_le_two_of_windingNumber_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneResidualLower.lean)
-/
@[path]
private lemma fkRectZeroTurnLoopCount_le_two_of_windingNumber_eq_one_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
-- given
  (hU : fkRectUnorientedVerticalWindingNumber R omega = 1) :
-- imply
  fkRectZeroTurnLoopCount R omega ≤ 2 := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnLoopCount_le_two_of_windingNumber_eq_one R omega hU

/--
[windingOneResidual_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneResidualLower.lean)
-/
@[path]
private lemma windingOneResidual_lower_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration}
-- given
  (hq : 4 < q)
  (hU : fkRectUnorientedVerticalWindingNumber R omega = 1) :
-- imply
  (2 / Real.sqrt q) ^ 2 / q ≤ fkRectZeroTurnEulerResidual R q omega := by
-- proof
  apply StatMech.FrontierD.windingOneResidual_lower R hq omega hU

/--
[windingOneResidual_mul_mass_le_area_mul_allTiltExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneResidualLower.lean)
-/
@[path]
private lemma windingOneResidual_mul_mass_le_area_mul_allTiltExpectation_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  ((2 / Real.sqrt q) ^ 2 / q) * fkRectCriticalEventMass R q {omega | fkRectUnorientedVerticalWindingNumber R omega = 1} ≤ Real.sqrt q ^ (R.width * R.height : Nat) * (∑ omega : R.Configuration, fkRectCriticalRandomClusterProb R q omega * (if fkRectUnorientedVerticalWindingNumber R omega = 1 then fkRectAllOrientedLoopTilt R q (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)) omega else 0)) := by
-- proof
  apply StatMech.FrontierD.windingOneResidual_mul_mass_le_area_mul_allTiltExpectation R hq

/--
[windingOneResidual_mul_mass_le_modeCost_sq_mul_chargeOneRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneResidualLower.lean)
-/
@[path]
private lemma windingOneResidual_mul_mass_le_modeCost_sq_mul_chargeOneRatio_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  ((2 / Real.sqrt q) ^ 2 / q) * fkRectCriticalEventMass R q {omega | fkRectUnorientedVerticalWindingNumber R omega = 1} ≤ fkRectChargeOneModeCost (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)) ^ 2 * (sixVertexTorusFixedChargePartitionSum R.medialTorus 1 (one_le_fkRectMedial_halfWidth R) (fkQgt4SixVertexWeight q) / sixVertexTorusFixedChargePartitionSum R.medialTorus 0 (Nat.zero_le _) (fkQgt4SixVertexWeight q)) := by
-- proof
  apply StatMech.FrontierD.windingOneResidual_mul_mass_le_modeCost_sq_mul_chargeOneRatio R hq

/--
[fkRectSource_mul_windingResidual_le_modeCost_sq_mul_chargeOneRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneResidualLower.lean)
-/
@[path]
private lemma fkRectSource_mul_windingResidual_le_modeCost_sq_mul_chargeOneRatio_eq
  {R : FKRectTorus}
  {leftRight cut : Nat}
  {q : Real}
  {gap : R.EdgeIndex}
  {x : Fin R.width}
  {t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) × FKRectRightStripBandVertex R cut 1 (R.height - 1))}
-- given
  (hsep : leftRight < cut)
  (hleft : leftRight + 1 < R.width)
  (hq : 4 < q)
  (hgap : gap ∈ fkRectHorizontalCutEdges R)
  (hx : cut ≤ x.val)
  (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
  (hpair : (fkRectRightBandRowOne R cut x hx, fkRectRightBandLastRow R cut x hx) ∈ t) :
-- imply
  ((2 / Real.sqrt q) ^ 2 / q) * (FK.cFE (fkRectCriticalP q) q * (∏ xy ∈ t, FK.twoPointFun (fkRectInducedGraph R (fkRectRightStripBand R cut 1 (R.height - 1))) (fkRectCriticalP q) q xy.1 xy.2) * fkRectCriticalEventMass R q (fkRectSourceLeftBarrier R leftRight gap)) ≤ fkRectChargeOneModeCost (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)) ^ 2 * (sixVertexTorusFixedChargePartitionSum R.medialTorus 1 (one_le_fkRectMedial_halfWidth R) (fkQgt4SixVertexWeight q) / sixVertexTorusFixedChargePartitionSum R.medialTorus 0 (Nat.zero_le _) (fkQgt4SixVertexWeight q)) := by
-- proof
  apply StatMech.FrontierD.fkRectSource_mul_windingResidual_le_modeCost_sq_mul_chargeOneRatio R leftRight cut hsep hleft hq hgap x hx hchosen t hpair


-- created on 2026-10-23
