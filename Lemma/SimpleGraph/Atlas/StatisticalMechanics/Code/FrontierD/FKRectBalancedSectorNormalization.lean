import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedSectorNormalization.Part2
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[fkRectBalancedSectorNormalization_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorNormalization.lean)
-/
@[path]
private lemma fkRectBalancedSectorNormalization_le_one_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  fkRectBalancedSectorNormalization R q ≤ 1 := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedSectorNormalization_le_one R hq

/--
[fkRectBalancedSectorNormalization_mem_Ioc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorNormalization.lean)
-/
@[path]
private lemma fkRectBalancedSectorNormalization_mem_Ioc_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  fkRectBalancedSectorNormalization R q ∈ Set.Ioc 0 1 := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedSectorNormalization_mem_Ioc R hq

/--
[fkRectBalancedSectorNormalization_negLog_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorNormalization.lean)
-/
@[path]
private lemma fkRectBalancedSectorNormalization_negLog_nonneg_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  0 ≤ -Real.log (fkRectBalancedSectorNormalization R q) := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedSectorNormalization_negLog_nonneg R hq

/--
[fkRectBalancedNormalizationDefectDensity_eq_pressureDifference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorNormalization.lean)
-/
@[path]
private lemma fkRectBalancedNormalizationDefectDensity_eq_pressureDifference_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  fkRectBalancedNormalizationDefectDensity R q = fkRectCriticalReducedAreaDensity R q - Real.log (Real.sqrt q) - fkRectBalancedSectorAreaDensity R q := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedNormalizationDefectDensity_eq_pressureDifference R hq

/--
[tendsto_fkRectBalancedNormalizationDefectDensity_zero_iff_pressure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorNormalization.lean)
-/
@[path]
private lemma tendsto_fkRectBalancedNormalizationDefectDensity_zero_iff_pressure_eq
  {R : Nat → FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  Tendsto (fun n => fkRectBalancedNormalizationDefectDensity (R n) q) atTop (nhds 0) ↔ Tendsto (fun n => fkRectCriticalReducedAreaDensity (R n) q - Real.log (Real.sqrt q) - fkRectBalancedSectorAreaDensity (R n) q) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_fkRectBalancedNormalizationDefectDensity_zero_iff_pressure R hq

/--
[sixVertexFixedChargeRatio_mul_balancedNormalization_le_windingTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorNormalization.lean)
-/
@[path]
private lemma sixVertexFixedChargeRatio_mul_balancedNormalization_le_windingTail_eq
  {R : FKRectTorus}
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : r ≤ R.medialTorus.width / 2) :
-- imply
  (sixVertexTorusFixedChargePartitionSum R.medialTorus r hr (fkQgt4SixVertexWeight q) / sixVertexTorusFixedChargePartitionSum R.medialTorus 0 (Nat.zero_le _) (fkQgt4SixVertexWeight q)) * fkRectBalancedSectorNormalization R q ≤ fkRectCriticalWindingTailMass R q r := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeRatio_mul_balancedNormalization_le_windingTail R hq r hr

/--
[fkRectCriticalWindingTailMass_pos_of_fixedCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorNormalization.lean)
-/
@[path]
private lemma fkRectCriticalWindingTailMass_pos_of_fixedCharge_eq
  {R : FKRectTorus}
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : r ≤ R.medialTorus.width / 2) :
-- imply
  0 < fkRectCriticalWindingTailMass R q r := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalWindingTailMass_pos_of_fixedCharge R hq r hr

/--
[fixedCharge_logRatio_add_logBalanced_le_logWindingTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorNormalization.lean)
-/
@[path]
private lemma fixedCharge_logRatio_add_logBalanced_le_logWindingTail_eq
  {R : FKRectTorus}
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : r ≤ R.medialTorus.width / 2) :
-- imply
  Real.log (sixVertexTorusFixedChargePartitionSum R.medialTorus r hr (fkQgt4SixVertexWeight q) / sixVertexTorusFixedChargePartitionSum R.medialTorus 0 (Nat.zero_le _) (fkQgt4SixVertexWeight q)) + Real.log (fkRectBalancedSectorNormalization R q) ≤ Real.log (fkRectCriticalWindingTailMass R q r) := by
-- proof
  apply StatMech.FrontierD.fixedCharge_logRatio_add_logBalanced_le_logWindingTail R hq r hr

/--
[windingTail_negLogRate_le_fixedCharge_add_normalizationDefect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorNormalization.lean)
-/
@[path]
private lemma windingTail_negLogRate_le_fixedCharge_add_normalizationDefect_eq
  {R : FKRectTorus}
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : r ≤ R.medialTorus.width / 2) :
-- imply
  -Real.log (fkRectCriticalWindingTailMass R q r) / R.height ≤ -Real.log (sixVertexTorusFixedChargePartitionSum R.medialTorus r hr (fkQgt4SixVertexWeight q) / sixVertexTorusFixedChargePartitionSum R.medialTorus 0 (Nat.zero_le _) (fkQgt4SixVertexWeight q)) / R.height + -Real.log (fkRectBalancedSectorNormalization R q) / R.height := by
-- proof
  apply StatMech.FrontierD.windingTail_negLogRate_le_fixedCharge_add_normalizationDefect R hq r hr

/--
[tendsto_balancedNormalization_negLog_div_height_zero_of_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorNormalization.lean)
-/
@[path]
private lemma tendsto_balancedNormalization_negLog_div_height_zero_of_lower_eq
  {R : Nat → FKRectTorus}
  {q : Real}
  {lower : Nat → Real}
-- given
  (hq : 4 < q)
  (hlowerPos : ∀ n, 0 < lower n)
  (hlower : ∀ n, lower n ≤ fkRectBalancedSectorNormalization (R n) q)
  (hlowerCost : Tendsto (fun n => -Real.log (lower n) / (R n).height) atTop (nhds 0)) :
-- imply
  Tendsto (fun n => -Real.log (fkRectBalancedSectorNormalization (R n) q) / (R n).height) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_balancedNormalization_negLog_div_height_zero_of_lower R hq lower hlowerPos hlower hlowerCost

/--
[tendsto_balancedNormalization_negLog_div_height_zero_of_uniformLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorNormalization.lean)
-/
@[path]
private lemma tendsto_balancedNormalization_negLog_div_height_zero_of_uniformLower_eq
  {R : Nat → FKRectTorus}
  {q a : Real}
-- given
  (hq : 4 < q)
  (ha : 0 < a)
  (hlower : ∀ n, a ≤ fkRectBalancedSectorNormalization (R n) q)
  (hheight : Tendsto (fun n => ((R n).height : Real)) atTop atTop) :
-- imply
  Tendsto (fun n => -Real.log (fkRectBalancedSectorNormalization (R n) q) / (R n).height) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_balancedNormalization_negLog_div_height_zero_of_uniformLower R hq ha hlower hheight

/--
[windingTailRate_le_fixedChargeRate_add_normalizationRate_of_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorNormalization.lean)
-/
@[path]
private lemma windingTailRate_le_fixedChargeRate_add_normalizationRate_of_tendsto_eq
  {R : Nat → FKRectTorus}
  {q windingRate chargeRate normalizationRate : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : ∀ n, r ≤ (R n).medialTorus.width / 2)
  (hwind : Tendsto (fun n => -Real.log (fkRectCriticalWindingTailMass (R n) q r) / (R n).height) atTop (nhds windingRate))
  (hcharge : Tendsto (fun n => -Real.log (sixVertexTorusFixedChargePartitionSum (R n).medialTorus r (hr n) (fkQgt4SixVertexWeight q) / sixVertexTorusFixedChargePartitionSum (R n).medialTorus 0 (Nat.zero_le _) (fkQgt4SixVertexWeight q)) / (R n).height) atTop (nhds chargeRate))
  (hnormalization : Tendsto (fun n => -Real.log (fkRectBalancedSectorNormalization (R n) q) / (R n).height) atTop (nhds normalizationRate)) :
-- imply
  windingRate ≤ chargeRate + normalizationRate := by
-- proof
  apply StatMech.FrontierD.windingTailRate_le_fixedChargeRate_add_normalizationRate_of_tendsto R hq r hr hwind hcharge hnormalization

/--
[windingTailRate_le_fixedChargeRate_of_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorNormalization.lean)
-/
@[path]
private lemma windingTailRate_le_fixedChargeRate_of_tendsto_eq
  {R : Nat → FKRectTorus}
  {q windingRate chargeRate : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : ∀ n, r ≤ (R n).medialTorus.width / 2)
  (hwind : Tendsto (fun n => -Real.log (fkRectCriticalWindingTailMass (R n) q r) / (R n).height) atTop (nhds windingRate))
  (hcharge : Tendsto (fun n => -Real.log (sixVertexTorusFixedChargePartitionSum (R n).medialTorus r (hr n) (fkQgt4SixVertexWeight q) / sixVertexTorusFixedChargePartitionSum (R n).medialTorus 0 (Nat.zero_le _) (fkQgt4SixVertexWeight q)) / (R n).height) atTop (nhds chargeRate))
  (hnormalization : Tendsto (fun n => -Real.log (fkRectBalancedSectorNormalization (R n) q) / (R n).height) atTop (nhds 0)) :
-- imply
  windingRate ≤ chargeRate := by
-- proof
  apply StatMech.FrontierD.windingTailRate_le_fixedChargeRate_of_tendsto R hq r hr hwind hcharge hnormalization


-- created on 2026-10-23
