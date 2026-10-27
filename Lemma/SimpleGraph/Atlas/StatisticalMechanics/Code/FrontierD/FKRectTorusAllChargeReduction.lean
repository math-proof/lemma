import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusAllChargeReduction
open Matrix StatMech StatMech.FrontierD


/--
[sixVertexUpCount_eq_half_sub_iff_verticalFlux_eq_neg_two_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusAllChargeReduction.lean)
-/
@[path]
private lemma sixVertexUpCount_eq_half_sub_iff_verticalFlux_eq_neg_two_mul_eq
  {T : EvenTorus}
  {arrows : SixVertexArrows T}
  {r : Nat}
-- given
  (hr : r <= T.width / 2) :
-- imply
  sixVertexUpCount (svTorusVerticalRows T arrows (svFinLast T.height_pos)) = T.width / 2 - r ↔ fkOrientedLoopVerticalFlux T arrows = -(2 * (r : Int)) := by
-- proof
  apply StatMech.FrontierD.sixVertexUpCount_eq_half_sub_iff_verticalFlux_eq_neg_two_mul T arrows r hr

/--
[fkRectFixedChargeTilt_eq_verticalFluxTilt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusAllChargeReduction.lean)
-/
@[path]
private lemma fkRectFixedChargeTilt_eq_verticalFluxTilt_eq
  {R : FKRectTorus}
  {q lam : Real}
  {r : Nat}
  {omega : R.Configuration}
-- given
  (hr : r <= R.medialTorus.width / 2) :
-- imply
  fkRectFixedChargeTilt R q lam r hr omega = fkRectVerticalFluxTilt R q lam (-(2 * (r : Int))) omega := by
-- proof
  apply StatMech.FrontierD.fkRectFixedChargeTilt_eq_verticalFluxTilt R q lam r hr omega

/--
[sum_rcProb_mul_fkRectFixedChargeTilt_eq_partitionSum_div_Z](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusAllChargeReduction.lean)
-/
@[path]
private lemma sum_rcProb_mul_fkRectFixedChargeTilt_eq_partitionSum_div_Z_eq
  {R : FKRectTorus}
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : r <= R.medialTorus.width / 2) :
-- imply
  let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q) (∑ omega : R.Configuration, fkRectCriticalRandomClusterProb R q omega * fkRectFixedChargeTilt R q lam r hr omega) = sixVertexTorusFixedChargePartitionSum R.medialTorus r hr (fkQgt4SixVertexWeight q) / fkRectCriticalReducedZ R q := by
-- proof
  apply StatMech.FrontierD.sum_rcProb_mul_fkRectFixedChargeTilt_eq_partitionSum_div_Z R hq r hr

/--
[sum_rcProb_mul_fkRectVerticalFluxTilt_eq_partitionSum_div_Z](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusAllChargeReduction.lean)
-/
@[path]
private lemma sum_rcProb_mul_fkRectVerticalFluxTilt_eq_partitionSum_div_Z_eq
  {R : FKRectTorus}
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : r <= R.medialTorus.width / 2) :
-- imply
  let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q) (∑ omega : R.Configuration, fkRectCriticalRandomClusterProb R q omega * fkRectVerticalFluxTilt R q lam (-(2 * (r : Int))) omega) = sixVertexTorusFixedChargePartitionSum R.medialTorus r hr (fkQgt4SixVertexWeight q) / fkRectCriticalReducedZ R q := by
-- proof
  apply StatMech.FrontierD.sum_rcProb_mul_fkRectVerticalFluxTilt_eq_partitionSum_div_Z R hq r hr

/--
[sum_rcProb_mul_fkRectFixedChargeTilt_eq_sectorTrace_div_Z](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusAllChargeReduction.lean)
-/
@[path]
private lemma sum_rcProb_mul_fkRectFixedChargeTilt_eq_sectorTrace_div_Z_eq
  {R : FKRectTorus}
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : r <= R.medialTorus.width / 2) :
-- imply
  let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q) (∑ omega : R.Configuration, fkRectCriticalRandomClusterProb R q omega * fkRectFixedChargeTilt R q lam r hr omega) = Matrix.trace (sixVertexSectorTransfer R.medialTorus.width (R.medialTorus.width / 2 - r) (fkQgt4SixVertexWeight q) ^ R.medialTorus.height) / fkRectCriticalReducedZ R q := by
-- proof
  apply StatMech.FrontierD.sum_rcProb_mul_fkRectFixedChargeTilt_eq_sectorTrace_div_Z R hq r hr

/--
[one_le_fkRectMedial_halfWidth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusAllChargeReduction.lean)
-/
@[path]
private lemma one_le_fkRectMedial_halfWidth_eq
  {R : FKRectTorus} :
-- imply
  1 <= R.medialTorus.width / 2 := by
-- proof
  apply StatMech.FrontierD.one_le_fkRectMedial_halfWidth R

/--
[sum_rcProb_mul_fkRectOneWindingTilt_eq_partitionSum_div_Z](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusAllChargeReduction.lean)
-/
@[path]
private lemma sum_rcProb_mul_fkRectOneWindingTilt_eq_partitionSum_div_Z_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q) let hOne := one_le_fkRectMedial_halfWidth R (∑ omega : R.Configuration, fkRectCriticalRandomClusterProb R q omega * fkRectFixedChargeTilt R q lam 1 hOne omega) = sixVertexTorusFixedChargePartitionSum R.medialTorus 1 hOne (fkQgt4SixVertexWeight q) / fkRectCriticalReducedZ R q := by
-- proof
  apply StatMech.FrontierD.sum_rcProb_mul_fkRectOneWindingTilt_eq_partitionSum_div_Z R hq

/--
[sum_rcProb_mul_fkRectChargeOneFluxTilt_eq_partitionSum_div_Z](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusAllChargeReduction.lean)
-/
@[path]
private lemma sum_rcProb_mul_fkRectChargeOneFluxTilt_eq_partitionSum_div_Z_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q) let hOne := one_le_fkRectMedial_halfWidth R (∑ omega : R.Configuration, fkRectCriticalRandomClusterProb R q omega * fkRectVerticalFluxTilt R q lam (-2) omega) = sixVertexTorusFixedChargePartitionSum R.medialTorus 1 hOne (fkQgt4SixVertexWeight q) / fkRectCriticalReducedZ R q := by
-- proof
  apply StatMech.FrontierD.sum_rcProb_mul_fkRectChargeOneFluxTilt_eq_partitionSum_div_Z R hq


-- created on 2026-10-23
