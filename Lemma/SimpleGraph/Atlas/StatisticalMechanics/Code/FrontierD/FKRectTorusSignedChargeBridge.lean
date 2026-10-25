import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSignedChargeBridge.Part3
open Matrix StatMech StatMech.FrontierD


/--
[fkRectOrientedLoopPartitionSum_eq_generic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSignedChargeBridge.lean)
-/
@[path]
private lemma fkRectOrientedLoopPartitionSum_eq_generic_eq
  {R : FKRectTorus}
  {lam : Real} :
-- imply
  fkRectOrientedLoopPartitionSum R lam = fkOrientedLoopPartitionSum R.medialTorus lam := by
-- proof
  apply StatMech.FrontierD.fkRectOrientedLoopPartitionSum_eq_generic R lam

/--
[fkRectOrientedLoopPartitionSum_eq_sixVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSignedChargeBridge.lean)
-/
@[path]
private lemma fkRectOrientedLoopPartitionSum_eq_sixVertex_eq
  {R : FKRectTorus}
  {lam : Real} :
-- imply
  fkRectOrientedLoopPartitionSum R lam = sixVertexTorusArrowPartitionSum R.medialTorus (Real.exp (lam / 2) + Real.exp (-lam / 2)) := by
-- proof
  apply StatMech.FrontierD.fkRectOrientedLoopPartitionSum_eq_sixVertex R lam

/--
[fkRectOrientedLoopSectorPartitionSum_eq_generic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSignedChargeBridge.lean)
-/
@[path]
private lemma fkRectOrientedLoopSectorPartitionSum_eq_generic_eq
  {R : FKRectTorus}
  {n : Fin (R.medialTorus.width + 1)}
  {lam : Real} :
-- imply
  fkRectOrientedLoopSectorPartitionSum R n lam = fkOrientedLoopSectorPartitionSum R.medialTorus n lam := by
-- proof
  apply StatMech.FrontierD.fkRectOrientedLoopSectorPartitionSum_eq_generic R n lam

/--
[fkRectOrientedLoopSectorPartitionSum_eq_sectorTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSignedChargeBridge.lean)
-/
@[path]
private lemma fkRectOrientedLoopSectorPartitionSum_eq_sectorTrace_eq
  {R : FKRectTorus}
  {n : Fin (R.medialTorus.width + 1)}
  {lam : Real} :
-- imply
  fkRectOrientedLoopSectorPartitionSum R n lam = Matrix.trace (sixVertexSectorTransfer R.medialTorus.width n.val (Real.exp (lam / 2) + Real.exp (-lam / 2)) ^ R.medialTorus.height) := by
-- proof
  apply StatMech.FrontierD.fkRectOrientedLoopSectorPartitionSum_eq_sectorTrace R n lam

/--
[exp_add_exp_neg_sixVertexLambda_fkQgt4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSignedChargeBridge.lean)
-/
@[path]
private lemma exp_add_exp_neg_sixVertexLambda_fkQgt4_eq
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  Real.exp (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)) + Real.exp (-sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)) = Real.sqrt q := by
-- proof
  apply StatMech.FrontierD.exp_add_exp_neg_sixVertexLambda_fkQgt4 hq

/--
[exp_half_add_exp_neg_half_sixVertexLambda_fkQgt4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSignedChargeBridge.lean)
-/
@[path]
private lemma exp_half_add_exp_neg_half_sixVertexLambda_fkQgt4_eq
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q) Real.exp (lam / 2) + Real.exp (-lam / 2) = fkQgt4SixVertexWeight q := by
-- proof
  apply StatMech.FrontierD.exp_half_add_exp_neg_half_sixVertexLambda_fkQgt4 hq

/--
[sum_rcProb_mul_fkRectSignedChargeTilt_eq_sectorTrace_div_Z](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSignedChargeBridge.lean)
-/
@[path]
private lemma sum_rcProb_mul_fkRectSignedChargeTilt_eq_sectorTrace_div_Z_eq
  {R : FKRectTorus}
  {q : Real}
  {n : Fin (R.medialTorus.width + 1)}
  {lam : Real}
-- given
  (hq : 0 < q) :
-- imply
  (∑ omega : R.Configuration, fkRectCriticalRandomClusterProb R q omega * fkRectSignedChargeTilt R q lam n omega) = Matrix.trace (sixVertexSectorTransfer R.medialTorus.width n.val (Real.exp (lam / 2) + Real.exp (-lam / 2)) ^ R.medialTorus.height) / fkRectCriticalReducedZ R q := by
-- proof
  apply StatMech.FrontierD.sum_rcProb_mul_fkRectSignedChargeTilt_eq_sectorTrace_div_Z R hq n lam

/--
[sum_rcProb_mul_fkRectSignedChargeTilt_eq_canonicalSectorTrace_div_Z](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSignedChargeBridge.lean)
-/
@[path]
private lemma sum_rcProb_mul_fkRectSignedChargeTilt_eq_canonicalSectorTrace_div_Z_eq
  {R : FKRectTorus}
  {q : Real}
  {n : Fin (R.medialTorus.width + 1)}
-- given
  (hq : 4 < q) :
-- imply
  let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q) (∑ omega : R.Configuration, fkRectCriticalRandomClusterProb R q omega * fkRectSignedChargeTilt R q lam n omega) = Matrix.trace (sixVertexSectorTransfer R.medialTorus.width n.val (fkQgt4SixVertexWeight q) ^ R.medialTorus.height) / fkRectCriticalReducedZ R q := by
-- proof
  apply StatMech.FrontierD.sum_rcProb_mul_fkRectSignedChargeTilt_eq_canonicalSectorTrace_div_Z R hq n


-- created on 2026-10-23
