import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderTransverseTail
open StatMech StatMech.FrontierD


/--
[fkRectHorizontalCylinderCrossingTail_le_sqrtExact_pow_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTransverseTail.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderCrossingTail_le_sqrtExact_pow_pred_eq
  {q : Real}
  {R : FKRectTorus}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : 0 < r) :
-- imply
  StatMech.Probability.finiteEventMass (FK.fkProb (fkRectHorizontalCylinderGraph R) (fkRectCriticalP q) q) {rho | r <= fkRectHorizontalCylinderCrossingClusterCount R rho} <= Nat.choose R.width r * R.width ^ R.width * Real.sqrt (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height - 1)) ^ (r - 1) := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderCrossingTail_le_sqrtExact_pow_pred hq R r hr

/--
[fkRectCriticalHorizontalCut_crossingTail_le_sqrtExact_pow_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTransverseTail.lean)
-/
@[path]
private lemma fkRectCriticalHorizontalCut_crossingTail_le_sqrtExact_pow_pred_eq
  {q : Real}
  {R : FKRectTorus}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : 0 < r) :
-- imply
  fkRectCriticalHorizontalCutEventMass R q {eta | r <= fkRectHorizontalCutPrimalCrossingClusterCount R (fkRectForceHorizontalCutClosed R eta)} <= Nat.choose R.width r * R.width ^ R.width * Real.sqrt (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height - 1)) ^ (r - 1) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalHorizontalCut_crossingTail_le_sqrtExact_pow_pred hq R r hr

/--
[fkRectCriticalWindingTailMass_cFE_le_crossingPrefactor_mul_sqrtExact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTransverseTail.lean)
-/
@[path]
private lemma fkRectCriticalWindingTailMass_cFE_le_crossingPrefactor_mul_sqrtExact_eq
  {q : Real}
  {R : FKRectTorus}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hr : 0 < r)
  (hcross : FKRectWindingTailForcesHorizontalCylinderCrossings R r) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ (2 * R.width) * fkRectCriticalWindingTailMass R q r <= Nat.choose R.width r * R.width ^ R.width * Real.sqrt (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height - 1)) ^ (r - 1) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalWindingTailMass_cFE_le_crossingPrefactor_mul_sqrtExact hq R r hr hcross


-- created on 2026-10-23
