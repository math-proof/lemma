import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderTransverseRate
open Filter Topology StatMech StatMech.FrontierD


/--
[fkQgt4_sqrtExactDiagonal_heightSubOne_negLogRate_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTransverseRate.lean)
-/
@[path]
private lemma fkQgt4_sqrtExactDiagonal_heightSubOne_negLogRate_tendsto_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (R : Nat -> FKRectTorus)
  (hheight : Tendsto (fun n => (R n).height) atTop atTop) :
-- imply
  Tendsto (fun n => -Real.log (Real.sqrt (fkQgt4CriticalFreeExactDiagonalTwoPoint hq ((R n).height - 1))) / ((R n).height : Real)) atTop (nhds (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_sqrtExactDiagonal_heightSubOne_negLogRate_tendsto hq R hheight

/--
[fkQgt4_mul_pred_exactDiagonalHalf_le_windingTailRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTransverseRate.lean)
-/
@[path]
private lemma fkQgt4_mul_pred_exactDiagonalHalf_le_windingTailRate_eq
  {q tailRate : Real}
  {width r : Nat}
-- given
  (hq : 4 < q)
  (R : Nat -> FKRectTorus)
  (hr : 0 < r)
  (hrwidth : r <= width)
  (hwidth : forall n, (R n).width = width)
  (hheight : Tendsto (fun n => (R n).height) atTop atTop)
  (hcross : forall n, FKRectWindingTailForcesHorizontalCylinderCrossings (R n) r)
  (htailRate : Tendsto (fun n => -Real.log (fkRectCriticalWindingTailMass (R n) q r) / ((R n).height : Real)) atTop (nhds tailRate)) :
-- imply
  ((r - 1 : Nat) : Real) * (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) <= tailRate := by
-- proof
  apply StatMech.FrontierD.fkQgt4_mul_pred_exactDiagonalHalf_le_windingTailRate hq R width r hr hrwidth hwidth hheight hcross htailRate

/--
[fkQgt4_mul_pred_exactDiagonalHalf_le_windingTailRate_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTransverseRate.lean)
-/
@[path]
private lemma fkQgt4_mul_pred_exactDiagonalHalf_le_windingTailRate_unconditional_eq
  {q tailRate : Real}
  {width r : Nat}
-- given
  (hq : 4 < q)
  (R : Nat -> FKRectTorus)
  (hr : 0 < r)
  (hrwidth : r <= width)
  (hwidth : forall n, (R n).width = width)
  (hheight : Tendsto (fun n => (R n).height) atTop atTop)
  (htailRate : Tendsto (fun n => -Real.log (fkRectCriticalWindingTailMass (R n) q r) / ((R n).height : Real)) atTop (nhds tailRate)) :
-- imply
  ((r - 1 : Nat) : Real) * (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) <= tailRate := by
-- proof
  apply StatMech.FrontierD.fkQgt4_mul_pred_exactDiagonalHalf_le_windingTailRate_unconditional hq R width r hr hrwidth hwidth hheight htailRate


-- created on 2026-10-23
