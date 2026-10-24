import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectQuarterTurnPrimalCrossingTail
open StatMech StatMech.FrontierD


/--
[fkRectQuarterTurnCriticalCutFree_primalCrossingTail_le_choose_mul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurnPrimalCrossingTail.lean)
-/
@[path]
private lemma fkRectQuarterTurnCriticalCutFree_primalCrossingTail_le_choose_mul_pow_eq
  {R : FKRectTorus}
  {q : Real}
  {n : Nat}
-- given
  (hheight : 4 < R.height)
  (hq : 1 <= q) :
-- imply
  fkRectCriticalCutFreeEventMass (fkRectQuarterTurnTorus R hheight) q {eta | n < fkRectRawHorizontalCrossingClusterCount (fkRectQuarterTurnTorus R hheight) (fkRectForceCutClosed (fkRectQuarterTurnTorus R hheight) eta)} <= Nat.choose (2 * R.width) (n + 1) * ((StatMech.FK.freeInfiniteVolume 2 (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq)) (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq)) (zero_lt_one.trans_le hq) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))).real (StatMech.FK.boxBdryConnEvent 2 (R.height / 2 - 2))) ^ (n + 1) := by
-- proof
  apply StatMech.FrontierD.fkRectQuarterTurnCriticalCutFree_primalCrossingTail_le_choose_mul_pow R hheight hq n


-- created on 2026-10-23
