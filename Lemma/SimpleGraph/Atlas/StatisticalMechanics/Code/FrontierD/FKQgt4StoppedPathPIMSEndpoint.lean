import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKQgt4StoppedPathPIMSEndpoint
open Filter StatMech StatMech.FrontierD


/--
[fkQgt4_evenTwoByOneCrossingFloor_of_stoppedPathPIMS](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4StoppedPathPIMSEndpoint.lean)
-/
@[path]
private lemma fkQgt4_evenTwoByOneCrossingFloor_of_stoppedPathPIMS_eq
  {q : Real}
-- given
  (hq : 1 <= q)
  (hpims : FKQgt4EvenTwoByOneStoppedPathPIMS q) :
-- imply
  forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, (1 / (1 + q)) ^ 6 / (16 * (1 + q ^ 2)) <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_evenTwoByOneCrossingFloor_of_stoppedPathPIMS hq hpims

/--
[fkQgt4_firstOrder_of_stoppedPathPIMS](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4StoppedPathPIMSEndpoint.lean)
-/
@[path]
private lemma fkQgt4_firstOrder_of_stoppedPathPIMS_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hpims : FKQgt4EvenTwoByOneStoppedPathPIMS q) :
-- imply
  FK.IsFirstOrderTransition 2 (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_firstOrder_of_stoppedPathPIMS hq hpims


-- created on 2026-10-23
