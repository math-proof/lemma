import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4HeadlineReduction
open MeasureTheory Filter Topology StatMech StatMech.FrontierD


/--
[fkQgt4CriticalFreeTheta_eq_zero_of_gapRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4HeadlineReduction.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeTheta_eq_zero_of_gapRate_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hrate : Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop (nhds (fkQgt4SixVertexGapRate q))) :
-- imply
  FK.fkThetaFree 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) (q := q) = 0 := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeTheta_eq_zero_of_gapRate hq hrate

/--
[fkQgt4_firstOrder_of_gapRate_and_wiredPercolation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4HeadlineReduction.lean)
-/
@[path]
private lemma fkQgt4_firstOrder_of_gapRate_and_wiredPercolation_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hrate : Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop (nhds (fkQgt4SixVertexGapRate q)))
  (hWiredAlmostSure : let mu := ((FK.wiredInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) mu (percolationEvent 2) = 1) :
-- imply
  And (FK.IsFirstOrderTransition 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q)) (Ne (FK.freeInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q)) (FK.wiredInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q))) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_firstOrder_of_gapRate_and_wiredPercolation hq hrate hWiredAlmostSure


-- created on 2026-10-23
