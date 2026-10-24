import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKQgt4UnconditionalRateAssembly
open MeasureTheory Filter Topology StatMech StatMech.FrontierD


/--
[fkQgt4CriticalFreeExactDiagonalRateLimit_pos_of_gapRate_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4UnconditionalRateAssembly.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeExactDiagonalRateLimit_pos_of_gapRate_le_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hone : fkQgt4SixVertexGapRate q <= fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) :
-- imply
  0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeExactDiagonalRateLimit_pos_of_gapRate_le hq hone

/--
[fkQgt4CriticalFreeExactDiagonalRateLimit_pos_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4UnconditionalRateAssembly.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeExactDiagonalRateLimit_pos_of_winding_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hwind : FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q)) :
-- imply
  0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeExactDiagonalRateLimit_pos_of_winding hq hwind

/--
[fkQgt4CriticalFreeTwoPoint_eventually_exponential_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4UnconditionalRateAssembly.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeTwoPoint_eventually_exponential_of_winding_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hwind : FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q)) :
-- imply
  exists N : Nat, forall x : Site 2, N <= fkQgt4SiteRadius x -> fkQgt4CriticalFreeTwoPoint hq x <= Real.exp (-(fkQgt4CriticalFreeExactDiagonalRateLimit hq / 4) * (fkQgt4SiteRadius x : Real)) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeTwoPoint_eventually_exponential_of_winding hq hwind

/--
[fkQgt4CriticalFreeSphereConnectionEvent_eventually_exponential_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4UnconditionalRateAssembly.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeSphereConnectionEvent_eventually_exponential_of_winding_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hwind : FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q)) :
-- imply
  exists N : Nat, forall n : Nat, N <= n -> ((FK.freeInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))).real (fkQgt4CriticalFreeSphereConnectionEvent n) <= ((2 * n + 1 : Nat) : Real) ^ 2 * Real.exp (-(fkQgt4CriticalFreeExactDiagonalRateLimit hq / 4) * (n : Real)) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeSphereConnectionEvent_eventually_exponential_of_winding hq hwind

/--
[fkQgt4CriticalFreeDiagonalRate_tendsto_gap_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4UnconditionalRateAssembly.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeDiagonalRate_tendsto_gap_of_winding_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hwind : FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q)) :
-- imply
  Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop (nhds (fkQgt4SixVertexGapRate q)) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeDiagonalRate_tendsto_gap_of_winding hq hwind

/--
[fkQgt4_firstOrder_of_winding_and_wiredPercolation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4UnconditionalRateAssembly.lean)
-/
@[path]
private lemma fkQgt4_firstOrder_of_winding_and_wiredPercolation_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hwind : FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q))
  (hWiredAlmostSure : let mu := ((FK.wiredInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) mu (percolationEvent 2) = 1) :
-- imply
  And (FK.IsFirstOrderTransition 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q)) (Ne (FK.freeInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q)) (FK.wiredInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q))) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_firstOrder_of_winding_and_wiredPercolation hq hwind hWiredAlmostSure


-- created on 2026-10-23
