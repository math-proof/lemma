import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4CriticalFreeShellSummability
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierD


/--
[fkQgt4CriticalFreeSphereConnectionEvent_summable_of_ratePos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4CriticalFreeShellSummability.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeSphereConnectionEvent_summable_of_ratePos_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hpos : 0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq) :
-- imply
  Summable (fun n : Nat => ((FK.freeInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))).real (fkQgt4CriticalFreeSphereConnectionEvent n)) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeSphereConnectionEvent_summable_of_ratePos hq hpos

/--
[fkQgt4CriticalFreeSphereConnectionEvent_summable_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4CriticalFreeShellSummability.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeSphereConnectionEvent_summable_of_winding_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hwind : FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q)) :
-- imply
  Summable (fun n : Nat => ((FK.freeInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))).real (fkQgt4CriticalFreeSphereConnectionEvent n)) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeSphereConnectionEvent_summable_of_winding hq hwind

/--
[fkQgt4CriticalFreeSphereConnectionEvent_tsum_ne_top_of_ratePos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4CriticalFreeShellSummability.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeSphereConnectionEvent_tsum_ne_top_of_ratePos_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hpos : 0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq) :
-- imply
  (∑' n : Nat, ((FK.freeInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) (fkQgt4CriticalFreeSphereConnectionEvent n)) ≠ ⊤ := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeSphereConnectionEvent_tsum_ne_top_of_ratePos hq hpos

/--
[fkQgt4CriticalFreeSphereConnectionEvent_tsum_ne_top_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4CriticalFreeShellSummability.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeSphereConnectionEvent_tsum_ne_top_of_winding_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hwind : FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q)) :
-- imply
  (∑' n : Nat, ((FK.freeInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) (fkQgt4CriticalFreeSphereConnectionEvent n)) ≠ ⊤ := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeSphereConnectionEvent_tsum_ne_top_of_winding hq hwind

/--
[fkQgt4CriticalFreeSphereConnectionEvent_limsup_zero_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4CriticalFreeShellSummability.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeSphereConnectionEvent_limsup_zero_of_winding_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hwind : FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q)) :
-- imply
  ((FK.freeInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) (limsup fkQgt4CriticalFreeSphereConnectionEvent atTop) = 0 := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeSphereConnectionEvent_limsup_zero_of_winding hq hwind


-- created on 2026-10-23
