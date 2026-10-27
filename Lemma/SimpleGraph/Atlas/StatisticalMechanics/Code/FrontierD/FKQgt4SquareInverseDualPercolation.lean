import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareInverseDualPercolation
open Filter MeasureTheory Set SimpleGraph StatMech StatMech.FrontierD


/--
[inverseDual_allFinite_subset_axisAnchored_limsup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareInverseDualPercolation.lean)
-/
@[path]
private lemma inverseDual_allFinite_subset_axisAnchored_limsup_eq :
-- imply
  {omega : ConfigSpace (Sym2 (Site 2)) | ∀ x : Site 2, (cluster 2 (inverseFaceDualConfig omega) x).Finite} ⊆ limsup fkQgt4AxisAnchoredSphereConnectionEvent atTop := by
-- proof
  apply StatMech.FrontierD.inverseDual_allFinite_subset_axisAnchored_limsup

/--
[fkQgt4AxisAnchoredSphereConnectionEvent_tsum_ne_top_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareInverseDualPercolation.lean)
-/
@[path]
private lemma fkQgt4AxisAnchoredSphereConnectionEvent_tsum_ne_top_of_winding_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hwind : FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q)) :
-- imply
  (∑' n : Nat, ((FK.freeInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) (fkQgt4AxisAnchoredSphereConnectionEvent n)) ≠ ⊤ := by
-- proof
  apply StatMech.FrontierD.fkQgt4AxisAnchoredSphereConnectionEvent_tsum_ne_top_of_winding hq hwind

/--
[fkQgt4AxisAnchoredSphereConnectionEvent_limsup_zero_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareInverseDualPercolation.lean)
-/
@[path]
private lemma fkQgt4AxisAnchoredSphereConnectionEvent_limsup_zero_of_winding_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hwind : FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q)) :
-- imply
  ((FK.freeInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) (limsup fkQgt4AxisAnchoredSphereConnectionEvent atTop) = 0 := by
-- proof
  apply StatMech.FrontierD.fkQgt4AxisAnchoredSphereConnectionEvent_limsup_zero_of_winding hq hwind

/--
[fkQgt4CriticalFree_inverseDual_hasInfiniteCluster_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareInverseDualPercolation.lean)
-/
@[path]
private lemma fkQgt4CriticalFree_inverseDual_hasInfiniteCluster_of_winding_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hwind : FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q)) :
-- imply
  let mu := ((FK.freeInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) mu {omega | ∃ x : Site 2, (cluster 2 (inverseFaceDualConfig omega) x).Infinite} = 1 := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFree_inverseDual_hasInfiniteCluster_of_winding hq hwind


-- created on 2026-10-23
