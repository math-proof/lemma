import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKQgt4SquareWiredPercolation
open Filter MeasureTheory Set SimpleGraph StatMech StatMech.FrontierD


/--
[fci_faceDualConfig_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareWiredPercolation.lean)
-/
@[path]
private lemma fci_faceDualConfig_shift_eq
  {g : Multiplicative (Site 2)}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  fci_faceDualConfig (ConfigSpace.shift g omega) = ConfigSpace.shift g (fci_faceDualConfig omega) := by
-- proof
  apply StatMech.FrontierD.fci_faceDualConfig_shift g omega

/--
[fkQgt4CriticalFree_faceDual_originInfinite_pos_of_ratePos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareWiredPercolation.lean)
-/
@[path]
private lemma fkQgt4CriticalFree_faceDual_originInfinite_pos_of_ratePos_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hpos : 0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq) :
-- imply
  let mu := ((FK.freeInfiniteVolume 2 (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) 0 < mu.real (faceDualInfiniteAt (Percolation.origin 2)) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFree_faceDual_originInfinite_pos_of_ratePos hq hpos

/--
[fkQgt4CriticalFree_faceDual_originInfinite_pos_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareWiredPercolation.lean)
-/
@[path]
private lemma fkQgt4CriticalFree_faceDual_originInfinite_pos_of_winding_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hwind : FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q)) :
-- imply
  let mu := ((FK.freeInfiniteVolume 2 (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) 0 < mu.real (faceDualInfiniteAt (Percolation.origin 2)) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFree_faceDual_originInfinite_pos_of_winding hq hwind

/--
[fkQgt4CriticalWired_percolation_pos_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareWiredPercolation.lean)
-/
@[path]
private lemma fkQgt4CriticalWired_percolation_pos_of_winding_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hwind : FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q)) :
-- imply
  let mu := ((FK.wiredInfiniteVolume 2 (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) 0 < mu.real (Percolation.percolationEvent 2) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalWired_percolation_pos_of_winding hq hwind

/--
[fkQgt4CriticalWired_percolation_pos_of_ratePos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareWiredPercolation.lean)
-/
@[path]
private lemma fkQgt4CriticalWired_percolation_pos_of_ratePos_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hpos : 0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq) :
-- imply
  let mu := ((FK.wiredInfiniteVolume 2 (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) 0 < mu.real (Percolation.percolationEvent 2) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalWired_percolation_pos_of_ratePos hq hpos

/--
[fkQgt4_firstOrder_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareWiredPercolation.lean)
-/
@[path]
private lemma fkQgt4_firstOrder_of_winding_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hwind : FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q)) :
-- imply
  FK.IsFirstOrderTransition 2 (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_firstOrder_of_winding hq hwind


-- created on 2026-10-23
