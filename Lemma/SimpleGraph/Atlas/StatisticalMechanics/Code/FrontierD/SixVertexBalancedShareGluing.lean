import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBalancedShareGluing
open Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexDoubledBalancedShare_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedShareGluing.lean)
-/
@[path]
private lemma sixVertexDoubledBalancedShare_lower_eq
  {N M : Nat}
  {c : Real}
-- given
  (hN : 0 < N)
  (hM : 0 < M)
  (hc : 0 <= c) :
-- imply
  sixVertexRectangleToroidalPartitionSum N M c ^ 4 / ((2 : Real) ^ (4 * (N + M)) * sixVertexRectangleToroidalPartitionSum (N + N) (M + M) c) <= sixVertexDoubledBalancedShare N M c := by
-- proof
  apply StatMech.FrontierD.sixVertexDoubledBalancedShare_lower hN hM hc

/--
[sixVertexDoubledBalancedShare_negLog_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedShareGluing.lean)
-/
@[path]
private lemma sixVertexDoubledBalancedShare_negLog_le_eq
  {N M : Nat}
  {c : Real}
-- given
  (hN : 0 < N)
  (hM : 0 < M)
  (hc : 0 <= c) :
-- imply
  -Real.log (sixVertexDoubledBalancedShare N M c) <= Real.log (sixVertexRectangleToroidalPartitionSum (N + N) (M + M) c) - 4 * Real.log (sixVertexRectangleToroidalPartitionSum N M c) + (4 * (N + M) : Nat) * Real.log 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexDoubledBalancedShare_negLog_le hN hM hc

/--
[fkRectBalancedSectorShare_eq_doubledBalancedShare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedShareGluing.lean)
-/
@[path]
private lemma fkRectBalancedSectorShare_eq_doubledBalancedShare_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  fkRectBalancedSectorShare R q = sixVertexDoubledBalancedShare R.width (R.height / 2) (fkQgt4SixVertexWeight q) := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedSectorShare_eq_doubledBalancedShare R hq

/--
[fkRectBalancedSectorShare_lower_of_fourCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedShareGluing.lean)
-/
@[path]
private lemma fkRectBalancedSectorShare_lower_of_fourCopy_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  sixVertexRectangleToroidalPartitionSum R.width (R.height / 2) (fkQgt4SixVertexWeight q) ^ 4 / ((2 : Real) ^ (4 * (R.width + R.height / 2)) * sixVertexRectangleToroidalPartitionSum (R.width + R.width) (R.height / 2 + R.height / 2) (fkQgt4SixVertexWeight q)) <= fkRectBalancedSectorShare R q := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedSectorShare_lower_of_fourCopy R hq

/--
[fkRectBalancedSectorShare_negLog_le_fourCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedShareGluing.lean)
-/
@[path]
private lemma fkRectBalancedSectorShare_negLog_le_fourCopy_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  -Real.log (fkRectBalancedSectorShare R q) <= Real.log (sixVertexRectangleToroidalPartitionSum (R.width + R.width) (R.height / 2 + R.height / 2) (fkQgt4SixVertexWeight q)) - 4 * Real.log (sixVertexRectangleToroidalPartitionSum R.width (R.height / 2) (fkQgt4SixVertexWeight q)) + (4 * (R.width + R.height / 2) : Nat) * Real.log 2 := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedSectorShare_negLog_le_fourCopy R hq

/--
[fkRectBalancedNormalization_negLog_le_all_add_fourCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedShareGluing.lean)
-/
@[path]
private lemma fkRectBalancedNormalization_negLog_le_all_add_fourCopy_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  -Real.log (fkRectBalancedSectorNormalization R q) <= -Real.log (fkRectAllSectorNormalization R q) + (Real.log (sixVertexRectangleToroidalPartitionSum (R.width + R.width) (R.height / 2 + R.height / 2) (fkQgt4SixVertexWeight q)) - 4 * Real.log (sixVertexRectangleToroidalPartitionSum R.width (R.height / 2) (fkQgt4SixVertexWeight q)) + (4 * (R.width + R.height / 2) : Nat) * Real.log 2) := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedNormalization_negLog_le_all_add_fourCopy R hq

/--
[fkRectBalancedSectorShare_negLog_le_fourCopyCost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedShareGluing.lean)
-/
@[path]
private lemma fkRectBalancedSectorShare_negLog_le_fourCopyCost_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  -Real.log (fkRectBalancedSectorShare R q) <= fkRectFourCopyShareCost R q := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedSectorShare_negLog_le_fourCopyCost R hq

/--
[tendsto_balancedShare_negLog_div_height_zero_of_fourCopyCost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedShareGluing.lean)
-/
@[path]
private lemma tendsto_balancedShare_negLog_div_height_zero_of_fourCopyCost_eq
  {q : Real}
-- given
  (R : Nat -> FKRectTorus)
  (hq : 4 < q)
  (hcost : Tendsto (fun n => fkRectFourCopyShareCost (R n) q / (R n).height) atTop (nhds 0)) :
-- imply
  Tendsto (fun n => -Real.log (fkRectBalancedSectorShare (R n) q) / (R n).height) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_balancedShare_negLog_div_height_zero_of_fourCopyCost R hq hcost

/--
[tendsto_balancedNormalization_negLog_div_height_zero_of_all_and_fourCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedShareGluing.lean)
-/
@[path]
private lemma tendsto_balancedNormalization_negLog_div_height_zero_of_all_and_fourCopy_eq
  {q : Real}
-- given
  (R : Nat -> FKRectTorus)
  (hq : 4 < q)
  (hall : Tendsto (fun n => -Real.log (fkRectAllSectorNormalization (R n) q) / (R n).height) atTop (nhds 0))
  (hcost : Tendsto (fun n => fkRectFourCopyShareCost (R n) q / (R n).height) atTop (nhds 0)) :
-- imply
  Tendsto (fun n => -Real.log (fkRectBalancedSectorNormalization (R n) q) / (R n).height) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_balancedNormalization_negLog_div_height_zero_of_all_and_fourCopy R hq hall hcost


-- created on 2026-10-23
