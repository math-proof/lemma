import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedEndpointRate.Part2
open Filter Topology StatMech StatMech.FrontierD


/--
[fkRectDevelopedReflectedEndpointLowerOf_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointRate.lean)
-/
@[path]
private lemma fkRectDevelopedReflectedEndpointLowerOf_pos_eq
  {crossingFloor : Real}
  {n : Nat}
-- given
  (hcrossingFloor : 0 < crossingFloor) :
-- imply
  0 < fkRectDevelopedReflectedEndpointLowerOf crossingFloor n := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedReflectedEndpointLowerOf_pos hcrossingFloor n

/--
[fkRectDevelopedReflectedEndpointLower_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointRate.lean)
-/
@[path]
private lemma fkRectDevelopedReflectedEndpointLower_pos_eq
  {q : Real}
  {n : Nat}
-- given
  (hq : 1 ≤ q) :
-- imply
  0 < fkRectDevelopedReflectedEndpointLower q n := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedReflectedEndpointLower_pos hq n

/--
[fkRectDevelopedReflectedEndpointLowerOf_negLogRate_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointRate.lean)
-/
@[path]
private lemma fkRectDevelopedReflectedEndpointLowerOf_negLogRate_tendsto_zero_eq
  {crossingFloor : Real}
-- given
  (hcrossingFloor : 0 < crossingFloor) :
-- imply
  Tendsto (fun n => -Real.log (fkRectDevelopedReflectedEndpointLowerOf crossingFloor n) / (2 * (n + 1) : Real)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedReflectedEndpointLowerOf_negLogRate_tendsto_zero hcrossingFloor

/--
[fkRectDevelopedReflectedEndpointLower_negLogRate_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointRate.lean)
-/
@[path]
private lemma fkRectDevelopedReflectedEndpointLower_negLogRate_tendsto_zero_eq
  {q : Real}
-- given
  (hq : 1 ≤ q) :
-- imply
  Tendsto (fun n => -Real.log (fkRectDevelopedReflectedEndpointLower q n) / (2 * (n + 1) : Real)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedReflectedEndpointLower_negLogRate_tendsto_zero hq


-- created on 2026-10-23
