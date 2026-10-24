import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectDevelopedAxisSource
open Set StatMech StatMech.FrontierD


/--
[fkRectCritical_connectedWithinLower_sq_le_reflectedCarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedAxisSource.lean)
-/
@[path]
private lemma fkRectCritical_connectedWithinLower_sq_le_reflectedCarrier_eq
  {R : FKRectTorus}
  {q a : Real}
  {S : Set R.Vertex}
  {x y : S}
-- given
  (hq : 1 ≤ q)
  (ha : 0 ≤ a)
  (hlower : a ≤ fkRectCriticalEventMass R q {omega | FKRectConnectedWithin R omega S x y}) :
-- imply
  a ^ 2 ≤ fkRectCriticalEventMass R q (fkRectReflectedCarrierConnectionEvent R S x y) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_connectedWithinLower_sq_le_reflectedCarrier R hq S x y ha hlower

/--
[fkRectDevelopedThreeByOneTorusCarrier_row_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedAxisSource.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOneTorusCarrier_row_bounds_eq
  {R : FKRectTorus}
  {n : Nat}
  {v : R.Vertex}
-- given
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hv : v ∈ fkRectDevelopedThreeByOneTorusCarrier R n) :
-- imply
  v.2.val ≤ 4 * n := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOneTorusCarrier_row_bounds R n hwidth hheight hv

/--
[fkRectQuarterTurn_developedThreeByOneCarrier_column_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedAxisSource.lean)
-/
@[path]
private lemma fkRectQuarterTurn_developedThreeByOneCarrier_column_bounds_eq
  {R : FKRectTorus}
  {n : Nat}
  {v : (fkRectQuarterTurnTorus R hH).Vertex}
-- given
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hH : 4 < R.height)
  (hv : v ∈ fkRectQuarterTurnSet R hH (fkRectDevelopedThreeByOneTorusCarrier R n)) :
-- imply
  v.1.val ≤ 2 * n := by
-- proof
  apply StatMech.FrontierD.fkRectQuarterTurn_developedThreeByOneCarrier_column_bounds R n hwidth hheight hH hv

/--
[fkRectQuarterTurn_developedThreeByOne_reflectedUnion_column_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedAxisSource.lean)
-/
@[path]
private lemma fkRectQuarterTurn_developedThreeByOne_reflectedUnion_column_bounds_eq
  {R : FKRectTorus}
  {n : Nat}
  {center : Nat}
  {v : (fkRectQuarterTurnTorus R hH).Vertex}
-- given
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hH : 4 < R.height)
  (hv : v ∈ fkRectQuarterTurnSet R hH (fkRectDevelopedThreeByOneTorusCarrier R n) ∪ fkRectDevelopedReflectionSet (fkRectQuarterTurnTorus R hH) center (fkRectQuarterTurnSet R hH (fkRectDevelopedThreeByOneTorusCarrier R n))) :
-- imply
  v.1.val ≤ 2 * n := by
-- proof
  apply StatMech.FrontierD.fkRectQuarterTurn_developedThreeByOne_reflectedUnion_column_bounds R n hwidth hheight hH center hv

/--
[fkRectQuarterTurn_row_span_of_column_span](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedAxisSource.lean)
-/
@[path]
private lemma fkRectQuarterTurn_row_span_of_column_span_eq
  {R : FKRectTorus}
  {n : Nat}
  {x y : R.Vertex}
-- given
  (hH : 4 < R.height)
  (hspan : (n : Int) ≤ 4 * |(y.1.val : Int) - x.1.val|) :
-- imply
  (n : Int) ≤ 2 * := by
-- proof
  apply StatMech.FrontierD.fkRectQuarterTurn_row_span_of_column_span R hH n x y hspan

/--
[fkRectCritical_developedThreeByOne_exists_axisSelectedWindingBlock_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedAxisSource.lean)
-/
@[path]
private lemma fkRectCritical_developedThreeByOne_exists_axisSelectedWindingBlock_ge_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 1 ≤ n)
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hq : 1 ≤ q) :
-- imply
  let hH : 4 < R.height := by omega let RT := fkRectQuarterTurnTorus R hH ∃ p ∈ fkRectDevelopedThreeByOneVerticalEndpointPairs n, let S := fkRectDevelopedThreeByOneTorusCarrier R n let x : S := fkRectDevelopedThreeByOneCarrierVertex R n p.1 let y : S := fkRectDevelopedThreeByOneCarrierVertex R n p.2 ((n : Int) ≤ 2 * |(y.1.2.val : Int) - x.1.2.val| ∧ fkRectDevelopedReflectedEndpointLower q n ≤ fkRectCriticalEventMass R q (fkRectReflectedCarrierConnectionEvent R S x y)) ∨ (let ST := fkRectQuarterTurnSet R hH S let xT : ST := fkRectQuarterTurnSetEquiv R hH S x let yT : ST := fkRectQuarterTurnSetEquiv R hH S y (n : Int) ≤ 2 * |(yT.1.2.val : Int) - xT.1.2.val| + 2 ∧ fkRectDevelopedReflectedEndpointLower q n ≤ fkRectCriticalEventMass RT q (fkRectReflectedCarrierConnectionEvent RT ST xT yT)) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedThreeByOne_exists_axisSelectedWindingBlock_ge R n hn hwidth hheight hq


-- created on 2026-10-23
