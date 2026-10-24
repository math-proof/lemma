import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectDevelopedHardTransport
open StatMech StatMech.FrontierD


/--
[fkRectCritical_developedThreeByOne_horizontalMass_ge_of_twoByOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedHardTransport.lean)
-/
@[path]
private lemma fkRectCritical_developedThreeByOne_horizontalMass_ge_of_twoByOne_eq
  {R : FKRectTorus}
  {n : Nat}
  {q hardFloor squareFloor : Real}
-- given
  (hn : 0 < n)
  (hq : 1 <= q)
  (hhard : 0 <= hardFloor)
  (hsquare : 0 <= squareFloor)
  (hleft : hardFloor <= fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 (2 * (n : Int)) 0 n))
  (hmiddle : squareFloor <= fkRectCriticalEventMass R q (fkRectDevelopedRectangleVerticalCrossingEvent R n n (2 * (n : Int)) 0 n))
  (hright : hardFloor <= fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R n n (3 * (n : Int)) 0 n)) :
-- imply
  hardFloor * squareFloor * hardFloor <= fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 (3 * (n : Int)) 0 n) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedThreeByOne_horizontalMass_ge_of_twoByOne R n hn hq hhard hsquare hleft hmiddle hright

/--
[fkRectCritical_developedMiddleSquareVerticalMass_ge_of_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedHardTransport.lean)
-/
@[path]
private lemma fkRectCritical_developedMiddleSquareVerticalMass_ge_of_even_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 1 <= n)
  (hnEven : Even n)
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height)
  (hq : 1 <= q) :
-- imply
  1 / (1 + q) <= fkRectCriticalEventMass R q (fkRectDevelopedRectangleVerticalCrossingEvent R n n (2 * (n : Int)) 0 n) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedMiddleSquareVerticalMass_ge_of_even R n hn hnEven hwidth hheight hq

/--
[fkRectCritical_developedThreeByOne_horizontalMass_ge_of_even_twoByOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedHardTransport.lean)
-/
@[path]
private lemma fkRectCritical_developedThreeByOne_horizontalMass_ge_of_even_twoByOne_eq
  {R : FKRectTorus}
  {n : Nat}
  {q hardFloor : Real}
-- given
  (hn : 1 <= n)
  (hnEven : Even n)
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height)
  (hq : 1 <= q)
  (hhard : 0 <= hardFloor)
  (hleft : hardFloor <= fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 (2 * (n : Int)) 0 n))
  (hright : hardFloor <= fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R n n (3 * (n : Int)) 0 n)) :
-- imply
  hardFloor ^ 2 / (1 + q) <= fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 (3 * (n : Int)) 0 n) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedThreeByOne_horizontalMass_ge_of_even_twoByOne R n hn hnEven hwidth hheight hq hhard hleft hright


-- created on 2026-10-23
