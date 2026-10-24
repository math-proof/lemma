import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideCrossing
open Set StatMech StatMech.FrontierD


/--
[fkRectDevelopedRectangleHorizontalCrossingEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideCrossing.lean)
-/
@[path]
private lemma fkRectDevelopedRectangleHorizontalCrossingEvent_isIncreasing_eq
  {R : FKRectTorus}
  {placement : Nat}
  {a b c d : Int} :
-- imply
  IsIncreasing (fkRectDevelopedRectangleHorizontalCrossingEvent R placement a b c d) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedRectangleHorizontalCrossingEvent_isIncreasing R placement a b c d

/--
[fkRectDevelopedRectangleVerticalCrossingEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideCrossing.lean)
-/
@[path]
private lemma fkRectDevelopedRectangleVerticalCrossingEvent_isIncreasing_eq
  {R : FKRectTorus}
  {placement : Nat}
  {a b c d : Int} :
-- imply
  IsIncreasing (fkRectDevelopedRectangleVerticalCrossingEvent R placement a b c d) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedRectangleVerticalCrossingEvent_isIncreasing R placement a b c d

/--
[fkRectDevelopedRectangle_HVH_subset_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideCrossing.lean)
-/
@[path]
private lemma fkRectDevelopedRectangle_HVH_subset_horizontal_eq
  {R : FKRectTorus}
  {placement : Nat}
  {a m m' b c d : Int}
-- given
  (ham : a <= m)
  (hmm' : m <= m')
  (hm'b : m' <= b)
  (hamL : a < m')
  (hmbR : m < b)
  (hcd : c <= d) :
-- imply
  (fkRectDevelopedRectangleHorizontalCrossingEvent R placement a m' c d ∩ fkRectDevelopedRectangleVerticalCrossingEvent R placement m m' c d) ∩ fkRectDevelopedRectangleHorizontalCrossingEvent R placement m b c d ⊆ fkRectDevelopedRectangleHorizontalCrossingEvent R placement a b c d := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedRectangle_HVH_subset_horizontal R placement ham hmm' hm'b hamL hmbR hcd

/--
[fkRectCritical_developedRectangle_horizontalMass_ge_HVH](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideCrossing.lean)
-/
@[path]
private lemma fkRectCritical_developedRectangle_horizontalMass_ge_HVH_eq
  {R : FKRectTorus}
  {placement : Nat}
  {q : Real}
  {a m m' b c d : Int}
-- given
  (hq : 1 <= q)
  (ham : a <= m)
  (hmm' : m <= m')
  (hm'b : m' <= b)
  (hamL : a < m')
  (hmbR : m < b)
  (hcd : c <= d) :
-- imply
  fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R placement a m' c d) * fkRectCriticalEventMass R q (fkRectDevelopedRectangleVerticalCrossingEvent R placement m m' c d) * fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R placement m b c d) <= fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R placement a b c d) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedRectangle_horizontalMass_ge_HVH R placement hq ham hmm' hm'b hamL hmbR hcd

/--
[fkRectDevelopedRectangle_VHV_subset_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideCrossing.lean)
-/
@[path]
private lemma fkRectDevelopedRectangle_VHV_subset_vertical_eq
  {R : FKRectTorus}
  {placement : Nat}
  {a b c m m' d : Int}
-- given
  (hab : a <= b)
  (hcm : c <= m)
  (hmm' : m <= m')
  (hm'd : m' <= d)
  (hcm' : c < m')
  (hmd : m < d) :
-- imply
  (fkRectDevelopedRectangleVerticalCrossingEvent R placement a b c m' ∩ fkRectDevelopedRectangleHorizontalCrossingEvent R placement a b m m') ∩ fkRectDevelopedRectangleVerticalCrossingEvent R placement a b m d ⊆ fkRectDevelopedRectangleVerticalCrossingEvent R placement a b c d := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedRectangle_VHV_subset_vertical R placement hab hcm hmm' hm'd hcm' hmd

/--
[fkRectCritical_developedRectangle_verticalMass_ge_VHV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideCrossing.lean)
-/
@[path]
private lemma fkRectCritical_developedRectangle_verticalMass_ge_VHV_eq
  {R : FKRectTorus}
  {placement : Nat}
  {q : Real}
  {a b c m m' d : Int}
-- given
  (hq : 1 <= q)
  (hab : a <= b)
  (hcm : c <= m)
  (hmm' : m <= m')
  (hm'd : m' <= d)
  (hcm' : c < m')
  (hmd : m < d) :
-- imply
  fkRectCriticalEventMass R q (fkRectDevelopedRectangleVerticalCrossingEvent R placement a b c m') * fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R placement a b m m') * fkRectCriticalEventMass R q (fkRectDevelopedRectangleVerticalCrossingEvent R placement a b m d) <= fkRectCriticalEventMass R q (fkRectDevelopedRectangleVerticalCrossingEvent R placement a b c d) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedRectangle_verticalMass_ge_VHV R placement hq hab hcm hmm' hm'd hcm' hmd

/--
[fkRectCritical_developedThreeByOne_horizontalMass_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideCrossing.lean)
-/
@[path]
private lemma fkRectCritical_developedThreeByOne_horizontalMass_ge_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 0 < n)
  (hq : 1 <= q) :
-- imply
  fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 (2 * (n : Int)) 0 n) * fkRectCriticalEventMass R q (fkRectDevelopedRectangleVerticalCrossingEvent R n n (2 * (n : Int)) 0 n) * fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R n n (3 * (n : Int)) 0 n) <= fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 (3 * (n : Int)) 0 n) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedThreeByOne_horizontalMass_ge R n hn hq

/--
[fkRectCritical_developedOneByThree_verticalMass_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideCrossing.lean)
-/
@[path]
private lemma fkRectCritical_developedOneByThree_verticalMass_ge_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 0 < n)
  (hq : 1 <= q) :
-- imply
  fkRectCriticalEventMass R q (fkRectDevelopedRectangleVerticalCrossingEvent R n 0 n 0 (2 * (n : Int))) * fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 n n (2 * (n : Int))) * fkRectCriticalEventMass R q (fkRectDevelopedRectangleVerticalCrossingEvent R n 0 n n (3 * (n : Int))) <= fkRectCriticalEventMass R q (fkRectDevelopedRectangleVerticalCrossingEvent R n 0 n 0 (3 * (n : Int))) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedOneByThree_verticalMass_ge R n hn hq

/--
[fkRectCritical_developedThreeByThree_bottomTopHorizontalMass_mul_le_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideCrossing.lean)
-/
@[path]
private lemma fkRectCritical_developedThreeByThree_bottomTopHorizontalMass_mul_le_inter_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hq : 1 <= q) :
-- imply
  fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 (3 * (n : Int)) 0 n) * fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 (3 * (n : Int)) (2 * (n : Int)) (3 * (n : Int))) <= fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 (3 * (n : Int)) 0 n ∩ fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 (3 * (n : Int)) (2 * (n : Int)) (3 * (n : Int))) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedThreeByThree_bottomTopHorizontalMass_mul_le_inter R n hq

/--
[fkRectDevelopedSquareVertical_subset_threeByOneVertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideCrossing.lean)
-/
@[path]
private lemma fkRectDevelopedSquareVertical_subset_threeByOneVertical_eq
  {R : FKRectTorus}
  {n : Nat} :
-- imply
  fkRectDevelopedRectangleVerticalCrossingEvent R n 0 n 0 n ⊆ fkRectDevelopedRectangleVerticalCrossingEvent R n 0 (3 * (n : Int)) 0 n := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquareVertical_subset_threeByOneVertical R n

/--
[fkRectCritical_developedSquareVerticalMass_le_threeByOneVerticalMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideCrossing.lean)
-/
@[path]
private lemma fkRectCritical_developedSquareVerticalMass_le_threeByOneVerticalMass_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  fkRectCriticalEventMass R q (fkRectDevelopedRectangleVerticalCrossingEvent R n 0 n 0 n) <= fkRectCriticalEventMass R q (fkRectDevelopedRectangleVerticalCrossingEvent R n 0 (3 * (n : Int)) 0 n) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedSquareVerticalMass_le_threeByOneVerticalMass R n hq


-- created on 2026-10-23
