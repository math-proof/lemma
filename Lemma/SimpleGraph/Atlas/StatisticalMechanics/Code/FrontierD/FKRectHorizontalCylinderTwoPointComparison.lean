import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderTwoPointComparison.Part4
open MeasureTheory SimpleGraph StatMech StatMech.FrontierD


/--
[fkQgt4CriticalFree_infiniteTwoPointReal_eq_displacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTwoPointComparison.lean)
-/
@[path]
private lemma fkQgt4CriticalFree_infiniteTwoPointReal_eq_displacement_eq
  {q : Real}
  {x y : Site 2}
-- given
  (hq : 4 < q) :
-- imply
  FK.infiniteTwoPointReal (fkQgt4CriticalFreeMeasure hq : Measure (ConfigSpace (Sym2 (Site 2)))) x y = fkQgt4CriticalFreeTwoPoint hq (y - x) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFree_infiniteTwoPointReal_eq_displacement hq x y

/--
[fkQgt4CriticalFree_boxConnEvent_le_displacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTwoPointComparison.lean)
-/
@[path]
private lemma fkQgt4CriticalFree_boxConnEvent_le_displacement_eq
  {q : Real}
  {radius : Nat}
  {x y : FK.boxVerts 2 radius}
-- given
  (hq : 4 < q) :
-- imply
  ((fkQgt4CriticalFreeMeasure hq : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))).real (FK.boxConnEvent 2 radius x y) <= fkQgt4CriticalFreeTwoPoint hq (y.1 - x.1) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFree_boxConnEvent_le_displacement hq radius x y

/--
[fkRectHorizontalCylinder_displacement_add_correction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTwoPointComparison.lean)
-/
@[path]
private lemma fkRectHorizontalCylinder_displacement_add_correction_eq
  {dx : Int}
-- given
  (height : Nat) :
-- imply
  fkRectHorizontalCylinderLiftedDisplacement dx height + fkRectHorizontalCylinderCorrection dx = fkRectHorizontalCylinderVerticalDisplacement height := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinder_displacement_add_correction dx height

/--
[fkQgt4CriticalFreeTwoPoint_horizontalCylinder_mul_correction_le_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTwoPointComparison.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeTwoPoint_horizontalCylinder_mul_correction_le_vertical_eq
  {q : Real}
  {dx : Int}
-- given
  (hq : 4 < q)
  (height : Nat) :
-- imply
  fkQgt4CriticalFreeTwoPoint hq (fkRectHorizontalCylinderLiftedDisplacement dx height) * fkQgt4CriticalFreeTwoPoint hq (fkRectHorizontalCylinderCorrection dx) <= fkQgt4CriticalFreeTwoPoint hq (fkRectHorizontalCylinderVerticalDisplacement height) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeTwoPoint_horizontalCylinder_mul_correction_le_vertical hq dx height

/--
[fkQgt4CriticalFreeTwoPoint_horizontalCylinder_le_vertical_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTwoPointComparison.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeTwoPoint_horizontalCylinder_le_vertical_div_eq
  {q : Real}
  {dx : Int}
-- given
  (hq : 4 < q)
  (height : Nat) :
-- imply
  fkQgt4CriticalFreeTwoPoint hq (fkRectHorizontalCylinderLiftedDisplacement dx height) <= fkQgt4CriticalFreeTwoPoint hq (fkRectHorizontalCylinderVerticalDisplacement height) / fkQgt4CriticalFreeTwoPoint hq (fkRectHorizontalCylinderCorrection dx) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeTwoPoint_horizontalCylinder_le_vertical_div hq dx height

/--
[fkRectHorizontalCylinderCorrectionFloor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTwoPointComparison.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderCorrectionFloor_pos_eq
  {q : Real}
  {width : Nat}
-- given
  (hq : 4 < q) :
-- imply
  0 < fkRectHorizontalCylinderCorrectionFloor hq width := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderCorrectionFloor_pos hq width

/--
[fkRectHorizontalCylinderTwoPointFactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTwoPointComparison.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderTwoPointFactor_pos_eq
  {q : Real}
  {width : Nat}
-- given
  (hq : 4 < q) :
-- imply
  0 < fkRectHorizontalCylinderTwoPointFactor hq width := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderTwoPointFactor_pos hq width

/--
[fkRectHorizontalCylinderCorrectionFloor_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTwoPointComparison.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderCorrectionFloor_le_eq
  {q : Real}
  {width : Nat}
  {dx : Int}
-- given
  (hq : 4 < q)
  (hdx : dx.natAbs <= width) :
-- imply
  fkRectHorizontalCylinderCorrectionFloor hq width <= fkQgt4CriticalFreeTwoPoint hq (fkRectHorizontalCylinderCorrection dx) := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderCorrectionFloor_le hq hdx

/--
[fkQgt4CriticalFreeTwoPoint_horizontalCylinder_le_vertical_div_floor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTwoPointComparison.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeTwoPoint_horizontalCylinder_le_vertical_div_floor_eq
  {q : Real}
  {width : Nat}
  {dx : Int}
-- given
  (hq : 4 < q)
  (hdx : dx.natAbs <= width)
  (height : Nat) :
-- imply
  fkQgt4CriticalFreeTwoPoint hq (fkRectHorizontalCylinderLiftedDisplacement dx height) <= fkQgt4CriticalFreeTwoPoint hq (fkRectHorizontalCylinderVerticalDisplacement height) / fkRectHorizontalCylinderCorrectionFloor hq width := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeTwoPoint_horizontalCylinder_le_vertical_div_floor hq hdx height

/--
[fkQgt4CriticalFreeTwoPoint_horizontalCylinder_le_factor_mul_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTwoPointComparison.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeTwoPoint_horizontalCylinder_le_factor_mul_vertical_eq
  {q : Real}
  {width : Nat}
  {dx : Int}
-- given
  (hq : 4 < q)
  (hdx : dx.natAbs <= width)
  (height : Nat) :
-- imply
  fkQgt4CriticalFreeTwoPoint hq (fkRectHorizontalCylinderLiftedDisplacement dx height) <= fkRectHorizontalCylinderTwoPointFactor hq width * fkQgt4CriticalFreeTwoPoint hq (fkRectHorizontalCylinderVerticalDisplacement height) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeTwoPoint_horizontalCylinder_le_factor_mul_vertical hq hdx height

/--
[fkQgt4CriticalFree_boxConnEvent_le_vertical_div_floor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTwoPointComparison.lean)
-/
@[path]
private lemma fkQgt4CriticalFree_boxConnEvent_le_vertical_div_floor_eq
  {q : Real}
  {radius : Nat}
  {x y : FK.boxVerts 2 radius}
  {width height : Nat}
  {dx : Int}
-- given
  (hq : 4 < q)
  (hdisp : y.1 - x.1 = fkRectHorizontalCylinderLiftedDisplacement dx height)
  (hdx : dx.natAbs <= width) :
-- imply
  ((fkQgt4CriticalFreeMeasure hq : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))).real (FK.boxConnEvent 2 radius x y) <= fkQgt4CriticalFreeTwoPoint hq (fkRectHorizontalCylinderVerticalDisplacement height) / fkRectHorizontalCylinderCorrectionFloor hq width := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFree_boxConnEvent_le_vertical_div_floor hq radius x y hdisp hdx

/--
[fkQgt4CriticalFree_boxConnEvent_le_factor_mul_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTwoPointComparison.lean)
-/
@[path]
private lemma fkQgt4CriticalFree_boxConnEvent_le_factor_mul_vertical_eq
  {q : Real}
  {radius : Nat}
  {x y : FK.boxVerts 2 radius}
  {width height : Nat}
  {dx : Int}
-- given
  (hq : 4 < q)
  (hdisp : y.1 - x.1 = fkRectHorizontalCylinderLiftedDisplacement dx height)
  (hdx : dx.natAbs <= width) :
-- imply
  ((fkQgt4CriticalFreeMeasure hq : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))).real (FK.boxConnEvent 2 radius x y) <= fkRectHorizontalCylinderTwoPointFactor hq width * fkQgt4CriticalFreeTwoPoint hq (fkRectHorizontalCylinderVerticalDisplacement height) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFree_boxConnEvent_le_factor_mul_vertical hq radius x y hdisp hdx


-- created on 2026-10-23
