import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardHalfPlaneSegment
open StatMech StatMech.FrontierA


/--
[kw_openSegments_disjoint_of_cross_same_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardHalfPlaneSegment.lean)
-/
@[path]
private lemma kw_openSegments_disjoint_of_cross_same_sign_eq
  {A C X Y : ℂ}
-- given
  (hsign : (0 < kwComplexCross (C - A) (X - A) ∧ 0 < kwComplexCross (C - A) (Y - A)) ∨ (kwComplexCross (C - A) (X - A) < 0 ∧ kwComplexCross (C - A) (Y - A) < 0)) :
-- imply
  Disjoint {z : ℂ | Sbtw ℝ A z C} {z : ℂ | Sbtw ℝ X z Y} := by
-- proof
  apply StatMech.FrontierA.kw_openSegments_disjoint_of_cross_same_sign hsign

/--
[kw_segments_disjoint_of_cross_same_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardHalfPlaneSegment.lean)
-/
@[path]
private lemma kw_segments_disjoint_of_cross_same_sign_eq
  {A C X Y : ℂ}
-- given
  (hsign : (0 < kwComplexCross (C - A) (X - A) ∧ 0 < kwComplexCross (C - A) (Y - A)) ∨ (kwComplexCross (C - A) (X - A) < 0 ∧ kwComplexCross (C - A) (Y - A) < 0)) :
-- imply
  Disjoint (segment ℝ A C) (segment ℝ X Y) := by
-- proof
  apply StatMech.FrontierA.kw_segments_disjoint_of_cross_same_sign hsign

/--
[kw_cross_product_neg_of_openSegments_intersect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardHalfPlaneSegment.lean)
-/
@[path]
private lemma kw_cross_product_neg_of_openSegments_intersect_eq
  {A C X Y z : ℂ}
-- given
  (hzAC : Sbtw ℝ A z C)
  (hzXY : Sbtw ℝ X z Y)
  (hX : kwComplexCross (C - A) (X - A) ≠ 0)
  (hY : kwComplexCross (C - A) (Y - A) ≠ 0) :
-- imply
  kwComplexCross (C - A) (X - A) * kwComplexCross (C - A) (Y - A) < 0 := by
-- proof
  apply StatMech.FrontierA.kw_cross_product_neg_of_openSegments_intersect hzAC hzXY hX hY

/--
[kw_cross_right_eq_zero_of_openSegments_intersect_of_left_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardHalfPlaneSegment.lean)
-/
@[path]
private lemma kw_cross_right_eq_zero_of_openSegments_intersect_of_left_eq_zero_eq
  {A C X Y z : ℂ}
-- given
  (hzAC : Sbtw ℝ A z C)
  (hzXY : Sbtw ℝ X z Y)
  (hX : kwComplexCross (C - A) (X - A) = 0) :
-- imply
  kwComplexCross (C - A) (Y - A) = 0 := by
-- proof
  apply StatMech.FrontierA.kw_cross_right_eq_zero_of_openSegments_intersect_of_left_eq_zero hzAC hzXY hX

/--
[kw_cross_left_eq_zero_of_openSegments_intersect_of_right_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardHalfPlaneSegment.lean)
-/
@[path]
private lemma kw_cross_left_eq_zero_of_openSegments_intersect_of_right_eq_zero_eq
  {A C X Y z : ℂ}
-- given
  (hzAC : Sbtw ℝ A z C)
  (hzXY : Sbtw ℝ X z Y)
  (hY : kwComplexCross (C - A) (Y - A) = 0) :
-- imply
  kwComplexCross (C - A) (X - A) = 0 := by
-- proof
  apply StatMech.FrontierA.kw_cross_left_eq_zero_of_openSegments_intersect_of_right_eq_zero hzAC hzXY hY


-- created on 2026-10-23
