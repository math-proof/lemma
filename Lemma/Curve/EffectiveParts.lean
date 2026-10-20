import Mathlib
import sympy.Basic
import sympy.atlas.AlgebraicGeometry.Curve.EffectiveParts
open CurveDivisor


/--
[divZeros_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/EffectiveParts.lean)
-/
@[path]
private lemma divZeros_apply_eq
  {D : CurveDivisor C}
  {P : C} :
-- imply
  divZeros D P = max (D P) 0 := by
-- proof
  apply CurveDivisor.divZeros_apply D P

/--
[divPoles_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/EffectiveParts.lean)
-/
@[path]
private lemma divPoles_apply_eq
  {D : CurveDivisor C}
  {P : C} :
-- imply
  divPoles D P = max (-(D P)) 0 := by
-- proof
  apply CurveDivisor.divPoles_apply D P

/--
[divZeros_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/EffectiveParts.lean)
-/
@[path]
private lemma divZeros_nonneg_eq
  {D : CurveDivisor C} :
-- imply
  0 ≤ divZeros D := by
-- proof
  apply CurveDivisor.divZeros_nonneg D

/--
[divPoles_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/EffectiveParts.lean)
-/
@[path]
private lemma divPoles_nonneg_eq
  {D : CurveDivisor C} :
-- imply
  0 ≤ divPoles D := by
-- proof
  apply CurveDivisor.divPoles_nonneg D

/--
[divZeros_sub_divPoles](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/EffectiveParts.lean)
-/
@[path]
private lemma divZeros_sub_divPoles_eq
  {D : CurveDivisor C} :
-- imply
  divZeros D - divPoles D = D := by
-- proof
  apply CurveDivisor.divZeros_sub_divPoles D


-- created on 2026-10-20
