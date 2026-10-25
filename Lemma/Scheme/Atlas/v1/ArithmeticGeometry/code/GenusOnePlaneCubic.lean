import Mathlib
import sympy.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.GenusOnePlaneCubic
open MvPolynomial AlgebraicGeometry CategoryTheory Polynomial in


/--
[PlaneCubic.toSmoothProjectiveCurveOverField_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GenusOnePlaneCubic.lean)
-/
@[path]
private lemma toSmoothProjectiveCurveOverField_genus_eq
  [Field k]
  {F : PlaneCubic k} :
-- imply
  F.toSmoothProjectiveCurveOverField.genus = F.genus := by
-- proof
  apply PlaneCubic.toSmoothProjectiveCurveOverField_genus F

/--
[WeierstrassCurve.toPlaneCubic_hasRationalPoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GenusOnePlaneCubic.lean)
-/
@[path]
private lemma toPlaneCubic_hasRationalPoint_eq
  [Field k]
  {W : WeierstrassCurve k} :
-- imply
  W.toPlaneCubic.HasRationalPoint := by
-- proof
  apply WeierstrassCurve.toPlaneCubic_hasRationalPoint W

/--
[WeierstrassCurve.toPlaneCubic_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GenusOnePlaneCubic.lean)
-/
@[path]
private lemma toPlaneCubic_genus_eq
  [Field k]
  {W : WeierstrassCurve k}
-- given
  (_hW : W.IsElliptic) :
-- imply
  W.toPlaneCubic.genus = 1 := by
-- proof
  apply WeierstrassCurve.toPlaneCubic_genus W _hW


-- created on 2026-10-23
