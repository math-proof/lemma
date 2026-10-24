import Mathlib
import sympy.Basic
import sympy.atlas.AlgebraicGeometry.Curve.EffectiveParts
open CurveDivisor


/--
[divZeros_sub_divPoles](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/EffectiveParts.lean)
-/
@[path]
private lemma main
  {D : CurveDivisor C} :
-- imply
  divZeros D - divPoles D = D := by
-- proof
  ext P
  exact posPart_sub_negPart (D P)


-- created on 2026-10-20
-- updated on 2026-10-24
