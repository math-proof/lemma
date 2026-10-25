import Mathlib
import sympy.Basic
import Def.AlgebraicGeometry.Curve.EffectiveParts
open CurveDivisor


/--
[divPoles_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/EffectiveParts.lean)
-/
@[path]
private lemma main
  {D : CurveDivisor C} :
-- imply
  0 ≤ divPoles D :=
-- proof
  negPart_nonneg D


-- created on 2026-10-20
-- updated on 2026-10-24
