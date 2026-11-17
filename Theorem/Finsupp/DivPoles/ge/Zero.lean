module

public import Mathlib
public import Def.AlgebraicGeometry.Curve.EffectiveParts

public section

open CurveDivisor


/--
[divPoles_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/EffectiveParts.lean)
-/
public theorem Finsupp.DivPoles.ge.Zero
  {D : CurveDivisor C} :
-- imply
  0 ≤ divPoles D :=
-- proof
  negPart_nonneg D


-- created on 2026-10-20
-- updated on 2026-10-26
