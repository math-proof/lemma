module

public import Mathlib
public import Def.AlgebraicGeometry.Curve.EffectiveParts

public section

open CurveDivisor


/--
[divZeros_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/EffectiveParts.lean)
-/
public theorem Finsupp.DivZeros.ge.Zero
  {D : CurveDivisor C} :
-- imply
  0 ≤ divZeros D :=
-- proof
  posPart_nonneg D


-- created on 2026-10-20
-- updated on 2026-10-26
