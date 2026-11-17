module

public import Mathlib
public import Def.AlgebraicGeometry.Curve.EffectiveParts

public section

open CurveDivisor


/--
[divZeros_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/EffectiveParts.lean)
-/
public theorem Finsupp.DivZeros.eq.Max0
  {D : CurveDivisor C}
  {P : C} :
-- imply
  divZeros D P = max (D P) 0 :=
-- proof
  rfl


-- created on 2026-10-20
-- updated on 2026-10-26
