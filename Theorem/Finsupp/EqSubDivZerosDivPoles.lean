module

public import Mathlib
public import Def.AlgebraicGeometry.Curve.EffectiveParts

public section

open CurveDivisor


/--
[divZeros_sub_divPoles](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/EffectiveParts.lean)
-/
public theorem Finsupp.EqSubDivZerosDivPoles
  {D : CurveDivisor C} :
-- imply
  divZeros D - divPoles D = D := by
-- proof
  ext P
  exact posPart_sub_negPart (D P)


-- created on 2026-10-20
-- updated on 2026-10-26
