module

public import Mathlib
public import Def.AlgebraicGeometry.Curve.Evaluation

public section

open CurveDivisor


/--
[eval_eq_prod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/Evaluation.lean)
-/
public theorem Finsupp.Eval.eq.Prod_Pow
  [CommGroup G]
  {f : C → G}
  {D : CurveDivisor C} :
-- imply
  eval f D = D.prod (fun P n ↦ f P ^ n) :=
-- proof
  rfl


-- created on 2026-10-20
-- updated on 2026-10-26
