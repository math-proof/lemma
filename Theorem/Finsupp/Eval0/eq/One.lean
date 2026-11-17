module

public import Mathlib
public import Def.AlgebraicGeometry.Curve.Evaluation

public section

open CurveDivisor


/--
[eval_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/Evaluation.lean)
-/
public theorem Finsupp.Eval0.eq.One
  [CommGroup G]
  {f : C → G} :
-- imply
  eval f (0 : CurveDivisor C) = 1 := by
-- proof
  simp [eval]


-- created on 2026-10-20
-- updated on 2026-10-26
