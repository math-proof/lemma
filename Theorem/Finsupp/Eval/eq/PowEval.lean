module

public import Mathlib
public import Def.AlgebraicGeometry.Curve.Evaluation

public section

open CurveDivisor


/--
[eval_zsmul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/Evaluation.lean)
-/
public theorem Finsupp.Eval.eq.PowEval
  [CommGroup G]
  {f : C → G}
  {n : ℤ}
  {D : CurveDivisor C} :
-- imply
  eval f (n • D) = eval f D ^ n := by
-- proof
  change evalMonoidHom f (Multiplicative.ofAdd D ^ n) =
    evalMonoidHom f (Multiplicative.ofAdd D) ^ n
  exact map_zpow _ _ _


-- created on 2026-10-20
-- updated on 2026-10-26
