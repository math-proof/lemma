import Mathlib
import sympy.Basic
import Def.AlgebraicGeometry.Curve.Evaluation
open CurveDivisor


/--
[eval_zsmul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/Evaluation.lean)
-/
@[path]
private lemma main
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
-- updated on 2026-10-24
