import Mathlib
import sympy.Basic
import sympy.atlas.AlgebraicGeometry.Curve.Evaluation
open CurveDivisor


/--
[eval_eq_prod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/Evaluation.lean)
-/
@[path]
private lemma main
  [CommGroup G]
  {f : C → G}
  {D : CurveDivisor C} :
-- imply
  eval f D = D.prod (fun P n ↦ f P ^ n) :=
-- proof
  rfl


-- created on 2026-10-20
-- updated on 2026-10-24
