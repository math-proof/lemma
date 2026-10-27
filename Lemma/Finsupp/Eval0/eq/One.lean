import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.AlgebraicGeometry.Curve.Evaluation
open CurveDivisor


/--
[eval_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/Evaluation.lean)
-/
@[path]
private lemma main
  [CommGroup G]
  {f : C → G} :
-- imply
  eval f (0 : CurveDivisor C) = 1 := by
-- proof
  simp [eval]


-- created on 2026-10-20
-- updated on 2026-10-26
