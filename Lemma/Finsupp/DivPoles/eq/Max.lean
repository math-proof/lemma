import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.AlgebraicGeometry.Curve.EffectiveParts
open CurveDivisor


/--
[divPoles_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/EffectiveParts.lean)
-/
@[path]
private lemma main
  {D : CurveDivisor C}
  {P : C} :
-- imply
  divPoles D P = max (-(D P)) 0 :=
-- proof
  rfl


-- created on 2026-10-20
-- updated on 2026-10-26
