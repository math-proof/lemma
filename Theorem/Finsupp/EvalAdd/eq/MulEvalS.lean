module

public import Mathlib
public import Def.AlgebraicGeometry.Curve.Evaluation

public section

open CurveDivisor


/--
[eval_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/Evaluation.lean)
-/
public theorem Finsupp.EvalAdd.eq.MulEvalS
  [CommGroup G]
  {f : C → G}
  {D₁ D₂ : CurveDivisor C} :
-- imply
  eval f (D₁ + D₂) = eval f D₁ * eval f D₂ := by
-- proof
  change evalMonoidHom f (Multiplicative.ofAdd D₁ * Multiplicative.ofAdd D₂) =
    evalMonoidHom f (Multiplicative.ofAdd D₁) * evalMonoidHom f (Multiplicative.ofAdd D₂)
  exact map_mul _ _ _


-- created on 2026-10-20
-- updated on 2026-10-26
