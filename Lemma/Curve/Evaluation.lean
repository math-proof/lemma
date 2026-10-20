import Mathlib
import sympy.Basic
import sympy.atlas.AlgebraicGeometry.Curve.Evaluation
open CurveDivisor


/--
[eval_eq_prod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/Evaluation.lean)
-/
@[path]
private lemma eval_eq_prod_eq
  [CommGroup G]
  {f : C → G}
  {D : CurveDivisor C} :
-- imply
  eval f D = D.prod (fun P n ↦ f P ^ n) := by
-- proof
  apply CurveDivisor.eval_eq_prod f D

/--
[eval_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/Evaluation.lean)
-/
@[path]
private lemma eval_zero_eq
  [CommGroup G]
  {f : C → G} :
-- imply
  eval f (0 : CurveDivisor C) = 1 := by
-- proof
  apply CurveDivisor.eval_zero f

/--
[eval_single](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/Evaluation.lean)
-/
@[path]
private lemma eval_single_eq
  [CommGroup G]
  {f : C → G}
  {P : C}
  {n : ℤ} :
-- imply
  eval f (Finsupp.single P n) = f P ^ n := by
-- proof
  apply CurveDivisor.eval_single f P n

/--
[eval_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/Evaluation.lean)
-/
@[path]
private lemma eval_add_eq
  [CommGroup G]
  {f : C → G}
  {D₁ D₂ : CurveDivisor C} :
-- imply
  eval f (D₁ + D₂) = eval f D₁ * eval f D₂ := by
-- proof
  apply CurveDivisor.eval_add f D₁ D₂

/--
[eval_zsmul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/Evaluation.lean)
-/
@[path]
private lemma eval_zsmul_eq
  [CommGroup G]
  {f : C → G}
  {n : ℤ}
  {D : CurveDivisor C} :
-- imply
  eval f (n • D) = eval f D ^ n := by
-- proof
  apply CurveDivisor.eval_zsmul f n D


-- created on 2026-10-20
