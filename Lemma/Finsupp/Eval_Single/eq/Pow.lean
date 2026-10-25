import Mathlib
import sympy.Basic
import Def.AlgebraicGeometry.Curve.Evaluation
import Lemma.Finsupp.Eval.eq.Prod_Pow
open CurveDivisor
open Finsupp


/--
[eval_single](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/Evaluation.lean)
-/
@[path]
private lemma main
  [CommGroup G]
  {f : C → G}
  {P : C}
  {n : ℤ} :
-- imply
  eval f (Finsupp.single P n) = f P ^ n := by
-- proof
  rw [Eval.eq.Prod_Pow]
  exact Finsupp.prod_single_index (zpow_zero (f P))


-- created on 2026-10-20
-- updated on 2026-10-24
