module

public import Mathlib
public import Def.AlgebraicGeometry.Curve.Evaluation
public import Theorem.Finsupp.Eval.eq.Prod_Pow

public section

open CurveDivisor
open Finsupp


/--
[eval_single](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/Evaluation.lean)
-/
public theorem Finsupp.Eval_Single.eq.Pow
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
-- updated on 2026-10-26
