/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/Curve/Evaluation.lean -/


import Def.AlgebraicGeometry.Curve.Evaluation
import Lemma.Finsupp.Eval.eq.Prod_Pow
import Lemma.Finsupp.Eval0.eq.One
import Lemma.Finsupp.Eval_Single.eq.Pow
import Lemma.Finsupp.EvalAdd.eq.MulEvalS
import Lemma.Finsupp.Eval.eq.PowEval
open Finsupp


namespace CurveDivisor

variable {C G : Type*} [CommGroup G]

example (f : C → G) (D : CurveDivisor C) :
    eval f D = D.prod (fun P n ↦ f P ^ n) :=
  Eval.eq.Prod_Pow

example (f : C → G) : eval f (0 : CurveDivisor C) = 1 := by
  simp

example (f : C → G) (P : C) (n : ℤ) :
    eval f (Finsupp.single P n) = f P ^ n :=
  Eval_Single.eq.Pow

example (f : C → G) (D₁ D₂ : CurveDivisor C) :
    eval f (D₁ + D₂) = eval f D₁ * eval f D₂ :=
  EvalAdd.eq.MulEvalS

example (f : C → G) (n : ℤ) (D : CurveDivisor C) :
    eval f (n • D) = eval f D ^ n :=
  Eval.eq.PowEval

example (f : C → G) (P : C) :
    eval f (Finsupp.single P (2 : ℤ)) = f P ^ (2 : ℤ) :=
  Eval_Single.eq.Pow

example (f : C → G) (P : C) :
    eval f (Finsupp.single P (-1 : ℤ)) = (f P)⁻¹ := by
  rw [Eval_Single.eq.Pow, zpow_neg_one]

end CurveDivisor
