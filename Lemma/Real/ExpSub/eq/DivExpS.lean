import sympy.functions.elementary.exponential
import Lemma.Int.Sub.eq.Add_Neg
import Lemma.Algebra.Div.eq.Mul_Inv
open Algebra Int


@[main]
private lemma main
  [Exp R]
  {a b : R} :
-- imply
  exp (a - b) = exp a / exp b := by
-- proof
  rw [Sub.eq.Add_Neg]
  rw [Exp.exp_add]
  rw [Exp.exp_neg]
  rw [Div.eq.Mul_Inv]


-- created on 2025-10-04
