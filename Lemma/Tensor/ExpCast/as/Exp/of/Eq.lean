import Lemma.Bool.SEq.is.EqCast.of.Eq
import sympy.tensor.functions
open Bool


@[main, cast]
private lemma main
  [Exp α]
-- given
  (h : s = s')
  (X : Tensor α s) :
-- imply
  exp (cast (congrArg (Tensor α) h) X) ≃ exp X := by
-- proof
  apply SEq.of.Eq_Cast
  .
    grind
  .
    assumption


-- created on 2025-11-29
