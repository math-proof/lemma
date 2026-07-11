import Lemma.Bool.SEqUFnS.of.SEq
import sympy.tensor.functions
open Bool


@[main]
private lemma main
  [Exp α]
  {X : Tensor α s}
  {Y : Tensor α s'}
-- given
  (h : X ≃ Y) :
-- imply
  exp X ≃ exp Y := by
-- proof
  apply SEqUFnS.of.SEq h


-- created on 2025-12-04
