import sympy.tensor.Basic
import sympy.Basic
import sympy.tensor.functions


@[main]
private lemma main
  [Exp α]
-- given
  (h : s = s')
  (X : Tensor α s) :
-- imply
  have h := congrArg (Tensor α) h
  exp (cast h X) = cast h (exp X) := by
-- proof
  grind


-- created on 2025-11-29
