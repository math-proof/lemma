import sympy.Basic
import sympy.tensor.Basic
import sympy.tensor.functions


@[main]
private lemma main
  [Exp α]
-- given
  (h : n = n')
  (x : List.Vector α n) :
-- imply
  have h := congrArg (List.Vector α) h
  exp (cast h x) = cast h (exp x) := by
-- proof
  grind


-- created on 2025-11-29
