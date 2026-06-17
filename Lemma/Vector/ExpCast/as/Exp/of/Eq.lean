import Lemma.Bool.SEq.is.EqCast.of.Eq
import sympy.vector.functions
open Bool


@[main, cast]
private lemma main
  [Exp α]
-- given
  (h : n = n')
  (x : List.Vector α n) :
-- imply
  exp (cast (congrArg (List.Vector α) h) x) ≃ exp x := by
-- proof
  apply SEq.of.Eq_Cast
  .
    grind
  .
    assumption


-- created on 2025-11-29
