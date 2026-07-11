import Lemma.Bool.SEqUFnS.of.SEq
import sympy.vector.functions
open Bool


@[main]
private lemma main
  [Exp α]
  {x : List.Vector α n}
  {y : List.Vector α n'}
-- given
  (h : x ≃ y) :
-- imply
  exp x ≃ exp y := by
-- proof
  apply SEqUFnS.of.SEq h


-- created on 2025-12-04
